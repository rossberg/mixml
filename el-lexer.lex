(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

open Tokens

(* Types to match structure LEXER.UserDeclaration *)
type ('a,'b) token = ('a,'b) Tokens.token
type pos           = EL.pos
type svalue        = Tokens.svalue
type lexresult     = (svalue, pos) token

(* Handling lines and nested comments *)
val line = ref 1
val lines = ref [0]
val nesting = ref 0
val comments = ref [] : int list ref

fun newline yypos =
    (line := !line+1; lines := (yypos+1) :: !lines)
fun nest yypos =
    (nesting := !nesting+1; comments := yypos :: !comments)
fun unnest() =
    (nesting := !nesting-1; comments := List.tl(!comments))

fun lineColumn pos = lineColumn'(pos, !line, !lines)
and lineColumn'(pos, line, []) = (line, pos)
  | lineColumn'(pos, line, p::ps) =
    if pos >= p then (line, pos-p) else lineColumn'(pos, line-1, ps)

(*
val newline = fn pos =>
    (
        newline pos;
        print("[newline "^Int.toString(pos+1)^"]")
    )
val lineColumn = fn pos =>
    let
        val (l, c) = lineColumn pos
    in
        print("[token "^ Int.toString pos ^" -> "^Int.toString l^"."^Int.toString c^"]");
        (l, c)
    end
*)

fun toRegion(yypos, yytext) =
    let
        val left = yypos
        val right = left + String.size yytext
    in
        (lineColumn left, lineColumn right)
    end

fun eof() =
    let
        val lastLine = lineColumn(List.hd(!lines))  (* we ensure that last line is always empty *)
    in
        if !nesting = 0
        then Tokens.EOF(lastLine, lastLine)
        else raise EL.Error({l=lineColumn(List.hd(!comments)), r=lastLine}, "unclosed comment")
    end

(* Some helpers to create tokens *)
open Tokens

fun token(TOKEN, yypos, yytext) =
    TOKEN(toRegion(yypos, yytext))

fun tokenOf(TOKEN, toVal, yypos, yytext) =
    let
        val (l, r) = toRegion(yypos, yytext)
    in
        TOKEN(toVal yytext, l, r)
    end

fun error(yypos, yytext, s) =
    let
        val (l, r) = toRegion(yypos, yytext)
    in
        raise EL.Error({l=l, r=r}, s)
    end

fun invalid(yypos, yytext) =
    let
        val s = "invalid character `" ^ String.toString yytext ^ "'"
    in
        error(yypos, yytext, s)
    end

(* Convert identifiers *)
fun toId s = s

(* Convert constants *)
fun toInt s     = valOf(Int.fromString s)
fun toHexInt s  = valOf(StringCvt.scanString (Int.scan StringCvt.HEX) (String.substring(s, 2, String.size s-2)))
fun toReal s    = valOf(Real.fromString s)
fun toString s  = valOf(String.fromString(String.substring(s, 1, String.size s-2)))
fun toChar s    = valOf(Char.fromString(String.substring(s, 2, String.size s-3)))

%%


%header(functor LexerFn(structure Tokens : Parser_TOKENS));
%s COMMENT LCOMMENT;
%full

formatting = [\ \t\011\012\013]+;
letter     = [A-Za-z];
symbol     = [-!%&$#+/:<=>?@\\~`|*^];
digit      = [0-9];
hexdigit   = [0-9a-fA-F];

posdecint  = {digit}+;
poshexint  = "0x"{hexdigit}+;
negdecint  = "~"{posdecint};
neghexint  = "~"{poshexint};
decint     = {posdecint} | {negdecint};
hexint     = {poshexint} | {neghexint};

exp        = "E" | "e";
real       = ({decint}"."{digit}+ ({exp}{decint})?) | ({decint}{exp}{decint});

alpha      = {letter}({letter} | {digit} | [_'])*;
symbol     = {symbol}+;
id         = {alpha} | {symbol};
typvar     = "'"({letter} | {digit} | [_'])*;

printable  = [^\000-\032"\127\\];
escape     = "\\a" | "\\b" | "\\t" | "\\n" | "\\v" | "\\f" | "\\r" |
            ("\\^"[@-_])  | ("\\"{digit}{3})  | ("\\u"{hexdigit}{4}) |
            "\\\"" | "\\\\";
gap        = ("\\"{formatting}"\\");
stringchar = {printable} | " " | {escape};
string     = "\""({stringchar} | {gap})*"\"";
char       = "#\""{gap}*{stringchar}{gap}*"\"";

%%

<INITIAL>{formatting} => ( continue() );
<INITIAL>"\n" => ( newline yypos; continue() );

<INITIAL>"!"  => ( token(BANG,      yypos, yytext) );
<INITIAL>"@"  => ( token(AT,        yypos, yytext) );
<INITIAL>"+"  => ( token(PLUS,      yypos, yytext) );
<INITIAL>"++" => ( token(CAT,       yypos, yytext) );
<INITIAL>"-"  => ( token(MINUS,     yypos, yytext) );
<INITIAL>"#"  => ( token(HASH,      yypos, yytext) );
<INITIAL>"("  => ( token(LPAR,      yypos, yytext) );
<INITIAL>")"  => ( token(RPAR,      yypos, yytext) );
<INITIAL>","  => ( token(COMMA,     yypos, yytext) );
<INITIAL>"->" => ( token(ARROW,     yypos, yytext) );
<INITIAL>"."  => ( token(DOT,       yypos, yytext) );
<INITIAL>":"  => ( token(COLON,     yypos, yytext) );
<INITIAL>":>" => ( token(SEAL,      yypos, yytext) );
<INITIAL>";"  => ( token(SEMICOLON, yypos, yytext) );
<INITIAL>"<"  => ( token(LESS,      yypos, yytext) );
<INITIAL>"="  => ( token(EQUALS,    yypos, yytext) );
<INITIAL>"==" => ( token(ISEQUAL,   yypos, yytext) );
<INITIAL>"=>" => ( token(DARROW,    yypos, yytext) );
<INITIAL>"["  => ( token(LBRACK,    yypos, yytext) );
<INITIAL>"]"  => ( token(RBRACK,    yypos, yytext) );
<INITIAL>"_"  => ( token(UNDERBAR,  yypos, yytext) );
<INITIAL>"{"  => ( token(LBRACE,    yypos, yytext) );
<INITIAL>"|"  => ( token(BAR,       yypos, yytext) );
<INITIAL>"}"  => ( token(RBRACE,    yypos, yytext) );

<INITIAL>"bool"      => ( token(BOOL,      yypos, yytext) );
<INITIAL>"case"      => ( token(CASE,      yypos, yytext) );
<INITIAL>"data"      => ( token(DATA,      yypos, yytext) );
<INITIAL>"do"        => ( token(DO,        yypos, yytext) );
<INITIAL>"else"      => ( token(ELSE,      yypos, yytext) );
<INITIAL>"end"       => ( token(END,       yypos, yytext) );
<INITIAL>"export"    => ( token(EXPORT,    yypos, yytext) );
<INITIAL>"fn"        => ( token(FN,        yypos, yytext) );
<INITIAL>"false"     => ( token(FALSE,     yypos, yytext) );
<INITIAL>"forall"    => ( token(FORALL,    yypos, yytext) );
<INITIAL>"fun"       => ( token(FUN,       yypos, yytext) );
<INITIAL>"if"        => ( token(IF,        yypos, yytext) );
<INITIAL>"import"    => ( token(IMPORT,    yypos, yytext) );
<INITIAL>"in"        => ( token(IN,        yypos, yytext) );
<INITIAL>"int"       => ( token(INT,       yypos, yytext) );
<INITIAL>"let"       => ( token(LET,       yypos, yytext) );
<INITIAL>"link"      => ( token(LINK,      yypos, yytext) );
<INITIAL>"module"    => ( token(MODULE,    yypos, yytext) );
<INITIAL>"new"       => ( token(NEW,       yypos, yytext) );
<INITIAL>"of"        => ( token(OF,        yypos, yytext) );
<INITIAL>"open"      => ( token(OPEN,      yypos, yytext) );
<INITIAL>"out"       => ( token(OUT,       yypos, yytext) );
<INITIAL>"print"     => ( token(PRINT,     yypos, yytext) );
<INITIAL>"rec"       => ( token(REC,       yypos, yytext) );
<INITIAL>"seals"     => ( token(SEALS,     yypos, yytext) );
<INITIAL>"signature" => ( token(SIGNATURE, yypos, yytext) );
<INITIAL>"string"    => ( token(STRING,    yypos, yytext) );
<INITIAL>"then"      => ( token(THEN,      yypos, yytext) );
<INITIAL>"true"      => ( token(TRUE,      yypos, yytext) );
<INITIAL>"type"      => ( token(TYPE,      yypos, yytext) );
<INITIAL>"unit"      => ( token(UNIT,      yypos, yytext) );
<INITIAL>"val"       => ( token(VAL,       yypos, yytext) );
<INITIAL>"where"     => ( token(WHERE,     yypos, yytext) );
<INITIAL>"with"      => ( token(WITH,      yypos, yytext) );

<INITIAL>{decint}    => ( tokenOf(NUM,     toInt,    yypos, yytext) );
<INITIAL>{hexint}    => ( tokenOf(HEXNUM,  toHexInt, yypos, yytext) );
<INITIAL>{real}      => ( tokenOf(REAL,    toReal,   yypos, yytext) );
<INITIAL>{string}    => ( tokenOf(TEXT,    toString, yypos, yytext) );
<INITIAL>{char}      => ( tokenOf(CHAR,    toChar,   yypos, yytext) );
<INITIAL>{typvar}    => ( tokenOf(TYPVAR,  toId,     yypos, yytext) );
<INITIAL>{alpha}     => ( tokenOf(ALPHA,   toId,     yypos, yytext) );
<INITIAL>{symbol}    => ( tokenOf(SYMBOL,  toId,     yypos, yytext) );

<INITIAL>"(*)"       => ( YYBEGIN LCOMMENT; continue() );
<INITIAL>"(*"        => ( nest yypos; YYBEGIN COMMENT; continue() );

<LCOMMENT>.          => ( continue() );
<LCOMMENT>"\n"       => ( YYBEGIN (if !nesting = 0 then INITIAL else COMMENT);
                          newline yypos; continue() );

<COMMENT>"(*)"       => ( YYBEGIN LCOMMENT; continue() );
<COMMENT>"(*"        => ( nest yypos; continue() );
<COMMENT>"*)"        => ( unnest();
                          if !nesting = 0 then YYBEGIN INITIAL else ();
                          continue() );
<COMMENT>.           => ( continue() );
<COMMENT>"\n"        => ( newline yypos; continue() );

<INITIAL>"\""        => ( error(yypos, yytext, "invalid string") );
<INITIAL>.           => ( invalid(yypos, yytext) );
