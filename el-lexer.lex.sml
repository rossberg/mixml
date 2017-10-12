functor LexerFn(structure Tokens : Parser_TOKENS)  = struct

    structure yyInput : sig

        type stream
	val mkStream : (int -> string) -> stream
	val fromStream : TextIO.StreamIO.instream -> stream
	val getc : stream -> (Char.char * stream) option
	val getpos : stream -> int
	val getlineNo : stream -> int
	val subtract : stream * stream -> string
	val eof : stream -> bool
	val lastWasNL : stream -> bool

      end = struct

        structure TIO = TextIO
        structure TSIO = TIO.StreamIO
	structure TPIO = TextPrimIO

        datatype stream = Stream of {
            strm : TSIO.instream,
	    id : int,  (* track which streams originated 
			* from the same stream *)
	    pos : int,
	    lineNo : int,
	    lastWasNL : bool
          }

	local
	  val next = ref 0
	in
	fun nextId() = !next before (next := !next + 1)
	end

	val initPos = 2 (* ml-lex bug compatibility *)

	fun mkStream inputN = let
              val strm = TSIO.mkInstream 
			   (TPIO.RD {
			        name = "lexgen",
				chunkSize = 4096,
				readVec = SOME inputN,
				readArr = NONE,
				readVecNB = NONE,
				readArrNB = NONE,
				block = NONE,
				canInput = NONE,
				avail = (fn () => NONE),
				getPos = NONE,
				setPos = NONE,
				endPos = NONE,
				verifyPos = NONE,
				close = (fn () => ()),
				ioDesc = NONE
			      }, "")
	      in 
		Stream {strm = strm, id = nextId(), pos = initPos, lineNo = 1,
			lastWasNL = true}
	      end

	fun fromStream strm = Stream {
		strm = strm, id = nextId(), pos = initPos, lineNo = 1, lastWasNL = true
	      }

	fun getc (Stream {strm, pos, id, lineNo, ...}) = (case TSIO.input1 strm
              of NONE => NONE
	       | SOME (c, strm') => 
		   SOME (c, Stream {
			        strm = strm', 
				pos = pos+1, 
				id = id,
				lineNo = lineNo + 
					 (if c = #"\n" then 1 else 0),
				lastWasNL = (c = #"\n")
			      })
	     (* end case*))

	fun getpos (Stream {pos, ...}) = pos

	fun getlineNo (Stream {lineNo, ...}) = lineNo

	fun subtract (new, old) = let
	      val Stream {strm = strm, pos = oldPos, id = oldId, ...} = old
	      val Stream {pos = newPos, id = newId, ...} = new
              val (diff, _) = if newId = oldId andalso newPos >= oldPos
			      then TSIO.inputN (strm, newPos - oldPos)
			      else raise Fail 
				"BUG: yyInput: attempted to subtract incompatible streams"
	      in 
		diff 
	      end

	fun eof (Stream {strm, ...}) = TSIO.endOfStream strm

	fun lastWasNL (Stream {lastWasNL, ...}) = lastWasNL

      end

    datatype yystart_state = 
COMMENT | LCOMMENT | INITIAL
    structure UserDeclarations = 
      struct

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



      end

    datatype yymatch 
      = yyNO_MATCH
      | yyMATCH of yyInput.stream * action * yymatch
    withtype action = yyInput.stream * yymatch -> UserDeclarations.lexresult

    local

    val yytable = 
#[
([(#"\^@",#"\t",3),
(#"\v",#"'",3),
(#")",#")",3),
(#"+",#"\255",3),
(#"\n",#"\n",4),
(#"(",#"(",5),
(#"*",#"*",6)], []), ([(#"\^@",#"\t",10),
(#"\v",#"\255",10),
(#"\n",#"\n",11)], []), ([(#"\^@",#"\b",12),
(#"\^N",#"\^_",12),
(#"\127",#"\255",12),
(#"\t",#"\t",13),
(#"\v",#"\r",13),
(#" ",#" ",13),
(#"\n",#"\n",14),
(#"!",#"!",15),
(#"\"",#"\"",16),
(#"#",#"#",17),
(#"$",#"&",18),
(#"*",#"*",18),
(#"/",#"/",18),
(#">",#"?",18),
(#"\\",#"\\",18),
(#"^",#"^",18),
(#"`",#"`",18),
(#"'",#"'",19),
(#"(",#"(",20),
(#")",#")",21),
(#"+",#"+",22),
(#",",#",",23),
(#"-",#"-",24),
(#".",#".",25),
(#"0",#"0",26),
(#"1",#"9",27),
(#":",#":",28),
(#";",#";",29),
(#"<",#"<",30),
(#"=",#"=",31),
(#"@",#"@",32),
(#"A",#"Z",33),
(#"a",#"a",33),
(#"g",#"h",33),
(#"j",#"k",33),
(#"q",#"q",33),
(#"x",#"z",33),
(#"[",#"[",34),
(#"]",#"]",35),
(#"_",#"_",36),
(#"b",#"b",37),
(#"c",#"c",38),
(#"d",#"d",39),
(#"e",#"e",40),
(#"f",#"f",41),
(#"i",#"i",42),
(#"l",#"l",43),
(#"m",#"m",44),
(#"n",#"n",45),
(#"o",#"o",46),
(#"p",#"p",47),
(#"r",#"r",48),
(#"s",#"s",49),
(#"t",#"t",50),
(#"u",#"u",51),
(#"v",#"v",52),
(#"w",#"w",53),
(#"{",#"{",54),
(#"|",#"|",55),
(#"}",#"}",56),
(#"~",#"~",57)], []), ([], [75]), ([], [76]), ([(#"*",#"*",8)], [75]), ([(#")",#")",7)], [75]), ([], [74]), ([(#")",#")",9)], [73]), ([], [72]), ([], [70]), ([], [71]), ([], [78]), ([(#"\t",#"\t",204),
(#"\v",#"\r",204),
(#" ",#" ",204)], [0, 78]), ([], [1]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [2, 67, 78]), ([(#" ",#"!",193),
(#"#",#"[",193),
(#"]",#"~",193),
(#"\128",#"\255",193),
(#"\"",#"\"",194),
(#"\\",#"\\",195)], [77, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58),
(#"\"",#"\"",179)], [7, 67, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [67, 78]), ([(#"'",#"'",178),
(#"0",#"9",178),
(#"A",#"Z",178),
(#"_",#"_",178),
(#"a",#"z",178)], [65, 78]), ([(#"*",#"*",176)], [8, 78]), ([], [9, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"*",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58),
(#"+",#"+",175)], [4, 67, 78]), ([], [10, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"=",58),
(#"?",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58),
(#">",#">",174)], [6, 67, 78]), ([], [12, 78]), ([(#".",#".",61),
(#"0",#"9",60),
(#"E",#"E",62),
(#"e",#"e",62),
(#"x",#"x",66)], [60, 78]), ([(#".",#".",61),
(#"0",#"9",60),
(#"E",#"E",62),
(#"e",#"e",62)], [60, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"=",58),
(#"?",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58),
(#">",#">",173)], [13, 67, 78]), ([], [15, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [16, 67, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"<",58),
(#"?",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58),
(#"=",#"=",171),
(#">",#">",172)], [17, 67, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [3, 67, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [66, 78]), ([], [20, 78]), ([], [21, 78]), ([], [22, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"n",68),
(#"p",#"z",68),
(#"o",#"o",168)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"b",#"z",68),
(#"a",#"a",165)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"b",#"n",68),
(#"p",#"z",68),
(#"a",#"a",161),
(#"o",#"o",162)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"k",68),
(#"m",#"m",68),
(#"o",#"w",68),
(#"y",#"z",68),
(#"l",#"l",151),
(#"n",#"n",152),
(#"x",#"x",153)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"b",#"m",68),
(#"p",#"t",68),
(#"v",#"z",68),
(#"a",#"a",139),
(#"n",#"n",140),
(#"o",#"o",141),
(#"u",#"u",142)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"e",68),
(#"g",#"l",68),
(#"o",#"z",68),
(#"f",#"f",131),
(#"m",#"m",132),
(#"n",#"n",133)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"h",68),
(#"j",#"z",68),
(#"e",#"e",126),
(#"i",#"i",127)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"n",68),
(#"p",#"z",68),
(#"o",#"o",121)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",119)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"e",68),
(#"g",#"o",68),
(#"q",#"t",68),
(#"v",#"z",68),
(#"f",#"f",113),
(#"p",#"p",114),
(#"u",#"u",115)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"q",68),
(#"s",#"z",68),
(#"r",#"r",109)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",107)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"h",68),
(#"j",#"s",68),
(#"u",#"z",68),
(#"e",#"e",90),
(#"i",#"i",91),
(#"t",#"t",92)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"g",68),
(#"i",#"q",68),
(#"s",#"x",68),
(#"z",#"z",68),
(#"h",#"h",81),
(#"r",#"r",82),
(#"y",#"y",83)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"m",68),
(#"o",#"z",68),
(#"n",#"n",78)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"b",#"z",68),
(#"a",#"a",76)], [66, 78]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"g",68),
(#"j",#"z",68),
(#"h",#"h",69),
(#"i",#"i",70)], [66, 78]), ([], [23, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [24, 67, 78]), ([], [25, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58),
(#"0",#"0",59),
(#"1",#"9",60)], [67, 78]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [67]), ([(#".",#".",61),
(#"0",#"9",60),
(#"E",#"E",62),
(#"e",#"e",62),
(#"x",#"x",66)], [60]), ([(#".",#".",61),
(#"0",#"9",60),
(#"E",#"E",62),
(#"e",#"e",62)], [60]), ([(#"0",#"9",65)], []), ([(#"0",#"9",63),
(#"~",#"~",64)], []), ([(#"0",#"9",63)], [62]), ([(#"0",#"9",63)], []), ([(#"0",#"9",65),
(#"E",#"E",62),
(#"e",#"e",62)], [62]), ([(#"0",#"9",67),
(#"A",#"F",67),
(#"a",#"f",67)], []), ([(#"0",#"9",67),
(#"A",#"F",67),
(#"a",#"f",67)], [61]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",73)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",71)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"g",68),
(#"i",#"z",68),
(#"h",#"h",72)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [59, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"q",68),
(#"s",#"z",68),
(#"r",#"r",74)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",75)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [58, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"k",68),
(#"m",#"z",68),
(#"l",#"l",77)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [57, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"h",68),
(#"j",#"z",68),
(#"i",#"i",79)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",80)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [56, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",88)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"t",68),
(#"v",#"z",68),
(#"u",#"u",86)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"o",68),
(#"q",#"z",68),
(#"p",#"p",84)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",85)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [55, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",87)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [54, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"m",68),
(#"o",#"z",68),
(#"n",#"n",89)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [53, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"b",#"z",68),
(#"a",#"a",104)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"f",68),
(#"h",#"z",68),
(#"g",#"g",97)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"q",68),
(#"s",#"z",68),
(#"r",#"r",93)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"h",68),
(#"j",#"z",68),
(#"i",#"i",94)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"m",68),
(#"o",#"z",68),
(#"n",#"n",95)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"f",68),
(#"h",#"z",68),
(#"g",#"g",96)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [52, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"m",68),
(#"o",#"z",68),
(#"n",#"n",98)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"b",#"z",68),
(#"a",#"a",99)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",100)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"t",68),
(#"v",#"z",68),
(#"u",#"u",101)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"q",68),
(#"s",#"z",68),
(#"r",#"r",102)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",103)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [51, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"k",68),
(#"m",#"z",68),
(#"l",#"l",105)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"r",68),
(#"t",#"z",68),
(#"s",#"s",106)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [50, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"b",68),
(#"d",#"z",68),
(#"c",#"c",108)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [49, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"h",68),
(#"j",#"z",68),
(#"i",#"i",110)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"m",68),
(#"o",#"z",68),
(#"n",#"n",111)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",112)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [48, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [45, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",117)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",116)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [47, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"m",68),
(#"o",#"z",68),
(#"n",#"n",118)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [46, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"v",68),
(#"x",#"z",68),
(#"w",#"w",120)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [44, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"c",68),
(#"e",#"z",68),
(#"d",#"d",122)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"t",68),
(#"v",#"z",68),
(#"u",#"u",123)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"k",68),
(#"m",#"z",68),
(#"l",#"l",124)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",125)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [43, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",130)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"m",68),
(#"o",#"z",68),
(#"n",#"n",128)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"j",68),
(#"l",#"z",68),
(#"k",#"k",129)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [42, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [41, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [37, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"o",68),
(#"q",#"z",68),
(#"p",#"p",135)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",134)], [39, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [40, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"n",68),
(#"p",#"z",68),
(#"o",#"o",136)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"q",68),
(#"s",#"z",68),
(#"r",#"r",137)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",138)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [38, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"k",68),
(#"m",#"z",68),
(#"l",#"l",148)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [33, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"q",68),
(#"s",#"z",68),
(#"r",#"r",144)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"m",68),
(#"o",#"z",68),
(#"n",#"n",143)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [36, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"b",#"z",68),
(#"a",#"a",145)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"k",68),
(#"m",#"z",68),
(#"l",#"l",146)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"k",68),
(#"m",#"z",68),
(#"l",#"l",147)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [35, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"r",68),
(#"t",#"z",68),
(#"s",#"s",149)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",150)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [34, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"r",68),
(#"t",#"z",68),
(#"s",#"s",159)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"c",68),
(#"e",#"z",68),
(#"d",#"d",158)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"o",68),
(#"q",#"z",68),
(#"p",#"p",154)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"n",68),
(#"p",#"z",68),
(#"o",#"o",155)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"q",68),
(#"s",#"z",68),
(#"r",#"r",156)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",157)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [32, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [31, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",160)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [30, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"s",68),
(#"u",#"z",68),
(#"t",#"t",163)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [29, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"b",#"z",68),
(#"a",#"a",164)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [28, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"r",68),
(#"t",#"z",68),
(#"s",#"s",166)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"d",68),
(#"f",#"z",68),
(#"e",#"e",167)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [27, 66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"n",68),
(#"p",#"z",68),
(#"o",#"o",169)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"k",68),
(#"m",#"z",68),
(#"l",#"l",170)], [66]), ([(#"'",#"'",68),
(#"0",#"9",68),
(#"A",#"Z",68),
(#"_",#"_",68),
(#"a",#"z",68)], [26, 66]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [18, 67]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [19, 67]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [14, 67]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [11, 67]), ([(#"!",#"!",58),
(#"#",#"&",58),
(#"*",#"+",58),
(#"-",#"-",58),
(#"/",#"/",58),
(#":",#":",58),
(#"<",#"@",58),
(#"\\",#"\\",58),
(#"^",#"^",58),
(#"`",#"`",58),
(#"|",#"|",58),
(#"~",#"~",58)], [5, 67]), ([(#")",#")",177)], [69]), ([], [68]), ([(#"'",#"'",178),
(#"0",#"9",178),
(#"A",#"Z",178),
(#"_",#"_",178),
(#"a",#"z",178)], [65]), ([(#" ",#"!",180),
(#"#",#"[",180),
(#"]",#"~",180),
(#"\128",#"\255",180),
(#"\\",#"\\",181)], []), ([(#"\"",#"\"",190),
(#"\\",#"\\",191)], []), ([(#"\t",#"\t",182),
(#"\v",#"\r",182),
(#" ",#" ",182),
(#"\"",#"\"",180),
(#"\\",#"\\",180),
(#"a",#"b",180),
(#"f",#"f",180),
(#"n",#"n",180),
(#"r",#"r",180),
(#"t",#"t",180),
(#"v",#"v",180),
(#"0",#"9",183),
(#"^",#"^",184),
(#"u",#"u",185)], []), ([(#"\t",#"\t",182),
(#"\v",#"\r",182),
(#" ",#" ",182),
(#"\\",#"\\",179)], []), ([(#"0",#"9",189)], []), ([(#"@",#"_",180)], []), ([(#"0",#"9",186),
(#"A",#"F",186),
(#"a",#"f",186)], []), ([(#"0",#"9",187),
(#"A",#"F",187),
(#"a",#"f",187)], []), ([(#"0",#"9",188),
(#"A",#"F",188),
(#"a",#"f",188)], []), ([(#"0",#"9",180),
(#"A",#"F",180),
(#"a",#"f",180)], []), ([(#"0",#"9",180)], []), ([], [64]), ([(#"\t",#"\t",192),
(#"\v",#"\r",192),
(#" ",#" ",192)], []), ([(#"\t",#"\t",192),
(#"\v",#"\r",192),
(#" ",#" ",192),
(#"\\",#"\\",180)], []), ([(#" ",#"!",193),
(#"#",#"[",193),
(#"]",#"~",193),
(#"\128",#"\255",193),
(#"\"",#"\"",194),
(#"\\",#"\\",195)], []), ([], [63]), ([(#"\t",#"\t",196),
(#"\v",#"\r",196),
(#" ",#" ",196),
(#"\"",#"\"",193),
(#"\\",#"\\",193),
(#"a",#"b",193),
(#"f",#"f",193),
(#"n",#"n",193),
(#"r",#"r",193),
(#"t",#"t",193),
(#"v",#"v",193),
(#"0",#"9",197),
(#"^",#"^",198),
(#"u",#"u",199)], []), ([(#"\t",#"\t",196),
(#"\v",#"\r",196),
(#" ",#" ",196),
(#"\\",#"\\",193)], []), ([(#"0",#"9",203)], []), ([(#"@",#"_",193)], []), ([(#"0",#"9",200),
(#"A",#"F",200),
(#"a",#"f",200)], []), ([(#"0",#"9",201),
(#"A",#"F",201),
(#"a",#"f",201)], []), ([(#"0",#"9",202),
(#"A",#"F",202),
(#"a",#"f",202)], []), ([(#"0",#"9",193),
(#"A",#"F",193),
(#"a",#"f",193)], []), ([(#"0",#"9",193)], []), ([(#"\t",#"\t",204),
(#"\v",#"\r",204),
(#" ",#" ",204)], [0])]

    fun mk yyins = let
        (* current start state *)
        val yyss = ref INITIAL
	fun YYBEGIN ss = (yyss := ss)
	(* current input stream *)
        val yystrm = ref yyins
	(* get one char of input *)
	val yygetc = yyInput.getc
	(* create yytext *)
	fun yymktext(strm) = yyInput.subtract (strm, !yystrm)
        open UserDeclarations
        fun lex 
(yyarg as ()) = let 
     fun continue() = let
            val yylastwasn = yyInput.lastWasNL (!yystrm)
            fun yystuck (yyNO_MATCH) = raise Fail "stuck state"
	      | yystuck (yyMATCH (strm, action, old)) = 
		  action (strm, old)
	    val yypos = yyInput.getpos (!yystrm)
	    val yygetlineNo = yyInput.getlineNo
	    fun yyactsToMatches (strm, [],	  oldMatches) = oldMatches
	      | yyactsToMatches (strm, act::acts, oldMatches) = 
		  yyMATCH (strm, act, yyactsToMatches (strm, acts, oldMatches))
	    fun yygo actTable = 
		(fn (~1, _, oldMatches) => yystuck oldMatches
		  | (curState, strm, oldMatches) => let
		      val (transitions, finals') = Vector.sub (yytable, curState)
		      val finals = map (fn i => Vector.sub (actTable, i)) finals'
		      fun tryfinal() = 
		            yystuck (yyactsToMatches (strm, finals, oldMatches))
		      fun find (c, []) = NONE
			| find (c, (c1, c2, s)::ts) = 
		            if c1 <= c andalso c <= c2 then SOME s
			    else find (c, ts)
		      in case yygetc strm
			  of SOME(c, strm') => 
			       (case find (c, transitions)
				 of NONE => tryfinal()
				  | SOME n => 
				      yygo actTable
					(n, strm', 
					 yyactsToMatches (strm, finals, oldMatches)))
			   | NONE => tryfinal()
		      end)
	    in 
let
fun yyAction0 (strm, lastMatch : yymatch) = (yystrm := strm; ( continue() ))
fun yyAction1 (strm, lastMatch : yymatch) = (yystrm := strm;
      ( newline yypos; continue() ))
fun yyAction2 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(BANG,      yypos, yytext) )
      end
fun yyAction3 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(AT,        yypos, yytext) )
      end
fun yyAction4 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(PLUS,      yypos, yytext) )
      end
fun yyAction5 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(CAT,       yypos, yytext) )
      end
fun yyAction6 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(MINUS,     yypos, yytext) )
      end
fun yyAction7 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(HASH,      yypos, yytext) )
      end
fun yyAction8 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(LPAR,      yypos, yytext) )
      end
fun yyAction9 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(RPAR,      yypos, yytext) )
      end
fun yyAction10 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(COMMA,     yypos, yytext) )
      end
fun yyAction11 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(ARROW,     yypos, yytext) )
      end
fun yyAction12 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(DOT,       yypos, yytext) )
      end
fun yyAction13 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(COLON,     yypos, yytext) )
      end
fun yyAction14 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(SEAL,      yypos, yytext) )
      end
fun yyAction15 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(SEMICOLON, yypos, yytext) )
      end
fun yyAction16 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(LESS,      yypos, yytext) )
      end
fun yyAction17 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(EQUALS,    yypos, yytext) )
      end
fun yyAction18 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(ISEQUAL,   yypos, yytext) )
      end
fun yyAction19 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(DARROW,    yypos, yytext) )
      end
fun yyAction20 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(LBRACK,    yypos, yytext) )
      end
fun yyAction21 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(RBRACK,    yypos, yytext) )
      end
fun yyAction22 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(UNDERBAR,  yypos, yytext) )
      end
fun yyAction23 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(LBRACE,    yypos, yytext) )
      end
fun yyAction24 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(BAR,       yypos, yytext) )
      end
fun yyAction25 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(RBRACE,    yypos, yytext) )
      end
fun yyAction26 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(BOOL,      yypos, yytext) )
      end
fun yyAction27 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(CASE,      yypos, yytext) )
      end
fun yyAction28 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(DATA,      yypos, yytext) )
      end
fun yyAction29 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(DO,        yypos, yytext) )
      end
fun yyAction30 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(ELSE,      yypos, yytext) )
      end
fun yyAction31 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(END,       yypos, yytext) )
      end
fun yyAction32 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(EXPORT,    yypos, yytext) )
      end
fun yyAction33 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(FN,        yypos, yytext) )
      end
fun yyAction34 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(FALSE,     yypos, yytext) )
      end
fun yyAction35 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(FORALL,    yypos, yytext) )
      end
fun yyAction36 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(FUN,       yypos, yytext) )
      end
fun yyAction37 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(IF,        yypos, yytext) )
      end
fun yyAction38 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(IMPORT,    yypos, yytext) )
      end
fun yyAction39 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(IN,        yypos, yytext) )
      end
fun yyAction40 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(INT,       yypos, yytext) )
      end
fun yyAction41 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(LET,       yypos, yytext) )
      end
fun yyAction42 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(LINK,      yypos, yytext) )
      end
fun yyAction43 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(MODULE,    yypos, yytext) )
      end
fun yyAction44 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(NEW,       yypos, yytext) )
      end
fun yyAction45 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(OF,        yypos, yytext) )
      end
fun yyAction46 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(OPEN,      yypos, yytext) )
      end
fun yyAction47 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(OUT,       yypos, yytext) )
      end
fun yyAction48 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(PRINT,     yypos, yytext) )
      end
fun yyAction49 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(REC,       yypos, yytext) )
      end
fun yyAction50 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(SEALS,     yypos, yytext) )
      end
fun yyAction51 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(SIGNATURE, yypos, yytext) )
      end
fun yyAction52 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(STRING,    yypos, yytext) )
      end
fun yyAction53 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(THEN,      yypos, yytext) )
      end
fun yyAction54 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(TRUE,      yypos, yytext) )
      end
fun yyAction55 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(TYPE,      yypos, yytext) )
      end
fun yyAction56 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(UNIT,      yypos, yytext) )
      end
fun yyAction57 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(VAL,       yypos, yytext) )
      end
fun yyAction58 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(WHERE,     yypos, yytext) )
      end
fun yyAction59 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( token(WITH,      yypos, yytext) )
      end
fun yyAction60 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( tokenOf(NUM,     toInt,    yypos, yytext) )
      end
fun yyAction61 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( tokenOf(HEXNUM,  toHexInt, yypos, yytext) )
      end
fun yyAction62 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( tokenOf(REAL,    toReal,   yypos, yytext) )
      end
fun yyAction63 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( tokenOf(TEXT,    toString, yypos, yytext) )
      end
fun yyAction64 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( tokenOf(CHAR,    toChar,   yypos, yytext) )
      end
fun yyAction65 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( tokenOf(TYPVAR,  toId,     yypos, yytext) )
      end
fun yyAction66 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( tokenOf(ALPHA,   toId,     yypos, yytext) )
      end
fun yyAction67 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( tokenOf(SYMBOL,  toId,     yypos, yytext) )
      end
fun yyAction68 (strm, lastMatch : yymatch) = (yystrm := strm;
      ( YYBEGIN LCOMMENT; continue() ))
fun yyAction69 (strm, lastMatch : yymatch) = (yystrm := strm;
      ( nest yypos; YYBEGIN COMMENT; continue() ))
fun yyAction70 (strm, lastMatch : yymatch) = (yystrm := strm; ( continue() ))
fun yyAction71 (strm, lastMatch : yymatch) = (yystrm := strm;
      ( YYBEGIN (if !nesting = 0 then INITIAL else COMMENT);
                          newline yypos; continue() ))
fun yyAction72 (strm, lastMatch : yymatch) = (yystrm := strm;
      ( YYBEGIN LCOMMENT; continue() ))
fun yyAction73 (strm, lastMatch : yymatch) = (yystrm := strm;
      ( nest yypos; continue() ))
fun yyAction74 (strm, lastMatch : yymatch) = (yystrm := strm;
      ( unnest();
                          if !nesting = 0 then YYBEGIN INITIAL else ();
                          continue() ))
fun yyAction75 (strm, lastMatch : yymatch) = (yystrm := strm; ( continue() ))
fun yyAction76 (strm, lastMatch : yymatch) = (yystrm := strm;
      ( newline yypos; continue() ))
fun yyAction77 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( error(yypos, yytext, "invalid string") )
      end
fun yyAction78 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; ( invalid(yypos, yytext) )
      end
val yyactTable = Vector.fromList([yyAction0, yyAction1, yyAction2, yyAction3,
  yyAction4, yyAction5, yyAction6, yyAction7, yyAction8, yyAction9, yyAction10,
  yyAction11, yyAction12, yyAction13, yyAction14, yyAction15, yyAction16,
  yyAction17, yyAction18, yyAction19, yyAction20, yyAction21, yyAction22,
  yyAction23, yyAction24, yyAction25, yyAction26, yyAction27, yyAction28,
  yyAction29, yyAction30, yyAction31, yyAction32, yyAction33, yyAction34,
  yyAction35, yyAction36, yyAction37, yyAction38, yyAction39, yyAction40,
  yyAction41, yyAction42, yyAction43, yyAction44, yyAction45, yyAction46,
  yyAction47, yyAction48, yyAction49, yyAction50, yyAction51, yyAction52,
  yyAction53, yyAction54, yyAction55, yyAction56, yyAction57, yyAction58,
  yyAction59, yyAction60, yyAction61, yyAction62, yyAction63, yyAction64,
  yyAction65, yyAction66, yyAction67, yyAction68, yyAction69, yyAction70,
  yyAction71, yyAction72, yyAction73, yyAction74, yyAction75, yyAction76,
  yyAction77, yyAction78])
in
  if yyInput.eof(!(yystrm))
    then UserDeclarations.eof(yyarg)
    else (case (!(yyss))
       of COMMENT => yygo yyactTable (0, !(yystrm), yyNO_MATCH)
        | LCOMMENT => yygo yyactTable (1, !(yystrm), yyNO_MATCH)
        | INITIAL => yygo yyactTable (2, !(yystrm), yyNO_MATCH)
      (* end case *))
end
            end
	  in 
            continue() 	  
	    handle IO.Io{cause, ...} => raise cause
          end
        in 
          lex 
        end
    in
    fun makeLexer yyinputN = mk (yyInput.mkStream yyinputN)
    fun makeLexer' ins = mk (yyInput.mkStream ins)
    end

  end
