(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature EL_PARSER =
sig
    val parse : string -> EL.prog
end

structure ELParser : EL_PARSER =
struct
    structure LrVals = LrValsFn(structure Token = LrParser.Token)
    structure Lexer  = LexerFn (structure Tokens = LrVals.Tokens)
    structure Parser = Join    (structure LrParser   = LrParser
                                structure ParserData = LrVals.ParserData
                                structure Lex        = Lexer)

    val int = Int.toString

    fun parse source =
        let
            val yyread = ref false
            fun yyinput _ = if !yyread then "" else (yyread := true; source ^ "\n")
            val lexer = Parser.makeLexer yyinput
            fun onError(s, pos1, pos2) = raise EL.Error({l=pos1, r=pos2}, s)
        in
            Lexer.UserDeclarations.line := 1;
            Lexer.UserDeclarations.lines := [0];
            Lexer.UserDeclarations.nesting := 0;
            Lexer.UserDeclarations.comments := [];
            #1(Parser.parse(0, lexer, onError, ()))
        end
        handle e as EL.Error({l=(l1, c1), r=(l2, c2)}, s) =>
        (
            TextIO.output(TextIO.stdOut, int l1 ^ "." ^ int c1 ^ "-" ^ int l2 ^ "." ^ int c2 ^ ": " ^ s ^ "\n");
            raise e
        )
end
