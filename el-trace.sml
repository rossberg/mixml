(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature EL_TRACE =
sig
    val on : bool ref
    val assertOn : bool ref
    val width : int ref

    val assert : (unit -> bool) -> unit
    val trace : string -> unit
    val traceIn : unit -> unit
    val traceOut : unit -> unit
    val traceReset : unit -> unit

    val trace' : string -> string -> unit
    val traceKind : string -> EL.kind -> string -> unit
    val traceTyp : string -> EL.typ -> string -> unit
    val traceExp : string -> EL.exp -> string -> unit
    val traceModl : string -> EL.modl -> string -> unit
    val traceSign : string -> EL.sign -> string -> unit

    val traceB : string -> bool -> bool
    val traceSrc : string -> string -> string
    val traceP : string -> IL.var list -> IL.var list
    val traceK : string -> IL.kind -> IL.kind
    val traceT : string -> IL.typ -> IL.typ
    val traceS : string -> ELAux.sign -> ELAux.sign
    val traceF : string -> ELAux.funct -> ELAux.funct
    val traceAs : string -> IL.var list -> IL.var list
    val traceAKs : string -> (IL.var * IL.kind) list -> (IL.var * IL.kind) list
    val traceD : string -> ELAux.typ_context -> ELAux.typ_context
    val traceG : string -> ELAux.modl_context -> ELAux.modl_context
    val traceL : string -> ELAux.locator -> ELAux.locator
    val traceR : string -> IL.typ_subst -> IL.typ_subst
end

structure ELTrace : EL_TRACE =
struct
    val indent = ELPretty.indent
    val log = TextIO.stdOut

    val on = ref false
    val assertOn = ref false
    val width = ref 80
    val onScreen = ref true
    val nesting = ref 0

    open PrettyPrint infix ^^ ^/^

    fun right off =
        let
            val n = !indent * (!nesting + off)
        in
            if !onScreen andalso n > (!width * 3 div 4)
            then n mod (!width div 2) + !width div 4
            else n
        end
    fun tab n = CharVector.tabulate(n, fn _ => #" ")

    fun assert p = 
        if not(!assertOn) orelse p() then () else raise Fail "ASSERTION FAILURE!"

    fun trace s =
        if not(!on) then () else TextIO.output(log, tab(right 0) ^ s ^ "\n")

    fun traceReset() = nesting := 0
    fun traceIn() = nesting := !nesting + 1
    fun traceOut() = nesting := !nesting - 1

    fun trace' func mark = trace("@" ^ func ^ " [" ^ mark ^ "]")
    fun point func strX x mark = trace' (func ^ " " ^ strX x) mark

    fun traceKind func kind mark = point func ELPrint.strKind kind mark
    fun traceTyp func typ mark = point func ELPrint.strTyp typ mark
    fun traceExp func exp mark = point func ELPrint.strExp exp mark
    fun traceModl func modl mark = point func ELPrint.strModl modl mark
    fun traceSign func sign mark = point func ELPrint.strSign sign mark

    fun dump name ppX x =
        if not(!on) then x else
        let
            val indent = right 1
            val doc = nest (right 2) (abox(text(tab indent ^ name ^ " =") ^/^ ppX x)) ^^ break
        in
            PrettyPrint.output(log, doc, !width);
            x
        end

    fun ppB b = text(Bool.toString b)
    fun ppSrc s =
        let
            val lines = String.fields (fn c => c = #"\n") s
            val dots = if List.length lines > 1 then "\n..." else ""
        in
            text("\"" ^ String.toString(List.hd lines ^ dots) ^ "\"")
        end

    fun traceB name b = dump name ppB b
    fun traceSrc name s = dump name ppSrc s
    fun traceP name p = dump name ELPretty.ppP p
    fun traceK name k = dump name ELPretty.ppK k
    fun traceT name tau = dump name ELPretty.ppT tau
    fun traceS name sigma = dump name ELPretty.ppS sigma
    fun traceF name phi = dump name ELPretty.ppF phi
    fun traceAs name alphas = dump name ELPretty.ppAs alphas
    fun traceAKs name alphaks = dump name ELPretty.ppAKs alphaks
    fun traceD name delta = dump name ELPretty.ppD delta
    fun traceG name gamma = dump name ELPretty.ppG gamma
    fun traceL name loc = dump name ELPretty.ppL loc
    fun traceR name del = dump name ELPretty.ppR del
end
