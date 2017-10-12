(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

structure ILMachine =
struct
    open IL

    datatype value =
        IntV of int
      | StringV of string
      | TupleV of value list
      | VariantV of value * int * typ
      | LambdaV of var * sign * term
      | GenV of typvar list * term
      | FoldV of typvar
      | UnfoldV of typvar
      | ConV of typvar * typ list * value

    datatype modval =
        VarW of var
      | TypW of typ
      | TermW of value
      | StructW of (lab * modval) list
      | LambdaW of var * sign * modl
      | GenDownW of (typvar * kind) list * modl
      | GenUpW of (typvar * kind) list * modl

    datatype frame =
        ValF
      | PlusF1 of term
      | PlusF2 of int
      | MinusF1 of term
      | MinusF2 of int
      | EqualF1 of term
      | EqualF2 of int
      | LessF1 of term
      | LessF2 of int
      | CatF1 of term
      | CatF2 of string
      | TupleF of value list * term list
      | ProjF of int
      | VariantF of int * typ
      | CaseF of (var * term) list
      | AppF1 of modl
      | AppF2 of value
      | InstF of typ list
      | ConF1 of typ list * term
      | ConF2 of value * typ list
      | PrintF
      | TermF
      | StructF of (lab * modval) list * lab * (lab * modl) list
      | DotF of lab
      | ApplyF1 of modl
      | ApplyF2 of modval
      | LetF of var * modl
      | InstDownF of typ list
(* todo: real effect system
      | InstUpF of typvar list
*)
      | InstUpF1 of typvar list * modl
      | InstUpF2 of modval * typvar list
      | AssignF of modl
      | ForceF
      | NeededF of var
    type continuation = frame list

    datatype store_entry =
        Evaluated of modval
      | Evaluating
      | Defined of modl
      | Undefined
    type store = store_entry context

    datatype ('a,'b) ev = EXP of 'a | VAL of 'b
    datatype state =
        TermSt of typ_context * modl_context * store * continuation * (term, value) ev
      | ModSt of typ_context * modl_context * store * continuation * (modl, modval) ev
      | BlackHole of var


    fun toValue(ValE(m)) = NONE
      | toValue(IntE(n)) = SOME(IntV(n))
      | toValue(StringE(s)) = SOME(StringV(s))
      | toValue(PlusE _) = NONE
      | toValue(MinusE _) = NONE
      | toValue(EqualE _) = NONE
      | toValue(LessE _) = NONE
      | toValue(CatE _) = NONE
      | toValue(TupleE(es)) = (SOME(TupleV(List.map (valOf o toValue) es)) handle Option => NONE)
      | toValue(DotE _) = NONE
      | toValue(VariantE(e, i, tau)) = (SOME(VariantV(valOf(toValue e), i, tau)) handle Option => NONE)
      | toValue(CaseE _) = NONE
      | toValue(LambdaE(x, sigma, e)) = SOME(LambdaV(x, sigma, e))
      | toValue(ApplyE _) = NONE
      | toValue(GenE(alphas, e)) = SOME(GenV(alphas, e))
      | toValue(InstE _) = NONE
      | toValue(FoldE(alpha)) = SOME(FoldV(alpha))
      | toValue(UnfoldE(alpha)) = SOME(UnfoldV(alpha))
      | toValue(ConE(FoldE(alpha), taus, e)) = Option.map (fn v => ConV(alpha, taus, v)) (toValue e)
      | toValue(ConE _) = NONE
      | toValue(PrintE _) = NONE

    fun fromValue(IntV(n)) = IntE(n)
      | fromValue(StringV(s)) = StringE(s)
      | fromValue(TupleV(vs)) = TupleE(List.map fromValue vs)
      | fromValue(VariantV(v, i, tau)) = VariantE(fromValue v, i, tau)
      | fromValue(LambdaV(x, sigma, e)) = LambdaE(x, sigma, e)
      | fromValue(GenV(alphas, e)) = GenE(alphas, e)
      | fromValue(FoldV(alpha)) = FoldE(alpha)
      | fromValue(UnfoldV(alpha)) = UnfoldE(alpha)
      | fromValue(ConV(alpha, taus, v)) = ConE(FoldE(alpha), taus, fromValue v)

    fun toModval(VarM(x)) = SOME(VarW(x))
      | toModval(TypM(tau)) = SOME(TypW(tau))
      | toModval(TermM(e)) = Option.map TermW (toValue e)
      | toModval(StructM(lms)) = (SOME(StructW(List.map (fn(l, m) => (l, valOf(toModval m))) lms)) handle Option => NONE)
      | toModval(DotM _) = NONE
      | toModval(LambdaM(x, sigma, m)) = SOME(LambdaW(x, sigma, m))
      | toModval(ApplyM _) = NONE
      | toModval(LetM _) = NONE
      | toModval(GenDownM(alphaks, m)) = SOME(GenDownW(alphaks, m))
      | toModval(InstDownM _) = NONE
      | toModval(GenUpM(alphaks, m)) = SOME(GenUpW(alphaks, m))
      | toModval(InstUpM _) = NONE
      | toModval(NewTypM _) = NONE
      | toModval(DefEquiM _) = NONE
      | toModval(DefIsoM _) = NONE
      | toModval(NewTermM _) = NONE
      | toModval(AssignM _) = NONE
      | toModval(ForceM _) = NONE

    fun fromModval(VarW(x)) = VarM(x)
      | fromModval(TypW(tau)) = TypM(tau)
      | fromModval(TermW(v)) = TermM(fromValue v)
      | fromModval(StructW(lws)) = StructM(List.map (fn(l, w) => (l, fromModval w)) lws)
      | fromModval(LambdaW(x, sigma, m)) = LambdaM(x, sigma, m)
      | fromModval(GenDownW(alphaks, m)) = GenDownM(alphaks, m)
      | fromModval(GenUpW(alphaks, m)) = GenUpM(alphaks, m)
end
