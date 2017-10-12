(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature EL_PRINT =
sig
    val strS : ELAux.sign -> string
    val strF : ELAux.funct -> string

    val strKind : EL.kind -> string
    val strTyp : EL.typ -> string
    val strExp : EL.exp -> string
    val strModl : EL.modl -> string
    val strSign : EL.sign -> string
end

structure ELPrint : EL_PRINT =
struct
    open EL
    open ELAux
    open ILPrint

    fun list str xs = String.concatWith ", " (List.map str xs)

    fun strPM Plus = "+"
      | strPM Minus = "-"

    fun strAK(alpha, k) = alpha ^ ":" ^ strK k

    val rec strS =
        fn Typ(tau, k, pmo) =>
            "[" ^ strT tau ^ ":" ^ strK k ^ "]" ^ (case pmo of SOME pm => strPM pm | NONE => "")
         | Term(tau, pm) => "[" ^ strT tau ^ "]" ^ strPM pm
         | Funct(phi, pm) => "[" ^ strF phi ^ "]" ^ strPM pm
         | Struct(lsigmas) => "{" ^ list (fn(l, sigma) => l ^ " : " ^ strS sigma) lsigmas ^ "}"

    and strF =
        fn(alphaks, betaks, sigma) =>
            "!(" ^ list strAK alphaks ^ ")." ^
            "?(" ^ list strAK betaks ^ ")." ^
            strS sigma

    fun strVar x = "\"" ^ x ^ "\""
    fun strPath ls = strVar(String.concatWith "." ls)
    fun strList strX xs = "[" ^ String.concatWith ", " (List.map strX xs) ^ "]"

    fun strKind {it, region} = case it of
          StarK => "StarK"
        | ArrowK(n) => "ArrowK(" ^ Int.toString n ^ ")"

    fun strTyp {it, region} = case it of
          ModT(modl) => "ModT(_)"
        | LambdaT(alphas, typ) => "LambdaT(" ^ strList strVar alphas ^ ", _)"
        | ApplyT(typ, typs) => "ApplyT(_, _)"
        | IntT => "IntT"
        | StringT => "StringT"
        | TupleT(typs) => "TupleT(_)"
        | VariantT(typs) => "VariantT(_)"
        | ArrowT(typ1, typ2) => "ArrowT(_, _)"
        | UnivT(alphas, typ) => "UnivT(_, _)"

    and strExp {it, region} = case it of
          ModE(modl) => "ModE(_)"
        | IntE(n) => "IntE(" ^ Int.toString n ^ ")"
        | StringE(s) => "StringE(\"" ^ String.toString s ^ "\")"
        | PlusE(exp1, exp2) => "PlusE(_, _)"
        | MinusE(exp1, exp2) => "MinusE(_, _)"
        | EqualE(exp1, exp2) => "EqualE(_, _)"
        | LessE(exp1, exp2) => "LessE(_, _)"
        | CatE(exp1, exp2) => "CatE(_, _)"
        | TupleE(exps) => "TupleE(_)"
        | ProjE(exp, i) => "ProjE(_, " ^ Int.toString i ^ ")"
        | InjE(exp, i, typ) => "InjE(_, _, _)"
        | CaseE(exp, xexps) => "CaseE(_, _)"
        | LambdaE(x, typ, exp) => "LambdaE(" ^ strVar x ^ ", _, _)"
        | ApplyE(exp1, exp2) => "ApplyE(_, _)"
        | GenE(alphas, exp) => "GenE(" ^ strList strVar alphas ^ ", _)"
        | InstE(exp, typs) => "Inst(_, _)"
        | FoldE(modl, typs, exp) => "FoldE(_, _, _)"
        | UnfoldE(modl, typs, exp) => "UnfoldE(_, _, _)"
        | LetE(x, modl, exp) => "LetE(" ^ strVar x ^ ", _, _)"
        | PrintE(exp) => "PrintE(_)"

    and strModl {it, region} = case it of
          VarM(x) => "VarM(" ^ strVar x ^ ")"
        | EmptyM => "EmptyM"
        | ValM(exp) => "ValM(_)"
        | AbsValM(typ) => "AbsValM(_)"
        | TypM(typ) => "TypM(_)"
        | AbsTypM(kind) => "AbsTypM(_)"
        | DatTypM(typ) => "DatTypM(_)"
        | AbsDatTypM(typ) => "AbsDatTypM(_)"
        | UnitM(modl) => "UnitM(_)"
        | AbsUnitM(sign) => "AbsUnitM(_)"
        | NewM(modl) => "NewM(_)"
        | StructM(l, modl) => "StructM(" ^ strVar l ^ ", _)"
        | DotM(modl, l) => "DotM(_, " ^ strVar l ^ ")"
        | LinkM(x, modl1, modl2) => "LinkM(" ^ strVar x ^ ", _, _)"
        | OLinkM(x, modl1, modl2) => "OLinkM(" ^ strVar x ^ ", _, _)"
        | SealM(modl, sign) => "SealM(_, _)"

    and strSign {it, region} = case it of
          ImportS(modl, lss) => "ImportS(_, " ^ strList strPath lss ^ ")"
        | ExportS(modl, lss) => "ExportS(_, " ^ strList strPath lss ^ ")"
end
