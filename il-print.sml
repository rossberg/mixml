(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature IL_PRINT =
sig
    val strK : IL.kind -> string
    val strT : IL.typ  -> string
    val strS : IL.sign -> string
    val strF : ILMachine.frame -> string
    val strV : ILMachine.value -> string
    val strW : ILMachine.store -> ILMachine.modval -> string
    val strE : ILMachine.store -> IL.term -> string
    val strM : ILMachine.store -> IL.modl -> string
    val strO : ILMachine.store -> string
    val strSt : ILMachine.state -> string
end

structure ILPrint : IL_PRINT =
struct
    open VarOps
    open IL
    open ILMachine

    val TOP = 0
    val BIND = TOP+1
    val ARROW = BIND
    val ASSIGN = ARROW+1
    val COMP = ASSIGN
    val PLUS = COMP+1
    val TIMES = PLUS+1
    val APPLY = TIMES+1
    val DOT = APPLY
    val ATOM = DOT+1

    fun paren p p' s =
        if p' > p then "(" ^ s ^ ")" else s
    fun list str xs =
        String.concatWith ", " (List.map (str TOP) xs)

    fun strL p l = l
    fun strX p x = x
    fun strA p alpha = alpha

    fun strK p =
        fn StarK => "T"
         | ArrowK(1) => "T->T"
         | ArrowK(n) => "T^" ^ Int.toString n ^ "->T"

    fun strAK colon p (alpha, k) =
        strA ATOM alpha ^ colon ^ strK p k

    fun strField conn str p (l, x) = strL ATOM l ^ conn ^ str TOP x

    fun strT p =
        fn VarT(alpha) => alpha
         | IntT => "int"
         | StringT => "string"
         | TupleT[] => "1"
         | TupleT[tau] => "(* " ^ strT (TIMES+1) tau ^ ")"
         | TupleT(taus) =>
            paren TIMES p
            (
                String.concatWith " * "
                (
                    List.map (strT (TIMES+1)) taus
                )
            )
         | VariantT[] => "0"
         | VariantT[TupleT[], TupleT[]] => "bool"
         | VariantT[tau] => "(+ " ^ strT (PLUS+1) tau ^ ")"
         | VariantT(taus) =>
            paren PLUS p
            (
                String.concatWith " + "
                (
                    List.map (strT (PLUS+1)) taus
                )
            )
         | ArrowT(sigma, tau) =>
            paren ARROW p
            (
                strS (ARROW+1) sigma ^
                " -> " ^
                strT ARROW tau
            )
         | UnivT(alphas, tau) =>
            paren BIND p
            (
                "![" ^ list strA alphas ^ "]." ^
                strT BIND tau
            )
         | PureT(alphas, tau1, tau2) =>
            paren BIND p
            (
                "![" ^ list strA alphas ^ "]." ^
                strT (ARROW+1) tau1 ^
                strT ARROW tau2
            )
         | LambdaT(alphas, tau) =>
            paren BIND p
            (
                "\\[" ^ list strA alphas ^ "]." ^
                strT BIND tau
            )
         | ApplyT(tau, taus) =>
            paren APPLY p
            (
                strT APPLY tau ^
                "[" ^ list strT taus ^ "]"
            )

    and strS p =
        fn TypS(tau, k) => "[=" ^ strT APPLY tau ^ ":" ^ strK TOP k ^ "]"
         | TermS(tau) => "[" ^ strT TOP tau ^ "]"
         | StructS(lsigmas) => "{" ^ list (strField ":" strS) lsigmas ^ "}"
         | ArrowS(sigma1, sigma2) =>
            paren ARROW p
            (
                strS (ARROW+1) sigma1 ^
                " -> " ^
                strS ARROW sigma2
            )
         | LazyS(sigma) => paren APPLY p ("$" ^ strS APPLY sigma)
         | UnivS(alphaks, sigma) =>
            paren BIND p
            (
                "![" ^ list (strAK "/") alphaks ^ "]." ^
                strS BIND sigma
            )
         | ExistS(alphaks, sigma) =>
            paren BIND p
            (
                "?[" ^ list (strAK "\\") alphaks ^ "]." ^
                strS BIND sigma
            )

    fun strV p =
        fn IntV(n) => Int.toString n
         | StringV(s) => "\"" ^ String.toString s ^ "\""
         | TupleV(vs) => "(" ^ list strV vs ^ ")"
         | VariantV(TupleV[], 1, VariantT[TupleT[], TupleT[]]) => "false"
         | VariantV(TupleV[], 2, VariantT[TupleT[], TupleT[]]) => "true"
         | VariantV(v, i, VariantT(taus)) =>
           if List.nth(taus, i-1) = TupleT[] then
            "@" ^ Int.toString i
           else
            paren APPLY p
            (
                strV APPLY v ^
                "@" ^ Int.toString i
            )
         | VariantV(v, i, tau) =>
            paren APPLY p
            (
                strV APPLY v ^
                "@" ^ Int.toString i
            )
         | LambdaV(x, sigma, e) =>
            paren BIND p
            (
                "\\" ^ strX ATOM x ^ ":" ^ strS APPLY sigma ^ "." ^
                "e"
            )
         | GenV(alphas, e) =>
            paren BIND p
            (
                "/\\[" ^ list strA alphas ^ "]." ^
                "e"
            )
         | FoldV(alpha) => "fold_" ^ strA ATOM alpha
         | UnfoldV(alpha) => "unfold_" ^ strA ATOM alpha
         | ConV(alpha, taus, v) =>
            paren APPLY p
            (
                "fold_" ^ strA ATOM alpha ^
                "[" ^ list strT taus ^ "]" ^
                "(" ^ strV TOP v ^ ")"
            )

    fun strW omega p =
        fn VarW(x) => ("$" ^ strEntry omega p (lookup omega x) handle Lookup => x)
         | TypW(tau) => "[" ^ strT TOP tau ^ "]"
         | TermW(v) => "[" ^ strV TOP v ^ "]"
         | StructW(lws) => "{" ^ list (strField "=" (strW omega)) lws ^ "}"
         | LambdaW(x, sigma, m) => 
            paren BIND p
            (
                "\\" ^ strX ATOM x ^ ":" ^ strS APPLY sigma ^ "." ^
                "M"
            )
         | GenDownW(alphaks, m) =>
            paren BIND p
            (
                "/\\[" ^ list (strAK "\\") alphaks ^ "]." ^
                "M"
            )
         | GenUpW(alphaks, m) =>
            paren BIND p
            (
                "/\\[" ^ list (strAK "/") alphaks ^ "]." ^
                "M"
            )

    and strEntry omega p =
        fn Evaluated w => strW omega p w
         | Evaluating => "..."
         | Defined m => (case ILMachine.toModval m of SOME w => strW omega p w | NONE => "M")
         | Undefined => "?"

    fun strE omega p =
        fn ValE(m) => "ValE(" ^ strM omega TOP m ^ ")"
         | IntE(i) => Int.toString i
         | StringE(s) => String.toString s
         | PlusE(e1, e2) =>
            paren PLUS p
            (
                strE omega PLUS e1 ^
                " + " ^
                strE omega PLUS e2
            )
         | MinusE(e1, e2) =>
            paren PLUS p
            (
                strE omega PLUS e1 ^
                " - " ^
                strE omega PLUS e2
            )
         | EqualE(e1, e2) =>
            paren COMP p
            (
                strE omega (COMP + 1) e1 ^
                " == " ^
                strE omega (COMP + 1) e2
            )
         | LessE(e1, e2) =>
            paren PLUS p
            (
                strE omega PLUS e1 ^
                " < " ^
                strE omega PLUS e2
            )
         | CatE(e1, e2) =>
            paren PLUS p
            (
                strE omega PLUS e1 ^
                " ++ " ^
                strE omega PLUS e2
            )
         | TupleE(es) => "<" ^ list (strE omega) es ^ ">"
         | DotE(e, i) =>
            paren DOT p
            (
                strE omega DOT e ^
                "#" ^ Int.toString i
            )
         | VariantE(e, i, tau) =>
            paren APPLY p
            (
                strE omega APPLY e ^
                "@" ^ Int.toString i
            )
         | CaseE(e, xes) =>
            paren BIND p
            (
                "case " ^ strE omega COMP e ^ " of " ^
                String.concatWith " | " (List.map (fn(x, e) => x ^ " -> " ^ strE omega (BIND + 1) e) xes)
            )
         | LambdaE(x, sigma, e) =>
            paren BIND p
            (
                "\\" ^ x ^ ":" ^ strS APPLY sigma ^ "." ^
                strE omega BIND e
            )
         | ApplyE(e, m) =>
            paren APPLY p
            (
                strE omega APPLY e ^
                " " ^
                strM omega (APPLY + 1) m
            )
         | GenE(alphas, e) =>
            paren BIND p
            (
                "/\\[" ^ list strA alphas ^ "]." ^
                strE omega BIND e
            )
         | InstE(e, taus) =>
            paren APPLY p
            (
                strE omega APPLY e ^
                "[" ^ list strT taus ^ "]"
            )
         | FoldE(alpha) => "fold_" ^ strA ATOM alpha
         | UnfoldE(alpha) => "unfold_" ^ strA ATOM alpha
         | ConE(e1, taus, e2) =>
            paren APPLY p
            (
                strE omega APPLY e1 ^
                "[" ^ list strT taus ^ "]" ^
                "(" ^ strE omega TOP e2 ^ ")"
            )
         | PrintE(e) =>
            paren APPLY p
            (
                "print " ^
                strE omega ATOM e
            )

    and strM omega p =
        fn VarM(x) => x
         | TypM(tau) => "[" ^ strT TOP tau ^ "]"
         | TermM(e) => "[" ^ strE omega TOP e ^ "]"
         | StructM(lms) => "{" ^ list (strField "=" (strM omega)) lms ^ "}"
         | DotM(m, l) =>
            paren DOT p
            (
                strM omega DOT m ^ "." ^ l
            )
         | LambdaM(x, sigma, m) =>
            paren BIND p
            (
                "\\" ^ strX ATOM x ^ ":" ^ strS APPLY sigma ^ "." ^
                strM omega BIND m
            )
         | ApplyM(m1, m2) =>
            paren APPLY p
            (
                strM omega APPLY m1 ^
                " " ^
                strM omega (APPLY + 1) m2
            )
         | LetM(x, m1, m2) =>
            paren BIND p
            (
                "let " ^ x ^ " = " ^
                strM omega TOP m1 ^ " in " ^
                strM omega BIND m2
            )
         | GenDownM(alphaks, m) =>
            paren BIND p
            (
                "/\\[" ^ list (strAK "\\") alphaks ^ "]." ^
                strM omega BIND m
            )
         | InstDownM(m, taus) =>
            paren APPLY p
            (
                strM omega APPLY m ^
                "\\[" ^ list strT taus ^ "]"
            )
         | GenUpM(alphaks, m) =>
            paren BIND p
            (
                "/\\[" ^ list (strAK "/") alphaks ^ "]." ^
                strM omega BIND m
            )
         | InstUpM(m, alphas) =>
            paren APPLY p
            (
                strM omega APPLY m ^
                "/[" ^ list strA alphas ^ "]"
            )
         | NewTypM(alphaks, m) =>
            paren BIND p
            (
                "new [" ^ list (strAK "/") alphaks ^ "] in " ^
                strM omega BIND m
            )
         | DefEquiM(alpha, tau, m, sigma, _, _, _) =>
            paren BIND p
            (
                "def " ^ alpha ^ " = " ^ strT TOP tau ^ " in " ^
                strM omega BIND m
            )
         | DefIsoM(alpha, tau, m, sigma) =>
            paren BIND p
            (
                "def " ^ alpha ^ " ~ " ^ strT TOP tau ^ " in " ^
                strM omega BIND m
            )
         | NewTermM(x, sigma, m) =>
            paren BIND p
            (
                "new " ^ x ^ ":" ^ strS APPLY sigma ^ " in " ^
                strM omega BIND m
            )
         | AssignM(m1, m2) =>
            paren ASSIGN p
            (
                strM omega (ASSIGN + 1) m1 ^
                " := " ^
                strM omega ASSIGN m2
            )
         | ForceM(m) =>
            paren APPLY p
            (
                strM omega APPLY m ^ "!"
            )

    val strF =
        fn ValF => "ValF"
         | PlusF1 _ => "PlusF1"
         | PlusF2 _ => "PlusF2"
         | MinusF1 _ => "MinusF1"
         | MinusF2 _ => "MinusF2"
         | EqualF1 _ => "EqualF1"
         | EqualF2 _ => "EqualF2"
         | LessF1 _ => "LessF1"
         | LessF2 _ => "LessF2"
         | CatF1 _ => "CatF1"
         | CatF2 _ => "CatF2"
         | TupleF _ => "TupleF"
         | ProjF _ => "ProjF"
         | VariantF _ => "VariantF"
         | CaseF _ => "CaseF"
         | AppF1 _ => "AppF1"
         | AppF2 _ => "AppF2"
         | InstF _ => "InstF"
         | ConF1 _ => "ConF1"
         | ConF2 _ => "ConF2"
         | PrintF => "PrintF"
         | TermF => "TermF"
         | StructF _ => "StructF"
         | DotF _ => "DotF"
         | ApplyF1 _ => "ApplyF1"
         | ApplyF2 _ => "ApplyF2"
         | LetF _ => "LetF"
         | InstDownF _ => "InstDownF"
(* todo: real effect system
         | InstUpF _ => "InstUpF"
*)
         | InstUpF1 _ => "InstUpF1"
         | InstUpF2 _ => "InstUpF2"
         | AssignF _ => "AssignF"
         | ForceF => "ForceF"
         | NeededF _ => "NeededF"

    val strK = strK TOP
    val strT = strT TOP
    val strS = strS TOP
    val strV = strV TOP
    val strW = fn omega => strW omega TOP
    val strE = fn omega => strE omega TOP
    val strM = fn omega => strM omega TOP

    fun strO omega =
        String.concat(List.map (fn(x, entry) =>
                                x ^ " = " ^ strEntry omega TOP entry ^ "\n") (entries omega))

    fun strSt(BlackHole(x)) = "Black hole at " ^ x ^ "\n"
      | strSt(TermSt(delta, gamma, omega, cc, VAL v)) = strSt'(delta, gamma, omega, cc, strV v)
      | strSt(TermSt(delta, gamma, omega, cc, EXP e)) = strSt'(delta, gamma, omega, cc, strE omega e)
      | strSt(ModSt(delta, gamma, omega, cc, VAL w)) = strSt'(delta, gamma, omega, cc, strW omega w)
      | strSt(ModSt(delta, gamma, omega, cc, EXP m)) = strSt'(delta, gamma, omega, cc, strM omega m)
    and strSt'(delta, gamma, omega, cc, s) =
        "Current : " ^ s ^ "\n" ^
        "Continuation : " ^ String.concatWith ", " (List.map strF cc) ^ "\n" ^
        "Store :\n" ^ strO omega
end
