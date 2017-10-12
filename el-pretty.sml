(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature EL_PRETTY =
sig
    val indent : int ref
    val depth : int ref
    val ppAs : IL.var list -> PrettyPrint.doc
    val ppAKs : (IL.var * IL.kind) list -> PrettyPrint.doc
    val ppP : IL.lab list -> PrettyPrint.doc
    val ppK : IL.kind -> PrettyPrint.doc
    val ppT : IL.typ -> PrettyPrint.doc
    val ppS : ELAux.sign -> PrettyPrint.doc
    val ppF : ELAux.funct -> PrettyPrint.doc
    val ppD : ELAux.typ_context -> PrettyPrint.doc
    val ppG : ELAux.modl_context -> PrettyPrint.doc
    val ppL : ELAux.locator -> PrettyPrint.doc
    val ppR : IL.typ_subst -> PrettyPrint.doc
end

structure ELPretty : EL_PRETTY =
struct
    open PrettyPrint infix ^^ ^/^
    open IL
    open VarOps
    open ELAux

    fun asArrowsT(ArrowT(LazyS(IL.TermS(tau1)), tau2)) =
            let val taus = asArrowsT tau2 in tau1::taus end
      | asArrowsT(ArrowT(sigma, tau2)) =
            let val taus = asArrowsT tau2 in VarT("Sigma")::taus end
      | asArrowsT(tau) = [tau]

    fun asTypstruct[("type", Typ t)] = SOME t
      | asTypstruct _ = NONE

    fun asDatstruct[("type", Typ(IL.VarT(alpha), IL.StarK, pmo)),
                    ("in", Term(PureT(_, tau, _), _)),
                    ("out", _)] =
            SOME(alpha, tau, IL.StarK, pmo)
      | asDatstruct[("type", Typ(IL.VarT(alpha), k, pmo)),
                    ("in", Term(PureT(betas, tau, _), _)),
                    ("out", _)] =
            (case tau of
                  IL.ApplyT(tau', taus) =>
                  if taus = List.map IL.VarT betas
                  then SOME(alpha, tau', k, pmo)
                  else SOME(alpha, IL.LambdaT(betas, tau), k, pmo)
                | _ => SOME(alpha, IL.LambdaT(betas, tau), k, pmo)
            )
      | asDatstruct _ = NONE

    val indent = ref 2
    val depth = ref 8

    val TOP = 0
    val BIND = TOP+1
    val ARROW = BIND
    val PLUS = ARROW
    val TIMES = PLUS+1
    val APPLY = TIMES+1
    val ATOM = APPLY+1

    val nest = fn doc => nest (!indent) doc
    val hidden = fn _ => text "_"

    fun paren doc = text "(" ^^ fbox doc ^^ text ")"
    fun brace doc = text "{" ^^ fbox doc ^^ text "}"
    fun brack doc = text "[" ^^ fbox doc ^^ text "]"
    fun inner doc = abox(nest(ebreak ^^ abox(below doc)) ^^ ebreak)

    fun parenAt p p' doc = if p' > p then paren doc else doc

    fun ppList ppX (d, p) [] = empty
      | ppList ppX (d, p) [x] = ppX (d, p) x
      | ppList ppX (d, p) (x::xs) = ppX (d, p) x ^^ text "," ^/^ ppList ppX (d, p) xs

    fun ppListWith sep ppX (d, p) [] = empty
      | ppListWith sep ppX (d, p) [x] = ppX (d, p) x
      | ppListWith sep ppX (d, p) (x::xs) =
            ppX (d, p) x ^/^ text(sep ^ " ") ^^ ppListWith sep ppX (d, p) xs

    fun ppMap symbol ppX (d, p) =
        fn (a, x) =>
            abox(nest(
                text a ^^ text " " ^^ text symbol ^/^
                ppX (d, p) x
            ))

    fun ppColon ppX = ppMap ":" ppX

    fun ppA (d, p) alpha = text alpha
    fun ppAs (d, p) alphas = fbox(below(ppList ppA (d, TOP) alphas))
    fun ppP (d, p) ls = text(String.concatWith "." ls)

    fun ppK (d, p) =
        fn StarK => text "#"
         | ArrowK(1) => text "#->#"
         | ArrowK(n) => text("#" ^ Int.toString n ^ "->#")

    fun ppAKs (d, p) alphaks = fbox(below(ppList (ppColon ppK) (d, TOP) alphaks))

    fun ppT (0, p) = hidden
      | ppT (d, p) =
        fn VarT(alpha) => text alpha
         | IntT => text "int"
         | StringT => text "string"
         | TupleT[] => text "1"
         | TupleT[tau] => paren(text "* " ^^ ppT (d-1, TIMES+1) tau)
         | TupleT(taus) =>
            parenAt TIMES p
            (
                fbox(below(
                    ppListWith "*" ppT (d-1, TIMES+1) taus
                ))
            )
         | VariantT[] => text "0"
         | VariantT[TupleT[], TupleT[]] => text "bool"
         | VariantT[tau] => paren(text "| " ^^ ppT (d-1, PLUS+1) tau)
         | VariantT(taus) =>
            parenAt PLUS p
            (
                fbox(below(
                    ppListWith "|" ppT (d-1, PLUS+1) taus
                ))
            )
         | tau as ArrowT _ =>
            let val taus = asArrowsT tau in
            parenAt ARROW p
            (
                fbox(below(
                    ppListWith "->" ppT (d-1, ARROW+1) taus
                ))
            )
            end
         | UnivT(alphas, tau) =>
            parenAt BIND p
            (
                abox(below(
                    text "!" ^^ paren(ppAs (d, TOP) alphas) ^^ text "." ^/^
                    ppT (d, BIND) tau
                ))
            )
         | PureT(alphas, tau1, tau2) =>
            parenAt BIND p
            (
                abox(below(
                    text "!" ^^ paren(ppAs (d, TOP) alphas) ^^ text "." ^/^
                    abox(
                        ppT (d-1, ARROW+1) tau1 ^/^
                        text "=> " ^^ ppT (d-1, ARROW) tau2
                    )
                ))
            )
         | LambdaT(alphas, tau) =>
            parenAt BIND p
            (
                abox(below(
                    text "\\" ^^ paren(ppAs (d, TOP) alphas) ^^ text "." ^/^
                    ppT (d, BIND) tau
                ))
            )
         | ApplyT(tau, taus) =>
            parenAt APPLY p
            (
                abox(nest(
                    ppT (d, APPLY) tau ^/^
                    paren(inner(
                        ppList ppT (d-1, TOP) taus
                    ))
                ))
            )

    fun ppPM Plus = text "+"
      | ppPM Minus = text "-"

    fun ppS (0, p) = hidden
      | ppS (d, p) =
        fn Typ(tau, k, pmo) =>
            brack(inner(
                ppT (d-1, TOP) tau ^/^
                text ": " ^^
                ppK (d-1, TOP) k
            )) ^^ (case pmo of SOME pm => ppPM pm | NONE => empty)
         | Term(tau, pm) =>
            brack(inner(
                ppT (d-1, TOP) tau
            )) ^^ ppPM pm
         | Funct(phi, pm) =>
            brack(inner(
                ppF (d-1, TOP) phi
            )) ^^ ppPM pm
         | Struct(lsigmas) =>
            case asTypstruct lsigmas of
                SOME(tau, k, pmo) =>
                    brack(inner(
                        text "=" ^/^
                        ppT (d-1, TOP) tau ^/^
                        text ": " ^^
                        ppK (d-1, TOP) k
                    )) ^^ (case pmo of SOME pm => ppPM pm | NONE => empty)
              | NONE =>
            case asDatstruct lsigmas of
                SOME(alpha, tau, k, pmo) =>
                    brack(inner(
                        abox(
                            abox(
                                text "=" ^/^ text alpha ^/^ text "~"
                                ) ^^
                                nest(break ^^
                                ppT (d-1, TOP) tau
                            )
                        ) ^/^
                        text ": " ^^
                        ppK (d-1, TOP) k
                    )) ^^ (case pmo of SOME pm => ppPM pm | NONE => empty)
              | NONE =>
                brace(inner(
                    ppList (ppColon ppS) (d+1, TOP) lsigmas
                ))

    and ppF (0, p) = hidden
      | ppF (d, p) =
        fn(alphaks, betaks, sigma) =>
            abox(below(
                abox(
                    text "!" ^^ paren(ppAKs (d, TOP) alphaks) ^^ text "." ^/^
                    text "?" ^^ paren(ppAKs (d, TOP) betaks) ^^ text "."
                ) ^/^
                ppS (d-1, BIND) sigma
            ))

    fun ppD (d, p) =
        fn delta =>
            fbox(below(
                ppAKs (d, p) (entries delta)
            ))

    fun ppG (d, p) =
        fn gamma =>
            vbox(below(
                ppList (ppColon ppS) (d, p) (entries gamma)
            ))

    fun ppL (d, p) =
        fn loc =>
            fbox(below(
                ppList (ppMap "->" ppP) (d, p) (entries loc)
            ))

    fun ppR (d, p) =
        fn del =>
            fbox(below(
                ppList (ppMap "->" ppT) (d, p) (entries del)
            ))

    val ppAs = ppAs (!depth, TOP)
    val ppAKs = ppAKs (!depth, TOP)
    val ppP = ppP (!depth, TOP)
    val ppK = ppK (!depth, TOP)
    val ppT = ppT (!depth, TOP)
    val ppS = ppS (!depth, TOP)
    val ppF = ppF (!depth, TOP)
    val ppD = ppD (!depth, TOP)
    val ppG = ppG (!depth, TOP)
    val ppL = ppL (!depth, TOP)
    val ppR = ppR (!depth, TOP)
end
