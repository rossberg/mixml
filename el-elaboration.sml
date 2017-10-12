(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature EL_ELABORATION =
sig
    type context = ELAux.typ_context * ELAux.modl_context
    val emptyContext : context
    val elab : context -> EL.prog -> ELAux.funct * IL.modl
end

structure ELElaboration : EL_ELABORATION =
struct
    open VarOps infix |-> |=> |=>* ++ -- || \/ /\ \
    open ILOps
    open ELAux infix at
    open ELTrace

    (* Auxiliaries *)

    datatype pass = Stat | Dyn

    val dummyP = IL.VarM(rename "_dummy")
    val dummyE = IL.IntE(666)
    val dummyM = IL.StructM[]
    val dummyS = Struct[]

    fun renamesAKls alphaks ls =
        let
            val (alphaks', del) = renamesAK alphaks
            val prefix = if List.null ls then "" else String.concatWith "." ls ^ "."
            val alphaks'' = mapFst (fn alpha => prefix ^ alpha) alphaks'
            val del' = mapRan (fn IL.VarT(alpha) => IL.VarT(prefix ^ alpha) | tau => tau) del
        in
            (alphaks'', del')
        end

    fun sort lsigmas = entries(map lsigmas)

    fun asStruct(Struct(lsigmas)) = lsigmas
      | asStruct _ = raise Fail "asStruct"

    fun asTyp(Typ(tau, k, pmo)) = (tau, k, pmo)
      | asTyp _ = raise Fail "asTyp"

    fun asAbsTyp(Typ(IL.VarT(alpha), _, _)) = alpha
      | asAbsTyp _ = raise Fail "asAbsTyp"

    (* Solving *)

    exception Circular of IL.typvar

    fun solve delta (sigma1, sigma2) =
        let
            val _ = (traceIn(); trace' "solve" "begin"; traceD "delta" delta;
                     traceS "sigma1" sigma1; traceS "sigma2" sigma2)
            val del =  solve_ delta (sigma1, sigma2)
        in
            trace' "solve" "end"; traceR "del" del; traceOut();
            del
        end
    and solve_ delta (sigma1, sigma2) =
        let
            val loc1 = locator Minus sigma1 -- dom(locator Minus sigma2)
            val loc2 = locator Minus sigma2 -- dom(locator Minus sigma1)
            val _ = (trace' "solve" "1"; traceL "loc1" loc1; traceL "loc2" loc2)
            val eqs = composePartial sigma1 loc2 ++ composePartial sigma2 loc1
            val _ = (trace' "solve" "2"; traceR "eqs" eqs)
        in
            solve' delta (mapRan (normT delta) eqs, map[])
        end
    and solve' delta (eqs, del) =
        if isId eqs then del else
        case Map.entries(Map.filter (fn(alpha, tau) => not(member (fvT(tau)) alpha)) eqs) of
            [] => raise Circular(#1(List.hd(entries eqs)))
          | (alpha, tau)::_ =>
            let
                val del' = map[alpha |-> tau]
                val eqs' =
                    mapRan (normT delta o substT del') (eqs -- set[alpha])
            in
                solve' delta (eqs', mapRan (substT del') del ++ del')
            end


    (* Merging and matching *)

    exception Mismatch of EL.labs

    fun merge pass delta (sigma1, sigma2) p =
        case (sigma1, sigma2) of
            (Struct[], _) =>
                (sigma2, IL.StructM[], p)
          | (_, Struct[]) =>
                (sigma1, p, IL.StructM[])
          | (Typ(tau1, k1, pmo), Typ(tau2, k2, SOME Minus)) =>
            (*if not(k1 = k2 andalso equivT delta (tau1, tau2)) then raise Mismatch [] else*)
                (Typ(tau1, k1, pmo), p, p)
          | (Typ(tau1, k1, SOME Minus), Typ(tau2, k2, pmo)) =>
            (*if not(k1 = k2 andalso equivT delta (tau1, tau2)) then raise Mismatch [] else*)
                (Typ(tau2, k2, pmo), p, p)
          | (Typ(tau1, k1, pmo as (NONE | SOME Plus)), Typ(tau2, k2, NONE)) =>
            if not(k1 = k2 andalso equivT delta (tau1, tau2)) then raise Mismatch [] else
                (Typ(tau1, k1, pmo), p, p)
          | (Typ(tau1, k1, NONE), Typ(tau2, k2, pmo as SOME Plus)) =>
            if not(k1 = k2 andalso equivT delta (tau1, tau2)) then raise Mismatch [] else
                (Typ(tau2, k2, pmo), p, p)
          | (Term(tau1, Plus), Term(tau2, Minus)) =>
            let
                val (_, f) =
                    if pass = Stat then (map[], dummyE) else
                    matchT (delta, set[]) (tau1, tau2)
            in
                (Term(tau1, Plus),
                 p, ILOps.lazyM(IL.TermM(IL.ApplyE(f, IL.ForceM(p))), IL.TermS(tau2)))
            end
          | (Term(tau1, Minus), Term(tau2, Plus)) =>
            let
                val (_, f) =
                    if pass = Stat then (map[], dummyE) else
                    matchT (delta, set[]) (tau2, tau1)
            in
                (Term(tau2, Plus),
                 ILOps.lazyM(IL.TermM(IL.ApplyE(f, IL.ForceM(p))), IL.TermS(tau1)), p)
            end
          | (Term(tau1, Minus), Term(tau2, Minus)) =>
            let
                val (tau, m1, m2) =
                    let
                        val (_, f) = matchT (delta, set[]) (tau1, tau2)
                    in
                        (tau1,
                         p, ILOps.lazyM(IL.TermM(IL.ApplyE(f, IL.ForceM(p))), IL.TermS(tau2)))
                    end
                    handle Mismatch _ =>
                    let
                        val (_, f) = matchT (delta, set[]) (tau2, tau1)
                    in
                        (tau2,
                         ILOps.lazyM(IL.TermM(IL.ApplyE(f, IL.ForceM(p))), IL.TermS(tau1)), p)
                    end
                    handle Mismatch ls => raise Mismatch ls
            in
                (Term(tau, Minus), m1, m2)
            end
          | (Funct(phi1, Plus), Funct(phi2, Minus)) =>
            let
                val f = matchF pass delta (phi1, phi2)
                    handle Mismatch ls => raise Mismatch ls
            in
                (Funct(phi1, Plus), p, ILOps.lazyM(IL.ApplyM(f, IL.ForceM(p)), eraseF(phi2)))
            end
          | (Funct(phi1, Minus), Funct(phi2, Plus)) =>
            let
                val f = matchF pass delta (phi2, phi1)
                    handle Mismatch ls => raise Mismatch ls
            in
                (Funct(phi2, Plus), ILOps.lazyM(IL.ApplyM(f, IL.ForceM(p)), eraseF(phi1)), p)
            end
          | (Funct(phi1, Minus), Funct(phi2, Minus)) =>
            let
(*
                val (phi, m1, m2) =
                    let
                        val f = matchF pass delta (phi1, phi2)
                    in
                        (phi1, p, ILOps.lazyM(IL.ApplyM(f, IL.ForceM(p)), eraseF(phi2)))
                    end
                    handle Mismatch _ =>
                    let
                        val f = matchF pass delta (phi2, phi1)
                    in
                        (phi2, ILOps.lazyM(IL.ApplyM(f, IL.ForceM(p)), eraseF(phi1)), p)
                    end
                    handle Mismatch ls => raise Mismatch ls
            in
                (Funct(phi, Minus), m1, m2)
*)
                val () = if equivF delta (phi1, phi2) then () else raise Mismatch []
            in
                (Funct(phi1, Minus), p, p)
            end
          | (Struct(lsigmas1), Struct(lsigmas2)) =>
            let
                val (lsigmas, lms1, lms2) = merge' pass delta (sort lsigmas1, lsigmas2) p
            in
                (Struct(lsigmas), IL.StructM(lms1), IL.StructM(lms2))
            end
          | _ => raise Mismatch []
    and merge' pass delta (lsigmas1, lsigmas2) p =
        case (lsigmas1, lsigmas2) of
            ([], []) =>
                ([], [], [])
          | ((l, sigma)::lsigmas1', []) =>
            let
                val (lsigmas, lms1, lms2) = merge' pass delta (lsigmas1', lsigmas2) p
            in
                ((l, sigma)::lsigmas, (l, IL.DotM(p, l))::lms1, lms2)
            end
          | ([], (l, sigma)::lsigmas2') =>
            let
                val (lsigmas, lms1, lms2) = merge' pass delta (lsigmas1, lsigmas2') p
            in
                ((l, sigma)::lsigmas, lms1, (l, IL.DotM(p, l))::lms2)
            end
          | ((l1, sigma1)::lsigmas1', (l2, sigma2)::lsigmas2') =>
            case Var.compare(l1, l2) of
                LESS =>
                let
                    val (lsigmas', lms1, lms2) = merge' pass delta (lsigmas1', lsigmas2) p
                in
                    ((l1, sigma1)::lsigmas', (l1, IL.DotM(p, l1))::lms1, lms2)
                end
              | GREATER =>
                let
                    val (lsigmas', lms1, lms2) = merge' pass delta (lsigmas1, lsigmas2') p
                in
                    ((l2, sigma2)::lsigmas', lms1, (l2, IL.DotM(p, l2))::lms2)
                end
              | EQUAL =>
                let
                    val l = l1
                    val (sigma, m1, m2) = merge pass delta (sigma1, sigma2) (IL.DotM(p, l))
                        handle Mismatch ls => raise Mismatch(l::ls)
                    val (lsigmas', lms1', lms2') = merge' pass delta (lsigmas1', lsigmas2') p
                in
                    ((l, sigma)::lsigmas', (l, m1)::lms1', (l, m2)::lms2')
                end

    and matchF pass delta ((alphaks1, betaks1, sigma1), (alphaks2, betaks2, sigma2)) =
        let
            (* todo: rename? *)
            val del = solve (delta ++ map(alphaks1) ++ map(betaks1) ++ map(alphaks2) ++ map(betaks2)) (sigma1, neg sigma2)
                handle Circular alpha => raise Mismatch [alpha]
                     | Locate ls => raise Mismatch ls
            val f = matchS pass delta (substS del sigma1, substS del sigma2)
            val g = rename "_matchF.G"
            val x2 = rename "_matchF.X2"
        in
            IL.LambdaM(g, eraseF(alphaks1, betaks1, sigma1),
                IL.GenDownM(alphaks2, IL.GenUpM(betaks2,
                    IL.LambdaM(x2, eraseS(sigma2),
                        IL.NewTypM(betaks1,
                            ILOps.defEquiM(List.map (fn(beta2, k) =>
                                                     (beta2, substT del (IL.VarT(beta2)))) betaks2,
                                IL.ApplyM(
                                    IL.ApplyM(
                                        f,
                                        IL.InstUpM(
                                            IL.InstDownM(
                                                IL.VarM(g),
                                                List.map (substT del o IL.VarT o #1) alphaks1
                                            ),
                                            List.map #1 betaks1
                                        )
                                    ),
                                    IL.VarM(x2)
                                ),
                                IL.StructS[]
                            )
                        )
                    )
                ))
            )
        end

    and matchS pass delta (sigma1, sigma2) =
        let
            val x = rename "_matchS.X"
            val f = rename "_matchS.F"
            val x2 = rename "_matchS.X2"
            val x2' = rename "_matchS.X2'"
            val (sigma, m1, m2) = merge pass delta (sigma1, neg sigma2) (IL.VarM(x))
        in
            IL.LambdaM(f, IL.ArrowS(eraseS(sigma1), IL.StructS[]),
                IL.LambdaM(x2, eraseS(sigma2),
                    IL.LetM(x, create(sigma),
                        IL.LetM(x2', m2,
                            ILOps.seqM[
                                copy(IL.VarM(x2'), IL.VarM(x2), sigma2),
                                IL.ApplyM(IL.VarM(f), m1)
                            ]
                        )
                    )
                )
            )
        end

    and matchT (delta, alphas) (tau1, tau2) =
        let
            (* todo: match polymorphic types *)
            val x = rename "_matchT.X"
        in
            if equivT delta (tau1, tau2)
            then (map[], IL.LambdaE(x, IL.TermS(tau1), IL.ValE(IL.VarM(x))))
            else raise Mismatch []
        end
    and matchT_ (delta, alphas) (tau1, tau2) =
        case (tau1, tau2) of
            (IL.UnivT(alphas1, tau1'), IL.UnivT(alphas2, tau2')) =>
            let
                val (alphas1', del1) = renamesA alphas1
                val (alphas2', del2) = renamesA alphas2
                val (del, f) =
                    matchT (delta ++ map(alphas1' |=>* IL.StarK) ++ map(alphas2' |=>* IL.StarK), alphas \/ set(alphas1')) (substT del1 tau1', substT del2 tau2')
                val x = rename "_matchT.X"
            in
                (del,
                 IL.LambdaE(x, IL.TermS(tau1),
                    IL.GenE(alphas2',
                        IL.ApplyE(f,
                            IL.TermM(
                                IL.InstE(IL.ValE(IL.VarM(x)),
                                    List.map (substT del o IL.VarT) alphas1'
                                )
                            )
                        )
                    )
                 )
                )
            end
          | (IL.UnivT(alphas1, tau1'), _) =>
            let
                val (alphas1', del1) = renamesA alphas1
                val (del, f) = matchT (delta ++ map(alphas1' |=>* IL.StarK), alphas \/ set(alphas1')) (substT del1 tau1', tau2)
                val x = rename "_matchT.X"
            in
                (del,
                 IL.LambdaE(x, IL.TermS(tau1),
                    IL.ApplyE(f,
                        IL.TermM(
                            IL.InstE(IL.ValE(IL.VarM(x)),
                                List.map (substT del o IL.VarT) alphas1'
                            )
                        )
                    )
                 )
                )
            end
          | (_, IL.UnivT([], tau2')) =>
            let
                val (del, f) = matchT (delta, alphas) (tau1, tau2')
                val x = rename "_matchT.X"
            in
                (del,
                 IL.LambdaE(x, IL.TermS(tau1),
                    IL.ApplyE(f,
                        IL.TermM(
                            IL.GenE([], IL.ValE(IL.VarM(x)))
                        )
                    )
                 )
                )
            end
          | (_, _) =>
            let
                val (del, alphas') = unify (delta, map[], alphas) (tau1, tau2)
                val x = rename "_unify.X"
            in
                (del,
                 IL.LambdaE(x, IL.TermS(tau1), IL.ValE(IL.VarM(x)))
                )
            end

    and unify (delta, del, alphas) (tau1, tau2) =
        let
            (* todo: match polymorphic types *)
            val x = rename "_matchT.X"
        in
            if equivT delta (tau1, tau2)
            then (map[], set[])
            else raise Mismatch []
        end


    (* Kinds *)

    fun elabK {it, region} =
        case it of
            EL.StarK => IL.StarK
          | EL.ArrowK(n) => IL.ArrowK(n)


    (* Types *)

    fun elabT (delta, gamma) {it, region} =
        case it of
(*
            EL.VarT(alpha) =>
            let
                val k = lookup delta alpha
                    handle Lookup => raise EL.Error(region, "unbound type variable " ^ alpha)
            in
                (IL.VarT(alpha), k)
            end
*)
            EL.ModT(modl) =>
            let
                val (sigma, _) = elabMclosed Stat (delta, gamma) modl
                val (tau, k) =
                    (case sigma at ["type"] of
                        Typ(tau, k, pmo) => (tau, k)
                      | _ => raise EL.Error(region, "module is not a type")
                    ) handle At => raise EL.Error(region, "module is not a type")
            in
                (tau, k)
            end
          | EL.IntT =>
                (IL.IntT, IL.StarK)
          | EL.StringT =>
                (IL.StringT, IL.StarK)
          | EL.TupleT(typs) =>
            let
                val taus = List.map (fn typ => elabT' (delta, gamma) typ) typs
            in
                (IL.TupleT(taus), IL.StarK)
            end
          | EL.VariantT(typs) =>
            let
                val taus = List.map (fn typ => elabT' (delta, gamma) typ) typs
            in
                (IL.VariantT(taus), IL.StarK)
            end
          | EL.ArrowT(typ1, typ2) =>
            let
                val tau1 = elabT' (delta, gamma) typ1
                val tau2 = elabT' (delta, gamma) typ2
            in
                (IL.ArrowT(IL.LazyS(IL.TermS(tau1)), tau2), IL.StarK)
            end
          | EL.UnivT(alphas, typ) =>
            let
                val tau = elabT' (delta ++ map(alphas |=>* IL.StarK),
                                  gamma ++ map(List.map (fn alpha => (alpha, typstruct(IL.VarT(alpha), IL.StarK, NONE))) alphas)) typ
            in
                (IL.UnivT(alphas, tau), IL.StarK)
            end
          | EL.LambdaT(alphas, typ) =>
            let
                val tau = elabT' (delta ++ map(alphas |=>* IL.StarK),
                                  gamma ++ map(List.map (fn alpha => (alpha, typstruct(IL.VarT(alpha), IL.StarK, NONE))) alphas)) typ
            in
                (IL.LambdaT(alphas, tau), IL.ArrowK(List.length alphas))
            end
          | EL.ApplyT(typ, typs) =>
            let
                val (tau, n) =
                    case elabT (delta, gamma) typ of
                        (tau, IL.ArrowK(n)) => (tau, n)
                      | (tau, IL.StarK) => raise EL.Error(#region typ, "not a type constructor")
                val taus = List.map (fn typ_i => elabT' (delta, gamma) typ_i) typs
            in
                case Int.compare(List.length taus, n) of
                    EQUAL => (IL.ApplyT(tau, taus), IL.StarK)
                  | LESS => raise EL.Error(region, "too few arguments in type application")
                  | GREATER => raise EL.Error(region, "too many arguments in type application")
            end

    and elabT' (delta, gamma) typ =
        case elabT (delta, gamma) typ of
            (tau, IL.StarK) => normT delta tau
          | (tau, IL.ArrowK(n)) => raise EL.Error(#region typ, "type not ground")


    (* Expressions *)

    and elabE (delta, gamma) {it, region} =
        case it of
            EL.ModE(modl) =>
            let
                val (tau, m) =
                    case elabMclosed Dyn (delta, gamma) modl of
                        (Term(tau, pm), m) => (tau, m)
                      | _ => raise EL.Error(region, "module is not a value")
            in
                (tau, IL.ValE(IL.ForceM(m)))
            end
          | EL.IntE(n) =>
            let
            in
                (IL.IntT, IL.IntE(n))
            end
          | EL.StringE(s) =>
            let
            in
                (IL.StringT, IL.StringE(s))
            end
          | EL.PlusE(exp1, exp2) =>
            let
                val e1 = elabE' (delta, gamma) exp1 IL.IntT "addition operand"
                val e2 = elabE' (delta, gamma) exp2 IL.IntT "addition operand"
            in
                (IL.IntT, IL.PlusE(e1, e2))
            end
          | EL.MinusE(exp1, exp2) =>
            let
                val e1 = elabE' (delta, gamma) exp1 IL.IntT "subtraction operand"
                val e2 = elabE' (delta, gamma) exp2 IL.IntT "subtraction operand"
            in
                (IL.IntT, IL.MinusE(e1, e2))
            end
          | EL.EqualE(exp1, exp2) =>
            let
                val e1 = elabE' (delta, gamma) exp1 IL.IntT "comparison operand"
                val e2 = elabE' (delta, gamma) exp2 IL.IntT "comparison operand"
            in
                (IL.VariantT[IL.TupleT[], IL.TupleT[]], IL.EqualE(e1, e2))
            end
          | EL.LessE(exp1, exp2) =>
            let
                val e1 = elabE' (delta, gamma) exp1 IL.IntT "comparison operand"
                val e2 = elabE' (delta, gamma) exp2 IL.IntT "comparison operand"
            in
                (IL.VariantT[IL.TupleT[], IL.TupleT[]], IL.LessE(e1, e2))
            end
          | EL.CatE(exp1, exp2) =>
            let
                val e1 = elabE' (delta, gamma) exp1 IL.StringT "concatenation operand"
                val e2 = elabE' (delta, gamma) exp2 IL.StringT "concatenation operand"
            in
                (IL.StringT, IL.CatE(e1, e2))
            end
          | EL.TupleE(exps) =>
            let
                val (taus, es) = ListPair.unzip(List.map (fn exp => elabE (delta, gamma) exp) exps)
            in
                (IL.TupleT(taus), IL.TupleE(es))
            end
          | EL.ProjE(exp, i) =>
            let
                val (taus, e) =
                    case elabE (delta, gamma) exp of
                        (IL.TupleT(taus), e) => (taus, e)
                      | _ => raise EL.Error(region, "expression is not a tuple")
                val tau_i = List.nth(taus, i-1)
                    handle Subscript => raise EL.Error(region, "index out of range")
            in
                (tau_i, IL.DotE(e, i))
            end
          | EL.InjE(exp, i, typ) =>
            let
                val taus =
                    case elabT' (delta, gamma) typ of
                        IL.VariantT(taus) => taus
                      | _ => raise EL.Error(region, "type is not a variant")
                val tau_i = List.nth(taus, i-1)
                    handle Subscript => raise EL.Error(region, "index out of range")
                val e = elabE' (delta, gamma) exp tau_i "variant constructor"
            in
                (IL.VariantT(taus), IL.VariantE(e, i, IL.VariantT(taus)))
            end
          | EL.CaseE(exp, xexps) =>
            let
                val (taus, e) =
                    case elabE (delta, gamma) exp of
                        (IL.VariantT(taus), e) => (taus, e)
                      | _ => raise EL.Error(region, " not a variant")
                val (tau, xes) =
                    (case ListPair.mapEq
                            (fn((x, exp), tau) =>
                                (x, elabE (delta, gamma ++ map[x |-> Term(tau, Plus)]) exp))
                            (xexps, taus) of
                        [] => (IL.VariantT[], [])
                      | (x, (tau, e))::xtaues =>
                        if List.all (fn(x, (tau', e)) => equivT delta (tau, tau')) xtaues
                        then (tau, (x, e) :: List.map (fn(x, (tau, e)) => (x, e)) xtaues)
                        else raise EL.Error(region, "inconsistent branch types")
                    ) handle ListPair.UnequalLengths => raise EL.Error(region, "wrong number of branches")
            in
                (tau, IL.CaseE(e, xes))
            end
          | EL.LambdaE(x, typ, exp) =>
            let
                val tau1 = elabT' (delta, gamma) typ
                val (tau2, e) = elabE (delta, gamma ++ map[x |-> Term(tau1, Plus)]) exp
            in
                (IL.ArrowT(IL.LazyS(IL.TermS(tau1)), tau2),
                 IL.LambdaE(x, IL.LazyS(IL.TermS(tau1)), e))
            end
          | EL.ApplyE(exp1, exp2) =>
            let
                val ((tau2, tau), e1) =
                    case elabE (delta, gamma) exp1 of
                        (IL.ArrowT(IL.LazyS(IL.TermS(tau2)), tau), e1) => ((tau2, tau), e1)
                      | _ => raise EL.Error(#region exp1, "expression is not a function")
                val e2 = elabE' (delta, gamma) exp2 tau2 "function argument"
                val x = rename "_apply.X"
            in
                (tau,
                 IL.ApplyE(e1, IL.LetM(x, IL.TermM(e2), ILOps.lazyM(IL.VarM(x), IL.TermS(tau2)))))
            end
          | EL.GenE(alphas, exp) =>
            let
                val sigmas = List.map (fn alpha => typstruct(IL.VarT(alpha), IL.StarK, NONE)) alphas
                val (tau, e) = elabE (delta ++ map(alphas |=>* IL.StarK), gamma ++ map(alphas |=> sigmas)) exp
            in
                (IL.UnivT(alphas, tau),
                 IL.GenE(alphas,
                    ILOps.letE(alphas |=> List.map create sigmas,
                        e
                    )
                 )
                )
            end
          | EL.InstE(exp, typs) =>
            let
                val ((alphas, tau), e) =
                    case elabE (delta, gamma) exp of
                        (IL.UnivT(args), e) => (args, e)
                      | _ => raise EL.Error(#region exp, "expression is not polymorphic")
                val taus = List.map (fn typ => elabT' (delta, gamma) typ) typs
            in
                (substT (map(alphas |=> taus)) tau, IL.InstE(e, taus))
            end
          | EL.FoldE(modl, typs, exp) =>
            let
                val (sigma, _) = elabMclosed Stat (delta, gamma) modl
                val alpha =
                    (case sigma at ["type"] of
                        Typ(IL.VarT(alpha), k, pmo) => alpha
                      | _ => raise EL.Error(region, "module is not a data type")
                    ) handle At => raise EL.Error(region, "module is not a data type")
                val (alphas, tau1, tau2) =
                    (case sigma at ["in"] of
                        Term(IL.PureT(args), pm) => args
                      | _ => raise EL.Error(region, "module is not a data type")
                    ) handle At => raise EL.Error(region, "module is not a data type")
                val taus = List.map (fn typ => elabT' (delta, gamma) typ) typs
                val del = map(alphas |=> taus)
                    handle ListPair.UnequalLengths =>
                        raise EL.Error(region, "incorrect number of type arguments")
                val tau1' = substT del tau1
                val tau2' = substT del tau2
                val e = elabE' (delta, gamma) exp tau1' "constructor application"
            in
                (tau2', IL.ConE(IL.FoldE(alpha), taus, e))
            end
          | EL.UnfoldE(modl, typs, exp) =>
            let
                val (sigma, _) = elabMclosed Stat (delta, gamma) modl
                val alpha =
                    (case sigma at ["type"] of
                        Typ(IL.VarT(alpha), k, pmo) => alpha
                      | _ => raise EL.Error(region, "module is not a data type")
                    ) handle At => raise EL.Error(region, "module is not a data type")
                val (alphas, tau1, tau2) =
                    (case sigma at ["out"] of
                        Term(IL.PureT(args), pm) => args
                      | _ => raise EL.Error(region, "module is not a value")
                    ) handle At => raise EL.Error(region, "module is not a data type")
                val taus = List.map (fn typ => elabT' (delta, gamma) typ) typs
                val del = map(alphas |=> taus)
                    handle ListPair.UnequalLengths =>
                        raise EL.Error(region, "incorrect number of type arguments")
                val tau1' = substT del tau1
                val tau2' = substT del tau2
                val e = elabE' (delta, gamma) exp tau1' "deconstructor application"
            in
                (tau2', IL.ConE(IL.UnfoldE(alpha), taus, e))
            end
          | EL.LetE(x, modl, exp) =>
            let
                val (betaks', sigma', f) =
                    case elabU (delta, gamma) modl of
                        (([], betaks, sigma), f) => (betaks, sigma, f)
                      | _ => raise EL.Error(#region modl, "imports in local module")
                val (betaks, del) = renamesAK betaks'
                val sigma = substS del sigma'
                val betas = List.map #1 betaks
                val (tau, e) = elabE (delta ++ map(betaks), gamma ++ map[x |-> sigma]) exp
            in
                if not(equivS delta (sigma, abs sigma))
                then raise EL.Error(region, "imports in local module")
                else if not(isEmpty(fvT(tau) /\ set(betas)))
                then raise EL.Error(region, "local type name escapes scope")
                else (tau,
                    IL.ValE(
                        IL.NewTypM(betaks,
                            IL.LetM(x, create(sigma),
                                ILOps.seqM[
                                    IL.ApplyM(
                                        IL.InstUpM(
                                            IL.InstDownM(f, []),
                                            betas
                                        ),
                                        IL.VarM(x)
                                    ),
                                    IL.TermM(e)
                                ]
                            )
                        )
                    )
                )
            end
          | EL.PrintE(exp) =>
            let
                val (tau, e) = elabE (delta, gamma) exp
            in
                (IL.TupleT[], IL.PrintE(e))
            end

    and elabE' (delta, gamma) exp tau blame =
        let
            val (tau', e) = elabE (delta, gamma) exp
        in
            if equivT delta (tau, tau')
            then e
            else raise EL.Error(#region exp, "type mismatch in " ^ blame)
        end


    (* Template Modules *)

    and templateM (delta, gamma) modl ls =
        let
            val _ = (traceIn(); traceModl "templateM" modl "begin";
                     traceD "delta" delta; traceG "gamma" gamma; traceP "ls" ls)
            val (sigma, alphaks, betaks) = templateM_ (delta, gamma) modl ls
        in
            traceModl "templateM" modl "end"; traceS "sigma" sigma;
            traceAKs "alphaks" alphaks; traceAKs "betaks" betaks; traceOut();
            assert(fn() => subset(fvF(alphaks, betaks, sigma), dom(delta)));
            assert(fn() => equal(dom(locator Minus sigma), dom(map(alphaks))));
            (sigma, alphaks, betaks)
        end
    and templateM_ (delta, gamma) (this as {it, region}) ls =
        case it of
            EL.VarM(x) =>
            let
                val sigma = lookup gamma x
                    handle Lookup => raise EL.Error(region, "unbound variable " ^ x)
            in
                 (abs(staticS sigma), [], [])
            end
          | EL.EmptyM => (Struct[], [], [])
          | EL.ValM(exp) => (Term(staticT, Plus), [], [])
          | EL.AbsValM(typ) => (Term(staticT, Minus), [], [])
          | EL.TypM(typ) =>
            let
                val (tau, k) = elabT (delta, gamma) typ
            in
                (typstruct(tau, k, NONE), [], [])
            end
          | EL.AbsTypM(kind) =>
            let
                val k = elabK kind
                val alpha = rename(if List.null ls then "_type" else String.concatWith "." ls)
            in
                (typstruct(IL.VarT(alpha), k, SOME Minus), [alpha |-> k], [])
            end
          | EL.DatTypM(typ) =>
            let
                val (tau, k) = elabT (delta, gamma) typ
                val beta = rename(if List.null ls then "_data" else String.concatWith "." ls)
            in
                (typstruct(IL.VarT(beta), k, SOME Plus), [], [beta |-> k])
            end
          | EL.AbsDatTypM(typ) =>
            let
                val (tau, k) = elabT (delta, gamma) typ
                val alpha = rename(if List.null ls then "_data" else String.concatWith "." ls)
            in
                (typstruct(IL.VarT(alpha), k, SOME Minus), [alpha |-> k], [])
            end
          | EL.UnitM(modl) => (Funct(templateU (delta, gamma) modl, Plus), [], [])
          | EL.AbsUnitM(sign) => (Funct(templateS (delta, gamma) sign [], Minus), [], [])
          | EL.NewM(modl) =>
            let
                val (alphaks', betaks', sigma') =
                    case templateM (delta, gamma) modl ls of
                        (Funct(phi, Plus), [], []) => phi
                      | (Funct(phi, Minus), _, _) => raise EL.Error(region, "undefined unit")
                      | _ => raise EL.Error(region, "module not a unit")
                val (alphaks, del1) = renamesAKls alphaks' ls
                val (betaks, del2) = renamesAKls betaks' ls
            in
                (substS (del1 ++ del2) sigma', alphaks, betaks)
            end
          | EL.StructM(l, modl) =>
            let
                val (sigma, alphaks, betaks) = templateM (delta, gamma) modl (ls@[l])
            in
                (Struct[(l, sigma)], alphaks, betaks)
            end
          | EL.DotM(modl, l) =>
            let
                val (sigma, alphaks, betaks) = templateM (delta, gamma) modl []
            in
                if not(List.all (fn(_, []) => false | (_, l'::ls) => l' = l)
                                (entries(locator Minus sigma)))
                then raise EL.Error(region, "left-over imports in local module")
                else
                (sigma at [l], alphaks, betaks)
                handle At => raise EL.Error(region, "unknown field " ^ l)
            end
          | EL.LinkM(x, modl1, modl2) =>
            let
                val (sigma1', alphaks1'', betaks1) = templateM (delta, gamma) modl1 ls
                val (sigma2', alphaks2'', betaks2) =
                    templateM (delta ++ map(alphaks1'') ++ map(betaks1),
                               gamma ++ map[x |-> sigma1']) modl2 ls
                val del2 = composePartial sigma1' (locator Minus sigma2')
                    handle Locate ls =>
                        raise EL.Error(region, "linked modules inconsistent" ^
                                               (if List.null ls then "" else " at path " ^
                                                String.concatWith "." ls))
                val sigma2'' = substS del2 sigma2'
                val alphas = List.foldr op\/ (set[]) (List.map (fvT o #2) (entries del2))
                val del1 = composePartial sigma2'' (locator Minus sigma1' -- alphas)
                    handle Locate ls =>
                        raise EL.Error(region, "linked modules inconsistent" ^
                                               (if List.null ls then "" else " at path " ^
                                                String.concatWith "." ls))
                val sigma1 = substS del1 sigma1'
                val sigma2 = substS del1 sigma2''
                val alphaks1 = List.filter (not o member (dom(del1)) o #1) alphaks1''
                val alphaks2 = List.filter (not o member (dom(del2)) o #1) alphaks2''
                val _ = (traceModl "templateM" this "1";
                         traceS "sigma1'" sigma1';
                         traceAKs "alphaks1''" alphaks1''; traceAKs "betaks1" betaks1;
                         traceS "sigma2'" sigma2';
                         traceAKs "alphaks2''" alphaks2''; traceAKs "betaks2" betaks2;
                         traceR "del2" del2; traceS "sigma2''" sigma2'';
                         traceAs "alphas" (items alphas);
                         traceR "del1" del1; traceS "sigma1" sigma1; traceS "sigma2" sigma2;
                         traceAKs "alphaks1" alphaks1; traceAKs "alphaks2" alphaks2)
                val (sigma, _, _) = merge Stat (delta ++ map(alphaks1'') ++ map(alphaks2'') ++ map(betaks1) ++ map(betaks2)) (sigma1, sigma2) dummyP
                    handle Mismatch ls =>
                        raise EL.Error(region, "linked modules inconsistent" ^
                                               (if List.null ls then "" else " at path " ^
                                                String.concatWith "." ls))
                val fv = fvF(alphaks1 @ alphaks2, betaks1 @ betaks2, sigma) \ dom(delta)
            in
                if isEmpty fv
                then (sigma, alphaks1 @ alphaks2, betaks1 @ betaks2)
                else raise EL.Error(region, "linking produces circularity for type " ^ choose fv)
            end
          | EL.OLinkM(x, modl1, modl2) =>
            let
                val (sigma, alphaks, betaks) = templateM (delta, gamma) modl1 ls
            in
                (abs(sigma), [], alphaks @ betaks)
            end
          | EL.SealM(modl, sign) =>
            let
                val (alphaks, betaks, sigma) = templateS (delta, gamma) sign ls
            in
                (sigma, alphaks, betaks)
            end
(*
          | EL.LetM(x, modl1, modl2) =>
            let
                val (sigma1, alphaks1, betaks1) = templateM (delta, gamma) modl1 ls
                val (sigma2, alphaks2, betaks2) =
                    templateM (delta ++ map(alphaks1) ++ map(betaks1), gamma ++ map[x |-> sigma1])
                              modl2 ls
            in
                if not(List.null alphaks1)
                then raise EL.Error(region, "imports in local module")
                else (sigma2, alphaks2, betaks1 @ betaks2)
            end
*)

    and templateU (delta, gamma) modl =
        let
            val _ = (traceIn(); traceModl "templateU" modl "begin";
                     traceD "delta" delta; traceG "gamma" gamma)
            val _ = assert(fn() => subset(fvG(gamma), dom(delta)))
            val (sigma, alphaks, betaks) = templateM (delta, gamma) modl []
        in
            traceModl "templateU" modl "end";
            traceF "phi" (alphaks, betaks, sigma); traceOut();
            assert(fn() => subset(fvF(alphaks, betaks, sigma), dom(delta)));
            assert(fn() => equal(dom(locator Minus sigma), dom(map(alphaks))));
            (alphaks, betaks, sigma)
        end

    and templateS (delta, gamma) sign ls =
        let
            val _ = (traceIn(); traceSign "templateS" sign "begin";
                     traceD "delta" delta; traceG "gamma" gamma; traceP "ls" ls)
            val _ = assert(fn() => subset(fvG(gamma), dom(delta)))
            val phi = templateS_ (delta, gamma) sign ls
        in
            traceSign "templateS" sign "end"; traceF "phi" phi; traceOut();
            assert(fn() => subset(fvF(phi), dom(delta)));
            assert(fn() => equal(dom(locator Minus (#3 phi)), dom(map(#1 phi))));
            phi
        end
    and templateS_ (delta, gamma) {it, region} ls =
        case it of
            EL.ExportS(modl, lss) =>
            let
                val (sigma', alphaks', betaks') = templateM (delta, gamma) modl ls
                val sigma = export lss sigma'
                val alphaks = List.filter (member(dom(locator Minus sigma)) o #1) alphaks'
                val betaks = List.filter (member(dom(locator Plus sigma)) o #1) alphaks'
            in
                if not(List.null betaks')
                then raise EL.Error(region, "non-abstract module in signature expression")
                else (alphaks, betaks, sigma)
            end
          | EL.ImportS(modl, lss) =>
            let
                val (sigma', alphaks', betaks') = templateM (delta, gamma) modl ls
                val sigma = neg(export lss sigma')
                val alphaks = List.filter (member(dom(locator Minus sigma)) o #1) alphaks'
                val betaks = List.filter (member(dom(locator Plus sigma)) o #1) alphaks'
            in
                if not(List.null betaks')
                then raise EL.Error(region, "non-abstract module in signature expression")
                else (alphaks, betaks, sigma)
            end


    (* elabM : pass -> typ_context * modl_context * typvar list * sign -> modl -> path ->
               sign * typvar list * IL.modl *)
    and elabM pass (delta, gamma, betas0, sigma0) modl p =
        let
            val _ = (traceIn(); traceModl "elabM" modl "begin"; traceB "static" (pass = Stat);
                     traceD "delta" delta; traceG "gamma" gamma;
                     traceAs "betas0" betas0; traceS "sigma0" sigma0)
            val _ = assert(fn() => subset(fvG(gamma) \/ set(betas0) \/ fvS(sigma0), dom(delta)))
            val (sigma, betas, m) = elabM_ pass (delta, gamma, betas0, sigma0) modl p
        in
            traceModl "elabM" modl "end"; traceS "sigma" sigma; traceAs "betas'" betas;
            traceOut();
            assert(fn() => subset(fvS(sigma), dom(delta)));
            (sigma, betas, m)
        end
    and elabM_ pass (delta, gamma, betas0, sigma0) (this as {it, region}) p =
        case it of
            EL.VarM(x) =>
            let
                val sigma = lookup gamma x
                    handle Lookup => raise EL.Error(region, "unbound variable " ^ x)
                val sigma = if pass = Stat then staticS sigma else sigma
            in
                (abs(sigma), betas0, copy(IL.VarM(x), p, abs(sigma)))
            end
          | EL.EmptyM =>
            let
            in
                (Struct[], betas0, IL.StructM[])
            end
          | EL.ValM(exp) =>
            let
                val (tau, e) =
                    if pass = Stat then (staticT, dummyE)
                    else elabE (delta, gamma) exp
                val x = rename "_val.X"
            in
                (Term(tau, Plus), betas0,
                 IL.LetM(x, IL.TermM(e), IL.AssignM(p, IL.VarM(x))))
            end
          | EL.AbsValM(typ) =>
            let
                val tau =
                    if pass = Stat then staticT else
                    case elabT (delta, gamma) typ of
                        (tau, IL.StarK) => tau
                      | _ => raise EL.Error(region, "value type is not ground")
            in
                (Term(tau, Minus), betas0, IL.StructM[])
            end
          | EL.TypM(typ) =>
            let
                val (tau, k) = elabT (delta, gamma) typ
            in
                (typstruct(tau, k, NONE), betas0, IL.StructM[])
            end
          | EL.AbsTypM(kind) =>
            let
                val k = elabK kind
(* without realisers:
                val alpha = asAbsTyp(sigma0 at ["type"])
            in
                if lookup delta alpha <> k then raise EL.Error(region, "inconsistent kind")
                else (typstruct(IL.VarT(alpha), k, SOME Minus), betas0, IL.StructM[])
*)
                val (tau, k', pmo) = asTyp(sigma0 at ["type"])
            in
                if k' <> k then raise EL.Error(region, "inconsistent kind")
                else (typstruct(tau, k, Option.map (fn pm => Minus) pmo), betas0, IL.StructM[])
            end
          | EL.DatTypM(typ) =>
            let
                val (tau, k) = elabT (delta, gamma) typ
                val beta = List.hd betas0
                    handle Empty => raise EL.Error(region, "linearity failure at datatype")
            in
                if lookup delta beta <> k then raise EL.Error(region, "inconsistent kind")
                else (datstruct(beta, tau, k, SOME Plus), List.tl betas0,
                      IL.DefIsoM(beta, tau,
                        ILOps.seqM[
                            IL.AssignM(IL.DotM(p, "in"), IL.TermM(IL.FoldE(beta))),
                            IL.AssignM(IL.DotM(p, "out"), IL.TermM(IL.UnfoldE(beta)))
                        ],
                        IL.StructS[]
                      )
                     )
            end
          | EL.AbsDatTypM(typ) =>
            let
                val (tau, k) = elabT (delta, gamma) typ
(* without realisers:
                val alpha = asAbsTyp(sigma0 at ["type"])
            in
                if lookup delta alpha <> k then raise EL.Error(region, "inconsistent kind")
                else (datstruct(alpha, tau, k, Minus), betas0, IL.StructM[])
*)
                val (alpha, pmo) =
                    case asTyp(sigma0 at ["type"]) of
                        (IL.VarT(alpha), k', pmo) => (alpha, pmo)
                      | _ => raise EL.Error(region, "not an abstract type")
            in
                if lookup delta alpha <> k then raise EL.Error(region, "inconsistent kind")
                else (datstruct(alpha, tau, k, Option.map (fn pm => Minus) pmo), betas0, IL.StructM[])
            end
          | EL.UnitM(modl) =>
            let
                val (phi, f) = elabU (delta, gamma) modl
            in
                (Funct(phi, Plus), betas0, IL.AssignM(p, f))
            end
          | EL.AbsUnitM(sign) =>
            let
                val phi = elabS (delta, gamma) sign
            in
                (Funct(phi, Minus), betas0, IL.StructM[])
            end
          | EL.NewM(modl) =>
            let
                val x = rename "_new.X"
                val ((alphaks', betaks', sigma), m) =
                    case elabM pass (delta, gamma, [], Struct[]) modl (IL.VarM(x)) of
                        (Funct(phi, Plus), [], m) => (phi, m)
                      | (Funct(phi, Minus), _, _) => raise EL.Error(region, "undefined unit")
                      | _ => raise EL.Error(region, "module not a unit")
                val _ = (traceModl "elabM" this "1";
                         traceAKs "alphaks'" alphaks'; traceAKs "betaks'" betaks';
                         traceS "sigma0" sigma0; traceS "sigma" sigma)
                val (delA, rea) = composeImport sigma0 (locator Minus sigma)
                val _ = (traceModl "elabM" this "2";
                         traceR "delA" delA; traceR "rea" rea)
                val alphaks = mapFst (substA delA) alphaks'
                val betaks = ListPair.zip(betas0, List.map #2 betaks')
                val alphas = List.map #1 alphaks
                val betas = List.map #1 betaks
                val _ = (traceModl "elabM" this "3";
                         traceAKs "alphaks" alphaks; traceAKs "betaks" betaks)
                val delB = map(List.map #1 betaks' |=> List.map IL.VarT betas)
                val _ = (traceModl "elabM" this "4"; traceR "delB" delB)
                val sigma' = realS rea (substS (delA ++ delB) sigma)
                val _ = (traceModl "elabM" this "5"; traceS "sigma'" sigma')
            in
                if List.exists (fn(alpha, k) => lookup delta alpha <> k) (betaks)
                then raise EL.Error(region, "inconsistent kinding at instantiation") else
                (sigma', List.drop(betas0, List.length betas),
                 IL.NewTermM(x, eraseF(alphaks', betaks', sigma),
                    ILOps.seqM[
                        m,
                        IL.ApplyM(
                            IL.InstUpM(
                                IL.InstDownM(
                                    IL.ForceM(IL.VarM(x)),
                                    List.map (substT (delA ++ rea) o IL.VarT o #1) alphaks'
                                ),
                                betas
                            ),
                            p
                        )
                    ]
                 )
                )
            end
          | EL.StructM(l, modl) =>
            let
                val (sigma, betas', m) =
                    elabM pass (delta, gamma, betas0, lookup (map(asStruct sigma0)) l)
                               modl (IL.DotM(p, l))
            in
                (Struct[(l, sigma)], betas', m)
            end
          | EL.DotM(modl, l) =>
            let
                val x = rename "_dot.X"
                val x' = rename "_dot.X'"
                val (sigma0', _, _) = templateM (delta, gamma) modl []
                val sigma0'_l = lookup (map(asStruct sigma0')) l
                val (delA, rea) = composeImport sigma0 (locator Minus sigma0'_l)
                val delB = compose sigma0 (locator Plus sigma0'_l)
                val sigma0'' = realS rea (substS (delA ++ delB) sigma0')
                val _ = (traceModl "DotM" this "1";
                         traceR "rea" rea;
                         traceS "sigma0'" sigma0'; traceS "sigma0''" sigma0'')
                val (lsigmas, betas', m) =
                    case elabM pass (delta, gamma, betas0, sigma0'') modl (IL.VarM(x)) of
                        (Struct(lsigmas), betas', m) => (map(lsigmas), betas', m)
                      | _ => raise EL.Error(region, "module is not a structure")
                val sigma = lookup lsigmas l
                    handle Lookup => raise EL.Error(region, "unknown field " ^ l)
                val lsigmas' = entries(lsigmas -- set[l])
            in
                if not(List.all (fn(l, sigma') => equivS delta (sigma', abs sigma')) lsigmas')
                then raise EL.Error(region, "left-over imports in local module")
                else
                (sigma, betas',
                 IL.LetM(x', create(Struct(lsigmas')),
                    IL.LetM(x,
                        IL.StructM((l, p) ::
                            List.map (fn(l', _) => (l', IL.DotM(IL.VarM(x'), l'))) lsigmas'
                        ),
                        m
                    )
                 )
                )
            end
          | EL.LinkM(x1, modl1, modl2) =>
            let
                val alphas12 = dom(locator Minus sigma0)
                val (sigma01', alphaks1'', betaks1'') = templateM (delta, gamma) modl1 []
(* without realisers:
                val del1a' = compose sigma0 (locator Minus sigma01')
                val del1a = filter (fn(_, IL.VarT(alpha)) => member alphas12 alpha | _ => false) del1a'
                val del1b = compose sigma0 (locator Plus sigma01')
                val sigma01 = substS (del1a ++ del1b) sigma01'
                val (sigma02', alphaks2'', _) = templateM (delta ++ map(alphaks1'') ++ map(betaks1''), gamma ++ map[x1 |-> sigma01]) modl2 []
                val del2a' = compose sigma0 (locator Minus sigma02')
                val del2a = filter (fn(_, IL.VarT(alpha)) => member alphas12 alpha | _ => false) del2a'
                val del2b = compose sigma0 (locator Plus sigma02')
                val sigma02 = substS (del2a ++ del2b) sigma02'
*)
(* with realisers: *)
                val (del1a, rea1) = composeImport sigma0 (locator Minus sigma01')
                val del1b = compose sigma0 (locator Plus sigma01')
                val sigma01 = realS rea1 (substS (del1a ++ del1b) sigma01')
                val (sigma02', alphaks2'', _) = templateM (delta ++ map(alphaks1'') ++ map(betaks1''), gamma ++ map[x1 |-> sigma01]) modl2 []
                val (del2a, rea2) = composeImport sigma0 (locator Minus sigma02')
                val del2b = compose sigma0 (locator Plus sigma02')
                val sigma02 = realS rea2 (substS (del2a ++ del2b) sigma02')
(**)
                val _ = (traceModl "elabM" this "1";
                         traceAs "alphas12" (items alphas12);
                         traceS "sigma01'" sigma01'; traceS "sigma02'" sigma02';
                         traceAKs "alphaks1''" alphaks1''; traceAKs "alphaks2''" alphaks2'';
                         traceR "del1a" del1a; traceR "del1b" del1b;
                         traceR "del2a" del2a; traceR "del2b" del2b;
                         traceS "sigma01" sigma01; traceS "sigma02" sigma02)
(* without realisers:
                val alphaks1'' = mapFst (substA del1a) alphaks1''
                val alphaks2'' = mapFst (substA del2a) alphaks2''
*)
                val (alphaks1, alphaks1') = List.partition (member alphas12 o #1) alphaks1''
                val (alphaks2, alphaks2') = List.partition (member alphas12 o #1) alphaks2''
                val _ = (traceModl "elabM" this "2";
                         traceAKs "alphaks1" alphaks1; traceAKs "alphaks2" alphaks2;
                         traceAKs "alphaks1'" alphaks1'; traceAKs "alphaks2'" alphaks2')
                val (sigma1, betas1, m1) =
                    elabM pass (delta ++ map(alphaks1'), gamma, betas0, sigma01) modl1 (IL.VarM(x1))
                val _ = (traceModl "elabM" this "3"; traceS "sigma1" sigma1)
                val (sigma2, betas2, _) =
                    elabM Stat (delta ++ map(alphaks1') ++ map(alphaks2'),
                                gamma ++ map[x1 |-> sigma1], betas1, sigma02) modl2 dummyP
                val _ = (traceModl "elabM" this "4"; traceS "sigma2" sigma2)
(* without realisers:
                val () = locates sigma1 (List.map #1 alphaks1 @ List.map #1 alphaks1')
                val () = locates sigma2 (List.map #1 alphaks2 @ List.map #1 alphaks2')
*)
                val del = solve (delta ++ map(alphaks1') ++ map(alphaks2')) (sigma1, sigma2)
                    handle Circular alpha =>
                        raise EL.Error(region, "linking produces circularity for type " ^ alpha)
                      | Locate ls =>
                        raise EL.Error(region, "linked modules inconsistent at path " ^
                                               String.concatWith "." ls)
                val _ = (traceModl "elabM" this "5"; traceR "del" del)
                val x2 = rename "_link.X2"
                val (sigma2', m2) =
                    if pass = Stat then (realS del sigma2, dummyM) else
                    let
                        val (sigma2', betas2', m2) =
                            elabM Dyn (delta,
                                       gamma ++ map[x1 |-> realS del sigma1],
                                       betas1, realS del sigma02)
                                      modl2 (IL.VarM(x2))
                    in
                        if betas2 <> betas2'
                        then raise EL.Error(region, "linearity failure at linking")
                        else (sigma2', m2)
                    end
                val _ = (traceModl "elabM" this "6";
                         traceS "sigma1" sigma1; traceS "sigma2" sigma2;
                         traceS "sigma2'" sigma2'; traceD "delta" delta)
                val (sigma, m1', m2') =
                    merge pass (delta ++ map(alphaks1') ++ map(alphaks2'))
                        (realS del sigma1, realS del sigma2') p
                    handle Mismatch ls =>
                        raise EL.Error(region, "linked modules inconsistent at path " ^
                                               String.concatWith "." ls)
(* without realisers:
                val () = if equal(set(List.map #1 alphaks1) \/ set(List.map #1 alphaks2),
                                   dom(locator Minus sigma)) then () else
                    raise Fail "inconsistent set of abstract types"
*)
            in
                (sigma, betas2,
                 IL.LetM(x1, m1', IL.LetM(x2, m2', ILOps.seqM[substM del m1, m2])))
            end
          | EL.OLinkM(x1, modl1, modl2) =>
            let
                val (sigma01', alphaks1', betaks1') = templateM (delta, gamma) modl1 []
                val del1a = compose sigma0 (locator Minus sigma01')
                val del1b = compose sigma0 (locator Plus sigma01')
                val sigma01 = substS (del1a ++ del1b) sigma01'
                val alphaks1 = mapFst (substA del1a) alphaks1'
                val betaks1 = mapFst (substA del1b) betaks1'
                val alphas1 = List.map #1 alphaks1
                val betas1 = List.map #1 betaks1
                val alphasbetas1 = set(alphas1) \/ set(betas1)
                val _ = (traceModl "elabM" this "1";
                         traceS "sigma01'" sigma01';
                         traceAKs "alphaks1'" alphaks1'; traceAKs "betaks1'" betaks1';
                         traceAKs "alphaks1" alphaks1; traceAKs "betaks1" betaks1;
                         traceR "del1a" del1a; traceR "del1b" del1b;
                         traceS "sigma01" sigma01)
                val (sigma1, m1) =
                    case elabM pass (delta, gamma, betas1, sigma01) modl1 (IL.VarM(x1)) of
                        (sigma1, [], m1) => (sigma1, m1)
                      | _ => raise EL.Error(#region modl1, "linearity failure at linking 1a")
(* without realisers:
                val () = locates sigma1 alphas1
*)
                val () = if List.all (member alphasbetas1) (List.take(betas0, size alphasbetas1)) then () else
                    raise EL.Error(#region modl1, "linearity failure at linking 1c")
                val x = rename "_seals.X"
                val x2 = rename "_seals.X2"
                val (sigma, del, betaks2, m2, m1', m2') =
                    if pass = Stat then (dummyS, map[], [], dummyM, dummyM, dummyM) else
                    let
                        val (sigma02, alphaks2, betaks2) = templateM (delta, gamma ++ map[x1 |-> sigma01]) modl2 []
                        val alphas2 = List.map #1 alphaks2
                        val betas2 = List.map #1 betaks2
                        val sigma2 =
                            case elabM Stat (delta ++ map(alphaks2) ++ map(betaks2),
                                             gamma ++ map[x1 |-> sigma1], betas2, sigma02) modl2 dummyP of
                                (sigma2, [], _) => sigma2
                              | _ => raise EL.Error(#region modl2, "linearity failure at linking 2a")
(* without realisers:
                        val () = locates sigma2 alphas2
*)
                        val del = solve (delta ++ map(alphaks2) ++ map(betaks2)) (sigma1, sigma2)
                            handle Circular alpha =>
                                raise EL.Error(region, "linking produces circularity for type " ^ alpha)
                              | Locate ls =>
                                raise EL.Error(region, "linked modules inconsistent at path " ^
                                                       String.concatWith "." ls)
                        val (sigma2', m2) =
                            case elabM Dyn (delta ++ map(betaks2),
                                       substG del gamma ++ map[x1 |-> realS del sigma1],
                                       betas2, realS del sigma02)
                                      modl2 (IL.VarM(x2)) of
                                (sigma2', [], m2) => (sigma2', m2)
                              | _ => raise EL.Error(#region modl2, "linearity failure at linking 2b")
                        val _ = (traceModl "elabM" this "2";
                                 traceS "sigma1" sigma1;
                                 traceR "del" del;
                                 traceS "del(sigma1)" (realS del sigma1);
                                 traceS "sigma2'" sigma2')
                        val (sigma, m1', m2') =
                            merge pass (delta ++ map(betaks2)) (realS del sigma1, sigma2') (IL.VarM(x))
                            handle Mismatch ls =>
                                raise EL.Error(region, "linked modules inconsistent at path " ^
                                                       String.concatWith "." ls)
                    in
                        if equivS (delta ++ map(betaks2)) (sigma, abs(sigma))
                        then (sigma, del, betaks2, m2, m1', m2')
                        else raise EL.Error(region, "left-over imports after sealing")
                    end
            in
                (abs(sigma1), List.drop(betas0, size alphasbetas1),
                 IL.NewTypM(betaks2,
                    ILOps.defEquiM(List.map (fn(alpha1, _) => (alpha1, substT del (IL.VarT(alpha1)))) alphaks1,
                        IL.LetM(x, ELAux.create(abs sigma),
                            IL.LetM(x1, m1',
                                IL.LetM(x2, m2',
                                    ILOps.seqM[
                                        copy(IL.VarM(x1), p, abs(sigma1)),
                                        substM del m1,
                                        m2
                                    ]
                                )
                            )
                        ),
                        IL.StructS[]
                    )
                 )
                )
            end
          | EL.SealM(modl, sign) =>
            let
                val (alphaks', betaks', sigma') = elabS (delta, gamma) sign
                val (delA, rea) = composeImport sigma0 (locator Minus sigma')
                val alphaks = mapFst (substA delA) alphaks'
                val betaks = ListPair.zip(betas0, List.map #2 betaks')
                val alphas = List.map #1 alphaks
                val betas = List.map #1 betaks
                val delB = map(List.map #1 betaks' |=> List.map IL.VarT betas)
                val sigma = realS rea (substS (delA ++ delB) sigma')
                val _ = (traceModl "elabM" this "1";
                         traceS "sigma'" sigma';
                         traceAKs "alphaks'" alphaks'; traceAKs "betaks'" betaks';
                         traceAKs "alphaks" alphaks; traceAKs "betaks" betaks;
                         traceR "delA" delA; traceR "delB" delB;
                         traceS "sigma0" sigma0; traceS "sigma" sigma)
                val delta' = delta -- set(alphas) -- set(betas)
                val x = rename "_seal.X"
                val (betaks1, sigma1', m, del, f) =
                    if pass = Stat then ([], dummyS, dummyM, map[], dummyM) else
                    let
                        val (sigma01, alphaks1, betaks1) = templateM (delta, gamma) modl []
                        val betas1 = List.map #1 betaks1
                        val sigma1 =
                            case elabM Stat (delta ++ map(alphaks1) ++ map(betaks1),
                                             gamma, betas1, sigma01) modl (IL.VarM(x)) of
                                (sigma1, [], _) => sigma1
                              | _ => raise EL.Error(region, "linearity failure at sealing")
(* without realisers:
                        val () = locates sigma1 (List.map #1 alphaks1)
*)
                        val del = solve (delta ++ map(alphaks) ++ map(alphaks1) ++ map(betaks1)) (sigma1, neg sigma)
                            handle Circular alpha =>
                                raise EL.Error(region, "sealing is circular at type " ^ alpha)
                              | Locate ls =>
                                raise EL.Error(region, "mismatch at path " ^
                                                       String.concatWith "." ls)
                        val (sigma1', m) =
                            case elabM Dyn (delta' ++ map(betaks) ++ map(alphaks1) ++ map(betaks1),
                                            substG del gamma, betas1, sigma01)
                                           modl (IL.VarM(x)) of
                                (sigma1, [], m) => (sigma1, m)
                              | _ => raise EL.Error(region, "linearity failure at sealing (2)")
                        val _ = (traceModl "elabM" this "2";
                                 traceS "sigma'" sigma';
                                 traceAKs "alphaks" alphaks; traceAKs "betaks" betaks;
                                 traceAKs "alphaks1" alphaks1; traceAKs "betaks1" betaks1;
                                 traceS "sigma1'" sigma1'; traceS "sigma" sigma;
                                 traceR "del" del;
                                 traceS "del(sigma1')" (substS del sigma1');
                                 traceS "del(sigma)" (substS del sigma))
                        val f = matchS Dyn (delta ++ map(alphaks) ++ map(alphaks1) ++ map(betaks1)) (substS del sigma1', substS del sigma)
                            handle Mismatch ls =>
                                raise EL.Error(region,
                                               "mismatch at path " ^ String.concatWith "." ls)
                    in
                        (betaks1, sigma1', m, del, f)
                    end
            in
                if List.exists (fn(alpha, k) => lookup delta alpha <> k) (alphaks @ betaks)
                then raise EL.Error(region, "inconsistent kinding at instantiation") else
                (sigma, List.drop(betas0, List.length betas),
                 IL.NewTypM(betaks1,
                    ILOps.defEquiM(List.map (fn beta => (beta, substT del (IL.VarT(beta)))) betas,
                        IL.ApplyM(IL.ApplyM(f, IL.LambdaM(x, eraseS(substS del sigma1'), m)), p),
                        IL.StructS[]
                    )
                 )
                )
            end
(*
          | EL.LetM(x, modl1, modl2) =>
            let
                val sigma01 =
                    case templateM (delta, gamma) modl1 [] of
                        (sigma01, [], _) => sigma01
                      | _ => raise EL.Error(region, "imports in local module")
                val (sigma1, betas1, m1) =
                    elabM pass (delta, gamma, betas0, sigma01) modl1 (IL.VarM(x))
                val (sigma2, betas2, m2) =
                    elabM pass (delta, gamma ++ map[x |-> sigma1], betas1, sigma0) modl2 p
            in
                if not(equivS delta (sigma1, abs sigma1))
                then raise EL.Error(region, "imports in local module")
                else
                (sigma2, betas2,
                 IL.LetM(x, create(sigma1), ILOps.seqM[m1, m2]))
            end
*)

    (* Units *)

    and elabU (delta, gamma) modl =
        let
            val _ = (traceIn(); traceModl "elabU" modl "begin";
                     traceD "delta" delta; traceG "gamma" gamma)
            val _ = assert(fn() => subset(fvG(gamma), dom(delta)))
            val (sigma0, alphaks, betaks) = templateM (delta, gamma) modl []
            val _ = (traceModl "elabU" modl "1"; traceS "sigma0" sigma0)
            val alphas = List.map #1 alphaks
            val betas = List.map #1 betaks
            val x = rename "_unit.X"
            val (sigma, m) =
                case elabM Dyn (delta ++ map(alphaks) ++ map(betaks), gamma, betas, sigma0)
                           modl (IL.VarM(x)) of
                    (sigma, [], m) => (sigma, m)
                  | _ => raise EL.Error(#region modl, "linearity failure for unit")
(* without realisers:
            val () = locates sigma alphas
*)
        in
            traceModl "elabU" modl "end"; traceF "phi" (alphaks, betaks, sigma); traceOut();
            assert(fn() => subset(fvF(alphaks, betaks, sigma), dom(delta)));
            assert(fn() => equal(dom(locator Minus sigma), dom(map(alphaks))));
            ((alphaks, betaks, sigma),
             IL.GenDownM(alphaks, IL.GenUpM(betaks, IL.LambdaM(x, eraseS(sigma), m))))
        end

    and elabMclosed pass (delta, gamma) modl =
        let
            val _ = (traceIn(); traceModl "elabMclosed" modl "begin";
                     traceD "delta" delta; traceG "gamma" gamma)
            val (sigma0, betaks) =
                case templateM (delta, gamma) modl [] of
                    (sigma0, [], betaks) => (sigma0, betaks)
                  | _ => raise EL.Error(#region modl, "module has left-over imports")
            val betas = List.map #1 betaks
            val x = rename "_closed.X"
            val (sigma, m) =
                case elabM Dyn (delta ++ map(betaks), gamma, betas, sigma0) modl (IL.VarM(x)) of
                    (sigma, [], m) => (sigma, m)
                  | _ => raise EL.Error(#region modl, "linearity failure for module")
        in
            if equivS (delta ++ map(betaks)) (sigma, abs sigma) then () else
                raise EL.Error(#region modl, "module has left-over imports");
            traceModl "elabMclosed" modl "end"; traceS "sigma" sigma; traceOut();
            assert(fn() => subset(fvS(sigma), dom(delta)));
            (sigma,
             IL.NewTypM(betaks,
                IL.LetM(x, create(sigma),
                    ILOps.seqM[m, IL.VarM(x)]
                )
             )
            )
        end

    and locates sigma alphas =
        (* This is a sanity check only, should never actually fail *)
        let
            val loc = locator Minus sigma
                handle Collision => raise Fail "locates 1"
(* without realisers:
            val () = if equal(set(alphas), dom(loc)) then () else
*)
            val () = if subset(set(alphas), dom(loc)) then () else
                raise Fail "locates 2"
        in
            ()
        end

    (* Signatures *)

    and elabS (delta, gamma) sign =
        let
            val _ = (traceIn(); traceSign "elabS" sign "begin")
            val _ = (traceD "delta" delta; traceG "gamma" gamma)
            val _ = assert(fn() => subset(fvG(gamma), dom(delta)))
            val phi = elabS_ (delta, gamma) sign
        in
            traceSign "elabS" sign "end"; traceF "phi" phi; traceOut();
            assert(fn() => subset(fvF(phi), dom(delta)));
            assert(fn() => equal(dom(locator Minus (#3 phi)), dom(map(#1 phi))));
            phi
        end
    and elabS_ (delta, gamma) (this as {it, region}) =
        case it of
            EL.ExportS(modl, lss) =>
            let
                val (alphaks', sigma') =
                    case elabU (delta, gamma) modl of
                        ((alphaks', [], sigma'), _) => (alphaks', sigma')
                      | ((alphaks', _, sigma'), _) =>
                            raise EL.Error(region, "module is not fully abstract")
                val sigma = export lss sigma'
                    handle Export ls =>
                        raise EL.Error(region, "unknown path " ^ String.concatWith "." ls)
                val betas = dom(locator Plus sigma)
                val (betaks, alphaks) = List.partition (member betas o #1) alphaks'
            in
                (alphaks, betaks, sigma)
            end
          | EL.ImportS(modl, lss) =>
            let
                val (alphaks', sigma') =
                    case elabU (delta, gamma) modl of
                        ((alphaks', [], sigma'), _) => (alphaks', sigma')
                      | ((alphaks', _, sigma'), _) =>
                            raise EL.Error(region, "module is not fully abstract")
                val sigma = neg(export lss sigma')
                    handle Export ls =>
                        raise EL.Error(region, "unknown path " ^ String.concatWith "." ls)
                val betas = dom(locator Plus sigma)
                val (betaks, alphaks) = List.partition (member betas o #1) alphaks'
                val _ = (traceSign "elabS" this "1"; traceS "sigma" sigma;
                         traceAKs "alphaks'" alphaks'; traceS "sigma'" sigma';
                         traceAs "betas" (items betas))
            in
                (alphaks, betaks, sigma)
            end

    (* Definitions and Programs *)

    type context = typ_context * modl_context
    val emptyContext = (map[], map[]) : context

    fun elab (delta, gamma) modl =
        let
            val (phi as (_, betaks, sigma), f) =
                case elabU (delta, gamma) modl of
                    (phi as ([], betaks, sigma as Struct(_)), f) => (phi, f)
                  | (([], _, _), _) => raise EL.Error(#region modl, "program is not a structure")
                  | _ => raise EL.Error(#region modl, "program has left-over imports")
        in
            if not(equivS (delta ++ map(betaks)) (sigma, abs sigma))
            then raise EL.Error(#region modl, "program has left-over imports")
            else (phi, f)
        end
end
