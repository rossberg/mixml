(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature IL_CHECKED_EVALUATION =
sig
    exception Stuck of ILMachine.state
    exception Black of IL.var
    exception Bug of string
    type context = ILEvaluation.context
    val run : context * IL.modl -> context * ILMachine.modval
end

structure ILCheckedEvaluation : IL_CHECKED_EVALUATION =
struct
    open IL
    open ILOps infix @@
    open VarOps infix |-> |=> |=>* ++
    open ILMachine
    open ILTyping

    exception Stuck = ILEvaluation.Stuck
    exception Black = ILEvaluation.Black
    exception Bug = ILTyping.Error
    type context = ILEvaluation.context

    val lookup = fn map => fn x => fn blame =>
        lookup map x handle Lookup => raise Bug(blame ^ ": unbound variable " ^ x)

    datatype tausigma = TAU of typ | SIGMA of sign

    fun checkF (delta, gamma) (ff, TAU tau) = checkF' (delta, gamma) (ff, TAU(normT delta tau))
      | checkF (delta, gamma) (ff, SIGMA sigma) = checkF' (delta, gamma) (ff, SIGMA sigma)
    and checkF' (delta, gamma) =
        fn (ValF, SIGMA(TermS(tau))) =>
            let
                val () = checkT' delta tau StarK "ValF"
            in
                (TAU tau, [])
            end
         | (PlusF1(e), TAU IntT) =>
            let
                val () = checkE' (delta, gamma) e IntT "PlusF1"
            in
                (TAU IntT, [])
            end
         | (PlusF2(n), TAU IntT) =>
            let
            in
                (TAU IntT, [])
            end
         | (MinusF1(e), TAU IntT) =>
            let
                val () = checkE' (delta, gamma) e IntT "MinusF1"
            in
                (TAU IntT, [])
            end
         | (MinusF2(n), TAU IntT) =>
            let
            in
                (TAU IntT, [])
            end
         | (EqualF1(e), TAU IntT) =>
            let
                val () = checkE' (delta, gamma) e IntT "EqualF1"
            in
                (TAU(VariantT[TupleT[], TupleT[]]), [])
            end
         | (EqualF2(n), TAU IntT) =>
            let
            in
                (TAU(VariantT[TupleT[], TupleT[]]), [])
            end
         | (LessF1(e), TAU IntT) =>
            let
                val () = checkE' (delta, gamma) e IntT "LessF1"
            in
                (TAU(VariantT[TupleT[], TupleT[]]), [])
            end
         | (LessF2(n), TAU IntT) =>
            let
            in
                (TAU(VariantT[TupleT[], TupleT[]]), [])
            end
         | (CatF1(e), TAU StringT) =>
            let
                val () = checkE' (delta, gamma) e StringT "CatF1"
            in
                (TAU StringT, [])
            end
         | (CatF2(n), TAU StringT) =>
            let
            in
                (TAU StringT, [])
            end
         | (TupleF(vs1, es2), TAU tau) =>
            let
                val taus1 = List.map (fn v => checkE (delta, gamma) (fromValue v)) vs1
                val () = checkT' delta tau StarK "TupleF 1"
                val taus2 =
                    case normT delta (checkE (delta, gamma) (TupleE(es2))) of
                        TupleT(taus2) => taus2
                      | _ => raise Bug "TupleF 2: impossible"
            in
                (TAU(TupleT(taus1 @ [tau] @ taus2)), [])
            end
         | (ProjF(i), TAU(TupleT(taus))) =>
            let
                val tau_i = List.nth(taus, i-1)
                    handle Subscript => raise Bug "ProjF 1: index out of range"
            in
                (TAU tau_i, [])
            end
         | (VariantF(i, tau'), TAU tau) =>
            let
                val () = checkT' delta tau' StarK "VariantF 1"
                val taus =
                    case normT delta tau' of
                        VariantT(taus) => taus
                      | _ => raise Bug "VariantF 2: not a variant type"
                val tau_i = List.nth(taus, i-1)
                    handle Subscript => raise Bug "VariantF 1: index out of range"
            in
                if equivT delta (tau, tau_i)
                then (TAU(VariantT(taus)), [])
                else raise Bug "VariantF 2: inconsistent annotation"
            end
         | (CaseF(xes), TAU(VariantT(taus))) =>
            let
                val tau =
                    (case ListPair.mapEq
                            (fn((x, e), tau) => checkE (delta, gamma ++ map[x |-> TermS(tau)]) e)
                            (xes, taus) of
                        [] => VariantT[]
                      | tau::taus' =>
                        if List.all (fn tau' => equivT delta (tau, tau')) taus'
                        then tau
                        else raise Bug "CaseF 1: inconsistent branch types"
                    ) handle ListPair.UnequalLengths => raise Bug "CaseF 2: arity mismatch"
            in
                (TAU tau, [])
            end
        | (AppF1(m), TAU(ArrowT(sigma, tau))) =>
            let
                val () = checkS delta sigma
                val () = checkT' delta tau StarK "AppF2 1"
                val () = checkMpure' (delta, gamma) m sigma "AppF1 2"
            in
                (TAU tau, [])
            end
        | (AppF2(v), SIGMA sigma) =>
            let
                val tau =
                    case normT delta (checkE (delta, gamma) (fromValue v)) of
                        ArrowT(sigma', tau) =>
                            if equivS delta (sigma', sigma)
                            then tau
                            else raise Bug "AppF2 2: argument type mismatch"
                      | _ => raise Bug "AppF2 1: value not a function"
            in
                (TAU tau, [])
            end
        | (InstF(taus), TAU(UnivT(alphas, tau))) =>
            let
                val () = checkT' (delta ++ map(alphas |=>* Colon StarK)) tau StarK "InstF 1"
                val () = List.app (fn tau => checkT' delta tau StarK "InstF 2") taus
            in
                (TAU(substT (map(alphas |=> taus)) tau), [])
                handle ListPair.UnequalLengths => raise Bug "InstF 3: arity mismatch"
            end
         | (ConF1(taus, e), TAU(PureT(alphas, tau1, tau2))) =>
            let
                val () = List.app (fn tau => checkT' delta tau StarK "ConF1 1") taus
                val () = checkE' (delta, gamma) e (substT (map(alphas |=> taus)) tau1) "ConF1 2"
                val () = checkT' (delta ++ map(alphas |=>* Colon StarK)) tau2 StarK "ConF1 3"
            in
                (TAU(substT (map(alphas |=> taus)) tau2), [])
            end
         | (ConF2(v, taus), TAU tau1') =>
            let
                val () = List.app (fn tau => checkT' delta tau StarK "ConF2 2") taus
                val (alphas, tau1, tau2) =
                    case normT delta (checkE (delta, gamma) (fromValue v)) of
                        PureT args => args
                      | _ => raise Bug "ConF2 1: not a constructor value"
            in
                if equivT delta (tau1', substT (map(alphas |=> taus)) tau1)
                then (TAU(substT (map(alphas |=> taus)) tau2), [])
                     handle ListPair.UnequalLengths => raise Bug "ConF2 3: arity mismatch"
                else raise Bug "ConF2 4: mismatch on in-type"
            end
         | (PrintF, TAU tau) =>
            let
                val () = checkT' delta tau StarK "PrintF"
            in
                (TAU(TupleT[]), [])
            end
         | (TermF, TAU tau) =>
            let
                val () = checkT' delta tau StarK "TermF"
            in
                (SIGMA(TermS(tau)), [])
            end
         | (StructF(lws1, l, lms2), SIGMA sigma) =>
            let
                val lsigmas1 = mapSnd (fn w => checkMpure (delta, gamma) (fromModval w) "StructF 1") lws1
                val () = checkS delta sigma
                val (lsigmas2, betas) =
                    case checkM (delta, gamma) (StructM(lms2)) of
                        (StructS(lsigmas2), betas) => (lsigmas2, betas)
                      | _ => raise Bug "StructF 2: impossible"
            in
                (SIGMA(StructS(lsigmas1 @ [(l, sigma)] @ lsigmas2)), betas)
            end
         | (DotF(l), SIGMA sigma) =>
            let
                val () = checkS delta sigma
                val sigma_l =
                    case sigma of
                        StructS(lsigmas) => lookup (map(lsigmas)) l "DotF 1"
                      | _ => raise Bug "DotF 2: not a structure signature"
            in
                (SIGMA sigma_l, [])
            end
        | (ApplyF1(m), SIGMA(ArrowS(sigma2, sigma))) =>
            let
                val () = checkS delta sigma2
                val () = checkS delta sigma
                val alphas = checkM' (delta, gamma) m sigma2 "ApplyF1"
            in
                (SIGMA sigma, alphas)
            end
        | (ApplyF2(w), SIGMA sigma2) =>
            let
                val (sigma, alphas) =
                    case checkM (delta, gamma) (fromModval w) of
                        (ArrowS(sigma2', sigma), alphas) =>
                            if equivS delta (sigma2', sigma2)
                            then (sigma, alphas)
                            else raise Bug "ApplyF2 2: argument signature mismatch"
                      | _ => raise Bug "ApplyF2 1: module value not a functor"
            in
                (SIGMA sigma, alphas)
            end
        | (LetF(x, m), SIGMA sigma) =>
            let
                val (sigma', alphas) = checkM (delta, gamma ++ map[x |-> sigma]) m
            in
                (SIGMA sigma', alphas)
            end
        | (InstDownF(taus), SIGMA(UnivS(alphaks, sigma))) =>
            let
                val (alphas, ks) = ListPair.unzip alphaks
                val () = checkS (delta ++ map(mapSnd Colon alphaks)) sigma
                val () = List.app (fn tau => checkT' delta tau StarK "InstDownF 1") taus
            in
                (SIGMA(substS (map(alphas |=> taus)) sigma), [])
                handle ListPair.UnequalLengths => raise Bug "InstDownF 2: arity mismatch"
            end
(* todo: real effect system
        | (InstUpF(betas), SIGMA(ExistS(alphaks, sigma))) =>
            let
                val (alphas, ks) = ListPair.unzip alphaks
                val () = checkS (delta ++ map(mapSnd Up alphaks)) sigma
            in
                if List.all (fn(beta, k) => lookup delta beta "InstUpF 1" = Up k) (ListPair.zipEq(betas, ks))
                then (SIGMA(substS (map(alphas |=> List.map VarT betas)) sigma), betas)
                     handle ListPair.UnequalLengths => raise Bug "InstUpF 2: arity mismatch"
                else raise Bug "InstUpF 3: unwritable betas"
            end
*)
        | (InstUpF1(betas, m), SIGMA(ExistS(alphaks, ArrowS(sigma2, sigma)))) =>
            let
                val (alphas, ks) = ListPair.unzip alphaks
                val delta' = delta ++ map(mapSnd Up alphaks)
                val del = map(alphas |=> List.map VarT betas)
                    handle ListPair.UnequalLengths => raise Bug "InstUpF1 2: arity mismatch"
                val sigma2' = substS del sigma2
                val sigma' = substS del sigma
                val () = checkS delta' sigma2'
                val () = checkS delta' sigma'
                val alphas = checkM' (delta, gamma) m sigma2' "InstUpF1"
            in
                if List.all (fn(beta, k) => lookup delta beta "InstUpF1 1" = Up k) (ListPair.zipEq(betas, ks))
                then (SIGMA sigma', alphas @ betas)
                else raise Bug "InstUpF1 3: unwritable betas"
            end
        | (InstUpF2(w, betas), SIGMA sigma2) =>
            let
                val (ks, sigma, alphas) =
                    case checkM (delta, gamma) (fromModval w) of
                        (ExistS(betaks', ArrowS(sigma2', sigma)), alphas) =>
                        let
                            val (betas', ks) = ListPair.unzip betaks'
                            val del = map(betas' |=> List.map VarT betas)
                                handle ListPair.UnequalLengths =>
                                    raise Bug "InstUpF2 1: arity mismatch"
                        in
                            if equivS delta (substS del sigma2', sigma2)
                            then (ks, substS del sigma, alphas)
                            else raise Bug "InstUpF2 2: argument signature mismatch"
                        end
                      | _ => raise Bug "InstUpF2 3: module value not an existential functor"
            in
                if List.all (fn(beta, k) => lookup delta beta "InstUpF2 4" = Up k) (ListPair.zipEq(betas, ks))
                then (SIGMA sigma, alphas @ betas)
                else raise Bug "InstUpF2 5: unwritable betas"
            end
        | (AssignF(m), SIGMA(LazyS(sigma))) =>
            let
                val () = checkS delta sigma
                val betas = checkM' (delta, gamma) m sigma "AssignF"
            in
                (SIGMA(StructS([])), betas)
            end
        | (ForceF, SIGMA(LazyS(sigma))) =>
            let
                val () = checkS delta sigma
            in
                (SIGMA sigma, [])
            end
        | (NeededF(x), SIGMA sigma) =>
            let
                val () = checkS delta sigma
            in
                if equivS delta (lookup gamma x "NeededF", LazyS(sigma))
                then (SIGMA sigma, [])
                else raise Bug "NeededF: variable has inconsistent signature"
            end
        | (ff, TAU tau) =>
            raise Bug("ill-typed continuation frame " ^ ILPrint.strF ff ^ " : " ^ ILPrint.strT tau)
        | (ff, SIGMA sigma) =>
            raise Bug("ill-typed continuation frame " ^ ILPrint.strF ff ^ " : " ^ ILPrint.strS sigma)

    fun checkC (delta, gamma) =
        fn ([], TAU tau) =>
            let
                val () = checkT' delta tau StarK "continuation type"
            in
                ()
            end
         | ([], SIGMA sigma) =>
            let
                val () = checkS delta sigma
            in
                ()
            end
         | (ff::cc, tau_sigma1) =>
            let
                val (tau_sigma2, betas) = checkF (delta, gamma) (ff, tau_sigma1)
                val () = checkC (delta @@ DownE(betas), gamma) (cc, tau_sigma2)
            in
                ()
            end

    fun checkO delta (omega, gamma) =
        let
            val () = checkG delta gamma
            val _ = mapRani (fn(x, LazyS(sigma)) =>
                               (case lookup omega x "store" of
                                   Undefined => ()
                                 | Defined(m) => ignore(checkM' (delta, gamma) m sigma "Defined")
                                 | Evaluating => ()
                                 | Evaluated(w) => checkMpure' (delta, gamma) (fromModval w) sigma "Evaluated"
                               )
                               | _ => raise Fail "store" 
                            ) gamma
        in
            if equal(dom omega, dom gamma)
            then ()
            else raise Bug "store: domain mismatch"
        end

    fun checkSt om =
        case om of
            BlackHole x => ()
          | TermSt(delta, gamma, omega, cc, ev) =>
            let
                val e = case ev of EXP e => e | VAL v => fromValue v
                val () = checkO delta (omega, gamma)
                val tau = checkE (delta, gamma) e
                val () = checkC (delta, gamma) (cc, TAU tau)
            in
                ()
            end
          | ModSt(delta, gamma, omega, cc, mw) =>
            let
                val m = case mw of EXP m => m | VAL w => fromModval w
                val () = checkO delta (omega, gamma)
                val (sigma, betas) = checkM (delta, gamma) m
                val () = checkC (delta @@ DownE(betas), gamma) (cc, SIGMA sigma)
            in
                ()
            end

    fun step s =
        let
            val s' = ILEvaluation.step s
            val () = checkSt s'
        in
            s'
        end

    val progress = ""
    val completion = ""

    fun run((delta, gamma, omega), m) =
        run'(ModSt(delta, gamma, omega, [], EXP m)) before print completion
    and run' s =
        case s of
            BlackHole x => raise ILEvaluation.Black x
          | ModSt(delta, gamma, omega, [], VAL w) => ((delta, gamma, omega), w)
          | ModSt(delta, gamma, omega, [], EXP m) =>
            (case toModval m of
                NONE => run'(step s before print progress)
              | SOME w => ((delta, gamma, omega), w)
            )
          | _ => run'(step s before print progress)
end
