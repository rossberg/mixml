(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature IL_TYPING =
sig
    exception Error of string

    val checkT  : IL.typ_context -> IL.typ -> IL.kind
    val checkT' : IL.typ_context -> IL.typ -> IL.kind -> string -> unit
    val checkS : IL.typ_context -> IL.sign -> unit
    val checkE : IL.typ_context * IL.modl_context -> IL.term -> IL.typ
    val checkE': IL.typ_context * IL.modl_context -> IL.term -> IL.typ -> string -> unit
    val checkM  : IL.typ_context * IL.modl_context -> IL.modl -> IL.sign * IL.typvar list
    val checkM' : IL.typ_context * IL.modl_context -> IL.modl -> IL.sign -> string -> IL.typvar list
    val checkMpure  : IL.typ_context * IL.modl_context -> IL.modl -> string -> IL.sign
    val checkMpure' : IL.typ_context * IL.modl_context -> IL.modl -> IL.sign -> string -> unit
    val checkD : IL.typ_context -> unit
    val checkG : IL.typ_context -> IL.modl_context -> unit
end

structure ILTyping : IL_TYPING =
struct
    open IL 
    open ILOps infix @@
    open VarOps infix \/ /\ \ |-> |=> |=>* ++

    exception Error of string

    fun impossible s = raise Fail("Impossible: " ^ s)
    fun error s = raise Error s

    val lookup = fn map => fn x => fn blame =>
        lookup map x handle Lookup => error(blame ^ ": unbound variable " ^ x)

    (* Type well-formedness *)

    fun checkT delta =
        fn VarT(alpha) => kind(lookup delta alpha "VarT")
         | IntT => StarK
         | StringT => StarK
         | TupleT(taus) =>
            let
                val () = List.app (fn tau => checkT' delta tau StarK "TupleT") taus
            in
                StarK
            end
         | VariantT(taus) =>
            let
                val () = List.app (fn tau => checkT' delta tau StarK "VariantT") taus
            in
                StarK
            end
         | ArrowT(sigma, tau) =>
            let
                val () = checkS delta sigma
                val () = checkT' delta tau StarK "ArrowT"
            in
                StarK
            end
         | UnivT(alphas, tau) =>
            let
                val (alphas', del) = renamesA alphas
                val delta' = delta ++ map(alphas' |=>* Colon StarK)
                val () = checkT' delta' (substT del tau) StarK "UnivT"
            in
                StarK
            end
         | PureT(alphas, tau1, tau2) =>
            let
                val (alphas', del) = renamesA alphas
                val delta' = delta ++ map(alphas' |=>* Colon StarK)
                val () = checkT' delta' (substT del tau1) StarK "PureT 1"
                val () = checkT' delta' (substT del tau2) StarK "PureT 2"
            in
                StarK
            end
         | LambdaT(alphas, tau) =>
            let
                val (alphas', del) = renamesA alphas
                val delta' = delta ++ map(alphas' |=>* Colon StarK)
                val () = checkT' delta' (substT del tau) StarK "LambdaT"
            in
                ArrowK(List.length alphas)
            end
         | ApplyT(tau, taus) =>
            let
                val n =
                    case checkT delta tau of
                        ArrowK(n) => n
                    | _ => error "ApplyT 1: not a constructor"
                val () = List.app (fn tau => checkT' delta tau StarK "ApplyT") taus
            in
                if List.length taus = n
                then StarK
                else error "ApplyT 2: arity mismatch"
            end

    and checkT' delta tau k blame =
        if checkT delta tau = k
        then ()
        else error(blame ^ ": kind mismatch")

    and checkTstable' delta tau k blame =
        (
            checkT' delta tau k blame;
            ()
(*
            if Set.isEmpty(basis delta tau)
            then ()
            else error(blame ^ ": type unstable")
*)
        )

    (* Signature well-formedness *)

    and checkS delta =
        fn TypS(tau, k) =>
            let
                val k' = checkT delta tau
            in
                if k' = k
                then ()
                else error "TypS: kind mismatch"
            end
         | TermS(tau) =>
            let
                val () = checkT' delta tau StarK "TermS"
            in
                ()
            end
         | StructS(lsigmas) =>
            let
                val (ls, sigmas) = ListPair.unzip lsigmas
                val () = List.app (fn sigma => checkS delta sigma) sigmas
            in
                (* check disjointness of labels? *)
                ()
            end
         | ArrowS(sigma1, sigma2) =>
            let
                val () = checkS delta sigma1
                val () = checkS delta sigma2
            in
                ()
            end
         | LazyS(sigma) =>
            let
                val () = checkS delta sigma
            in
                ()
            end
         | UnivS(alphaks, sigma) =>
            let
                val (alphaks', del) = renamesAK alphaks
                val delta' = delta ++ map(mapSnd Down alphaks')
                val () = checkS delta' (substS del sigma)
            in
                ()
            end
         | ExistS(alphaks, sigma) =>
            let
                val (alphaks', del) = renamesAK alphaks
                val delta' = delta ++ map(mapSnd Up alphaks')
(* todo: real effect system
                val () = checkS delta' (substS del sigma)
*)
                val () =
                    case sigma of
                        ArrowS(sigma1, sigma2) =>
                        let
                            val () = checkS delta' (substS del sigma1)
                            val () = checkS delta' (substS del sigma2)
                        in
                            ()
                        end
                      | _ => error("ExistS: malformed existential type")
            in
                ()
            end


    (* Term well-formedness *)

    fun checkE (delta, gamma) =
        fn ValE(m) =>
            let
                val tau =
                    case checkMpure (delta, gamma) m "ValE" of
                        TermS(tau) => tau
                    | _ => error "ValE: not a value module"
            in
                tau
            end
         | IntE(n) => IntT
         | StringE(s) => StringT
         | PlusE(e1, e2) =>
            let
                val () = checkE' (delta, gamma) e1 IntT "PlusE 1"
                val () = checkE' (delta, gamma) e2 IntT "PlusE 2"
            in
                IntT
            end
         | MinusE(e1, e2) =>
            let
                val () = checkE' (delta, gamma) e1 IntT "MinusE 1"
                val () = checkE' (delta, gamma) e2 IntT "MinusE 2"
            in
                IntT
            end
         | EqualE(e1, e2) =>
            let
                val () = checkE' (delta, gamma) e1 IntT "EqualE 1"
                val () = checkE' (delta, gamma) e2 IntT "EqualE 2"
            in
                VariantT[TupleT[], TupleT[]]
            end
         | LessE(e1, e2) =>
            let
                val () = checkE' (delta, gamma) e1 IntT "LessE 1"
                val () = checkE' (delta, gamma) e2 IntT "LessE 2"
            in
                VariantT[TupleT[], TupleT[]]
            end
         | CatE(e1, e2) =>
            let
                val () = checkE' (delta, gamma) e1 StringT "CatE 1"
                val () = checkE' (delta, gamma) e2 StringT "CatE 2"
            in
                StringT
            end
        | TupleE(es) =>
            let
                val taus = List.map (fn e => checkE (delta, gamma) e) es
            in
                TupleT(taus)
            end
        | DotE(e, i) =>
            let
                val taus =
                    case checkE (delta, gamma) e of
                        TupleT(taus) => taus
                      | _ => error "DotE 1: not a tuple"
            in
                if i <= 0 then error "DotE 2: illformed index"
                else if i > List.length taus then error "DotE 3: index out of range"
                else List.nth(taus, i-1)
            end
         | VariantE(e, i, tau) =>
            let
                val () = checkT' delta tau StarK "VariantE 1"
                val taus =
                    case normT delta tau of
                        VariantT(taus) => taus
                      | _ => error "VariantE 2: not a variant type"
                val tau_i = List.nth(taus, i-1)
                    handle Subscript => error "VariantE 3: index out of range"
                val () = checkE' (delta, gamma) e tau_i "VariantE 4"
            in
                VariantT(taus)
            end
         | CaseE(e, xes) =>
            let
                val taus =
                    case checkE (delta, gamma) e of
                        VariantT(taus) => taus
                      | _ => error "CaseE 1: not a variant"
                val tau =
                    (case ListPair.mapEq
                            (fn((x, e), tau) => checkE (delta, gamma ++ map[x |-> TermS(tau)]) e)
                            (xes, taus) of
                        [] => VariantT[]
                      | tau::taus' =>
                        if List.all (fn tau' => equivT delta (tau, tau')) taus'
                        then tau
                        else error "CaseE 3: inconsistent branch types"
                    ) handle ListPair.UnequalLengths => error "CaseE 2: arity mismatch"
            in
                tau
            end
         | LambdaE(x, sigma, e) =>
            let
                val () = checkS delta sigma
                val tau = checkE (delta, gamma ++ map[x |-> sigma]) e
            in
                ArrowT(sigma, tau)
            end
         | ApplyE(f, m) =>
            let
                val (sigma, tau) =
                    case checkE (delta, gamma) f of
                        ArrowT(args) => args
                      | _ => error "ApplyE 1: not a function"
                val () = checkMpure' (delta, gamma) m sigma "ApplyE 2"
            in
                tau
            end
         | GenE(alphas, e) =>
            let
                val (alphas', del) = renamesA alphas
                val tau =
                    checkE (delta ++ map(alphas |=>* Colon StarK), gamma) (substE del e)
            in
                UnivT(alphas', tau)
            end
         | InstE(f, taus) =>
            let
                val (alphas, tau) =
                    case checkE (delta, gamma) f of
                        UnivT(args) => args
                    | _ => error "InstE 1: not a universal function"
                val () = List.app (fn tau => checkT' delta tau StarK "InstE 2") taus
                    handle ListPair.UnequalLengths => error "InstE 3: arity mismatch"
            in
                substT (map(alphas |=> taus)) tau
            end
        | FoldE(alpha) =>
            (
                case lookup delta alpha "FoldE 1" of
                    Iso(tau, StarK) =>
                        PureT([], tau, VarT(alpha))
                  | Iso(tau, ArrowK(n)) =>
                    let
                        val betas = List.tabulate(n, fn _ => rename "beta")
                        val betaTs = List.map VarT betas
                    in
                        PureT(betas, ApplyT(tau, betaTs), ApplyT(VarT alpha, betaTs))
                    end
                  | _ => error("FoldE 2: " ^ alpha ^ " is not a recursive type variable")
            )
         | UnfoldE(alpha) =>
            (
                case lookup delta alpha "UnfoldE 1" of
                    Iso(tau, StarK) =>
                        PureT([], VarT(alpha), tau)
                  | Iso(tau, ArrowK(n)) =>
                    let
                        val betas = List.tabulate(n, fn _ => fresh())
                        val betaTs = List.map VarT betas
                    in
                        PureT(betas, ApplyT(VarT alpha, betaTs), ApplyT(tau, betaTs))
                    end
                  | _ => error("UnfoldE 2: " ^ alpha ^ " is not a recursive type variable")
            )
         | ConE(e1, taus, e2) =>
            let
                val (alphas, tau2, tau) =
                    case checkE (delta, gamma) e1 of
                        PureT(args) => args
                    | _ => error "ConE 1: not a constructor"
                val _ = List.app (fn tau => checkT' delta tau StarK "ConE 2") taus
                val tau2' = checkE (delta, gamma) e2
            in
                if equivT delta (tau2', substT (map(alphas |=> taus)) tau2)
                then substT (map(alphas |=> taus)) tau
                else error "ConE 3: argument type mismatch"
            end
          | PrintE(e) =>
            let
                val tau = checkE (delta, gamma) e
            in
                TupleT[]
            end

    and checkE' (delta, gamma) e tau blame =
        let
            val tau' = checkE (delta, gamma) e
        in
            if equivT delta (tau', tau)
            then ()
            else error(blame ^ ": type mismatch")
        end


    (* Module well-formedness *)

    and checkM (delta, gamma) =
        fn VarM(x) =>
            let
                val sigma = lookup gamma x "VarM"
            in
                (sigma, [])
            end
         | TypM(tau) =>
            let
                val k = checkT delta tau
            in
                (TypS(tau, k), [])
            end
         | TermM(e) =>
            let
                val tau = checkE (delta, gamma) e
            in
                (TermS(tau), [])
            end
         | StructM[] =>
            let
            in
                (StructS([]), [])
            end
         | StructM((l1, m1)::lms) =>
            let
                val (sigma1, alphas1) = checkM (delta, gamma) m1
                val (lsigmas, alphas) =
                    case checkM (delta @@ DownE(alphas1), gamma) (StructM(lms)) of
                        (StructS(lsigmas), alphas) => (lsigmas, alphas)
                    | _ => impossible "StructM"
            in
                (StructS((l1,sigma1)::lsigmas), alphas1@alphas)
            end
         | DotM(m, l) =>
            let
                val (sigma, alphas) =
                    case checkM (delta, gamma) m of
                        (StructS(lsigmas), alphas) => (lookup (map(lsigmas)) l "DotM 1", alphas)
                    | _ => error "DotM 2: not a structure"
            in
                (sigma, alphas)
            end
         | LambdaM(x, sigma1, m) =>
            let
                val () = checkS delta sigma1
                val sigma2 = checkMpure (delta, gamma ++ map[x |-> sigma1]) m "LambdaM"
            in
                (ArrowS(sigma1, sigma2), [])
            end
         | ApplyM(f, m) =>
            let
                val ((sigma2, sigma), alphas1) =
                    case checkM (delta, gamma) f of
                        (ArrowS(args), alphas1) => (args, alphas1)
                      | _ => error "ApplyM 1: not a function"
                val alphas2 = checkM' (delta, gamma) m sigma2 "ApplyM 2"
            in
                (sigma, alphas1@alphas2)
            end
         | LetM(x, m1, m2) =>
            let
                val (sigma1, alphas1) = checkM (delta, gamma) m1
                val (sigma2, alphas2) = checkM (delta, gamma ++ map[x |-> sigma1]) m2
            in
                (sigma2, alphas1@alphas2)
            end
         | GenDownM(alphaks, m) =>
            let
                val (alphaks', del) = renamesAK alphaks
                val sigma =
                    checkMpure (delta ++ map(mapSnd Down alphaks'), gamma) (substM del m) "GenDownM"
            in
                (UnivS(alphaks', sigma), [])
            end
         | InstDownM(f, taus) =>
            let
                val (alphaks, sigma) =
                    case checkMpure (delta, gamma) f "InstDownM 1" of
                        UnivS(args) => args
                    | _ => error "InstDownM 2: not a universal function"
                val (alphas, ks) = ListPair.unzip alphaks
                val () = ListPair.appEq (fn(tau, k) => checkTstable' delta tau k "InstDownM 3") (taus, ks)
                    handle ListPair.UnequalLengths => error "InstDownM 4: arity mismatch"
            in
                (substS (map(alphas |=> taus)) sigma, [])
            end
         | GenUpM(alphaks, m) =>
            let
                val (alphaks', del) = renamesAK alphaks
(* todo: real effect system
                val sigma =
                    checkMpure (delta ++ map(mapSnd Up alphaks'), gamma) (substM del m) "GenUpM"
*)
                val sigma =
                    case substM del m of
                        LambdaM(x, sigma1, m2) =>
                        let
                            val delta' = delta ++ map(mapSnd Up alphaks')
                            val () = checkS delta' sigma1
                            val (sigma2, betas) = checkM (delta', gamma ++ map[x |-> sigma1]) m2
                        in
                            if Set.equal(set(betas), set(List.map #1 alphaks'))
                            then ArrowS(sigma1, sigma2)
                            else error("GenUpM 2: effect mismatch")
                        end
                      | _ => error("GenUpM 1: malformed existential generic")
            in
                (ExistS(alphaks', sigma), [])
            end
         | InstUpM(f, betas) =>
            let
                val (alphaks, sigma) =
                    case checkMpure (delta, gamma) f "InstUpM 1" of
                        ExistS(args) => args
                    | _ => error "InstUpM 2: not an existential function"
                val (alphas, ks) = ListPair.unzip alphaks
                val b = ListPair.allEq (fn(beta, k) => lookup delta beta "InstUpM 3" = Up k) (betas, ks)
                    handle ListPair.UnequalLengths => error "InstUpM 4: arity mismatch"
            in
                if b
(* todo: real effect system
                then (substS (map(alphas |=> List.map VarT betas)) sigma, [])
*)
                then (substS (map(alphas |=> List.map VarT betas)) sigma, betas)
                else error "InstUpM 5: kind mismatch or not writable"
            end
         | NewTypM(alphaks, m) =>
            let
                val (alphaks', del) = renamesAK alphaks
                val (sigma, betas') = checkM (delta ++ map(mapSnd Up alphaks'), gamma) (substM del m)
                val alphas' = set(List.map #1 alphaks')
                val betas = List.filter (fn beta => not(member alphas' beta)) betas'
            in
                if not(subset(alphas', set(betas')))
                then error("NewTypM 1: type variable " ^ choose(alphas' \ set(betas')) ^ " never defined")
                else if not(isEmpty(fvS(sigma) /\ alphas'))
                then error("NewTypM 2: type variable " ^ choose(alphas' /\ fvS(sigma)) ^ " escapes scope")
                else (sigma, betas)
            end
         | DefEquiM(alpha, tau, m, sigma, del, gam, contexts) =>
            let
                val alpha' = substA del alpha
                val k =
                    case lookup delta alpha' "DefEquiM 1" of
                        Up k => k
                      | _ => error("DefEquiM 2: type variable " ^ alpha ^ " not writable")
                val (delta', gamma') =
                    case !contexts of
                        NONE => (contexts := SOME(delta, gamma); (delta, gamma))
                      | SOME contexts' => contexts'
                val () = checkT' delta' tau k "DefEquiM 3"
                val alphas = checkM' (delta' @@ EquiE(alpha, tau), gamma') m sigma "DefEquiM 4"
                val () = checkD' delta del delta'
                val () = checkG' (delta, gamma) gam gamma'
            in
                if subset(basis delta' tau, writable(delta') (* \ set[alpha] *))
                then (substS del sigma, List.map (substA del) (alpha::alphas))
                else error "DefEquiM 5: circular definition"
            end
(*
         | DefEquiM(alpha, tau, m, sigma) =>
            let
                val k =
                    case lookup delta alpha "DefEquiM 1" of
                        Up k => k
                    | _ => error("DefEquiM 2: type variable " ^ alpha ^ " not writable")
                val () = checkT' delta tau k "DefEquiM 3"
                val alphas = checkM' (delta @@ EquiE(alpha, tau), gamma) m sigma "DefEquiM 4"
            in
                if subset(basis delta tau, writable(delta) \ set[alpha])
                then (sigma, alpha::alphas)
                else error "DefEquiM 5: circular definition"
                (*
                if subset(basis delta tau, set(alphas))
                then (sigma, alpha::alphas)
                else error "DefEquiM 5: circular definition"
                *)
            end
*)
         | DefIsoM(alpha, tau, m, sigma) =>
            let
                val k =
                    case lookup delta alpha "DefIsoM 1" of
                        Up k => k
                      | _ => error("DefIsoM 2: type variable " ^ alpha ^ " not writable")
                val () = checkT' delta tau k "DefIsoM 3"
                val alphas = checkM' (delta @@ IsoE(alpha, tau), gamma) m sigma "DefIsoM 4"
            in
                (sigma, alpha::alphas)
            end
         | NewTermM(x, sigma, m) =>
            let
                val () = checkS delta sigma
                val (sigma',alphas) = checkM (delta, gamma ++ map[x |-> LazyS(sigma)]) m
            in
                (sigma', alphas)
            end
         | AssignM(m1, m2) =>
            let
                val (sigma, alphas1) =
                    case checkM (delta, gamma) m1 of
                        (LazyS(sigma), alphas1) => (sigma, alphas1)
                    | _ => error "AssignM 1: not a hole"
                val alphas2 = checkM' (delta @@ DownE(alphas1), gamma) m2 sigma "AssignM 2"
            in
                (StructS([]), alphas1@alphas2)
            end
         | ForceM(m) =>
            let
                val (sigma, alphas) =
                    case checkM (delta, gamma) m of
                        (LazyS(sigma), alphas) => (sigma, alphas)
                    | _ => error "ForceM: not a hole"
            in
                (sigma, alphas)
            end

    and checkM' (delta, gamma) m sigma blame =
        let
            val (sigma', alphas) = checkM (delta, gamma) m
        in
            if equivS delta (sigma', sigma)
            then alphas
            else error(blame ^ ": signature mismatch")
        end

    and checkMpure (delta, gamma) m blame =
        case checkM (delta, gamma) m of
            (sigma, []) => sigma
          | _ => error(blame ^ ": non-empty effect")

    and checkMpure' (delta, gamma) m sigma blame =
        let
            val sigma' = checkMpure (delta, gamma) m blame
        in
            if equivS delta (sigma', sigma)
            then ()
            else error(blame ^ ": signature mismatch\nsigma1 = " ^ ILPrint.strS sigma' ^ "\nsigma2 = " ^ ILPrint.strS sigma)
        end

    and checkD' delta del delta' =
        ignore(
            mapRani (fn(alpha, entry) =>
                     checkT' delta (Map.lookup del alpha) (kind entry) "checkD'"
                     handle Lookup => ()) delta'
        )

    and checkG' (delta, gamma) gam gamma' =
        ignore(
            mapRani (fn(x, sigma) =>
                     checkMpure' (delta, gamma) (Map.lookup gam x) sigma "checkG'"
                     handle Lookup => ()) gamma'
        )

    fun checkD delta =
        (* isAcyclic delta *)
        ignore(mapRan (fn(Colon k | Up k | Down k) => ()
                        |(Equi(tau, k) | Iso(tau, k)) => checkT' delta tau k "checkD") delta)

    fun checkG delta gamma =
        (
            checkD delta;
            ignore(mapRan (fn sigma => checkS delta sigma) gamma)
        )
end
