(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature IL_OPS =
sig
    val pathM : IL.var * IL.lab list -> IL.modl
    val letM : (IL.var * IL.modl) list * IL.modl -> IL.modl
    val seqM : IL.modl list -> IL.modl
    val lazyM : IL.modl * IL.sign -> IL.modl
    val defEquiM : (IL.typvar * IL.typ) list * IL.modl * IL.sign -> IL.modl
    val defIsoM : (IL.typvar * IL.typ) list * IL.modl * IL.sign -> IL.modl
    val letE : (IL.var * IL.modl) list * IL.term -> IL.term

    val mapFst : (IL.var -> IL.var) -> (IL.var * 'a) list -> (IL.var * 'a) list
    val mapSnd : ('a -> 'b) -> (IL.var * 'a) list -> (IL.var * 'b) list

    val renameX : IL.var -> IL.var * IL.modl_subst
    val renamesA : IL.typvar list -> IL.typvar list * IL.typ_subst
    val renamesAK : (IL.typvar * IL.kind) list -> (IL.typvar * IL.kind) list * IL.typ_subst

    val substA : IL.typ_subst -> IL.typvar -> IL.typvar
    val substT : IL.typ_subst -> IL.typ -> IL.typ
    val substS : IL.typ_subst -> IL.sign -> IL.sign
    val substE : IL.typ_subst -> IL.term -> IL.term
    val substM : IL.typ_subst -> IL.modl -> IL.modl
    val substXE : IL.modl_subst -> IL.term -> IL.term
    val substXM : IL.modl_subst -> IL.modl -> IL.modl

    val normT : IL.typ_context -> IL.typ -> IL.typ
    val normS : IL.typ_context -> IL.sign -> IL.sign
    val equivT : IL.typ_context -> IL.typ * IL.typ -> bool
    val equivS : IL.typ_context -> IL.sign * IL.sign -> bool

    val fvT : IL.typ -> Set.set
    val fvS : IL.sign -> Set.set
    val basis : IL.typ_context -> IL.typ -> Set.set

    val @@ : IL.typ_context * IL.effect -> IL.typ_context
    val kind : IL.typ_entry -> IL.kind
    val writable : IL.typ_context -> Set.set
end

structure ILOps : IL_OPS =
struct
    open VarOps infix \/ /\ \ |-> |=> |=>* ++
    open IL

    fun kind(Colon k | Up k | Down k | Equi(_, k) | Iso(_, k)) = k

    fun writable delta = dom(Map.filter (fn(_, Up k) => true | _ => false) delta)
    fun unstable delta = dom(Map.filter (fn(_, (Up k | Colon k)) => true | _ => false) delta)

    fun fvT(VarT(alpha)) = set[alpha]
      | fvT(IntT) = set[]
      | fvT(StringT) = set[]
      | fvT(TupleT(taus)) = List.foldl op\/ (set[]) (List.map fvT taus)
      | fvT(VariantT(taus)) = List.foldl op\/ (set[]) (List.map fvT taus)
      | fvT(ArrowT(sigma, tau)) = fvS sigma \/ fvT tau
      | fvT(UnivT(alphas, tau)) = fvT tau \ set(alphas)
      | fvT(PureT(alphas, tau1, tau2)) = fvT tau1 \/ fvT tau2 \ set(alphas)
      | fvT(LambdaT(alphas, tau)) = fvT tau \ set(alphas)
      | fvT(ApplyT(tau, taus)) = List.foldl op\/ (fvT tau) (List.map fvT taus)

    and fvS(TypS(tau, k)) = fvT tau
      | fvS(TermS(tau)) = fvT tau
      | fvS(StructS(lsigmas)) = List.foldl op\/ (set[]) (List.map (fvS o #2) lsigmas)
      | fvS(ArrowS(sigma1, sigma2)) = fvS sigma1 \/ fvS sigma2
      | fvS(LazyS(sigma)) = fvS sigma
      | fvS(UnivS(alphaks, sigma)) = fvS sigma \ set(List.map #1 alphaks)
      | fvS(ExistS(alphaks, sigma)) = fvS sigma \ set(List.map #1 alphaks)

    (* Substitutions *)

    fun mapFst f = List.map (fn(x, y) => (f x, y))
    fun mapSnd f = List.map (fn(x, y) => (x, f y))

    fun renameX x =
        let
            val x' = rename x
        in
            (x', map[x |-> VarM(x')])
        end

    fun renamesA alphas =
        let
            val alphas' = List.map rename alphas
        in
            (alphas', map(alphas |=> List.map VarT alphas'))
        end

    fun renamesAK alphaks =
        let
            val (alphas, ks) = ListPair.unzip alphaks
            val (alphas', del) = renamesA alphas
        in
            (ListPair.zipEq(alphas', ks), del)
        end

    fun substA del alpha =
        (case lookup del alpha of
            VarT(alpha') => alpha'
          | _ => raise Domain
        ) handle Lookup => alpha

    fun substT del =
        fn VarT(alpha) => (lookup del alpha handle Lookup => VarT(alpha))
         | IntT => IntT
         | StringT => StringT
         | TupleT(taus) => TupleT(List.map (substT del) taus)
         | VariantT(taus) => VariantT(List.map (substT del) taus)
         | ArrowT(sigma, tau) => ArrowT(substS del sigma, substT del tau)
         | UnivT(alphas, tau) =>
            let
                val (alphas', del') = renamesA alphas
            in
                UnivT(alphas', substT (del ++ del') tau)
            end
         | PureT(alphas, tau1, tau2) =>
            let
                val (alphas', del') = renamesA alphas
            in
                PureT(alphas', substT (del ++ del') tau1, substT (del ++ del') tau2)
            end
         | LambdaT(alphas, tau) =>
            let
                val (alphas', del') = renamesA alphas
            in
                LambdaT(alphas', substT (del ++ del') tau)
            end
         | ApplyT(tau, taus) => ApplyT(substT del tau, List.map (substT del) taus)

    and substS del =
        fn TypS(tau, k) => TypS(substT del tau, k)
         | TermS(tau) => TermS(substT del tau)
         | StructS(lsigmas) => StructS(mapSnd (substS del) lsigmas)
         | ArrowS(sigma1, sigma2) => ArrowS(substS del sigma1, substS del sigma2)
         | LazyS(sigma) => LazyS(substS del sigma)
         | UnivS(alphaks, sigma) =>
            let
                val (alphaks', del') = renamesAK alphaks
            in
                UnivS(alphaks', substS (del ++ del') sigma)
            end
         | ExistS(alphaks, sigma) =>
            let
                val (alphaks', del') = renamesAK alphaks
            in
                ExistS(alphaks', substS (del ++ del') sigma)
            end

    fun substE del =
        fn ValE(m) => ValE(substM del m)
         | IntE(n) => IntE(n)
         | StringE(s) => StringE(s)
         | PlusE(e1, e2) => PlusE(substE del e1, substE del e2)
         | MinusE(e1, e2) => MinusE(substE del e1, substE del e2)
         | EqualE(e1, e2) => EqualE(substE del e1, substE del e2)
         | LessE(e1, e2) => LessE(substE del e1, substE del e2)
         | CatE(e1, e2) => CatE(substE del e1, substE del e2)
         | TupleE(es) => TupleE(List.map (substE del) es)
         | DotE(e, i) => DotE(substE del e, i)
         | VariantE(e, i, tau) => VariantE(substE del e, i, substT del tau)
         | CaseE(e, xes) => CaseE(substE del e, mapSnd (substE del) xes)
         | LambdaE(x, sigma, e) => LambdaE(x, substS del sigma, substE del e)
         | ApplyE(e, m) => ApplyE(substE del e, substM del m)
         | GenE(alphas, e) =>
            let
                val (alphas', del') = renamesA alphas
            in
                GenE(alphas', substE (del ++ del') e)
            end
         | InstE(e, taus) => InstE(substE del e, List.map (substT del) taus)
         | FoldE(alpha) => FoldE(substA del alpha)
         | UnfoldE(alpha) => UnfoldE(substA del alpha)
         | ConE(e1, taus, e2) => ConE(substE del e1, List.map (substT del) taus, substE del e2)
         | PrintE(e) => PrintE(substE del e)

    and substM del =
        fn VarM(x) => VarM(x)
         | TypM(tau) => TypM(substT del tau)
         | TermM(e) => TermM(substE del e)
         | StructM(lms) => StructM(mapSnd (substM del) lms)
         | DotM(m, l) => DotM(substM del m, l)
         | LambdaM(x, sigma, m) => LambdaM(x, substS del sigma, substM del m)
         | ApplyM(f, m) => ApplyM(substM del f, substM del m)
         | LetM(x, m1, m2) => LetM(x, substM del m1, substM del m2)
         | GenDownM(alphaks, m) =>
            let
                val (alphaks', del') = renamesAK alphaks
            in
                GenDownM(alphaks', substM (del ++ del') m)
            end
         | InstDownM(m, taus) => InstDownM(substM del m, List.map (substT del) taus)
         | GenUpM(alphaks, m) =>
            let
                val (alphaks', del') = renamesAK alphaks
            in
                GenUpM(alphaks', substM (del ++ del') m)
            end
         | InstUpM(m, alphas) => InstUpM(substM del m, List.map (substA del) alphas)
         | NewTypM(alphaks, m) =>
            let
                val (alphaks', del') = renamesAK alphaks
            in
                NewTypM(alphaks', substM (del ++ del') m)
            end
         | DefEquiM(alpha, tau, m, sigma, del', gam', contexts as ref NONE) =>
            (* initial alpha renaming substitutions have to be performed directly! *)
            if isId del' andalso isId gam' then
                DefEquiM(substA del alpha, substT del tau, substM del m,
                         substS del sigma, del', gam', ref NONE)
            else
                raise Fail "subst on DefEqui"
         | DefEquiM(alpha, tau, m, sigma, del', gam', contexts) =>
                DefEquiM(alpha, tau, m, sigma, composeT del del', composeM del gam', contexts)
(*
         | DefEquiM(alpha, tau, m, sigma) =>
                DefEquiM(substA del alpha, substT del tau, substM del m, substS del sigma)
*)
         | DefIsoM(alpha, tau, m, sigma) =>
                DefIsoM(substA del alpha, substT del tau, substM del m, substS del sigma)
         | NewTermM(x, sigma, m) => NewTermM(x, substS del sigma, substM del m)
         | AssignM(m1, m2) => AssignM(substM del m1, substM del m2)
         | ForceM(m) => ForceM(substM del m)

    and composeT del del' = mapRan (substT del) del' ++ del
    and composeM del gam = mapRan (substM del) gam

    fun substXE gam =
        fn ValE(m) => ValE(substXM gam m)
         | IntE(n) => IntE(n)
         | StringE(s) => StringE(s)
         | PlusE(e1, e2) => PlusE(substXE gam e1, substXE gam e2)
         | MinusE(e1, e2) => MinusE(substXE gam e1, substXE gam e2)
         | EqualE(e1, e2) => EqualE(substXE gam e1, substXE gam e2)
         | LessE(e1, e2) => LessE(substXE gam e1, substXE gam e2)
         | CatE(e1, e2) => CatE(substXE gam e1, substXE gam e2)
         | TupleE(es) => TupleE(List.map (substXE gam) es)
         | DotE(e, i) => DotE(substXE gam e, i)
         | VariantE(e, i, tau) => VariantE(substXE gam e, i, tau)
         | CaseE(e, xes) =>
            let
                val xes' =
                    List.map (fn(x, e) =>
                              let val (x', gam') = renameX x in (x', substXE (gam ++ gam') e) end
                             ) xes
            in
                CaseE(substXE gam e, xes')
            end
         | LambdaE(x, sigma, e) =>
            let
                val (x', gam') = renameX x
            in
                LambdaE(x', sigma, substXE (gam ++ gam') e)
            end
         | ApplyE(e, m) => ApplyE(substXE gam e, substXM gam m)
         | GenE(alphas, e) => GenE(alphas, substXE gam e)
         | InstE(e, taus) => InstE(substXE gam e, taus)
         | FoldE(alpha) => FoldE(alpha)
         | UnfoldE(alpha) => UnfoldE(alpha)
         | ConE(e1, taus, e2) => ConE(substXE gam e1, taus, substXE gam e2)
         | PrintE(e) => PrintE(substXE gam e)

    and substXM gam =
        fn VarM(x) => (lookup gam x handle Lookup => VarM(x))
         | TypM(tau) => TypM(tau)
         | TermM(e) => TermM(substXE gam e)
         | StructM(lms) => StructM(mapSnd (substXM gam) lms)
         | DotM(m, l) => DotM(substXM gam m, l)
         | LambdaM(x, sigma, m) =>
            let
                val (x', gam') = renameX x
            in
                LambdaM(x', sigma, substXM (gam ++ gam') m)
            end
         | ApplyM(f, m) => ApplyM(substXM gam f, substXM gam m)
         | LetM(x, m1, m2) =>
            let
                val (x', gam') = renameX x
            in
                LetM(x', substXM gam m1, substXM (gam ++ gam') m2)
            end
         | GenDownM(alphaks, m) => GenDownM(alphaks, substXM gam m)
         | InstDownM(m, taus) => InstDownM(substXM gam m, taus)
         | GenUpM(alphaks, m) => GenUpM(alphaks, substXM gam m)
         | InstUpM(m, alphas) => InstUpM(substXM gam m, alphas)
         | NewTypM(alphaks, m) => NewTypM(alphaks, substXM gam m)
         | DefEquiM(alpha, tau, m, sigma, del', gam', contexts as ref NONE) =>
            (* initial alpha renaming substitutions have to be performed directly! *)
            if isId del' andalso isId gam' then
                DefEquiM(alpha, tau, substXM gam m, sigma, del', gam', ref NONE)
            else
                raise Fail "subst on DefEqui"
         | DefEquiM(alpha, tau, m, sigma, del', gam', contexts) =>
            DefEquiM(alpha, tau, m, sigma, del', composeX gam gam', contexts)
(*
         | DefEquiM(alpha, tau, m, sigma) => DefEquiM(alpha,taua, substXM gam m, sigma)
*)
         | DefIsoM(alpha, tau, m, sigma) => DefIsoM(alpha, tau, substXM gam m, sigma)
         | NewTermM(x, sigma, m) =>
            let
                val (x', gam') = renameX x
            in
                NewTermM(x', sigma, substXM (gam ++ gam') m)
            end
         | AssignM(m1, m2) => AssignM(substXM gam m1, substXM gam m2)
         | ForceM(m) => ForceM(substXM gam m)

    and composeX gam gam' = mapRan (substXM gam) gam' ++ gam

    (* Type normalisation *)

    fun normT delta =
        fn tau as VarT(alpha) =>
(
            (case lookup delta alpha of
                Equi(tau', k) =>
                    if tau' = tau
                    then tau
                    else normT delta tau'
              | entry => tau
            )
(*DEBUG*)
handle e => (print "normT lookup failed for ";print alpha;print"\n";
print("  delta = " ^ String.concatWith ", " (List.map (fn(alpha,k) => alpha) (entries delta)) ^ "\n");
raise e))
         | IntT => IntT
         | StringT => StringT
         | TupleT(taus) => TupleT(List.map (normT delta) taus)
         | VariantT(taus) => VariantT(List.map (normT delta) taus)
         | ArrowT(sigma, tau) => ArrowT(normS delta sigma, normT delta tau)
         | UnivT(alphas, tau) =>
            let
                val delta' = delta ++ map(alphas |=>* Colon StarK)
            in
                UnivT(alphas, normT delta' tau)
            end
         | PureT(alphas, tau1, tau2) =>
            let
                val delta' = delta ++ map(alphas |=>* Colon StarK)
            in
                PureT(alphas, normT delta' tau1, normT delta' tau2)
            end
         | LambdaT(alphas, tau) =>
            let
                val delta' = delta ++ map(alphas |=>* Colon StarK)
            in
                case normT delta' tau of
                    tau' as ApplyT(tau'', taus') =>
                        if taus' = List.map VarT alphas andalso isEmpty(fvT tau' /\ set(alphas))
                        then tau''
                        else LambdaT(alphas, ApplyT(tau'', taus'))
                  | tau' => LambdaT(alphas, tau')
            end
         | ApplyT(tau, taus) =>
            let
            in
                case normT delta tau of
                    LambdaT(alphas, tau) => normT delta (substT (map(alphas |=> taus)) tau)
                  | tau' => ApplyT(tau', List.map (normT delta) taus)
            end

    and normS delta =
        fn TypS(tau, k) => TypS(normT delta tau, k)
         | TermS(tau) => TermS(normT delta tau)
         | StructS(lsigmas) => StructS(mapSnd (normS delta) lsigmas)
         | ArrowS(sigma1, sigma2) => ArrowS(normS delta sigma1, normS delta sigma2)
         | LazyS(sigma) => LazyS(normS delta sigma)
         | UnivS(alphaks, sigma) => UnivS(alphaks, normS (delta ++ mapRan Down (map alphaks)) sigma)
         | ExistS(alphaks, sigma) => ExistS(alphaks, normS (delta ++ mapRan Up (map alphaks)) sigma)

    (* Type equivalence *)

    fun equivT delta (tau1, tau2) = equivT' delta (normT delta tau1, normT delta tau2)
handle e => raise e
    and equivT' delta =
        fn (VarT(alpha1), VarT(alpha2)) =>
            let
                (* bound variables are equalised using delta *)
                val alpha1' = case lookup delta alpha1 of Equi(VarT(alpha), _) => alpha | _ => alpha1
            in
                alpha1' = alpha2
            end
         | (IntT, IntT) => true
         | (StringT, StringT) => true
         | (TupleT(taus1), TupleT(taus2)) => ListPair.allEq (equivT' delta) (taus1, taus2)
         | (VariantT(taus1), VariantT(taus2)) => ListPair.allEq (equivT' delta) (taus1, taus2)
         | (ArrowT(sigma1, tau1), ArrowT(sigma2, tau2)) =>
                equivS delta (sigma1, sigma2) andalso equivT' delta (tau1, tau2)
         | (UnivT(alphas1, tau1), UnivT(alphas2, tau2)) =>
            let
                val delta' = delta ++ map(alphas2 |=>* Colon StarK)
                    ++ map(alphas1 |=> List.map Equi (mapFst VarT (alphas2 |=>* StarK)))
            in
                equivT' delta' (tau1, tau2)
            end
         | (PureT(alphas1, tau11, tau12), PureT(alphas2, tau21, tau22)) =>
            let
                val delta' = delta ++ map(alphas2 |=>* Colon StarK)
                    ++ map(alphas1 |=> List.map Equi (mapFst VarT (alphas2 |=>* StarK)))
            in
                equivT' delta' (tau11, tau21) andalso equivT' delta' (tau12, tau22)
            end
         | (LambdaT(alphas1, tau1), LambdaT(alphas2, tau2)) =>
            let
                val delta' = delta ++ map(alphas2 |=>* Colon StarK)
                    ++ map(alphas1 |=> List.map Equi (mapFst VarT (alphas2 |=>* StarK)))
            in
                equivT' delta' (tau1, tau2)
            end
         | (ApplyT(tau1, taus1), ApplyT(tau2, taus2)) =>
                equivT' delta (tau1, tau2) andalso ListPair.allEq (equivT' delta) (taus1, taus2)
         | (_, _) => false

    and sortFields lsigmas = entries(map lsigmas)

    and equivS delta =
        fn (TypS(tau1, k1), TypS(tau2, k2)) => k1 = k2 andalso equivT delta (tau1, tau2)
         | (TermS(tau1), TermS(tau2)) => equivT delta (tau1, tau2)
         | (StructS(lsigmas1), StructS(lsigmas2)) =>
                ListPair.allEq
                    (fn((l1, sigma1), (l2, sigma2)) =>
                        l1 = l2 andalso equivS delta (sigma1, sigma2))
                    (sortFields lsigmas1, sortFields lsigmas2)
         | (ArrowS(sigma11, sigma12), ArrowS(sigma21, sigma22)) =>
                equivS delta (sigma11, sigma21) andalso equivS delta (sigma12, sigma22)
         | (LazyS(sigma1), LazyS(sigma2)) => equivS delta (sigma1, sigma2)
         | (UnivS(alphaks1, sigma1), UnivS(alphaks2, sigma2)) =>
            let
                val (alphas1, ks1) = ListPair.unzip alphaks1
                val (alphas2, ks2) = ListPair.unzip alphaks2
                fun delta'() = delta ++ map(mapSnd Colon alphaks2) ++ map(alphas1 |=> List.map Equi (mapFst VarT alphaks2))
            in
                ListPair.allEq op= (ks1, ks2) andalso equivS (delta'()) (sigma1, sigma2)
            end
         | (ExistS(alphaks1, sigma1), ExistS(alphaks2, sigma2)) =>
            let
                val (alphas1, ks1) = ListPair.unzip alphaks1
                val (alphas2, ks2) = ListPair.unzip alphaks2
                fun delta'() = delta ++ map(mapSnd Colon alphaks2) ++ map(alphas1 |=> List.map Equi (mapFst VarT alphaks2))
            in
                ListPair.allEq op= (ks1, ks2) andalso equivS (delta'()) (sigma1, sigma2)
            end
         | (_, _) => false

    fun basis delta tau = fvT(normT delta tau) /\ unstable(delta)

    (* Effects *)

    infix 5 @@
    fun delta @@ (DownE(alphas)) = app(delta, Down, alphas)
      | delta @@ (IsoE(alpha, tau)) = app(delta, fn k => Iso(tau, k), [alpha])
      | delta @@ (EquiE(alpha, tau)) = app(delta, fn k => Equi(normT delta tau, k), [alpha])
    and app(delta, f, alphas) =
        mapRani (fn(alpha, Up k) =>
                    if List.exists (fn alpha' => alpha' = alpha) alphas then f k else Up k
                  |(alpha, other) => other
                ) delta

    (* Sugar *)

    fun pathM(x, ls) = List.foldl (fn(l, p) => IL.DotM(p, l)) (IL.VarM(x)) ls

    fun letM(xms, m) = List.foldr (fn((x, m1), m2) => LetM(x, m1, m2)) m xms
    fun letE(xms, e) = ValE(letM(xms, TermM(e)))

    fun seqM [] = StructM[]
      | seqM[m] = m
      | seqM(m::ms) = LetM(rename "_seq", m, seqM ms)

    fun lazyM(m, sigma) =
        let
            val x = rename "_lazy"
        in
            NewTermM(x, sigma, seqM[AssignM(VarM(x), m), VarM(x)])
        end

    fun defEquiM(alphataus, m, sigma) =
        List.foldr (fn((alpha, tau), m) => DefEquiM(alpha, tau, m, sigma, map[], map[], ref NONE)) m alphataus
    fun defIsoM(alphataus, m, sigma) =
        List.foldr (fn((alpha, tau), m) => DefIsoM(alpha, tau, m, sigma)) m alphataus
end
