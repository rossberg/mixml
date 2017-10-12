(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature EL_AUX =
sig
    datatype variance = Plus | Minus
    datatype sign =
          Struct of (IL.lab * sign) list
        | Funct of funct * variance
        | Term of IL.typ * variance
        | Typ of IL.typ * IL.kind * variance option
    withtype funct = (IL.typvar * IL.kind) list * (IL.typvar * IL.kind) list * sign

    type typ_context = IL.kind Map.map
    type modl_context = sign Map.map
    type locator = IL.lab list Map.map

    exception At
    exception Locate of IL.lab list
    exception Export of IL.lab list

    val typstruct : IL.typ * IL.kind * variance option -> sign
    val datstruct : IL.typvar * IL.typ * IL.kind * variance option -> sign

    val fvS : sign -> Set.set
    val fvF : funct -> Set.set
    val fvG : modl_context -> Set.set
    val substS : IL.typ_subst -> sign -> sign
    val substF : IL.typ_subst -> funct -> funct
    val substG : IL.typ_subst -> modl_context -> modl_context
    val realS : IL.typ_subst -> sign -> sign

    val normT : typ_context -> IL.typ -> IL.typ
    val equivT : typ_context -> IL.typ * IL.typ -> bool
    val equivS : typ_context -> sign * sign -> bool
    val equivF : typ_context -> funct * funct -> bool

    val at : sign * IL.lab list -> sign
    val locator : variance -> sign -> locator
    val compose : sign -> locator -> IL.typ_subst
    val composePartial : sign -> locator -> IL.typ_subst
(* with realisers: *)
    val composeImport : sign -> locator -> IL.typ_subst * IL.typ_subst
(**)

    val eraseS : sign -> IL.sign
    val eraseF : funct -> IL.sign
    val staticT : IL.typ
    val staticS : sign -> sign
    val staticF : funct -> funct
    val abs : sign -> sign
    val neg : sign -> sign
    val export : IL.lab list list -> sign -> sign

    val create : sign -> IL.modl
    val copy : IL.modl * IL.modl * sign -> IL.modl
end

structure ELAux : EL_AUX =
struct
    open VarOps infix \/ \ |-> |=> ++
    open ILOps

    datatype variance = Plus | Minus
    datatype sign =
          Struct of (IL.lab * sign) list
        | Funct of funct * variance
        | Term of IL.typ * variance
        | Typ of IL.typ * IL.kind * variance option
    withtype funct = (IL.typvar * IL.kind) list * (IL.typvar * IL.kind) list * sign

    type typ_context = IL.kind Map.map
    type modl_context = sign Map.map

    type locator = IL.lab list Map.map

    (* Signature abbreviations *)

    fun typstruct(tau, k, pmo) = Struct["type" |-> Typ(tau, k, pmo)]
    fun datstruct(alpha, tau, k, pmo) =
        let
            val pm = Option.getOpt(pmo, Plus)
            val betas =
                case k of
                    IL.StarK => []
                  | IL.ArrowK(n) => List.tabulate(n, fn _ => rename "beta")
            val alphaT = IL.VarT(alpha)
            fun applyT(tau, []) = tau
              | applyT(tau, betas) = IL.ApplyT(tau, List.map IL.VarT betas)
        in
            Struct[
                "type" |-> Typ(alphaT, k, pmo),
                "in" |-> Term(IL.PureT(betas, applyT(tau, betas), applyT(alphaT, betas)), pm),
                "out" |-> Term(IL.PureT(betas, applyT(alphaT, betas), applyT(tau, betas)), pm)
            ]
        end

    (* Signature meta ops *)

    val rec fvS =
        fn Struct(lsigmas) => List.foldl op\/ (set[]) (List.map (fvS o #2) lsigmas)
         | Funct(phi, pm) => fvF phi
         | Term(tau, pm) => fvT tau
         | Typ(tau, k, pmo) => fvT tau
    and fvF =
        fn (alphaks, betaks, sigma) => fvS(sigma) \ set(List.map #1 alphaks) \ set(List.map #1 betaks)
    val fvG = List.foldl op\/ (set[]) o List.map (fvS o #2) o entries

    fun substS del =
        fn Struct(lsigmas) => Struct(mapSnd (substS del) lsigmas)
         | Funct(phi, pm) => Funct(substF del phi, pm)
         | Term(tau, pm) => Term(substT del tau, pm)
         | Typ(tau, k, pmo) => Typ(substT del tau, k, pmo)
    and substF del =
        fn(alphaks, betaks, sigma) =>
        let
            val (alphaks', del1') = renamesAK alphaks
            val (betaks', del2') = renamesAK betaks
        in
            (alphaks', betaks', substS (del ++ del1' ++ del2') sigma)
        end
    fun substG del gamma = mapRan (substS del) gamma

    fun realS del =
        fn Struct(lsigmas) => Struct(mapSnd (realS del) lsigmas)
         | Funct(phi, pm) => Funct(substF del phi, pm)
         | Term(tau, pm) => Term(substT del tau, pm)
         | Typ(IL.VarT(alpha), k, pmo) =>
            (Typ(lookup del alpha, k, NONE) handle Lookup => Typ(IL.VarT(alpha), k, pmo))
         | Typ(tau, k, pmo) => Typ(substT del tau, k, NONE)


    (* Path access and locators *)

    exception At
    exception Locate of IL.lab list

    infix at
    fun sigma at [] = sigma
      | (Struct(lsigmas)) at (l::ls) = (lookup (map lsigmas) l at ls handle Lookup => raise At)
      | sigma at _ = raise At

    fun locator pm =
        fn Struct(lsigmas) => List.foldl op+|+ (map[]) (List.map (fn(l, sigma) => mapRan (fn ls => l::ls) (locator pm sigma)) lsigmas)
         | Funct(phi, pm) => map[]
         | Term(tau, pm) => map[]
         | Typ(IL.VarT(alpha), k, SOME pm') => if pm = pm' then map[alpha |-> []] else map[]
         | Typ(tau, k, SOME pm') => raise Fail "locator: malformed signature"
         | Typ(tau, k, _) => map[]

    fun compose sigma loc =
        mapRan (fn ls =>
                    case sigma at ls handle At => raise Locate ls of
                        Typ(tau, k, pmo) => tau
                      | _ => raise Locate ls
               ) loc

    fun composePartial sigma loc =
        List.foldl (fn((alpha, ls), del) =>
                        (case sigma at ls of
                            Typ(tau, k, pmo) => del ++ map[alpha |-> tau]
                          | _ => raise Locate ls
                        ) handle At => del
        ) (map[]) (entries loc)

(* with realisers: *)
    fun composeImport sigma loc =
        List.foldl (fn((alpha, ls), (del, rea)) =>
                        case sigma at ls of
                            Typ(tau, k, SOME Minus) => (del ++ map[alpha |-> tau], rea)
                          | Typ(tau, k, pmo) => (del, rea ++ map[alpha |-> tau])
                          | _ => raise Locate ls
        ) (map[], map[]) (entries loc)
(**)

    (* Normalization & equivalence *)

    fun normT delta = ILOps.normT (mapRan IL.Colon delta)

    fun equivT delta = ILOps.equivT (mapRan IL.Colon delta)

    fun sortFields lsigmas = entries(map lsigmas)

    fun equivS delta =
        fn (Typ(tau1, k1, pmo1), Typ(tau2, k2, pmo2)) =>
                k1 = k2 andalso equivT delta (tau1, tau2) andalso pmo1 = pmo2
         | (Term(tau1, pm1), Term(tau2, pm2)) => equivT delta (tau1, tau2) andalso pm1 = pm2
         | (Funct(phi1, pm1), Funct(phi2, pm2)) => equivF delta (phi1, phi2) andalso pm1 = pm2
         | (Struct(lsigmas1), Struct(lsigmas2)) =>
                ListPair.allEq
                    (fn((l1, sigma1), (l2, sigma2)) =>
                        l1 = l2 andalso equivS delta (sigma1, sigma2))
                    (sortFields lsigmas1, sortFields lsigmas2)
         | (_, _) => false

    and equivF delta =
        fn ((alphaks1, betaks1, sigma1), (alphaks2, betaks2, sigma2)) =>
            let
                val (alphas1, ks1) = ListPair.unzip alphaks1
                val (alphas2, ks2) = ListPair.unzip alphaks2
                val (betas1, ks1') = ListPair.unzip betaks1
                val (betas2, ks2') = ListPair.unzip betaks2
                val delta' = delta ++ map(alphaks1) ++ map(betaks1)
                fun del() = map(alphas2 |=> List.map IL.VarT alphas1) ++
                            map(betas2 |=> List.map IL.VarT betas1)
            in
                ListPair.allEq op= (ks1, ks2) andalso ListPair.allEq op= (ks1', ks2')
                andalso equivS delta' (sigma1, substS (del()) sigma2)
            end

    (* Signature modifications *)

    val rec eraseS =
        fn Struct(lsigmas) => IL.StructS(mapSnd eraseS lsigmas)
         | Funct(phi, pm) => IL.LazyS(eraseF phi)
         | Term(tau, pm) => IL.LazyS(IL.TermS(tau))
         | Typ(tau, k, pmo) => IL.TypS(tau, k)
    and eraseF =
        fn(alphaks, betaks, sigma) =>
            IL.UnivS(alphaks, IL.ExistS(betaks, IL.ArrowS(eraseS sigma, IL.StructS[])))

    val staticT = IL.TupleT[IL.TupleT[]]
    val rec staticS =
        fn Struct(lsigmas) => Struct(mapSnd staticS lsigmas)
         | Funct(phi, pm) => Funct(staticF phi, pm)
         | Term(tau, pm) => Term(staticT, pm)
         | Typ(tau, k, pmo) => Typ(tau, k, pmo)
    and staticF =
        fn(alphaks, betaks, sigma) => (alphaks, betaks, staticS sigma)

    val rec abs =
        fn Struct(lsigmas) => Struct(mapSnd abs lsigmas)
         | Funct(phi, pm) => Funct(phi, Plus)
         | Term(tau, pm) => Term(tau, Plus)
         | Typ(tau, k, pmo) => Typ(tau, k, Option.map (fn _ => Plus) pmo)

    fun inv Plus = Minus
      | inv Minus = Plus

    val rec neg =
        fn Struct(lsigmas) => Struct(mapSnd neg lsigmas)
         | Funct(phi, pm) => Funct(phi, inv pm)
         | Term(tau, pm) => Term(tau, inv pm)
         | Typ(tau, k, pmo) => Typ(tau, k, Option.map inv pmo)

    exception Export of IL.lab list

    fun export [] sigma = sigma
      | export [[]] (Funct(phi, Minus)) = Funct(phi, Plus)
      | export [[]] (Term(tau, Minus)) = Term(tau, Plus)
      | export [[]] (Typ(tau, k, SOME Minus)) = Typ(tau, k, SOME Plus)
      | export [[]] (Typ(tau, k, NONE)) = Typ(tau, k, NONE)
      | export lss (Struct(lsigmas)) =
        let
            fun lss' li =
                List.mapPartial (fn [] => SOME [] | l::ls => if l = li then SOME ls else NONE) lss
            val struc = map(lsigmas)
        in
            List.app
                (fn [] => ()
                  | ls as l::_ => if defined struc l then () else raise Export ls
                ) lss;
            Struct(List.map (fn(li, psii) => (li, export (lss' li) psii) handle Export ls => raise Export(li::ls)) lsigmas)
        end
      | export lss psi = raise Export(List.hd lss)

    (* Modules *)

    fun create sigma = create' (rename "_create") sigma
    and create' x =
        fn Struct(lsigmas) =>
                IL.StructM(List.map (fn(l, sigma) => (l, create' (x ^ "." ^ l) sigma)) lsigmas)
         | Funct(phi, pm) => IL.NewTermM(x, eraseF phi, IL.VarM(x))
         | Term(tau, pm) => IL.NewTermM(x, IL.TermS(tau), IL.VarM(x))
         | Typ(tau, k, pmo) => IL.TypM(tau)

    fun select Plus (ppm, pmp) = ppm
      | select Minus (ppm, pmp) = pmp

    fun copy(pmp, ppm, sigma) =
        case sigma of
            Struct(lsigmas) => seqM(List.map (fn(l, sigma) => copy(IL.DotM(pmp, l), IL.DotM(ppm, l), sigma)) lsigmas)
          | Funct(phi, pm) => IL.AssignM(select pm (ppm, pmp), IL.ForceM(select pm (pmp, ppm)))
          | Term(tau, pm) => IL.AssignM(select pm (ppm, pmp), IL.ForceM(select pm (pmp, ppm)))
          | Typ(tau, k, pmo) => IL.StructM[]
end
