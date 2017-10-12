(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature IL_EVALUATION =
sig
    exception Stuck of ILMachine.state
    exception Black of IL.var
    type context = ILMachine.typ_context * ILMachine.modl_context * ILMachine.store
    val emptyContext : context
    val step : ILMachine.state -> ILMachine.state
    val run : context * IL.modl -> context * ILMachine.modval
end

structure ILEvaluation : IL_EVALUATION =
struct
    open ILMachine
    open ILOps infix @@
    open VarOps infix |-> |=> ++

    exception Stuck of ILMachine.state
    exception Black of IL.var

    infix @@@
    fun omega @@@ (x, st) = mapRani (fn(x', st') => if x' = x then st else st') omega

    fun step s =
        case s of
           TermSt(delta, gamma, omega, cc, EXP(e as ConE(e1, taus, e2))) =>
            (case toValue e of
                NONE => TermSt(delta, gamma, omega, ConF1(taus, e2)::cc, EXP e1)
              | SOME v => step(TermSt(delta, gamma, omega, cc, VAL v))
            )
         | TermSt(delta, gamma, omega, ConF1(taus, e)::cc, VAL v) =>
                TermSt(delta, gamma, omega, ConF2(v, taus)::cc, EXP e)
         | TermSt(delta, gamma, omega, ConF2(FoldV(alpha), taus)::cc, VAL v) =>
                TermSt(delta, gamma, omega, cc, VAL(ConV(alpha, taus, v)))
         | TermSt(delta, gamma, omega, ConF2(UnfoldV(alpha), taus1)::cc, VAL(ConV(beta, taus2, v))) =>
                TermSt(delta, gamma, omega, cc, VAL v)
         | TermSt(delta, gamma, omega, cc, EXP(PlusE(e1, e2))) =>
                TermSt(delta, gamma, omega, PlusF1(e2)::cc, EXP e1)
         | TermSt(delta, gamma, omega, PlusF1(e)::cc, VAL(IntV(n))) =>
                TermSt(delta, gamma, omega, PlusF2(n)::cc, EXP e)
         | TermSt(delta, gamma, omega, PlusF2(n1)::cc, VAL(IntV(n2))) =>
                TermSt(delta, gamma, omega, cc, VAL(IntV(n1 + n2)))
         | TermSt(delta, gamma, omega, cc, EXP(MinusE(e1, e2))) =>
                TermSt(delta, gamma, omega, MinusF1(e2)::cc, EXP e1)
         | TermSt(delta, gamma, omega, MinusF1(e)::cc, VAL(IntV(n))) =>
                TermSt(delta, gamma, omega, MinusF2(n)::cc, EXP e)
         | TermSt(delta, gamma, omega, MinusF2(n1)::cc, VAL(IntV(n2))) =>
                TermSt(delta, gamma, omega, cc, VAL(IntV(n1 - n2)))
         | TermSt(delta, gamma, omega, cc, EXP(EqualE(e1, e2))) =>
                TermSt(delta, gamma, omega, EqualF1(e2)::cc, EXP e1)
         | TermSt(delta, gamma, omega, EqualF1(e)::cc, VAL(IntV(n))) =>
                TermSt(delta, gamma, omega, EqualF2(n)::cc, EXP e)
         | TermSt(delta, gamma, omega, EqualF2(n1)::cc, VAL(IntV(n2))) =>
            let
                val i = if n1 = n2 then 2 else 1
            in
                TermSt(delta, gamma, omega, cc, VAL(VariantV(TupleV[], i, VariantT[TupleT[], TupleT[]])))
            end
         | TermSt(delta, gamma, omega, cc, EXP(LessE(e1, e2))) =>
                TermSt(delta, gamma, omega, LessF1(e2)::cc, EXP e1)
         | TermSt(delta, gamma, omega, LessF1(e)::cc, VAL(IntV(n))) =>
                TermSt(delta, gamma, omega, LessF2(n)::cc, EXP e)
         | TermSt(delta, gamma, omega, LessF2(n1)::cc, VAL(IntV(n2))) =>
            let
                val i = if n1 < n2 then 2 else 1
            in
                TermSt(delta, gamma, omega, cc, VAL(VariantV(TupleV[], i, VariantT[TupleT[], TupleT[]])))
            end
         | TermSt(delta, gamma, omega, cc, EXP(CatE(e1, e2))) =>
                TermSt(delta, gamma, omega, CatF1(e2)::cc, EXP e1)
         | TermSt(delta, gamma, omega, CatF1(e)::cc, VAL(StringV(s))) =>
                TermSt(delta, gamma, omega, CatF2(s)::cc, EXP e)
         | TermSt(delta, gamma, omega, CatF2(s1)::cc, VAL(StringV(s2))) =>
                TermSt(delta, gamma, omega, cc, VAL(StringV(s1 ^ s2)))
         | TermSt(delta, gamma, omega, cc, EXP(e as TupleE(e1::es2))) =>
            (case toValue e of
                NONE => TermSt(delta, gamma, omega, TupleF([], es2)::cc, EXP e1)
              | SOME v => step(TermSt(delta, gamma, omega, cc, VAL v))
            )
         | TermSt(delta, gamma, omega, TupleF(vs1, e3::es4)::cc, VAL v2) =>
                TermSt(delta, gamma, omega, TupleF(vs1@[v2], es4)::cc, EXP e3)
         | TermSt(delta, gamma, omega, TupleF(vs1, [])::cc, VAL v2) =>
                TermSt(delta, gamma, omega, cc, VAL(TupleV(vs1@[v2])))
         | TermSt(delta, gamma, omega, cc, EXP(DotE(e, i))) =>
                TermSt(delta, gamma, omega, ProjF(i)::cc, EXP e)
         | TermSt(delta, gamma, omega, ProjF(i)::cc, VAL(TupleV(vs))) =>
            let
                val v_i = List.nth(vs, i-1)
            in
                TermSt(delta, gamma, omega, cc, VAL v_i)
            end
         | TermSt(delta, gamma, omega, cc, EXP(VariantE(e, i, tau))) =>
            (case toValue e of
                NONE => TermSt(delta, gamma, omega, VariantF(i, tau)::cc, EXP e)
              | SOME v => step(TermSt(delta, gamma, omega, cc, VAL(VariantV(v, i, tau))))
            )
         | TermSt(delta, gamma, omega, VariantF(i, tau)::cc, VAL v) =>
                TermSt(delta, gamma, omega, cc, VAL(VariantV(v, i, tau)))
         | TermSt(delta, gamma, omega, cc, EXP(CaseE(e, xes))) =>
                TermSt(delta, gamma, omega, CaseF(xes)::cc, EXP e)
         | TermSt(delta, gamma, omega, CaseF(xes)::cc, VAL(VariantV(v, i, tau))) =>
           let
                val (x, e) = List.nth(xes, i-1)
           in
                TermSt(delta, gamma, omega, cc, EXP(substXE (map[x |-> TermM(fromValue v)]) e))
           end
         | TermSt(delta, gamma, omega, cc, EXP(ApplyE(f, m))) =>
                TermSt(delta, gamma, omega, AppF1(m)::cc, EXP f)
         | TermSt(delta, gamma, omega, AppF1(m)::cc, VAL v) =>
                ModSt(delta, gamma, omega, AppF2(v)::cc, EXP m)
         | ModSt(delta, gamma, omega, AppF2(LambdaV(x, sigma, e))::cc, VAL w) =>
                TermSt(delta, gamma, omega, cc, EXP(substXE (map[x |-> fromModval w]) e))
         | TermSt(delta, gamma, omega, cc, EXP(InstE(f, taus))) =>
                TermSt(delta, gamma, omega, InstF(taus)::cc, EXP f)
         | TermSt(delta, gamma, omega, InstF(taus)::cc, VAL(GenV(alphas, e))) =>
                TermSt(delta, gamma, omega, cc, EXP(substE (map(alphas |=> taus)) e))
         | TermSt(delta, gamma, omega, cc, EXP(PrintE(e))) =>
                TermSt(delta, gamma, omega, PrintF::cc, EXP(e))
         | TermSt(delta, gamma, omega, PrintF::cc, VAL(v)) =>
            (
                print(case v of StringV(s) => s | v => ILPrint.strV v);
                TermSt(delta, gamma, omega, cc, VAL(TupleV[]))
            )
         | TermSt(delta, gamma, omega, cc, EXP(ValE(m))) =>
                ModSt(delta, gamma, omega, ValF::cc, EXP m)
         | ModSt(delta, gamma, omega, ValF::cc, VAL(TermW(v))) =>
                TermSt(delta, gamma, omega, cc, VAL v)
         | ModSt(delta, gamma, omega, cc, EXP(TermM(e))) =>
            (case toValue e of
                NONE => TermSt(delta, gamma, omega, TermF::cc, EXP e)
              | SOME v => step(ModSt(delta, gamma, omega, cc, VAL(TermW(v))))
            )
         | TermSt(delta, gamma, omega, TermF::cc, VAL v) =>
                ModSt(delta, gamma, omega, cc, VAL(TermW(v)))
         | ModSt(delta, gamma, omega, cc, EXP(m as StructM((l1, m1)::lms2))) =>
            (case toModval m of
                NONE => ModSt(delta, gamma, omega, StructF([], l1, lms2)::cc, EXP m1)
              | SOME w => step(ModSt(delta, gamma, omega, cc, VAL w))
            )
         | ModSt(delta, gamma, omega, StructF(lws1, l2, (l3, m3)::lms4)::cc, VAL w2) =>
                ModSt(delta, gamma, omega, StructF(lws1@[(l2, w2)], l3, lms4)::cc, EXP m3)
         | ModSt(delta, gamma, omega, StructF(lws1, l2, [])::cc, VAL w2) =>
                ModSt(delta, gamma, omega, cc, VAL(StructW(lws1@[(l2, w2)])))
         | ModSt(delta, gamma, omega, cc, EXP(DotM(m, l))) =>
                ModSt(delta, gamma, omega, DotF(l)::cc, EXP m)
         | ModSt(delta, gamma, omega, DotF(l)::cc, VAL(StructW(lws))) =>
            let
                val w_l = lookup (map(lws)) l
            in
                ModSt(delta, gamma, omega, cc, VAL w_l)
            end
(* todo: real effect system *)
         | ModSt(delta, gamma, omega, cc, EXP(ApplyM(InstUpM(f, betas), m))) =>
                ModSt(delta, gamma, omega, InstUpF1(betas, m)::cc, EXP f)
         | ModSt(delta, gamma, omega, cc, EXP(ApplyM(f, m))) =>
                ModSt(delta, gamma, omega, ApplyF1(m)::cc, EXP f)
         | ModSt(delta, gamma, omega, ApplyF1(m)::cc, VAL v) =>
                ModSt(delta, gamma, omega, ApplyF2(v)::cc, EXP m)
         | ModSt(delta, gamma, omega, ApplyF2(LambdaW(x, sigma, m))::cc, VAL w) =>
                ModSt(delta, gamma, omega, cc, EXP(substXM (map[x |-> fromModval w]) m))
         | ModSt(delta, gamma, omega, cc, EXP(LetM(x, m1, m2))) =>
                ModSt(delta, gamma, omega, LetF(x, m2)::cc, EXP m1)
         | ModSt(delta, gamma, omega, LetF(x, m)::cc, VAL w) =>
                ModSt(delta, gamma, omega, cc, EXP(substXM (map[x |-> fromModval w]) m))
         | ModSt(delta, gamma, omega, cc, EXP(InstDownM(f, taus))) =>
                ModSt(delta, gamma, omega, InstDownF(taus)::cc, EXP f)
         | ModSt(delta, gamma, omega, InstDownF(taus)::cc, VAL(GenDownW(alphaks, m))) =>
                ModSt(delta, gamma, omega, cc, EXP(substM (map(List.map #1 alphaks |=> taus)) m))
(* todo: real effect system
         | ModSt(delta, gamma, omega, cc, EXP(InstUpM(f, betas))) =>
                ModSt(delta, gamma, omega, InstUpF(betas)::cc, EXP f)
         | ModSt(delta, gamma, omega, InstUpF(betas)::cc, VAL(GenUpW(alphaks, m))) =>
                ModSt(delta, gamma, omega, cc, EXP(substM (map(List.map #1 alphaks |=> List.map VarT betas)) m))
*)
         | ModSt(delta, gamma, omega, InstUpF1(betas, m)::cc, VAL w) =>
                ModSt(delta, gamma, omega, InstUpF2(w, betas)::cc, EXP m)
         | ModSt(delta, gamma, omega, InstUpF2(GenUpW(alphaks, LambdaM(x, sigma, m)), betas)::cc, VAL w) =>
                ModSt(delta, gamma, omega, cc, EXP(substXM (map[x |-> fromModval w]) (substM (map(List.map #1 alphaks |=> List.map VarT betas)) m)))
         | ModSt(delta, gamma, omega, cc, EXP(NewTypM(alphaks, m))) =>
            let
                val (alphaks', del) = renamesAK alphaks
            in
                ModSt(delta ++ map(mapSnd Up alphaks'), gamma, omega, cc, EXP(substM del m))
            end
         | ModSt(delta, gamma, omega, cc, EXP(DefEquiM(alpha, tau, m, sigma, del, gam, _))) =>
            let
                val alpha' = substA del alpha
                val tau' = substT del tau
                val m' = substXM gam (substM del m)
            in
                if member (writable(delta)) alpha' (* andalso not(member (fvT(normT delta tau')) alpha') *)
                then ModSt(delta @@ EquiE(alpha', tau'), gamma, omega, cc, EXP m')
                else raise Stuck s
            end
(*
         | ModSt(delta, gamma, omega, cc, EXP(DefEquiM(alpha, tau, m, sigma))) =>
            if member (writable(delta)) alpha andalso not(member (fvT(normT delta tau)) alpha)
            then ModSt(delta @@ EquiE(alpha, tau), gamma, omega, cc, EXP m)
            else raise Stuck s
*)
         | ModSt(delta, gamma, omega, cc, EXP(DefIsoM(alpha, tau, m, sigma))) =>
            if member (writable(delta)) alpha
            then ModSt(delta @@ IsoE(alpha, tau), gamma, omega, cc, EXP m)
            else raise Stuck s
         | ModSt(delta, gamma, omega, cc, EXP(NewTermM(x, sigma, m))) =>
            let
                val (x', del) = renameX x
            in
                ModSt(delta, gamma ++ map[x' |-> LazyS(sigma)], omega ++ map[x' |-> Undefined], cc, EXP(substXM del m))
            end
         | ModSt(delta, gamma, omega, cc, EXP(AssignM(m1, m2))) =>
                ModSt(delta, gamma, omega, AssignF(m2)::cc, EXP m1)
         | ModSt(delta, gamma, omega, AssignF(m)::cc, VAL(VarW(x))) =>
                ModSt(delta, gamma, omega @@@ (x, Defined m), cc, VAL(StructW[]))
         | ModSt(delta, gamma, omega, cc, EXP(ForceM(m))) =>
                ModSt(delta, gamma, omega, ForceF::cc, EXP m)
         | ModSt(delta, gamma, omega, ForceF::cc, VAL(VarW(x))) =>
            (case lookup omega x of
                Evaluated v => ModSt(delta, gamma, omega, cc, VAL v)
              | Evaluating => BlackHole x
              | Defined m => ModSt(delta, gamma, omega @@@ (x, Evaluating), NeededF(x)::cc, EXP m)
              | Undefined => BlackHole x
            )
         | ModSt(delta, gamma, omega, NeededF(x)::cc, VAL w) =>
                ModSt(delta, gamma, omega @@@ (x, Evaluated w), cc, VAL w)
         | TermSt(delta, gamma, omega, cc as _::_, EXP e) =>
            (case toValue e of
                NONE => raise Stuck s
              | SOME v => step(TermSt(delta, gamma, omega, cc, VAL v))
            )
         | ModSt(delta, gamma, omega, cc as _::_, EXP m) =>
            (case toModval m of
                NONE => raise Stuck s
              | SOME w => step(ModSt(delta, gamma, omega, cc, VAL w))
            )
         | s => raise Stuck s

    val step' = fn s =>
        let
            val text1 =
                case s of
                    ModSt(_, _, _, ff::cc, _) => ILPrint.strF ff
                  | TermSt(_, _, _, ff::cc, _) => ILPrint.strF ff
                  | _ => ""
            val text2 =
                case s of
                    BlackHole x => "BlackHole " ^ x
                  | ModSt(_, _, omega, _, VAL w) => ILPrint.strW omega w
                  | ModSt(_, _, omega, _, EXP m) => ILPrint.strM omega m
                  | TermSt(_, _, _, _, VAL v) => ILPrint.strV v
                  | TermSt(_, _, omega, _, EXP e) => ILPrint.strE omega e
        in
            print(text1 ^ "_" ^ text2);
            step s
        end

    type context = ILMachine.typ_context * ILMachine.modl_context * ILMachine.store
    val emptyContext = (map[], map[], map[]) : context

    val progress = ""
    val completion = ""

    fun run((delta, gamma, omega), m) =
        run'(ModSt(delta, gamma, omega, [], EXP m)) before print completion
    and run' s =
        case s of
            BlackHole x => raise Black x
          | ModSt(delta, gamma, omega, [], VAL w) => ((delta, gamma, omega), w)
          | ModSt(delta, gamma, omega, [], EXP m) =>
            (case toModval m of
                NONE => run'(step s before print progress)
              | SOME w => ((delta, gamma, omega), w)
            )
          | _ => run'(step s before print progress)
end
