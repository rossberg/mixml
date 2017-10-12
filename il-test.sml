(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

structure ILTest : sig end =
struct
    open IL

    infix 5 ++
    val op++ = op^

    (* sugar to write ASTs compactly *)

    infixr 9 --->
    val T = StarK
    fun T--->StarK = ArrowK(1)
      | T--->(ArrowK(n)) = ArrowK(n+1)

    infix 9 ^^
    fun `alpha = VarT(alpha)
    val int = IntT
    fun forallt alphas tau1==>tau2 = PureT(alphas, tau1, tau2)
    val ==> = ()
    fun \\alphas tau = LambdaT(alphas, tau)
    fun a^^taus = ApplyT(a, taus)

    infixr 9 -->
    fun sty[(a,k)] = TypS(a, k)
    fun stm[tau] = TermS(tau)
    fun sstruc(lsigmas) = StructS(lsigmas)
    fun l/sigma = (l, sigma)
    fun sigma1-->sigma2 = ArrowS(sigma1, sigma2)
    fun lazy(sigma) = LazyS(sigma)
    fun forall alphaks sigma = UnivS(alphaks, sigma)
    fun exist alphaks sigma = ExistS(alphaks, sigma)
    val unit = StructS([])

    infix 9 ^:
    val Val = ValE
    fun fold(alpha) = FoldE(alpha)
    fun unfold(alpha) = UnfoldE(alpha)
    fun (e1^:taus):^e2 = ConE(e1, taus, e2)
    val :^ = ()
    fun ##n = IntE(n)
    fun e1+e2 = PlusE(e1, e2)

    infix 9 ^ ^! ^? @
    infixr 2 &
    infix 0 ==
    fun $x = VarM(x)
    fun tm[e] = TermM(e)
    fun ty[tau] = TypM(tau)
    fun struc(lms) = StructM(lms)
    fun l==m = (l, m)
    fun m@l = DotM(m, l)
    fun \(x,sigma) m = LambdaM(x, sigma, m)
    fun m1^m2 = ApplyM(m1, m2)
    fun letm x m1 m2 = LetM(x, m1, m2)
    fun m1 & m2 = LetM(Var.fresh(), m1, m2)
    fun /\!alphaks m = GenDownM(alphaks, m)
    fun /\?alphaks m = GenUpM(alphaks, m)
    fun m^!taus = InstDownM(m, taus)
    fun m^?alphas = InstUpM(m, alphas)
    fun newt alphaks m = NewTypM(alphaks, m)
    datatype equi_iso = :== | :~~
    fun def alpha:==tau sigma m = DefEquiM(alpha, tau, m, sigma, Map.map[], Map.map[], ref NONE)
      | def alpha:~~tau sigma m = DefIsoM(alpha, tau, m, sigma)
    fun new x sigma m = NewTermM(x, sigma, m)
    fun m1:=m2 = AssignM(m1, m2)
    fun **m = ForceM(m)

    infixr 1 --
    fun f -- x = f x

    (* simple examples *)

    val s = forall["c"/T--->T--->T] -- exist["a"/T,"b"/T] -- sstruc["x"/stm[`"c"^^[`"a",int]], "t"/sty[`"b"/T]]
    val _ = print(ILPrint.strS s ++ "\n")

    val f = \("X"/stm[int]) -- struc["result"==tm[Val($"X") + Val($"X")]]
    val m = ApplyM(VarM"F", TermM(IntE 6))
    val m = $"F"^tm[##6]
    val delta = Map.map[] : typ_context
    val gamma = Map.map[] : modl_context
    val (sf, rho) = ILTyping.checkM (delta, gamma) f
    val _ = print("F : " ++ ILPrint.strS sf ++ "\n")
    val gamma' = Map.map[("F", sf)]
    val (sm, rho) = ILTyping.checkM (delta, gamma') m
    val _ = print("M : " ++ ILPrint.strS sm ++ "\n")

    val fm = (\("F"/sf) m)^f
    val (w, delta, omega) = ILEvaluation.run(ILEvaluation.emptyContext, fm)
    val _ = print(ILPrint.strW omega w ++ "\n")
    val (w, delta, omega) = ILCheckedEvaluation.run(ILEvaluation.emptyContext, fm) handle e as ILCheckedEvaluation.Bug s => (print(s ++ "\n"); raise e)
    val _ = print(ILPrint.strW omega w ++ "\n")

    val m1 =
        newt ["a" / T] --
        newt ["b" / T] --
        def "b" :== (`"a") (forall["a"/T] -- stm[int]-->(stm[int]-->unit)-->unit) --
        def "a" :== int (forall["a"/T] -- stm[int]-->(stm[int]-->unit)-->unit) --
        /\!["a'" / T] --
        \("X" / stm[`"b"]) --
        \("F" / stm[`"a"]-->unit) --
        $"F"^ $"X"

    val m1 =
        newt ["a" / T] --
        def "a" :== int (sstruc[]) --
        struc[]
    val (sm, rho) = ILTyping.checkM (Map.map[], Map.map[]) m1

    val _ = print("M1 : " ++ ILPrint.strS sm ++ "\n")

    (* the running example from RMC paper *)

    fun pair(m1, m2) = struc["1"==m1, "2"==m2]
    fun fst m = m@"1"
    fun snd m = m@"2"
    fun spair(sigma1, sigma2) = sstruc["1"/sigma1, "2"/sigma2]

    val rmc_f = \("X"/stm[`"a"]) -- letm "p" ( **($"g")^tm[Val($"X") + ##3] ) -- pair(fst($"p"), tm[Val(snd($"p")) + ##5])
    val rmc_g = \("X"/stm[`"a"]) -- pair(tm[##0], tm[Val($"X")])
    val rmc_sigma_f = stm[`"a"] --> spair(stm[`"b"], stm[`"a"])
    val rmc_sigma_g = stm[`"a"] --> spair(stm[`"b"], stm[`"a"])
    val rmc_sigma_a = sstruc["u"/sty[`"b"/T], "t"/sty[`"a"/T], "f"/lazy rmc_sigma_f, "h"/lazy (stm[`"a"] --> stm[int]), "x"/lazy (stm[`"a"])]
    val rmc_sigma_b = sstruc["t"/sty[`"a"/T], "u"/sty[`"b"/T], "g"/lazy rmc_sigma_g]
    val rmc =
        newt ["a" / T] --
        newt ["b" / T] --
        new "f" rmc_sigma_f --
        new "g" rmc_sigma_g --
        new "h" (stm[`"a"] --> stm[int]) --
        new "x" (stm[`"a"]) --
        letm "AB" (struc[
            "A" ==
                def "a" :== int (rmc_sigma_a) --
                $"f" := rmc_f &
                $"h" := (\("x"/stm[int]) -- $"x") &
                $"x" := tm[##666] &
                struc["u"==ty[`"b"], "t"==ty[int], "f"== $"f", "h"== $"h", "x"== $"x"],
            "B" ==
                def "b" :== int (rmc_sigma_b) --
                $"g" := rmc_g &
                struc["t"==ty[`"a"], "u"==ty[int], "g"== $"g"]
        ]) --
        **($"AB"@"A"@"h") ^ (( **($"AB"@"A"@"f") ^ **($"AB"@"A"@"x"))@"2")

    val (srmc, rho) = ILTyping.checkM (Map.map[], Map.map[]) rmc
    val _ = print("RMC : " ++ ILPrint.strS srmc ++ "\n")
    val (w, delta, omega) = ILEvaluation.run(ILEvaluation.emptyContext, rmc)
    val _ = print(ILPrint.strW omega w ++ "\n")
    val (w, delta, omega) = ILCheckedEvaluation.run(ILEvaluation.emptyContext, rmc) handle e as ILCheckedEvaluation.Bug s => (print(s ++ "\n"); raise e)
    val _ = print(ILPrint.strW omega w ++ "\n")
end
