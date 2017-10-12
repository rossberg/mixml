(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature EL_OPS =
sig
    type path_subst = EL.path Map.map

    val fresh : unit -> EL.var
    val renameX : EL.var -> EL.var * path_subst

    val substE : path_subst -> EL.exp -> EL.exp
    val substT : path_subst -> EL.typ -> EL.typ
    val substM : path_subst -> EL.modl -> EL.modl
    val substS : path_subst -> EL.sign -> EL.sign
end

structure ELOps : EL_OPS =
struct
    open VarOps infix |-> ++
    open EL
    open ILOps

    type path_subst = EL.path Map.map

    fun renameX x =
        let
            val x' = rename x
        in
            (x', map[x |-> (x', [])])
        end

    fun substT gam {it, region} = {it = substT' gam it, region = region}
    and substT' gam =
        fn ModT(modl) => ModT(substM gam modl)
         | IntT => IntT
         | StringT => StringT
         | TupleT(typs) => TupleT(List.map (substT gam) typs)
         | VariantT(typs) => VariantT(List.map (substT gam) typs)
         | ArrowT(typ1, typ2) => ArrowT(substT gam typ1, substT gam typ2)
         | UnivT(alphas, typ) => UnivT(alphas, substT gam typ)
         | LambdaT(alphas, typ) => LambdaT(alphas, substT gam typ)
         | ApplyT(typ, typs) => ApplyT(substT gam typ, List.map (substT gam) typs)

    and substE gam {it, region} = {it = substE' gam it, region = region}
    and substE' gam =
        fn ModE(modl) => ModE(substM gam modl)
         | FoldE(modl, typs, exp) => FoldE(substM gam modl, List.map (substT gam) typs, substE gam exp)
         | UnfoldE(modl, typs, exp) => UnfoldE(substM gam modl, List.map (substT gam) typs, substE gam exp)
         | IntE(i) => IntE(i)
         | StringE(s) => StringE(s)
         | PlusE(exp1, exp2) => PlusE(substE gam exp1, substE gam exp2)
         | MinusE(exp1, exp2) => MinusE(substE gam exp1, substE gam exp2)
         | EqualE(exp1, exp2) => EqualE(substE gam exp1, substE gam exp2)
         | LessE(exp1, exp2) => LessE(substE gam exp1, substE gam exp2)
         | CatE(exp1, exp2) => CatE(substE gam exp1, substE gam exp2)
         | TupleE(exps) => TupleE(List.map (substE gam) exps)
         | ProjE(exp, i) => ProjE(substE gam exp, i)
         | InjE(exp, i, typ) => InjE(substE gam exp, i, substT gam typ)
         | CaseE(exp, xexps) =>
            let
                val xexps' =
                    List.map (fn(x, exp) =>
                              let val (x', gam') = renameX x in (x', substE (gam ++ gam') exp) end
                             ) xexps
            in
                CaseE(substE gam exp, xexps')
            end
         | LambdaE(x, typ, exp) =>
            let
                val (x', gam') = renameX x
            in
                LambdaE(x', substT gam typ, substE (gam ++ gam') exp)
            end
         | ApplyE(exp1, exp2) => ApplyE(substE gam exp1, substE gam exp2)
         | GenE(alphas, exp) => GenE(alphas, substE gam exp)
         | InstE(exp, typs) => InstE(substE gam exp, List.map (substT gam) typs)
         | LetE(x, modl, exp) =>
            let
                val (x', gam') = renameX x
            in
                LetE(x', substM gam modl, substE (gam ++ gam') exp)
            end
         | PrintE(exp) => PrintE(substE gam exp)

    and substM gam {it, region} = {it = substM' gam region it, region = region}
    and substM' gam region =
        fn VarM(x) =>
            let
                val (x', ls) = lookup gam x handle Lookup => (x, [])
            in
                List.foldl (fn(l, modl) => DotM({it = modl, region = region}, l)) (VarM(x')) ls
            end
         | EmptyM => EmptyM
         | ValM(exp) => ValM(substE gam exp)
         | AbsValM(typ) => AbsValM(substT gam typ)
         | TypM(typ) => TypM(substT gam typ)
         | AbsTypM(kind) => AbsTypM(kind)
         | DatTypM(typ) => DatTypM(substT gam typ)
         | AbsDatTypM(typ) => AbsDatTypM(substT gam typ)
         | UnitM(modl) => UnitM(substM gam modl)
         | AbsUnitM(sign) => AbsUnitM(substS gam sign)
         | NewM(modl) => NewM(substM gam modl)
         | StructM(l, modl) => StructM(l, substM gam modl)
         | DotM(modl, l) => DotM(substM gam modl, l)
         | LinkM(x, modl1, modl2) =>
            let
                val (x', gam') = renameX x
            in
                LinkM(x', substM gam modl1, substM (gam ++ gam') modl2)
            end
         | OLinkM(x, modl1, modl2) =>
            let
                val (x', gam') = renameX x
            in
                OLinkM(x', substM gam modl1, substM (gam ++ gam') modl2)
            end
         | SealM(modl, sign) => SealM(substM gam modl, substS gam sign)
(*
         | LetM(x, modl1, modl2) =>
            let
                val (x', gam') = renameX x
            in
                LetM(x', substM gam modl1, substM (gam ++ gam') modl2)
            end
*)

    and substS gam {it, region} = {it = substS' gam it, region = region}
    and substS' gam =
        fn ImportS(modl, lss) => ImportS(substM gam modl, lss)
         | ExportS(modl, lss) => ExportS(substM gam modl, lss)
end
