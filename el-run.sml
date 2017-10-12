(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature EL_RUN =
sig
    type context
    val initialContext : context
    val showing : bool ref
    val checked : bool ref
    val compile : ELElaboration.context -> string -> EL.prog * ELAux.funct * IL.modl
    val check : ELElaboration.context -> string -> ELElaboration.context option
    val run : context -> string -> context option
end

structure ELRun :> EL_RUN =
struct
    open VarOps infix \ |-> |=> ++
    open ILOps
    open ELTrace
    open PrettyPrint infix ^^ ^/^

    val showing = ref false
    val checked = ref false

    type context = ELElaboration.context * ILEvaluation.context * ILMachine.modval
    val initialContext = (ELElaboration.emptyContext, ILEvaluation.emptyContext, ILMachine.StructW[])

    fun catch f =
        (traceReset(); SOME(f()))
        handle EL.Error({l = (l1, c1), r = (l2, c2)}, message) =>
        (
            TextIO.output(TextIO.stdErr,
                Int.toString l1 ^ "." ^ Int.toString c1 ^ "-" ^
                Int.toString l2 ^ "." ^ Int.toString c2 ^ ": " ^ message ^ "\n"
            );
            NONE
        )
        | ILTyping.Error message =>
            (TextIO.output(TextIO.stdErr, "Internal type error: " ^ message ^ "\n"); NONE)
        | ILEvaluation.Stuck s =>
            (TextIO.output(TextIO.stdErr, "Evaluation is stuck\n" ^ ILPrint.strSt s); NONE)
        | ILEvaluation.Black x =>
            (TextIO.output(TextIO.stdErr, "Black hole encountered at " ^ x ^ "\n"); NONE)
        | Fail s =>
            (TextIO.output(TextIO.stdErr, "Internal failure: " ^ s ^ "\n"); NONE)
        | IO.Io{name, function, cause} =>
            (TextIO.output(TextIO.stdErr, "I/O failure in " ^ name ^ ", " ^ function ^ ": " ^ exnName cause ^ "\n"); NONE)
        | exn =>
            (TextIO.output(TextIO.stdErr, "Internal exception: " ^ exnName exn ^ "\n"); NONE)

    fun compile cStat source =
        let
            val _ = (trace "[Parsing...]"; traceSrc "source" source)
            val prog = ELParser.parse source
            val _ = trace "[Elaborating...]"
            val (phi as (_, betaks, _), lsigmas, f) =
                case ELElaboration.elab cStat prog of
                    (phi as ([], betaks, ELAux.Struct(lsigmas)), f) => (phi, lsigmas, f)
                  | _ => raise Fail "compile: elab"
            val _ = trace "[Finished.]"
        in
            if not(!showing) then () else
                PrettyPrint.output(TextIO.stdOut,
                    ELPretty.ppD(map(betaks)) ^/^ ELPretty.ppG(map(lsigmas)) ^^ break,
                    80
                );
            (prog, phi, f)
        end

    fun check (cStat as (delta, gamma)) source =
        catch (fn() =>
        let
            val (betaks, lsigmas) =
                case compile cStat source of
                    (_, ([], betaks, ELAux.Struct(lsigmas)), _) => (betaks, lsigmas)
                  | _ => raise Fail "check: compile"
        in
            (delta ++ map(betaks), gamma ++ map(lsigmas))
        end)

    fun run (c as (cStat as (delta, gamma), cDyn as (deltaDyn, gammaDyn, omega), w)) source =
        catch (fn() =>
        let
            val _ = (trace "[Parsing...]"; traceSrc "source" source)
            val prog = ELParser.parse source
            val _ = trace "[Elaborating...]"
            val (betaks, lsigmas, f) =
                case ELElaboration.elab cStat prog of
                    (([], betaks, ELAux.Struct(lsigmas)), f) => (betaks, lsigmas, f)
                  | _ => raise Fail "run: elab"
            val delta' = map(betaks)
            val gamma' = map(lsigmas)
            val cStat' = (delta ++ delta', gamma ++ gamma')
            val () = if not(!showing) then () else
                PrettyPrint.output(TextIO.stdOut,
                    ELPretty.ppD(map(betaks)) ^/^ ELPretty.ppG(map(lsigmas)) ^^ break,
                    80
                )
            val deltaDyn = deltaDyn ++ mapRan IL.Up delta'
            val cDyn = (deltaDyn, gammaDyn, omega)
            val m' =
                IL.LetM("_old", ILMachine.fromModval w,
                    ILOps.letM(List.map (fn x => (x, IL.DotM(IL.VarM("_old"), x))) (items(dom(gamma))),
                        IL.LetM("_run", ELAux.create(ELAux.Struct(lsigmas)),
                            ILOps.seqM[
                                IL.ApplyM(
                                    IL.InstUpM(IL.InstDownM(f, []), List.map #1 betaks),
                                    IL.VarM("_run")
                                ),
                                IL.StructM(
                                    List.map (fn x => (x, IL.VarM(x))) (items(dom(gamma) \ dom(gamma'))) @
                                    List.map (fn x => (x, IL.DotM(IL.VarM("_run"), x))) (items(dom(gamma')))
                                )
                            ]
                        )
                    )
                )
            val () = if not(!checked) then () else
                (
                    trace "[Checking...]";
                    ignore(ILTyping.checkM (deltaDyn ++ mapRan IL.Colon delta, gammaDyn) m')
                )
            val _ = trace "[Running...]"
            val (cDyn', w') = (if !checked then ILCheckedEvaluation.run else ILEvaluation.run)(cDyn, m')
            val _ = trace "[Finished.]"
        in
            (*trace(ILPrint.strO omega);*)
            (cStat', cDyn', w')
        end)
end
