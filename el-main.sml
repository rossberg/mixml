(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature MAIN =
sig
    val main : string * string list -> OS.Process.status
end

structure Main : MAIN =
struct
    fun prompt p =
        (
            print p;
            case TextIO.inputLine TextIO.stdIn of
                NONE => (print "\n"; OS.Process.exit OS.Process.success)
              | SOME line =>
                if String.size line > 1 andalso String.sub(line, String.size line - 2) = #";"
                then String.substring(line, 0, String.size line - 2) ^ "\n"
                else line ^ prompt "  "
        )

    val date = Date.toString(Date.fromTimeLocal(Time.now()))

    fun interactive(process, context) =
        (
            print("MixML - built " ^ date ^ "\n");
            interactive'(process, context)
        )
    and interactive'(process, context) =
        case process context (prompt "- ") of
            SOME context' => interactive'(process, context')
          | NONE => interactive'(process, context)

    fun batch (process, context) [] = OS.Process.exit OS.Process.success
      | batch (process, context) (name::files) =
        let
            val file = TextIO.openIn name
            val source = TextIO.inputAll file
        in
            TextIO.closeIn file;
            print("[Processing " ^ name ^ "...]\n");
            case process context source of
                SOME context' => batch (process, context') files
              | NONE => OS.Process.exit OS.Process.failure
        end
        handle IO.Io _ =>
        (
            TextIO.output(TextIO.stdOut, "error opening file " ^ name ^ "\n");
            OS.Process.exit OS.Process.failure
        )

    fun usage() =
        (
            TextIO.output(TextIO.stdErr,
                "Usage:  mixml [-c|t|v|x|h] [files...]\n\
                \\n\
                \Options:\n\
                \  -c  type-check only\n\
                \  -t  type-check only with tracing\n\
                \  -v  evaluate (default)\n\
                \  -x  evaluate in checked mode\n\
                \  -h  print usage\n"
            );
            OS.Process.exit OS.Process.success
        )

    val check = (ELRun.check, ELElaboration.emptyContext)
    val run = (ELRun.run, ELRun.initialContext)

    fun main(_, args) = main'(args, true)
    and main'("-c"::files, running) =
            (ELRun.showing := true; main'(files, false))
      | main'("-t"::files, running) =
            (ELRun.showing := true; ELTrace.on := true; ELTrace.assertOn := true; main'(files, false))
      | main'("-v"::files, running) = main'(files, true)
      | main'("-x"::files, running) =
            (ELTrace.assertOn := true; ELRun.checked := true; main'(files, true))
      | main'("-h"::files, _) = usage()
      | main'([], running) =
            (ELRun.showing := true; if running then interactive run else interactive check)
      | main'(files, running) =
        if List.exists (fn s => size s > 0 andalso String.sub(s, 0) = #"-") files then usage()
        else (if running then batch run else batch check) files
end
