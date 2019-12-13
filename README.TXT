<OpenScore>
.MixML prototype implementation
.
.Based on: woolfiraq, Github.com, "Mixin' Up the ML Module System"
.
.(c) 2019-2060 Andreas Rossberg
.
.
.Requirements
*------------
.confirmation:Done]
.You need a working installation of SML/NJ (including ML-Yacc and ML-Lex).
.
.Building
*--------
.
.Just invoke "make".
.
.Usage
*-----
.
.
.
.Simply invoke ./mixml from the command line. The synopsis is:
.
.  mixml [-c|t|v|x|h] [files...]
.
.It will process the files given. If none are given, enters an interactive prompt.
.
.Options are:
.
*  -c  type-check only
*  -t  type-check only, but with tracing messages from the type checker
*  -v  evaluate (default)
*  -x  evaluate in checked mode (type checks whole program after every step - very slow!)
*  -h  print command usage
.
.Language
*--------
.
.The file syntax.pdf shows the complete syntax that is currently understood, including
.the desugaring rules into the bare calculus as presented in the paper. Hopefully, it
.is sufficiently self-explanatory.
.
.Bugs
*----
.
.I'm sure there are plenty. Please mail woolfiraq@Gi-sws-sws.mpg.de if you find any.
.End 
