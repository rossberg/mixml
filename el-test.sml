(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

structure ELTest =
struct
    (*structure First = ILTest*)

    val _ = (ELTrace.on := true; ELTrace.assertOn := true)
    val run = fn c => valOf o ELRun.run c
    val c0 = ELRun.initialContext

    val s1 = "{val n = 10, val m = n+3, do print m}"
    val c1 = run c0 s1

    val s2 = "unit U2 = {type t} with {type t}"
    val c2 = run c0 s2

    val s3 = "unit U3 = {type t} with {type t = int}"
    val c3 = run c0 s3

    val s4 = "unit U4 = {type t = int} with {type t}"
    val c4 = run c0 s4

    val s5 = "unit U5 = {type t = int} with {type t = int}"
    val c5 = run c0 s5

    val s6 = "unit U6 = link X = {type t} with {type t = X.t}" (* ill-typed! *)
    (*val c6 = run c0 s6*)

    val s7 = "unit U7 = link X = {type t = int} with {type t = X.t}"
    val c7 = run c0 s7

    val rmc1 =
        "unit RMC1 = \
        \  link X = {module A = {type t}, module B = {type u}} with \
        \  { \
        \    module A = {type t = int type u = X.B.u} \
        \    module B = {type u = int type t = X.A.t} \
        \  } "
    val c_rmc1 = run c0 rmc1

    val rmc2 =
        "unit RMC2 = \
        \  link X = {module A = {type t}, module B = {type u}} with \
        \  { \
        \    module A = {type t = int type u = X.B.u} :> {type t, type u = X.B.u} \
        \    module B = {type u = int type t = X.A.t} :> {type u, type t = X.A.t} \
        \  } "
    val c_rmc2 = run c0 rmc2

    val rmc3 =
        "unit RMC3 = \
        \  link X = \
        \  { \
        \    module A = {type t} \
        \    module B = {type u, type t, val g : t -> (u, t)} \
        \  } \
         \  with \
        \  { \
        \    module A = \
        \    { \
        \      type t = int \
        \      type u = X.B.u \
        \      val x = 666 \
        \      val f(x : t) = let p = X.B.g(x + 3) in (p#1, p#2 + 5) \
        \    } :> {type t, type u = X.B.u, val x : t, val f : t -> (u, t)} \
        \    module B = \
        \    { \
        \      type u = int \
        \      type t = X.A.t \
        \      val y = A.x (*(A.f A.x)#2*) \
        \      val g(x : t) = (0, x) \
        \    } :> {type u, type t = X.A.t, val y : t, val g : t -> (u, t)} \
        \  } "
    val c_rmc3 = run c0 rmc3

    val rmc3' = "link R = !RMC3 with {do print (R.A.f R.B.y); print \"\\n\"}"
    val c_rmc3' = run c_rmc3 rmc3'

    val rmc4 =
        "unit RMC4 = \
        \  link X = \
        \  { \
        \    module A = {type t} \
        \    module B = {type u, type t, val g : t -> (u, t)} \
        \  } \
        \  with \
        \  { \
        \    module A = \
        \    {type t, type u = X.B.u, val x : t, val f : t -> (u, t)} seals \
        \    { \
        \      type t = int \
        \      type u = X.B.u \
        \      val x = 666 \
        \      val f(x : t) = let p = X.B.g(x + 3) in (p#1, p#2 + 5) \
        \    } \
        \    module B = \
        \    {type u, type t = X.A.t, val y : t, val g : t -> (u, t)} seals \
        \    { \
        \      type u = int \
        \      type t = X.A.t \
        \      val y = A.x (*(A.f A.x)#2*) \
        \      val g(x : t) = (0, x) \
        \    } \
        \  } "
    val c_rmc4 = run c0 rmc4

    val rmc4' = "link R = !RMC4 with {do print (R.A.f R.B.y); print \"\\n\"}"
    val c_rmc4' = run c_rmc4 rmc4'

    val _ = (ELTrace.on := false; ELTrace.assertOn := false)
end
