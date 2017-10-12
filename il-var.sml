(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

signature VAR =
sig
    type var = string

    val fresh : unit -> var
    val rename : var -> var
    val compare : var * var -> order
end

structure Var : VAR =
struct
    type var = string

    val compare = String.compare

    val n = ref 1
    fun fresh() = "%" ^ Int.toString(!n) before n := !n + 1

    structure Map = RedBlackMapFn(open String type ord_key = string)
    val table = ref(Map.empty : int Map.map)

    fun rename x =
        let
            val prefix =
                case String.fields (fn c => c = #"%") x of
                    [id, n] => id
                  | _ => x
            val n = Option.getOpt(Map.find(!table, prefix), 0) + 1
        in
            table := Map.insert(!table, prefix, n);
            prefix ^ "%" ^ Int.toString n
        end
end

signature SET =
sig
    type var = Var.var
    type set

    val set : var list -> set
    val \/ : set * set -> set
    val /\ : set * set -> set
    val \ : set * set -> set
    val isEmpty : set -> bool
    val size : set -> int
    val member : set -> var -> bool
    val equal : set * set -> bool
    val subset : set * set -> bool
    val filter : (var -> bool) -> set -> set
    val items : set -> var list
    val choose : set -> var
end

structure Set :> SET =
struct
    structure Set = RedBlackSetFn(open Var type ord_key = var)
    type var = Var.var
    type set = Set.set

    infix \/
    val set = Set.fromList
    val op\/ = Set.union
    val op/\ = Set.intersection
    val op\ = Set.difference
    val isEmpty = Set.isEmpty
    val size = Set.numItems
    fun member s x = Set.member(s, x)
    val equal = Set.equal
    val subset = Set.isSubset
    val filter = Set.filter
    val items = Set.listItems
    fun choose s = case Set.find (fn _ => true) s of SOME x => x | NONE => raise Empty
end

signature MAP =
sig
    type var = Var.var
    type 'a map

    exception Lookup
    exception Collision

    val map : (var * 'a) list -> 'a map
    val |-> : var * 'a -> var * 'a
    val |=> : var list * 'a list -> (var * 'a) list
    val |=>* : var list * 'a -> (var * 'a) list
    val ++ : 'a map * 'a map -> 'a map
    val +|+ : 'a map * 'a map -> 'a map
    val -- : 'a map * Set.set -> 'a map
    val || : 'a map * Set.set -> 'a map
    val defined : 'a map -> var -> bool
    val lookup : 'a map -> var -> 'a
    val dom : 'a map -> Set.set
    val filter : (var * 'a -> bool) -> 'a map -> 'a map
    val entries : 'a map -> (var * 'a) list
    val mapRan : ('a -> 'b) -> 'a map -> 'b map
    val mapRani : (var * 'a -> 'b) -> 'a map -> 'b map
    val isId : 'a map -> bool
end

structure Map :> MAP =
struct
    structure Map = RedBlackMapFn(open Var type ord_key = var)
    type var = Var.var
    type 'a map = 'a Map.map

    exception Lookup
    exception Collision

    infix |-> |=> |=>* ++ +|+ -- ||

    fun map xas = List.foldl Map.insert' Map.empty xas
    fun x |-> a = (x, a)
    val op|=> = ListPair.zipEq
    fun xs |=>* a = List.map (fn x => (x, a)) xs
    fun m1 ++ m2 = Map.unionWith #2 (m1, m2)
    fun m1 +|+ m2 = Map.unionWith (fn _ => raise Collision) (m1, m2)
    fun m -- s = Map.filteri (not o Set.member s o #1) m
    fun m || s = Map.filteri (Set.member s o #1) m
    fun defined m x = Map.inDomain(m, x)
    fun lookup m x = case Map.find(m, x) of SOME a => a | NONE => raise Lookup
    fun dom m = Set.set(Map.listKeys m)
    val filter = Map.filteri
    val entries = Map.listItemsi
    val mapRan = Map.map
    val mapRani = Map.mapi
    val isId = Map.isEmpty
end

structure VarOps =
struct
    open Var
    open Set
    open Map
end
