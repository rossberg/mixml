(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

structure EL =
struct
    type pos = int * int
    type region = {l : pos, r : pos}
    type 'a annotated = {it : 'a, region : region}

    type lab = string
    type var = string
    type typvar = string
    type labs = lab list
    type path = var * labs

    datatype kind' =
        StarK
      | ArrowK of int
    withtype kind = kind' annotated

    datatype typ' =
        ModT of modl
      | LambdaT of typvar list * typ
      | ApplyT of typ * typ list
      | IntT
      | StringT
      | TupleT of typ list
      | VariantT of typ list
      | ArrowT of typ * typ
      | UnivT of typvar list * typ

    and exp' =
        ModE of modl
      | IntE of int
      | StringE of string
      | PlusE of exp * exp
      | MinusE of exp * exp
      | EqualE of exp * exp
      | LessE of exp * exp
      | CatE of exp * exp
      | TupleE of exp list
      | ProjE of exp * int
      | InjE of exp * int * typ
      | CaseE of exp * (var * exp) list
      | LambdaE of var * typ * exp
      | ApplyE of exp * exp
      | GenE of typvar list * exp
      | InstE of exp * typ list
      | FoldE of modl * typ list * exp
      | UnfoldE of modl * typ list * exp
      | LetE of var * modl * exp
      | PrintE of exp

    and modl' =
        VarM of var
      | EmptyM
      | ValM of exp
      | AbsValM of typ
      | TypM of typ
      | AbsTypM of kind
      | DatTypM of typ
      | AbsDatTypM of typ
      | UnitM of modl
      | AbsUnitM of sign
      | NewM of modl
      | StructM of lab * modl
      | DotM of modl * lab
      | LinkM of var * modl * modl
      | OLinkM of var * modl * modl
      | SealM of modl * sign

    and sign' =
        ImportS of modl * labs list
      | ExportS of modl * labs list

    withtype typ = typ' annotated
    and exp = exp' annotated
    and modl = modl' annotated
    and sign = sign' annotated

    type prog = modl

    exception Error of region * string
end
