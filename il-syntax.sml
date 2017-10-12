(*
 * MixML prototype implementation
 *
 * Based on: Derek Dreyer, Andreas Rossberg, "Mixin' Up the ML Module System"
 *
 * (c) 2007-2008 Andreas Rossberg
 *)

structure IL =
struct
    type lab = Var.var
    type var = Var.var
    type typvar = Var.var

    datatype kind =
        StarK
      | ArrowK of int

    datatype typ =
        VarT of typvar
      | IntT
      | StringT
      | TupleT of typ list
      | VariantT of typ list
      | ArrowT of sign * typ
      | UnivT of typvar list * typ
      | PureT of typvar list * typ * typ
      | LambdaT of typvar list * typ
      | ApplyT of typ * typ list

    and sign =
        TypS of typ * kind
      | TermS of typ
      | StructS of (lab * sign) list
      | ArrowS of sign * sign
      | LazyS of sign
      | UnivS of (typvar * kind) list * sign
      | ExistS of (typvar * kind) list * sign

    withtype typ_subst = typ Map.map

    datatype effect =
        DownE of typvar list
      | EquiE of typvar * typ
      | IsoE of typvar * typ

    type 'a context = 'a Map.map
    datatype typ_entry =
        Colon of kind
      | Up of kind
      | Down of kind
      | Equi of typ * kind
      | Iso of typ * kind
    type typ_context = typ_entry context
    type modl_context = sign context

    datatype term =
        ValE of modl
      | IntE of int
      | StringE of string
      | PlusE of term * term
      | MinusE of term * term
      | EqualE of term * term
      | LessE of term * term
      | CatE of term * term
      | TupleE of term list
      | DotE of term * int
      | VariantE of term * int * typ
      | CaseE of term * (var * term) list
      | LambdaE of var * sign * term
      | ApplyE of term * modl
      | GenE of typvar list * term
      | InstE of term * typ list
      | FoldE of typvar
      | UnfoldE of typvar
      | ConE of term * typ list * term
      | PrintE of term

    and modl =
        VarM of var
      | TypM of typ
      | TermM of term
      | StructM of (lab * modl) list
      | DotM of modl * lab
      | LambdaM of var * sign * modl
      | ApplyM of modl * modl
      | LetM of var * modl * modl
      | GenDownM of (typvar * kind) list * modl
      | InstDownM of modl * typ list
      | GenUpM of (typvar * kind) list * modl
      | InstUpM of modl * typvar list
      | NewTypM of (typvar * kind) list * modl
      | DefEquiM of typvar * typ * modl * sign * typ_subst * modl_subst *
            (typ_context * modl_context) option ref
      | DefIsoM of typvar * typ * modl * sign
      | NewTermM of var * sign * modl
      | AssignM of modl * modl
      | ForceM of modl

    withtype modl_subst = modl Map.map
end
