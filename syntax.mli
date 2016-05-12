type index =
  | IdVar of int * int
  | IdInt of int
  | IdAdd of index * index

type prop =
  | PrTrue
  | PrFalse
  | PrNeg of prop
  | PrAnd of prop * prop
  | PrOr of prop * prop
  | PrLe of index * index

type sort =
  | SrInt
  | SrSubset of string * sort * prop

type ty =
  | TyInt of index
  | TyBool of index
  | TyUnit
  | TyProduct of ty * ty
  | TyArrow of ty * ty
  | TyDepUni of string * sort * ty
  | TyDepExi of string * sort * ty
  | TyDepApp of ty * index

type pat =
  | PtWild
  | PtVar of int * int
  | PtInt of int
  | PtBool of bool
  | PtUnit
  | PtPair of pat * pat

type term =
  | TmVar of int * int
  | TmInt of int
  | TmBool of bool
  | TmUnit
  | TmPair of term * term
  | TmIf of term * term * term
  | TmCase of term * (pat * term) list
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLet of string * term * term
  | TmFix of string * ty * term
  | TmDepAbs of string * sort * term
  | TmDepApp of term * index
  | TmDepPair of index * sort * term
  | TmDepLet of string * string * term * term

type binding =
  | BdType of string * ty
  | BdSort of string * sort
  | BdProp of prop

type context
val empty_ctx : context
val ctx_length : context -> int
val add_binding : context -> binding -> context

val shift_term : int -> term -> term
val shift_type : int -> ty -> ty
val shift_index : int -> index -> index
val shift_sort : int -> sort -> sort
