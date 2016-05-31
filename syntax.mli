type index =
  | IdVar of int * int
  | IdInt of int
  | IdAdd of index * index
  | IdSub of index * index
  | IdMul of index * index
  | IdDiv of index * index

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
  | TyBool
  | TyUnit
  | TyProduct of ty * ty
  | TyArrow of ty * ty
  | TyDepUni of string * sort * ty
  | TyDepExi of string * sort * ty

type pat =
  | PtWild
  | PtVar of string
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
  | TmCase of term * (pat * int * term) list
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLet of string * term * term
  | TmFix of string * ty * term
  | TmDepAbs of string * sort * term
  | TmDepApp of term * index
  | TmDepPair of index * term * ty
  | TmDepLet of string * string * term * term

type formula =
  | FmVar of int
  | FmIntConst of int
  | FmAdd of formula * formula
  | FmTrue
  | FmFalse
  | FmAnd of formula list
  | FmOr of formula list
  | FmNot of formula
  | FmLe of formula * formula
  | FmUni of (int list) * formula
  | FmExi of (int list) * formula
  | FmEq of formula * formula
  | FmImply of formula * formula

type binding =
  | NameBind
  | BdType of ty
  | BdSort of sort
  | BdProp of prop

type context
val empty_ctx : context
val ctx_length : context -> int
val add_binding : context -> string -> binding -> context
val get_binding : context -> int -> binding
val get_type_from_context : context -> int -> ty
val name2index : context -> string -> int
val add_name : context -> string -> context

val prelude_ctx : context

val shift_type_above : int -> int -> ty -> ty

val shift_term : int -> term -> term
val shift_type : int -> ty -> ty
val shift_sort : int -> sort -> sort
val shift_prop : int -> prop -> prop
val shift_index : int -> index -> index
val shift_formula : int -> formula -> formula

val subst_term_in_term : int -> term -> term -> term
val subst_term_in_term_top : term -> term -> term
val subst_index_in_index : int -> index -> index -> index
val subst_index_in_index_top : index -> index -> index
val subst_index_in_prop : int -> index -> prop -> prop
val subst_index_in_prop_top : index -> prop -> prop
val subst_index_in_sort : int -> index -> sort -> sort
val subst_index_in_sort_top : index -> sort -> sort
val subst_index_in_type : int -> index -> ty -> ty
val subst_index_in_type_top : index -> ty -> ty
val subst_index_in_term : int -> index -> term -> term
val subst_index_in_term_top : index -> term -> term

val printtm : term -> unit
val printty : ty -> unit
val printfm : formula -> unit
val printid : index -> unit

val print_raw : term -> unit
val print_raw_index : index -> unit
val print_raw_sort : sort -> unit
val print_raw_type : ty -> unit
