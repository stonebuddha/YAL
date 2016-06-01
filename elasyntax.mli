type ela_binop =
  | ElaBnPlus
  | ElaBnMinus
  | ElaBnTimes
  | ElaBnDiv
  | ElaBnLeq
  | ElaBnLt
  | ElaBnGeq
  | ElaBnGt
  | ElaBnNeq
  | ElaBnEq
  | ElaBnAnd
  | ElaBnOr

type ela_unop =
  | ElaUnNot

type ela_index =
  | ElaIdId of string
  | ElaIdVar of int * int
  | ElaIdInt of int
  | ElaIdBool of bool
  | ElaIdBinop of ela_binop * ela_index * ela_index
  | ElaIdUnop of ela_unop * ela_index

type ela_sort =
  | ElaSrVar of int * int
  | ElaSrInt
  | ElaSrBool
  | ElaSrSubset of string * ela_sort * ela_index

type ela_type =
  | ElaTyVar of int * int
  | ElaTyInt of ela_index
  | ElaTyBool of ela_index
  | ElaTyUnit
  | ElaTyFloat
  | ElaTyVector of ela_index
  | ElaTyMatrix of ela_index * ela_index
  | ElaTyProduct of ela_type * ela_type
  | ElaTyArrow of ela_type * ela_type
  | ElaTyDepUni of string * ela_sort * ela_type
  | ElaTyDepExi of string * ela_sort * ela_type

type ela_expr =
  | ElaExVar of int * int
  | ElaExInt of int
  | ElaExBool of bool
  | ElaExUnit
  | ElaExFloat of float
  | ElaExPair of ela_expr * ela_expr
  | ElaExIf of ela_expr * ela_expr * ela_expr
  | ElaExLet of string * ela_expr * ela_expr
  | ElaExApp of ela_expr * ela_expr
  | ElaExAbs of string * ela_expr
  | ElaExFix of string * ela_type * ela_expr
  | ElaExDepAbs of string * ela_sort * ela_expr
  | ElaExAs of ela_expr * ela_type

type ela_binding =
  | ElaBdName
  | ElaBdVar of ela_type
  | ElaBdIndex of ela_sort
  | ElaBdSortAbb of ela_sort
  | ElaBdTypeAbb of ela_type

type ela_command =
  | ElaCmdEval of ela_expr
  | ElaCmdVal of string * ela_expr
  | ElaCmdVar of string * ela_type
  | ElaCmdSortAbb of string * ela_sort
  | ElaCmdTypeAbb of string * ela_type

type ela_formula =
  | ElaFmTop
  | ElaFmBot
  | ElaFmProp of ela_index
  | ElaFmConj of ela_formula * ela_formula
  | ElaFmImply of ela_index * ela_formula
  | ElaFmEqv of ela_index * ela_index
  | ElaFmForall of string * ela_sort * ela_formula
  | ElaFmExists of string * ela_sort * ela_formula
  | ElaFmScope of ela_formula

type ela_context

val ela_empty_ctx : ela_context
val ela_ctx_length : ela_context -> int
val ela_add_binding : ela_context -> string -> ela_binding -> ela_context
val ela_add_name : ela_context -> string -> ela_context
val ela_name_to_index : ela_context -> string -> int
val ela_index_to_name : ela_context -> int -> string
val ela_is_name_bound : ela_context -> string -> bool
val ela_pick_fresh_name : ela_context -> string -> ela_context * string
val ela_get_binding : ela_context -> int -> ela_binding
val ela_prelude_ctx : ela_context

val ela_shift_expr_above : int -> int -> ela_expr -> ela_expr

val ela_shift_index : int -> ela_index -> ela_index
val ela_shift_type : int -> ela_type -> ela_type
val ela_shift_expr : int -> ela_expr -> ela_expr
val ela_shift_formula : int -> ela_formula -> ela_formula

val ela_subst_index_in_index_top : ela_index -> ela_index -> ela_index
val ela_subst_index_in_type_top : ela_index -> ela_type -> ela_type
val ela_subst_index_in_formula_top : ela_index -> ela_formula -> ela_formula

val ela_unsubst_id_in_type_top : int -> int -> string -> ela_type -> ela_type
val ela_unsubst_id_in_formula_top : int -> int -> string -> ela_formula -> ela_formula

val ela_convert_expr : ela_context -> ela_expr -> ela_expr

val ela_transform_formula : ela_context -> ela_formula -> Z3.context -> (string * ela_sort) list -> Z3.Expr.expr
