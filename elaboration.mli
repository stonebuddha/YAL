open Syntax

type exp =
  | ExVar of int * int
  | ExInt of int
  | ExBool of bool
  | ExUnit
  | ExPair of exp * exp
  | ExIf of exp * exp * exp
  | ExCase of exp * (pat * exp) list
  | ExAbs of string * ty option * exp
  | ExApp of exp * exp
  | ExLet of string * exp * exp
  | ExFix of string * ty option * exp
  | ExAs of exp * ty

val synthesize : context -> exp -> (ty * term)
val check : context -> exp -> ty -> term
