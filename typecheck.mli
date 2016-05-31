open Syntax

val typeof : context -> term -> (ty * formula)
val typeof_solved : context -> term -> ty
