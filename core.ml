open Syntax

exception NoRuleApplies

let rec isval ctx tm =
  match tm with
  | TmInt (_) -> true
  | TmBool (_) -> true
  | TmUnit -> true
  | TmPair (tm1, tm2) -> isval ctx tm1 && isval ctx tm2
  | TmAbs (_, _, _) -> true
  | TmDepAbs (_, _, _) -> true
  | TmDepPair (_, _, tm1) -> isval ctx tm1
  | _ -> false

let rec eval1 ctx tm =
  match tm with
  | TmIf (TmBool (true), tm2, tm3) -> tm2
  | TmIf (TmBool (false), tm2, tm3) -> tm3
  | TmIf (tm1, tm2, tm3) -> TmIf (eval1 ctx tm1, tm2, tm3)
  | _ -> raise NoRuleApplies

let rec eval ctx tm =
  try
    let tm' = eval1 ctx tm in eval ctx tm'
  with
  | NoRuleApplies -> tm
