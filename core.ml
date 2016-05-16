open Syntax

exception NoRuleApplies
exception TODO

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
  | TmPair (v1, tm2) when isval ctx v1 -> TmPair(v1, eval1 ctx tm2)
  | TmPair (tm1, tm2) -> TmPair (eval1 ctx tm1, tm2)
  | TmApp (TmAbs (x, tyx, tm1), v2) when isval ctx v2 -> subst_term_in_term_top v2 tm1
  | TmApp (v1, tm2) when isval ctx v1 -> TmApp (v1, eval1 ctx tm2)
  | TmApp (tm1, tm2) -> TmApp (eval1 ctx tm1, tm2)
  | TmLet (x, v1, tm2) when isval ctx v1 -> subst_term_in_term_top v1 tm2
  | TmLet (x, tm1, tm2) -> TmLet (x, eval1 ctx tm1, tm2)
  | TmFix (f, tyf, tm1) -> subst_term_in_term_top tm tm1
  | TmDepApp (TmDepAbs (a, sr, tm1), id) -> raise TODO
  | TmDepApp (tm1, id) -> TmDepApp (eval1 ctx tm1, id)
  | TmDepPair (id, sr, tm1) -> TmDepPair (id, sr, eval1 ctx tm1)
  | TmDepLet (a, x, TmDepPair(id, _, v1), tm2) when isval ctx v1 -> raise TODO
  | TmCase (v1, cases) when isval ctx v1 -> raise TODO
  | TmCase (tm1, cases) -> TmCase (eval1 ctx tm1, cases)
  | _ -> raise NoRuleApplies

let rec eval ctx tm =
  try
    let tm' = eval1 ctx tm in eval ctx tm'
  with
  | NoRuleApplies -> tm
