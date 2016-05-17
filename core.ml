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
  | TmDepPair (_,_,tm1) -> isval ctx tm1
  | _ -> false

let rec eval1 ctx tm =
  match tm with
  | TmIf (TmBool (true), tm2, tm3) -> tm2
  | TmIf (TmBool (false), tm2, tm3) -> tm3
  | TmIf (tm1, tm2, tm3) -> TmIf (eval1 ctx tm1, tm2, tm3)
  | TmApp(TmAbs(x,tyT11,t12),v2) when isval ctx v2 ->
      subst_term_in_term_top v2 t12
  | TmApp(v1,t2) when isval ctx v1 ->
      TmApp(v1,eval1 ctx t2)
  | TmApp(t1,t2) ->
      TmApp(eval1 ctx t1, t2)
  | TmLet(x,v1,t2) when isval ctx v1 ->
      subst_term_in_term_top v1 t2
  | TmLet(x,t1,t2) ->
      TmLet(x,eval1 ctx t1, t2)
  | TmFix(x,tyT1,t1) ->
      subst_term_in_term_top tm t1
  | TmDepApp(TmDepAbs(x,tyT11,t12),t2) ->
      subst_index_in_term_top t2 t12
  | TmDepApp(t1,t2) ->
      TmDepApp(eval1 ctx t1, t2)
  | TmDepLet(x1,x2,TmDepPair(i1,srS1,v1),t2) when isval ctx v1 ->
      subst_term_in_term_top v1 (subst_index_in_term_top i1 t2)
  | TmDepLet(x1,x2,t1,t2) ->
      TmDepLet(x1,x2,eval1 ctx t1, t2)
  | _ -> raise NoRuleApplies

let rec eval ctx tm =
  try
    let tm' = eval1 ctx tm in eval ctx tm'
  with
  | NoRuleApplies -> tm
