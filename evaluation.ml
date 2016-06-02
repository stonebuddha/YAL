open Syntax
open Support.Error

exception NoRuleApplies
exception NoMatchPattern

let rec isval ctx tm =
  match tm with
  | TmInt (_) -> true
  | TmBool (_) -> true
  | TmUnit -> true
  | TmPair (tm1, tm2) -> isval ctx tm1 && isval ctx tm2
  | TmAbs (_, _, _) -> true
  | TmDepAbs (_, _, _) -> true
  | TmDepPair (_,tm1,_) -> isval ctx tm1
  | _ -> false

let rec patmatch pattern t1 t2 =
  match pattern with
  | PtWild -> t2
  | PtInt(v2) -> 
      (match t1 with
        | TmInt(v3) when v2 = v3 -> t2
        | _ -> raise NoMatchPattern)
  | PtVar(_) -> subst_term_in_term_top t1 t2
  | PtBool(v2) ->
      (match t1 with
        | TmBool(v3) when v2 = v3 -> t2
        | _ -> raise NoMatchPattern)
  | PtUnit ->
      (match t1 with
        | TmUnit -> t2
        | _ -> raise NoMatchPattern)
  | PtPair(p1,p2) ->
      (match t1 with
        | TmPair(tp1,tp2) ->
            let t' = patmatch p1 tp1 t2 in
            patmatch p2 tp2 t'
        | _ -> raise NoMatchPattern)

let rec eval1 ctx tm =
  match tm with
  | TmIf (TmBool (true), tm2, tm3) -> tm2
  | TmIf (TmBool (false), tm2, tm3) -> tm3
  | TmIf (tm1, tm2, tm3) -> TmIf (eval1 ctx tm1, tm2, tm3)
  | TmApp(TmVar(x,n),TmPair(TmInt(v1),TmInt(v2))) ->
      let name = index2name ctx x in
      (match name with
        | "op+" -> TmInt(v1 + v2)
        | "op-" -> TmInt(v1 - v2)
        | "op*" -> TmInt(v1 * v2)
        | "op/" -> TmInt(v1 / v2)
        | _ -> error "unknown operators")
  | TmApp(TmVar(x,n),TmDepPair(_,TmInt(v1),_)) ->
      let name = index2name ctx x in
      (match name with
        | "iszero" ->
            (match v1 with
              | 0 -> TmBool(true)
              | _ -> TmBool(false))
        | _ -> error "unknown operators")
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
  | TmPair(v1, v2) when isval ctx tm -> tm
  | TmPair(v1, t2) when isval ctx v1 ->
      TmPair(v1, eval1 ctx t2)
  | TmPair(t1, t2) ->
      TmPair(eval1 ctx t1, t2)
  | TmCase(v1, branches) when isval ctx v1 ->
      let rec inner branch =
        match branch with
        | [] -> raise NoRuleApplies
        | (pattern, num, t)::rest ->
            try patmatch pattern v1 t
            with NoMatchPattern -> inner rest
      in inner branches
  | TmCase(t1,branches) ->
      TmCase(eval1 ctx t1, branches)
  | TmDepApp(TmVar(x,n),_) ->
      TmVar(x,n)
  | TmDepApp(TmDepAbs(x,_,t12),t2) ->
      subst_index_in_term_top t2 t12
  | TmDepApp(t1,t2) ->
      TmDepApp(eval1 ctx t1, t2)
  | TmDepLet(x1,x2,TmDepPair(i1,v1,_),t2) when isval ctx v1 ->
      subst_index_in_term_top i1 (subst_term_in_term_top v1 t2)
  | TmDepLet(x1,x2,t1,t2) ->
      TmDepLet(x1,x2,eval1 ctx t1, t2)
  | TmDepPair(v1,t2,tyT) ->
      TmDepPair(v1, eval1 ctx t2, tyT)
  | _ -> raise NoRuleApplies

let rec eval ctx tm =
  try
    print_raw tm;
    print_newline ();
    let tm' = eval1 ctx tm in eval ctx tm'
  with
  | NoRuleApplies -> tm