open Syntax
open Support.Pervasive
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
  | TmDepPair (_,_,tm1) -> isval ctx tm1
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

(* ------------------------   TYPING  ------------------------ *)

exception NotConsistent
exception EmptyCase

let rec sreqv ctx srS srT =
  true

let rec ideqv ctx idS idT =
  true

let rec tyeqv ctx tyS tyT =
  match (tyS,tyT) with
  | (TyUnit,TyUnit) -> true
  | (TyArrow(tyS1,tyS2),TyArrow(tyT1,tyT2)) ->
       (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
  | (TyBool,TyBool) -> true
  | (TyInt(id1), TyInt(id2)) ->
      ideqv ctx id1 id2
  | (TyProduct(tyS1,tyS2),TyProduct(tyT1,tyT2)) ->
      (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
  | (TyDepExi(sr1,ty1), TyDepExi(sr2,ty2)) ->
      (sreqv ctx sr1 sr2) && (tyeqv ctx ty1 ty2)
  | (TyDepUni(sr1,ty1), TyDepUni(sr2,ty2)) ->
      (sreqv ctx sr1 sr2) && (tyeqv ctx ty1 ty2)
  | _ -> false

let rec patcheck ctx p tyT =
  match p with
  | PtInt(p1) -> 
    if tyeqv ctx tyT (TyInt(IdInt(p1))) then true else false
  | PtBool(p1) ->
    if tyeqv ctx tyT TyBool then true else false
  | PtWild -> true
  | PtVar(_) -> true
  | PtUnit ->
    if tyeqv ctx tyT TyUnit then true else false
  | PtPair(p1,p2) -> 
    (match tyT with
    | TyProduct(tyT1, tyT2) -> (patcheck ctx p1 tyT1) && (patcheck ctx p2 tyT2)
    | _ -> false)

let rec sortof ctx i =
  SrInt

let rec typeof ctx t =
  match t with
  | TmVar(i,_) -> get_type_from_context ctx i
  | TmAbs(x,tyT1,t2) ->
      let ctx' = add_binding ctx x (BdType(tyT1)) in
      let tyT2 = typeof ctx' t2 in
      TyArrow(tyT1, shift_type (-1) tyT2)
  | TmApp(t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match tyT1 with
      | TyArrow(tyT11,tyT12) ->
        if tyeqv ctx tyT2 tyT11 then tyT12
        else error "parameter type mismatch"
      | _ -> error "arrow type expected")
  | TmBool(_) -> 
      TyBool
  | TmIf(t1,t2,t3) ->
      if tyeqv ctx (typeof ctx t1) TyBool then
        let tyT2 = typeof ctx t2 in
        if tyeqv ctx tyT2 (typeof ctx t3) then tyT2
        else error "arms of conditional have different types"
      else error "guard of conditional not a boolean"
  | TmLet(x,t1,t2) ->
     let tyT1 = typeof ctx t1 in
     let ctx' = add_binding ctx x (BdType(tyT1)) in         
     shift_type (-1) (typeof ctx' t2)
  | TmCase(t, cases) ->
      let tyT = typeof ctx t in
      (try
        let rec inner branch =
          (match branch with
          | [] -> raise Not_found
          | (p,_,_)::rest->
            if patcheck ctx p tyT then () else inner rest)
        in inner cases;
        try
          let rec consistent branch =
            match branch with
            | [] -> raise EmptyCase
            | (_,_,clause)::[] -> typeof ctx clause
            | (_,_,clause)::rest ->
                let tyT1 = typeof ctx clause in
                let otherT = consistent rest in
                if tyeqv ctx tyT1 otherT then tyT1 else raise NotConsistent
          in consistent cases
        with 
        | EmptyCase -> error "the body of case is empty"
        | NotConsistent -> error "types are not consistent in case branches"
      with Not_found -> error "no pattern matches with the term")
  | TmFix(x, tyT, t1) ->
      let tyT1 = typeof ctx t1 in
        (match tyT with 
           TyArrow(_,_) ->
             if tyeqv ctx tyT tyT1 then tyT
             else error "result of body not compatible with domain"
         | _ -> error "arrow type expected")
  | TmUnit -> TyUnit
  | TmInt(it) -> TyInt(IdInt(it))
  | TmPair(t1,t2) ->
      TyProduct(typeof ctx t1, typeof ctx t2)
  | TmDepAbs(x,sr1,t2) ->
      let ctx' = add_binding ctx x (BdSort(sr1)) in
      let tyT2 = typeof ctx' t2 in
      TyDepUni(sr1, shift_type (-1) tyT2)
  | TmDepApp(t1,id2) ->
      let tyT1 = typeof ctx t1 in
      let sr2 = sortof ctx id2 in
      (match tyT1 with
          TyDepUni(sr11,tyT12) ->
          if sreqv ctx sr11 sr2 then subst_index_in_type_top id2 tyT12
          else error "parameter type mismatch"
          | _ -> error "dependent universal type expected")
