open Syntax
open Support.Error
open Lacaml.D
open Lacaml_D.Mat

exception NoRuleApplies
exception NoMatchPattern

let rec isval ctx tm =
  match tm with
  | TmInt (_) -> true
  | TmBool (_) -> true
  | TmUnit -> true
  | TmFloat(_) -> true
  | TmPair (tm1, tm2) -> isval ctx tm1 && isval ctx tm2
  | TmAbs (_, _, _) -> true
  | TmDepAbs (_, _, _) -> true
  | TmDepPair (_,tm1,_) -> isval ctx tm1
  | TmVector(tms) -> 
      let rec inner ts n =
        if n = Array.length ts then true
        else isval ctx ts.(n) && inner ts (n + 1)
      in inner tms 0
  | TmMatrix(tms) ->
      let rec inner ts x y =
        if x = Array.length ts then true
        else
          let cond = (y = Array.length ts.(x) - 1) in
          let y' = (if cond then 0 else y + 1) in
          let x' = (if cond then x + 1 else x) in
          isval ctx ts.(x).(y) && inner ts x' y'
      in inner tms 0 0
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

let get_float_array t1 =
  Array.map (fun x ->
    match x with
    | TmFloat(f) -> f
    | _ -> error "not reached") t1

let get_float_array_array t1 =
  Array.map (fun x ->
    get_float_array x) t1

let to_tmfloat_array t1 =
  Array.map (fun x -> TmFloat(x)) t1

let to_tmfloat_array_array t1 =
  Array.map (fun x -> to_tmfloat_array x) t1

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
        | _ -> error "unknown operators. Do you mean iszero?")
  | TmApp(TmVar(x,n),TmPair(TmVector(v1), TmInt(v2)))->
      let name = index2name ctx x in
      (match name with
        | "vector_get" ->
          v1.(v2)
        | _ -> error "unknown operators. Do you mean Vector.get?")
  | TmApp(TmVar(x,n),TmPair(TmPair(TmVector(v1), TmInt(v2)), (TmFloat(v3) as t1))) ->
      let name = index2name ctx x in
      (match name with
        | "vector_set" ->
          v1.(v2) <- t1;
          TmVector(v1)
        | _ -> error "unknown operators. Do you mean Vector.set?")
  | TmApp(TmVar(x,n),TmPair(TmVector(v1),TmVector(v2))) ->
      let name = index2name ctx x in
      (match name with
        | "vector_append" ->
          let v3 = Array.append v1 v2 in
          TmVector(v3)
        | "dot" ->
          let x' = Vec.of_array (get_float_array v1) in
          let y' = Vec.of_array (get_float_array v2) in
          let v3 = dot x' y' in
          TmFloat(v3)
        | _ -> error "unknown operators. Do you mean Vector.append or dot?")
  | TmApp(TmVar(x,n),TmPair(TmMatrix(v1), TmVector(v2))) ->
      let name = index2name ctx x in
      (match name with
        | "gemv" ->
          let x' = Mat.of_array (get_float_array_array v1) in
          let y' = Vec.of_array (get_float_array v2) in
          let v3 = gemv x' y' in
          let v3' = to_tmfloat_array (Vec.to_array v3) in
          TmVector(v3')
        | _ -> error "unknown operators. Do you mean gemv?")
  | TmApp(TmVar(x,n),TmPair(TmMatrix(v1), TmMatrix(v2))) ->
      let name = index2name ctx x in
      (match name with
        | "gemm" ->
          let x' = Mat.of_array (get_float_array_array v1) in
          let y' = Mat.of_array (get_float_array_array v2) in
          let v3 = gemm x' y' in
          let v3' = to_tmfloat_array_array (Mat.to_array v3) in
          TmMatrix(v3')
        | _ -> error "unknown operators. Do you mean gemm?")
  | TmApp(TmVar(x,n),TmMatrix(v1)) ->
      let name = index2name ctx x in
      (match name with
        | "transpose" ->
          let x' = Mat.of_array (get_float_array_array v1) in
          let v2 = Mat.transpose_copy x' in
          let v2' = to_tmfloat_array_array (Mat.to_array v2) in
          TmMatrix(v2')
        | _ -> error "unknown operators. Do you mean transpose?")
  | TmApp(TmVar(x,n),TmPair(TmPair(TmMatrix(v1), TmInt(v2)), TmInt(v3))) ->
      let name = index2name ctx x in
      (match name with
        | "matrix_get" ->
          v1.(v2).(v3)
        | _ -> error "unknown operators. Do you mean matrix_get?")
  | TmApp(TmVar(x,n),TmPair(TmPair(TmPair(TmMatrix(v1), TmInt(v2)), TmInt(v3)), (TmFloat(v4) as t1))) ->
      let name = index2name ctx x in
      (match name with
        | "matrix_set" ->
          v1.(v2).(v3) <- t1;
          TmMatrix(v1)
        | _ -> error "unknown operators. Do you mean matrix_get?")
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
  | TmVector(t1) ->
      TmVector(Array.map (fun x -> eval1 ctx x) t1)
  | TmMatrix(t1) ->
      TmMatrix(Array.map (fun x -> Array.map (fun y -> eval1 ctx y) x) t1)
  | _ -> raise NoRuleApplies

let rec eval ctx tm =
  try
    let tm' = eval1 ctx tm in eval ctx tm'
  with
  | NoRuleApplies -> tm