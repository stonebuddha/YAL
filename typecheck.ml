open Syntax
open Support.Pervasive
open Support.Error
open Smt

exception NotConsistent
exception EmptyCase

let append_uniq l1 l2 =
  let l3 = List.append l1 l2 in
    List.sort_uniq 
      (fun x1 x2 -> if (x1 > x2) then 1 else if (x1 < x2) then -1 else 0)
      l3

let rec id_op_routine ctx idx idy op = 
  let (l1, f1) = get_id_fm ctx idx in
  let (l2, f2) = get_id_fm ctx idy in
  let l_new = List.append l1 l2 in
  match op with 
  | "+" -> (l_new, FmAdd(f1, f2))
  | "-" -> (l_new, FmSub(f1, f2))
  | "*" -> (l_new, FmMul(f1, f2))
  | "/" -> (l_new, FmDiv(f1, f2))
  | _ -> error "op for id can only be +,-,*,/"

and get_id_fm ctx id =
  match id with
  | IdVar(x,_) ->
    ([x],FmVar(x))
  | IdInt(i) ->
    ([],FmIntConst(i))
  | IdAdd(x,y) ->
    id_op_routine ctx x y "+"
  | IdSub(x,y) ->
    id_op_routine ctx x y "-"
  | IdMul(x,y) ->
    id_op_routine ctx x y "*"
  | IdDiv(x,y) ->
    id_op_routine ctx x y "/"

let rec get_prop_fm ctx pro =
  match pro with
  | PrTrue -> FmTrue
  | PrFalse -> FmFalse
  | PrNeg(pr1) -> FmNot(get_prop_fm ctx pr1)
  | PrAnd(pr1, pr2) -> 
      let f1 = get_prop_fm ctx pr1 in
      let f2 = get_prop_fm ctx pr2 in
      FmAnd([f1;f2])
  | PrOr(pr1, pr2) -> 
      let f1 = get_prop_fm ctx pr1 in
      let f2 = get_prop_fm ctx pr2 in
      FmOr([f1;f2])
  | PrLe(id1, id2) -> 
      let (l1,f1) = get_id_fm ctx id1 in
      let (l2,f2) = get_id_fm ctx id2 in
      FmLe(f1, f2)

let rec get_sr_fm ctx sr =
  match sr with
  | SrInt -> FmTrue
  | SrSubset(x,sr2,pro) ->
      let fsr = get_sr_fm ctx sr2 in
      let fpr = get_prop_fm ctx pro in
      FmAnd([fsr;fpr])

let rec sreqv ctx srS srT =
  let fmS = get_sr_fm ctx srS in
  let fmT = get_sr_fm ctx srT in
  (fmS, FmAnd([FmImply(fmS, fmT);FmImply(fmT,fmS)]))

let rec ideqv ctx idS idT =
  let (l1, f1) = get_id_fm ctx idS in
  let (l2, f2) = get_id_fm ctx idT in
  let l_new = append_uniq l1 l2 in
  (l_new, FmEq(f1, f2))


let rec tyeqv ctx tyS tyT =
  match (tyS,tyT) with
  | (TyUnit,TyUnit) -> ([], FmTrue)
  | (TyArrow(tyS1,tyS2),TyArrow(tyT1,tyT2)) ->
      let (l1, f1) = tyeqv ctx tyS1 tyT1 in
      let (l2, f2) = tyeqv ctx tyS2 tyT2 in
      let arg = [f1 ; f2] in
      let l3 = append_uniq l1 l2 in
      (l3, FmAnd(arg))
  | (TyBool,TyBool) -> ([], FmTrue)
  | (TyFloat, TyFloat) -> ([], FmTrue)
  | (TyInt(id1), TyInt(id2)) ->
      ideqv ctx id1 id2
  | (TyProduct(tyS1,tyS2),TyProduct(tyT1,tyT2)) ->
      let (l1, f1) = tyeqv ctx tyS1 tyT1 in
      let (l2, f2) = tyeqv ctx tyS2 tyT2 in
      let arg = [f1 ; f2] in
      let l3 = append_uniq l1 l2 in
      (l3, FmAnd(arg))
  | (TyDepExi(x1,sr1,ty1), TyDepExi(x2,sr2,ty2)) ->
      let (f3, f1) = sreqv ctx sr1 sr2 in
      let ctx' = add_binding ctx x1 (BdSort(sr1)) in
      let (l2, f2) = tyeqv ctx' ty1 ty2 in
      ([], FmUni(l2, FmAnd([f1;FmImply(f3, f2)])))
  | (TyDepUni(x1,sr1,ty1), TyDepUni(x2,sr2,ty2)) ->
      let (f3, f1) = sreqv ctx sr1 sr2 in
      let ctx' = add_binding ctx x1 (BdSort(sr1)) in
      let (l2, f2) = tyeqv ctx' ty1 ty2 in
      ([], FmUni(l2, FmAnd([f1; FmImply(f3, f2)])))
  | (TyVector(id1), TyVector(id2)) ->
      ideqv ctx id1 id2
  | (TyMatrix(id1, id2), TyMatrix(id3, id4)) ->
      let (l1, f1) = ideqv ctx id1 id3 in
      let (l2, f2) = ideqv ctx id2 id4 in
      let l3 = append_uniq l1 l2 in
      (l3, FmAnd([f1;f2]))
  | _ -> ([], FmFalse)

let rec concrete_tyeqv ctx tyS tyT =
  match (tyS, tyT) with
  | (TyUnit, TyUnit) -> true
  | (TyInt(IdInt(i1)), TyInt(IdInt(i2))) -> 
      if i1 = i2 then true else false
  | (TyBool, TyBool) -> true
  | (TyFloat, TyFloat) -> true
  | (TyArrow(tyS1,tyS2),TyArrow(tyT1,tyT2)) -> 
      (concrete_tyeqv ctx tyS1 tyT1) && (concrete_tyeqv ctx tyS2 tyT2)
  | (TyProduct(tyS1,tyS2),TyProduct(tyT1,tyT2)) ->
      (concrete_tyeqv ctx tyS1 tyT1) && (concrete_tyeqv ctx tyS2 tyT2)
  | (TyVector(IdInt(i1)), TyVector(IdInt(i2))) ->
      if i1 = i2 then true else false
  | (TyMatrix(IdInt(i1), IdInt(i2)), TyMatrix(IdInt(i3), IdInt(i4))) ->
      if (i1 = i3) && (i2 = i4) then true else false
  | _ -> false

let rec sr_id_fm ctx sr id =
  match sr with
  | SrInt -> FmTrue
  | SrSubset(x,sr2,pro) ->
      let fsr = sr_id_fm ctx sr2 id in
      let pr' = subst_index_in_prop_top id pro in
      let fpr = get_prop_fm ctx pr' in
      FmAnd([fsr;fpr])

and get_id_var_sort_fm ctx id = 
  match id with
  | IdVar(x,_) ->
    let sr = get_sort_from_context ctx x in
    let f1 = sr_id_fm ctx sr id in
    [f1]
  | IdAdd(x,y) ->
    let x' = get_id_var_sort_fm ctx x in
    let y' = get_id_var_sort_fm ctx y in
    List.append x' y'
  | IdSub(x,y) ->
    let x' = get_id_var_sort_fm ctx x in
    let y' = get_id_var_sort_fm ctx y in
    List.append x' y'
  | IdMul(x,y) ->
    let x' = get_id_var_sort_fm ctx x in
    let y' = get_id_var_sort_fm ctx y in
    List.append x' y'
  | IdDiv(x,y) ->
    let x' = get_id_var_sort_fm ctx x in
    let y' = get_id_var_sort_fm ctx y in
    List.append x' y'
  | IdInt(_) -> [FmTrue]

and get_prop_var_sort_fm ctx pro =
  match pro with
  | PrNeg(pr1) -> get_prop_var_sort_fm ctx pr1
  | PrAnd(pr1, pr2) -> 
      let l1 = get_prop_var_sort_fm ctx pr1 in
      let l2 = get_prop_var_sort_fm ctx pr2 in
      List.append l1 l2
  | PrOr(pr1, pr2) -> 
      let l1 = get_prop_var_sort_fm ctx pr1 in
      let l2 = get_prop_var_sort_fm ctx pr2 in
      List.append l1 l2
  | PrLe(id1, id2) -> 
      let l1 = get_id_var_sort_fm ctx id1 in
      let l2 = get_id_var_sort_fm ctx id2 in
      List.append l1 l2
  | _ -> []

let rec match_sr_id ctx sr id =
  (* print_string "match:";print_raw_sort sr;print_newline();print_raw_index id;print_newline (); *)
  match sr with
  | SrInt -> FmTrue
  | SrSubset(x,sr2,pr) ->
      let fsr = match_sr_id ctx sr2 id in
      let l1 = get_id_var_sort_fm ctx id in
      let pr' = subst_index_in_prop_top id pr in
      let fpr = get_prop_fm ctx pr' in
      let l2 = get_prop_var_sort_fm ctx pr' in
      let l3 = List.append l1 l2 in
      let f1' = if (List.length l3) = 1 then List.hd l3 else FmAnd(l3) in
      FmAnd([fsr;FmImply(f1',fpr)])


let rec patcheck ctx p tyT =
  match p with
  | PtInt(p1) -> 
    if concrete_tyeqv ctx tyT (TyInt(IdInt(p1))) then true else false
  | PtBool(p1) ->
    if concrete_tyeqv ctx tyT TyBool then true else false
  | PtWild -> true
  | PtVar(_) -> true
  | PtUnit ->
    if concrete_tyeqv ctx tyT TyUnit then true else false
  | PtPair(p1,p2) -> 
    (match tyT with
    | TyProduct(tyT1, tyT2) -> (patcheck ctx p1 tyT1) && (patcheck ctx p2 tyT2)
    | _ -> false)

let rec typeof ctx t =
  match t with
  | TmVar(i,_) -> 
    let tyT = get_type_from_context ctx i in (tyT, FmTrue)
  | TmAbs(x,tyT1,t2) ->
      let ctx' = add_binding ctx x (BdType(tyT1)) in
      let (tyT2, f2) = typeof ctx' t2 in
      let tyT2_new = shift_type (-1) tyT2 in
      let f3 = shift_formula (-1) f2 in
      let tty = TyArrow(tyT1, tyT2_new) in
      (tty, f3)
  | TmApp(t1,t2) ->
      let (tyT1, f1) = typeof ctx t1 in
      let (tyT2, f2) = typeof ctx t2 in
      (match tyT1 with
      | TyArrow(tyT11,tyT12) ->
        let (l3, f3) = tyeqv ctx tyT2 tyT11 in 
        (match f3 with
        | FmFalse -> error "TmApp:parameter type mismatch"
        | _ -> (tyT12, FmAnd([f1 ; f2 ; f3])))
      | _ -> error "TmApp: arrow type expected")
  | TmBool(_) -> 
      (TyBool, FmTrue)
  | TmFloat(_) ->
      (TyFloat, FmTrue)
  | TmIf(t1,t2,t3) ->
    let (tyT1, f1) = typeof ctx t1 in
      if concrete_tyeqv ctx tyT1 TyBool
      then
        let (tyT2, f2) = typeof ctx t2 in
        let (tyT3, f3) = typeof ctx t3 in
        let (l4, f4) = tyeqv ctx tyT2 tyT3 in
        (match f4 with 
        | FmFalse -> error "arms of conditional have different types"
        | _ ->
          let f_new = FmAnd([f1;f2;f3;f4]) in
          (tyT2, f_new))
      else error "guard of conditional not a boolean"
  | TmLet(x,t1,t2) ->
     let (tyT1,f1) = typeof ctx t1 in
     let ctx' = add_binding ctx x (BdType(tyT1)) in
     let (tyT2,f2) = typeof ctx' t2 in
     let tyT22 = shift_type (-1) tyT2 in
     let f3 = shift_formula (-1) f2 in
     (tyT22, FmAnd([f1;f3]))
  | TmCase(t, cases) ->
      let (tyT, f1) = typeof ctx t in
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
                let (tyT1,f1) = typeof ctx clause in
                let (otherT,f2) = consistent rest in
                let (_,f3) = tyeqv ctx tyT1 otherT in
                (match f3 with
                | FmFalse -> raise NotConsistent
                | _ -> (tyT1, FmAnd([f1;f2;f3])))
          in consistent cases
        with 
        | EmptyCase -> error "the body of case is empty"
        | NotConsistent -> error "types are not consistent in case branches"
      with Not_found -> error "no pattern matches with the term")
  | TmFix(x, tyT, t1) ->
      let ctx' = add_binding ctx x (BdType tyT) in
      let (tyT1,f1) = typeof ctx' t1 in
        (match tyT with 
            TyArrow(_,_) ->
              let (l2,f2) = tyeqv ctx tyT tyT1 in
              (match f1 with 
              | FmFalse -> error "TmFix: result of body not compatible with domain"
              | _ -> (tyT, FmAnd([f1;f2])))
         | _ -> error "TmFix: arrow type expected")
  | TmUnit -> (TyUnit, FmTrue)
  | TmInt(it) -> (TyInt(IdInt(it)), FmTrue)
  | TmPair(t1,t2) ->
      let (tyT1, f1) = typeof ctx t1 in
      let (tyT2, f2) = typeof ctx t2 in
      (TyProduct(tyT1, tyT2), FmAnd([f1;f2]))
  | TmDepAbs(x,sr1,t2) ->
      let ctx' = add_binding ctx x (BdSort(sr1)) in
      let (tyT2, f2) = typeof ctx' t2 in
      (TyDepUni(x, sr1, tyT2), f2)
  | TmDepApp(t1,id2) ->
      let (tyT1, f1) = typeof ctx t1 in
      (match tyT1 with
          TyDepUni(_, sr11,tyT12) ->
          let f2 = match_sr_id ctx sr11 id2 in
          (match f2 with
          | FmFalse -> error "TmDepApp:parameter type mismatch"
          | _ -> (subst_index_in_type_top id2 tyT12, FmAnd([f1;f2])))
      | _ -> error "dependent universal type expected")
  | TmDepPair(id,t1,tyT) ->
      (match tyT with
      | TyDepExi(_, sr, tyT1) ->
          let f1 = match_sr_id ctx sr id in
          let (tyT11, f2) = typeof ctx t1 in
          let tyT1' = subst_index_in_type_top id tyT1 in
          let (_, f3) = tyeqv ctx tyT11 tyT1' in
          (match f3 with
          | FmFalse -> error "type of pair mismatch"
          | _ -> (tyT, FmAnd([f1;f2;f3])))
      | _ -> error "dependent existential type expected") 
  | TmDepLet(x1,x2,t1,t2) ->
     let (tyT1,f1) = typeof ctx t1 in
     (match tyT1 with
      | TyDepExi(a, sr, tyT11) ->
          let ctx' = add_binding ctx x1 (BdSort(sr)) in
          let ctx'' = add_binding ctx' x2 (BdType(tyT11)) in
          let (tyT2,f2) = typeof ctx'' t2 in
          let tyT22 = shift_type (-2) tyT2 in
          let f2' = shift_formula (-1) f2 in
          let f4 = get_sr_fm ctx sr in
          let f3 = FmUni([0], FmImply(f4,f2')) in
          (tyT22, FmAnd([f1;f3]))
      | _ -> error "dependent existential type expected")
  | TmVector(tms) ->
      let fms_arr = Array.map (fun x -> 
              let (tyT, f1) = typeof ctx x in
              if concrete_tyeqv ctx tyT TyFloat then f1
              else error "elements in vector should be floats") tms in
      let fms = Array.to_list fms_arr in
      let len = Array.length tms in
      (TyVector(IdInt(len)), FmAnd(fms))
  | TmMatrix(tms) ->
      let _ = 
        let rec inner x =
          let len = Array.length tms.(x) in
          if x = (Array.length tms) - 1 then len
          else 
            let res  = inner (x + 1) in
            if len = res then len else error "each row of matrix should be of same size"
        in if (Array.length tms) = 0 then 0 else inner 0
      in ();
      let fms_arr2 = Array.map (fun x ->
                    Array.map (fun y ->
              let (tyT, f1) = typeof ctx y in
              if concrete_tyeqv ctx tyT TyFloat then f1
              else error "elements in matrix should be floats") x) tms in
      let fms_arr = Array.to_list fms_arr2 in
      let fms = List.flatten (List.map Array.to_list fms_arr) in
      let len1 = Array.length tms in
      let len2 = (if len1 = 0 then 0 else Array.length tms.(0)) in
      (TyMatrix(IdInt(len1), IdInt(len2)), FmAnd(fms))

  let typeof_solved ctx t =
    let (tyT,fm) = typeof ctx t in
    (* print_string "formula: ";printfm fm;print_newline ();print_string "type: ";printty tyT;print_newline (); *)
    let res = fm_solver fm in
    match res with
    | 1 -> tyT
    | 2 -> error "type unsatisfiable"
    | 3 -> error "type unknown"
    | _ -> error "not reached"

