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

type ela_context = (string * ela_binding) list

exception TODO
exception Error of string

let ela_empty_ctx = []

let ela_ctx_length ctx = List.length ctx

let ela_add_binding ctx x bind = (x, bind) :: ctx

let ela_add_name ctx x = ela_add_binding ctx x ElaBdName

let rec ela_name_to_index ctx x =
  match ctx with
  | [] -> raise (Error "ela_name_to_index")
  | (y, _) :: rest -> if x = y then 0 else 1 + ela_name_to_index rest x

let rec ela_index_to_name ctx n =
  let (x, _) = List.nth ctx n in
  x

let rec ela_is_name_bound ctx x =
  match ctx with
  | [] -> false
  | (y, _) :: rest -> if x = y then true else ela_is_name_bound rest x

let rec ela_pick_fresh_name ctx x =
  if ela_is_name_bound ctx x then
    ela_pick_fresh_name ctx (x ^ "'")
  else
    ((x, ElaBdName) :: ctx, x)

let ela_idmap onvar c id =
  let rec walk c id =
    match id with
    | ElaIdId (s) -> id
    | ElaIdVar (a, n) -> onvar c a n
    | ElaIdInt (i) -> id
    | ElaIdBool (b) -> id
    | ElaIdBinop (bop, id1, id2) -> ElaIdBinop (bop, walk c id1, walk c id2)
    | ElaIdUnop (uop, id1) -> ElaIdUnop (uop, walk c id1)
  in
  walk c id

let ela_srmap onvar onindex c sr =
  let rec walk c sr =
    match sr with
    | ElaSrVar (a, n) -> onvar c a n
    | ElaSrInt -> sr
    | ElaSrBool -> sr
    | ElaSrSubset (a, sr1, pr1) ->
      ElaSrSubset (a, walk c sr1, onindex (c + 1) pr1)
  in
  walk c sr

let ela_tymap onvar onindex onsort c ty =
  let rec walk c ty =
    match ty with
    | ElaTyVar (a, n) -> onvar c a n
    | ElaTyInt (id1) -> ElaTyInt (onindex c id1)
    | ElaTyBool (id1) -> ElaTyBool (onindex c id1)
    | ElaTyUnit -> ty
    | ElaTyFloat -> ty
    | ElaTyVector (id1) -> ElaTyVector (onindex c id1)
    | ElaTyMatrix (id1, id2) -> ElaTyMatrix (onindex c id1, onindex c id2)
    | ElaTyProduct (ty1, ty2) -> ElaTyProduct (walk c ty1, walk c ty2)
    | ElaTyArrow (ty1, ty2) -> ElaTyArrow (walk c ty1, walk c ty2)
    | ElaTyDepUni (a, sr1, ty1) ->
      ElaTyDepUni (a, onsort c sr1, walk (c + 1) ty1)
    | ElaTyDepExi (a, sr1, ty1) ->
      ElaTyDepExi (a, onsort c sr1, walk (c + 1) ty1)
  in
  walk c ty

let ela_exmap onvar onsort ontype c ex =
  let rec walk c ex =
    match ex with
    | ElaExVar (x, n) -> onvar c x n
    | ElaExInt (i) -> ex
    | ElaExBool (b) -> ex
    | ElaExUnit -> ex
    | ElaExFloat (f) -> ex
    | ElaExPair (ex1, ex2) -> ElaExPair (walk c ex1, walk c ex2)
    | ElaExIf (ex1, ex2, ex3) -> ElaExIf (ex1, ex2, ex3)
    | ElaExLet (x, ex1, ex2) -> ElaExLet (x, walk c ex1, walk (c + 1) ex2)
    | ElaExApp (ex1, ex2) -> ElaExApp (walk c ex1, walk c ex2)
    | ElaExAbs (x, ex1) -> ElaExAbs (x, walk (c + 1) ex1)
    | ElaExFix (f, tyf, ex1) -> ElaExFix (f, ontype c tyf, walk (c + 1) ex1)
    | ElaExDepAbs (a, sr1, ex1) ->
      ElaExDepAbs (a, onsort c sr1, walk (c + 1) ex1)
    | ElaExAs (ex1, ty1) -> ElaExAs (walk c ex1, ontype c ty1)
  in
  walk c ex

let ela_fmmap onindex onsort c fm =
  let rec walk c fm =
    match fm with
    | ElaFmTop -> fm
    | ElaFmBot -> fm
    | ElaFmProp (pr1) -> ElaFmProp (onindex c pr1)
    | ElaFmConj (fm1, fm2) -> ElaFmConj (walk c fm1, walk c fm2)
    | ElaFmImply (pr1, fm2) -> ElaFmImply (onindex c pr1, walk c fm2)
    | ElaFmEqv (id1, id2) -> ElaFmEqv (onindex c id1, onindex c id2)
    | ElaFmForall (a, sr1, fm1) ->
      ElaFmForall (a, onsort c sr1, walk (c + 1) fm1)
    | ElaFmExists (s, sr1, fm1) -> ElaFmExists (s, onsort c sr1, walk c fm1)
    | ElaFmScope (fm1) -> ElaFmScope (walk (c + 1) fm1)
  in
  walk c fm

let ela_shift_index_above d c id =
  ela_idmap
    (fun c a n ->
       if a >= c then ElaIdVar (a + d, n + d) else ElaIdVar (a, n + d))
    c id

let ela_shift_sort_above d c sr =
  ela_srmap
    (fun c a n ->
       if a >= c then ElaSrVar (a + d, n + d) else ElaSrVar (a, n + d))
    (ela_shift_index_above d)
    c sr

let ela_shift_type_above d c ty =
  ela_tymap
    (fun c a n ->
       if a >= c then ElaTyVar (a + d, n + d) else ElaTyVar (a, n + d))
    (ela_shift_index_above d)
    (ela_shift_sort_above d)
    c ty

let ela_shift_expr_above d c ex =
  ela_exmap
    (fun c x n ->
       if x >= c then ElaExVar (x + d, n + d) else ElaExVar (x, n + d))
    (ela_shift_sort_above d)
    (ela_shift_type_above d)
    c ex

let ela_shift_formula_above d c fm =
  ela_fmmap
    (ela_shift_index_above d)
    (ela_shift_sort_above d)
    c fm

let ela_shift_index d id = ela_shift_index_above d 0 id

let ela_shift_sort d sr = ela_shift_sort_above d 0 sr

let ela_shift_type d ty = ela_shift_type_above d 0 ty

let ela_shift_expr d ex = ela_shift_expr_above d 0 ex

let ela_shift_formula d fm = ela_shift_formula_above d 0 fm

let ela_subst_index_in_index j s id =
  ela_idmap
    (fun j a n -> if a = j then ela_shift_index j s else ElaIdVar (a, n))
    j id

let ela_subst_index_in_sort j s sr =
  ela_srmap
    (fun j a n -> ElaSrVar (a, n))
    (fun j id -> ela_subst_index_in_index j s id)
    j sr

let ela_subst_index_in_type j s ty =
  ela_tymap
    (fun j a n -> ElaTyVar (a, n))
    (fun j id -> ela_subst_index_in_index j s id)
    (fun j sr -> ela_subst_index_in_sort j s sr)
    j ty

let ela_subst_index_in_formula j s fm =
  ela_fmmap
    (fun j id -> ela_subst_index_in_index j s id)
    (fun j sr -> ela_subst_index_in_sort j s sr)
    j fm

let ela_subst_index_in_index_top s id =
  ela_shift_index (-1) (ela_subst_index_in_index 0 (ela_shift_index 1 s) id)

let ela_subst_index_in_sort_top s sr =
  ela_shift_sort (-1) (ela_subst_index_in_sort 0 (ela_shift_index 1 s) sr)

let ela_subst_index_in_type_top s ty =
  ela_shift_type (-1) (ela_subst_index_in_type 0 (ela_shift_index 1 s) ty)

let ela_subst_index_in_formula_top s fm =
  ela_shift_formula (-1) (ela_subst_index_in_formula 0 (ela_shift_index 1 s) fm)

let rec ela_unsubst_id_in_index_top c d s id =
  match id with
  | ElaIdId (s') -> if s = s' then ElaIdVar (d, c + 1) else id
  | ElaIdVar (a, n) -> id
  | ElaIdInt (i) -> id
  | ElaIdBool (b) -> id
  | ElaIdBinop (bop, id1, id2) ->
    let id1' = ela_unsubst_id_in_index_top c d s id1 in
    let id2' = ela_unsubst_id_in_index_top c d s id2 in
    ElaIdBinop (bop, id1', id2')
  | ElaIdUnop (uop, id1) ->
    let id1' = ela_unsubst_id_in_index_top c d s id1 in
    ElaIdUnop (uop, id1')

let rec ela_unsubst_id_in_sort_top c d s sr =
  match sr with
  | ElaSrVar (a, n) -> sr
  | ElaSrInt -> sr
  | ElaSrBool -> sr
  | ElaSrSubset (a, sr1, pr1) ->
    let sr1' = ela_unsubst_id_in_sort_top c d s sr1 in
    let pr1' = ela_unsubst_id_in_index_top (c + 1) (d + 1) s pr1 in
    ElaSrSubset (a, sr1', pr1')

let rec ela_unsubst_id_in_type_top c d s ty =
  match ty with
  | ElaTyVar (a, n) -> ty
  | ElaTyInt (id1) ->
    let id1' = ela_unsubst_id_in_index_top c d s id1 in
    ElaTyInt (id1')
  | ElaTyBool (id1) ->
    let id1' = ela_unsubst_id_in_index_top c d s id1 in
    ElaTyBool (id1')
  | ElaTyUnit -> ty
  | ElaTyFloat -> ty
  | ElaTyVector (id1) ->
    let id1' = ela_unsubst_id_in_index_top c d s id1 in
    ElaTyVector (id1')
  | ElaTyMatrix (id1, id2) ->
    let id1' = ela_unsubst_id_in_index_top c d s id1 in
    let id2' = ela_unsubst_id_in_index_top c d s id2 in
    ElaTyMatrix (id1', id2')
  | ElaTyProduct (ty1, ty2) ->
    let ty1' = ela_unsubst_id_in_type_top c d s ty1 in
    let ty2' = ela_unsubst_id_in_type_top c d s ty2 in
    ElaTyProduct (ty1', ty2')
  | ElaTyArrow (ty1, ty2) ->
    let ty1' = ela_unsubst_id_in_type_top c d s ty1 in
    let ty2' = ela_unsubst_id_in_type_top c d s ty2 in
    ElaTyArrow (ty1', ty2')
  | ElaTyDepUni (a, sr1, ty1) ->
    let sr1' = ela_unsubst_id_in_sort_top c d s sr1 in
    let ty1' = ela_unsubst_id_in_type_top (c + 1) (d + 1) s ty1 in
    ElaTyDepUni (a, sr1', ty1')
  | ElaTyDepExi (a, sr1, ty1) ->
    let sr1' = ela_unsubst_id_in_sort_top c d s sr1 in
    let ty1' = ela_unsubst_id_in_type_top (c + 1) (d + 1) s ty1 in
    ElaTyDepExi (a, sr1', ty1')

let rec ela_unsubst_id_in_formula_top c d s fm =
  match fm with
  | ElaFmTop -> fm
  | ElaFmBot -> fm
  | ElaFmProp (pr1) ->
    let pr1' = ela_unsubst_id_in_index_top c d s pr1 in
    ElaFmProp (pr1')
  | ElaFmConj (fm1, fm2) ->
    let fm1' = ela_unsubst_id_in_formula_top c d s fm1 in
    let fm2' = ela_unsubst_id_in_formula_top c d s fm2 in
    ElaFmConj (fm1', fm2')
  | ElaFmImply (pr1, fm2) ->
    let pr1' = ela_unsubst_id_in_index_top c d s pr1 in
    let fm2' = ela_unsubst_id_in_formula_top c d s fm2 in
    ElaFmImply (pr1', fm2')
  | ElaFmEqv (id1, id2) ->
    let id1' = ela_unsubst_id_in_index_top c d s id1 in
    let id2' = ela_unsubst_id_in_index_top c d s id2 in
    ElaFmEqv (id1', id2')
  | ElaFmForall (a, sr1, fm1) ->
    let sr1' = ela_unsubst_id_in_sort_top c d s sr1 in
    let fm1' = ela_unsubst_id_in_formula_top (c + 1) (d + 1) s fm1 in
    ElaFmForall (a, sr1', fm1')
  | ElaFmExists (s', sr1, fm1) ->
    let sr1' = ela_unsubst_id_in_sort_top c d s sr1 in
    let fm1' = ela_unsubst_id_in_formula_top c d s fm1 in
    ElaFmExists (s', sr1', fm1')
  | ElaFmScope (fm1) ->
    let fm1' = ela_unsubst_id_in_formula_top (c + 1) (d + 1) s fm1 in
    ElaFmScope (fm1')

let ela_shift_binding d bind =
  match bind with
  | ElaBdName -> bind
  | ElaBdVar (ty1) -> ElaBdVar (ela_shift_type d ty1)
  | ElaBdIndex (sr1) -> ElaBdIndex (ela_shift_sort d sr1)
  | ElaBdSortAbb (sr1) -> ElaBdSortAbb (ela_shift_sort d sr1)
  | ElaBdTypeAbb (ty1) -> ElaBdTypeAbb (ela_shift_type d ty1)

let ela_get_binding ctx i =
  let (_, bind) = List.nth ctx i in
  ela_shift_binding (i + 1) bind

let ela_gensym_cnt = ref 0

let ela_gensym () =
  let s = "%sym" ^ (string_of_int (!ela_gensym_cnt)) in
  incr ela_gensym_cnt;
  s

let rec ela_split_sort ctx sr =
  match sr with
  | ElaSrVar (a, n) ->
    (match ela_get_binding ctx a with
     | ElaBdSortAbb (sr') -> ela_split_sort ctx sr'
     | _ -> raise (Error "ela_split_sort"))
  | ElaSrInt -> (sr, ElaIdBool (true))
  | ElaSrBool -> (sr, ElaIdBool (true))
  | ElaSrSubset (a, sr1, pr1) ->
    let (ssr1, pr11) = ela_split_sort ctx sr1 in
    (ssr1, ElaIdBinop (ElaBnAnd, pr11, pr1))

let ela_eqv_prop pr1 pr2 =
  ElaFmConj
    (ElaFmImply (pr1, ElaFmProp (pr2)), ElaFmImply (pr2, ElaFmProp (pr1)))

let rec ela_coerce ctx ty1 ty2 =
  match (ty1, ty2) with
  | (ElaTyVar (a1, n1), _) ->
    (match ela_get_binding ctx a1 with
     | ElaBdTypeAbb (ty1') -> ela_coerce ctx ty1' ty2
     | _ -> ElaFmBot)
  | (_, ElaTyVar (a2, n2)) ->
    (match ela_get_binding ctx a2 with
     | ElaBdTypeAbb (ty2') -> ela_coerce ctx ty1 ty2'
     | _ -> ElaFmBot)
  | (ElaTyInt (id1), ElaTyInt (id2)) -> ElaFmEqv (id1, id2)
  | (ElaTyBool (id1), ElaTyBool (id2)) -> ElaFmEqv (id1, id2)
  | (ElaTyUnit, ElaTyUnit) -> ElaFmTop
  | (ElaTyFloat, ElaTyFloat) -> ElaFmTop
  | (ElaTyVector (id1), ElaTyVector (id2)) -> ElaFmEqv (id1, id2)
  | (ElaTyMatrix (id11, id12), ElaTyMatrix (id21, id22)) ->
    ElaFmConj (ElaFmEqv (id11, id21), ElaFmEqv (id12, id22))
  | (ElaTyProduct (ty11, ty12), ElaTyProduct (ty21, ty22)) ->
    ElaFmConj (ela_coerce ctx ty11 ty21, ela_coerce ctx ty12 ty22)
  | (ElaTyArrow (ty11, ty12), ElaTyArrow (ty21, ty22)) ->
    ElaFmConj (ela_coerce ctx ty21 ty11, ela_coerce ctx ty12 ty22)
  | (ty1, ElaTyDepUni (a, sr2, ty21)) ->
    let fm =
      ela_coerce
        (ela_add_binding ctx a (ElaBdIndex sr2)) (ela_shift_type 1 ty1) ty21 in
    let (ssr2, pr2) = ela_split_sort ctx sr2 in
    ElaFmForall (a, ssr2, ElaFmImply (pr2, fm))
  | (ElaTyDepExi (a, sr1, ty11), ty2) ->
    let fm =
      ela_coerce
        (ela_add_binding ctx a (ElaBdIndex sr1)) ty11 (ela_shift_type 1 ty2) in
    let (ssr1, pr1) = ela_split_sort ctx sr1 in
    ElaFmForall (a, ssr1, ElaFmImply (pr1, fm))
  | (ElaTyDepUni (a, sr1, ty11), ty2) ->
    let s = ela_gensym () in
    let id = ElaIdId (s) in
    let fm = ela_coerce ctx (ela_subst_index_in_type_top id ty11) ty2 in
    let (ssr1, pr1) = ela_split_sort ctx sr1 in
    ElaFmExists
      (s, ssr1, ElaFmConj (ElaFmProp (ela_subst_index_in_index_top id pr1), fm))
  | (ty1, ElaTyDepExi (a, sr2, ty21)) ->
    let s = ela_gensym () in
    let id = ElaIdId (s) in
    let fm = ela_coerce ctx ty1 (ela_subst_index_in_type_top id ty21) in
    let (ssr2, pr2) = ela_split_sort ctx sr2 in
    ElaFmExists
      (s, ssr2, ElaFmConj (ElaFmProp (ela_subst_index_in_index_top id pr2), fm))
  | _ -> ElaFmBot

let rec ela_unwrap_type_abb ctx ty =
  match ty with
  | ElaTyVar (a, n) ->
    (match ela_get_binding ctx a with
     | ElaBdTypeAbb (ty') -> ela_unwrap_type_abb ctx ty'
     | _ -> raise (Error "ela_unwrap_type_abb"))
  | _ -> ty

let rec ela_solve ctx s fm =
  match fm with
  | ElaFmTop -> None
  | ElaFmBot -> None
  | ElaFmProp (pr1) -> None
  | ElaFmConj (fm1, fm2) ->
    let res1 = ela_solve ctx s fm1 in
    let res2 = ela_solve ctx s fm2 in
    if res1 != None then res1 else res2
  | ElaFmImply (pr1, fm2) -> ela_solve ctx s fm2
  | ElaFmEqv (id1, id2) ->
    if id1 = ElaIdId (s) then
      Some (id2)
    else if id2 = ElaIdId (s) then
      Some (id1)
    else
      None
  | ElaFmForall (a, sr1, fm1) ->
    let res1 = ela_solve (ela_add_binding ctx a (ElaBdIndex sr1)) s fm1 in
    (match res1 with
     | Some (id1) -> Some (ela_shift_index (-1) id1)
     | None -> None)
  | ElaFmExists (_, sr1, fm1) -> ela_solve ctx s fm1
  | ElaFmScope (fm1) ->
    let res1 = ela_solve (ela_add_name ctx "%scope") s fm1 in
    (match res1 with
     | Some (id1) -> Some (ela_shift_index (-1) id1)
     | None -> None)

let rec ela_eleminate ctx fm =
  match fm with
  | ElaFmTop -> (fm, [])
  | ElaFmBot -> (fm, [])
  | ElaFmProp (pr1) -> (fm, [])
  | ElaFmConj (fm1, fm2) ->
    let (fm1', subst1) = ela_eleminate ctx fm1 in
    let (fm2', subst2) = ela_eleminate ctx fm2 in
    (ElaFmConj (fm1', fm2'), List.append subst2 subst1)
  | ElaFmImply (pr1, fm2) ->
    let (fm2', subst2) = ela_eleminate ctx fm2 in
    (ElaFmImply (pr1, fm2'), subst2)
  | ElaFmEqv (id1, id2) -> (fm, [])
  | ElaFmForall (a, sr1, fm1) ->
    let (fm1', subst1) =
      ela_eleminate (ela_add_binding ctx a (ElaBdIndex sr1)) fm1 in
    (ElaFmForall (a, sr1, fm1'),
     List.map (fun (s, id) -> (s, ela_shift_index (-1) id)) subst1)
  | ElaFmExists (s, sr1, fm1) ->
    let (fm1', subst1) = ela_eleminate ctx fm1 in
    let oid = ela_solve ctx s fm1' in
    (match oid with
     | Some id ->
       let (ssr1, pr1) = ela_split_sort ctx sr1 in
       let fm1'' =
         ElaFmConj
           (ElaFmProp (ela_subst_index_in_index_top (ElaIdId s) pr1), fm1') in
       (ela_subst_index_in_formula_top
          id
          (ela_unsubst_id_in_formula_top
             (ela_ctx_length ctx)
             0 s
             (ela_shift_formula 1 fm1'')),
        (s, id) :: subst1)
     | None -> (ElaFmExists (s, sr1, fm1'), subst1))
  | ElaFmScope (fm1) ->
    let (fm1', subst1) = ela_eleminate (ela_add_name ctx "%scope") fm1 in
    (ElaFmScope (fm1'),
     List.map (fun (s, id) -> (s, ela_shift_index (-1) id)) subst1)

let rec

  ela_synthesize ctx ex =
  match ex with
  | ElaExVar (x, n) ->
    (match ela_get_binding ctx x with
     | ElaBdVar (tyx) -> (tyx, [], ElaFmTop)
     | _ -> raise (Error "ela_synthesize"))
  | ElaExInt (i) -> (ElaTyInt (ElaIdInt i), [], ElaFmTop)
  | ElaExBool (b) -> (ElaTyBool (ElaIdBool b), [], ElaFmTop)
  | ElaExUnit -> (ElaTyUnit, [], ElaFmTop)
  | ElaExFloat (f) -> (ElaTyFloat, [], ElaFmTop)
  | ElaExPair (ex1, ex2) ->
    let (ty1, free1, fm1) = ela_synthesize ctx ex1 in
    let (ty2, free2, fm2) = ela_synthesize ctx ex2 in
    (ElaTyProduct (ty1, ty2), List.append free2 free1, ElaFmConj (fm1, fm2))
  | ElaExIf (ex1, ex2, ex3) -> raise (Error "ela_synthesize")
  | ElaExLet (x, ex1, ex2) ->
    let (ty1, free1, fm1) = ela_synthesize ctx ex1 in
    let rec inner ty1 ctx cnt =
      let ty1 = ela_unwrap_type_abb ctx ty1 in
      (match ty1 with
       | ElaTyDepExi (a, sr1, ty11) ->
         inner ty11 (ela_add_binding ctx a (ElaBdIndex sr1)) (cnt + 1)
       | _ -> (ty1, ctx, cnt)) in
    let (ty1', ctx', cnt) = inner ty1 ctx 0 in
    let ctx'' = ela_add_binding ctx' x (ElaBdVar ty1') in
    let ex2' = ela_shift_expr_above cnt 1 ex2 in
    let (ty2, free2, fm2) = ela_synthesize ctx'' ex2' in
    let fm2' =
      List.fold_right
        (fun (s, sr) acc ->
           let (ssr, pr) = ela_split_sort ctx'' sr in
           ElaFmExists
             (s, ssr,
              ElaFmConj
                (ElaFmProp (ela_subst_index_in_index_top (ElaIdId s) pr), acc)))
        free2 fm2 in
    let (fm2'', subst) = ela_eleminate ctx' (ElaFmScope fm2') in
    let ty2' =
      List.fold_right
        (fun (s, id) acc ->
           ela_subst_index_in_type_top
             id
             (ela_unsubst_id_in_type_top
                (ela_ctx_length ctx)
                0 s
                (ela_shift_type 1 acc)))
        subst (ela_shift_type (-1) ty2) in
    let rec wrap ty1 ty2 fm2 ctx =
      (match ela_unwrap_type_abb ctx ty1 with
       | ElaTyDepExi (a, sr1, ty11) ->
         let (ssr1, pr1) = ela_split_sort ctx sr1 in
         let (ty2', fm2') =
           wrap ty11 ty2 fm2 (ela_add_binding ctx a (ElaBdIndex sr1)) in
         (ElaTyDepExi (a, sr1, ty2'),
          ElaFmForall (a, ssr1, ElaFmImply (pr1, fm2')))
       | _ -> (ty2, fm2)) in
    let (ty2'', fm2''') = wrap ty1 ty2' fm2'' ctx in
    (ty2'', free1, ElaFmConj (fm1, fm2'''))
  | ElaExApp (ex1, ex2) ->
    let (ty1, free1, fm1) = ela_synthesize ctx ex1 in
    let rec unwrap ty1 free1 =
      let ty1 = ela_unwrap_type_abb ctx ty1 in
      (match ty1 with
       | ElaTyDepUni (a, sr1, ty11) ->
         let s = ela_gensym () in
         let id = ElaIdId (s) in
         let ty11' = ela_subst_index_in_type_top id ty11 in
         unwrap ty11' ((s, sr1) :: free1)
       | _ -> (ty1, free1)) in
    let (ty1', free1') = unwrap ty1 free1 in
    (match ty1' with
     | ElaTyArrow (ty11, ty12) ->
       let fm2 = ela_check ctx ex2 ty11 free1' in
       (ty12, free1', ElaFmConj (fm1, fm2))
     | _ -> raise (Error "ela_synthesize"))
  | ElaExAbs (x, ex1) -> raise (Error "ela_synthesize")
  | ElaExFix (f, tyf, ex1) ->
    let fm1 =
      ela_check
        (ela_add_binding ctx f (ElaBdVar tyf)) ex1 (ela_shift_type 1 tyf) [] in
    (tyf, [], fm1)
  | ElaExDepAbs (a, sr1, ex1) -> raise (Error "ela_synthesize")
  | ElaExAs (ex1, ty1) ->
    let fm1 = ela_check ctx ex1 ty1 [] in
    (ty1, [], fm1)

and

  ela_check ctx ex ty free =
  let ty = ela_unwrap_type_abb ctx ty in
  match ty with
  | ElaTyDepUni (a, sr1, ty1) ->
    (match ex with
     | ElaExDepAbs (a', sr1', ex1) ->
       let (ssr1, pr1) = ela_split_sort ctx sr1 in
       let (ssr1', pr1') = ela_split_sort ctx sr1' in
       if ssr1 = ssr1' then
         let fm1 =
           ela_check (ela_add_binding ctx a (ElaBdIndex sr1)) ex1 ty1 free in
         ElaFmForall
           (a, ssr1, ElaFmConj (ela_eqv_prop pr1 pr1', ElaFmImply (pr1, fm1)))
       else
         raise (Error "ela_check")
     | _ ->
       let (ssr1, pr1) = ela_split_sort ctx sr1 in
       let ex1 = ela_shift_expr 1 ex in
       let fm1 =
         ela_check (ela_add_binding ctx a (ElaBdIndex sr1)) ex1 ty1 free in
       ElaFmForall (a, ssr1, ElaFmImply (pr1, fm1)))
  | _ ->
    match ex with
    | ElaExVar (x, n) ->
      let (ty', free', fm) = ela_synthesize ctx ex in
      if fm = ElaFmTop then
        let fm' = ela_coerce ctx ty' ty in
        List.fold_right
          (fun (s, sr) acc ->
             let (ssr, pr) = ela_split_sort ctx sr in
             ElaFmExists
               (s, ssr,
                ElaFmConj
                  (ElaFmProp (ela_subst_index_in_index_top (ElaIdId (s)) pr),
                   acc)))
          free' fm'
      else
        raise (Error "ela_check")
    | ElaExInt (i) ->
      let (ty', free', fm) = ela_synthesize ctx ex in
      if fm = ElaFmTop then
        let fm' = ela_coerce ctx ty' ty in
        List.fold_right
          (fun (s, sr) acc ->
             let (ssr, pr) = ela_split_sort ctx sr in
             ElaFmExists
               (s, ssr,
                ElaFmConj
                  (ElaFmProp (ela_subst_index_in_index_top (ElaIdId (s)) pr),
                   acc)))
          free' fm'
      else
        raise (Error "ela_check")
    | ElaExBool (b) ->
      let (ty', free', fm) = ela_synthesize ctx ex in
      if fm = ElaFmTop then
        let fm' = ela_coerce ctx ty' ty in
        List.fold_right
          (fun (s, sr) acc ->
             let (ssr, pr) = ela_split_sort ctx sr in
             ElaFmExists
               (s, ssr,
                ElaFmConj
                  (ElaFmProp (ela_subst_index_in_index_top (ElaIdId (s)) pr),
                   acc)))
          free' fm'
      else
        raise (Error "ela_check")
    (* TODO: some cases may need analysis with ElaTyDepExi *)
    | ElaExUnit ->
      if ty = ElaTyUnit then ElaFmTop else raise (Error "ela_check")
    | ElaExFloat (f) ->
      if ty = ElaTyFloat then ElaFmTop else raise (Error "ela_check")
    | ElaExPair (ex1, ex2) ->
      (match ty with
       | ElaTyProduct (ty1, ty2) ->
         let fm1 = ela_check ctx ex1 ty1 free in
         let fm2 = ela_check ctx ex2 ty2 free in
         ElaFmConj (fm1, fm2)
       | _ -> raise (Error "ela_check"))
    | ElaExIf (ex1, ex2, ex3) ->
      let (ty1, free1, fm1) = ela_synthesize ctx ex1 in
      let rec inner ty1 ctx cnt =
        let ty1 = ela_unwrap_type_abb ctx ty1 in
        (match ty1 with
         | ElaTyDepExi (a, sr1, ty11) ->
           inner ty11 (ela_add_binding ctx a (ElaBdIndex sr1)) (cnt + 1)
         | _ -> (ty1, ctx, cnt)) in
      let (ty1', ctx', cnt) = inner ty1 ctx 0 in
      let ty' = ela_shift_type cnt ty in
      let fm2 =
        ela_check ctx' (ela_shift_expr cnt ex2) ty' (List.append free1 free) in
      let fm3 =
        ela_check ctx' (ela_shift_expr cnt ex3) ty' (List.append free1 free) in
      (* TODO: may need to eliminate *)
      let rec wrap ty1 ctx fm =
        let ty1 = ela_unwrap_type_abb ctx ty1 in
        (match ty1 with
         | ElaTyDepExi (a, sr1, ty11) ->
           let (ssr1, pr1) = ela_split_sort ctx sr1 in
           let fm' = wrap ty11 (ela_add_binding ctx a (ElaBdIndex sr1)) fm in
           ElaFmForall (a, ssr1, ElaFmImply (pr1, fm'))
         | _ -> fm) in
      (match ty1' with
       | ElaTyBool (id1) ->
         let fm =
           ElaFmConj
             (fm1,
              ElaFmConj
                (ElaFmImply (id1, wrap ty1 ctx fm2),
                 ElaFmImply (ElaIdUnop (ElaUnNot, id1), wrap ty1 ctx fm3))) in
         List.fold_right
           (fun (s, sr) acc ->
              let (ssr, pr) = ela_split_sort ctx sr in
              ElaFmExists
                (s, ssr,
                 ElaFmConj
                   (ElaFmProp (ela_subst_index_in_index_top (ElaIdId (s)) pr),
                    acc)))
           free1 fm
       | _ -> raise (Error "ela_check"))
    | ElaExLet (x, ex1, ex2) ->
      let (ty1, free1, fm1) = ela_synthesize ctx ex1 in
      let rec inner ty1 ctx cnt =
        let ty1 = ela_unwrap_type_abb ctx ty1 in
        (match ty1 with
         | ElaTyDepExi (a, sr1, ty11) ->
           inner ty11 (ela_add_binding ctx a (ElaBdIndex sr1)) (cnt + 1)
         | _ -> (ty1, ctx, cnt)) in
      let (ty1', ctx', cnt) = inner ty1 ctx 0 in
      let ex2' = ela_shift_expr_above cnt 1 ex2 in
      let ctx'' = ela_add_binding ctx' x (ElaBdVar ty1') in
      let fm2 = ela_check ctx'' ex2' (ela_shift_type (cnt + 1) ty) (List.append free1 free) in
      (* TODO: may need to eliminate *)
      let rec wrap ty1 ctx fm =
        let ty1 = ela_unwrap_type_abb ctx ty1 in
        (match ty1 with
         | ElaTyDepExi (a, sr1, ty11) ->
           let (ssr1, pr1) = ela_split_sort ctx sr1 in
           let fm' = wrap ty11 (ela_add_binding ctx a (ElaBdIndex sr1)) fm in
           ElaFmForall (a, ssr1, ElaFmImply (pr1, fm'))
         | _ -> fm) in
      let fm2' = wrap ty1 ctx (ElaFmScope (fm2)) in
      List.fold_right
        (fun (s, sr) acc ->
           let (ssr, pr) = ela_split_sort ctx sr in
           ElaFmExists
             (s, ssr,
              ElaFmConj
                (ElaFmProp (ela_subst_index_in_index_top (ElaIdId (s)) pr),
                 acc)))
        free1 (ElaFmConj (fm1, fm2'))
    | ElaExApp (ex1, ex2) ->
      let (ty', free', fm) = ela_synthesize ctx ex in
      let fm' = ela_coerce ctx ty' ty in
      List.fold_right
        (fun (s, sr) acc ->
           let (ssr, pr) = ela_split_sort ctx sr in
           ElaFmExists
             (s, ssr,
              ElaFmConj
                (ElaFmProp (ela_subst_index_in_index_top (ElaIdId (s)) pr),
                 acc)))
        free' (ElaFmConj (fm, fm'))
    | ElaExAbs (x, ex1) ->
      (match ty with
       | ElaTyArrow (ty1, ty2) ->
         let fm1 =
           ela_check
             (ela_add_binding ctx x (ElaBdVar ty1))
             ex1
             (ela_shift_type 1 ty2)
             free in
         ElaFmScope (fm1)
       | _ -> raise (Error "ela_check"))
    | ElaExFix (f, tyf, ex1) ->
      let fm1 =
        ela_check
          (ela_add_binding ctx f (ElaBdVar tyf))
          ex1
          (ela_shift_type 1 tyf)
          free in
      let fm2 =
        ela_check
          (ela_add_binding ctx f (ElaBdVar tyf))
          (ElaExVar (0, 1 + ela_ctx_length ctx))
          (ela_shift_type 1 ty)
          free in
      ElaFmScope (ElaFmConj (fm1, fm2))
    | ElaExDepAbs (a, sr1, ex1) -> raise (Error "ela_check")
    | ElaExAs (ex1, ty1) ->
      let (ty', free', fm) = ela_synthesize ctx ex1 in
      let fm' = ela_coerce ctx ty' ty in
      List.fold_right
        (fun (s, sr) acc ->
           let (ssr, pr) = ela_split_sort ctx sr in
           ElaFmExists
             (s, ssr,
              ElaFmConj
                (ElaFmProp (ela_subst_index_in_index_top (ElaIdId (s)) pr),
                 acc)))
        free' (ElaFmConj (fm, fm'))
