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

let ela_prelude = [
  ("op+", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 2)), ElaTyInt (ElaIdVar (0, 2))), ElaTyInt (ElaIdBinop (ElaBnPlus, ElaIdVar (1, 2), ElaIdVar (0, 2))))))));
  ("op-", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 3)), ElaTyInt (ElaIdVar (0, 3))), ElaTyInt (ElaIdBinop (ElaBnMinus, ElaIdVar (1, 3), ElaIdVar (0, 3))))))));
  ("op*", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 4)), ElaTyInt (ElaIdVar (0, 4))), ElaTyInt (ElaIdBinop (ElaBnTimes, ElaIdVar (1, 4), ElaIdVar (0, 4))))))));
  ("op/", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 5)), ElaTyInt (ElaIdVar (0, 5))), ElaTyInt (ElaIdBinop (ElaBnDiv, ElaIdVar (1, 5), ElaIdVar (0, 5))))))));
  ("op<=", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 6)), ElaTyInt (ElaIdVar (0, 6))), ElaTyBool (ElaIdBinop (ElaBnLeq, ElaIdVar (1, 6), ElaIdVar (0, 6))))))));
  ("op<", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 7)), ElaTyInt (ElaIdVar (0, 7))), ElaTyBool (ElaIdBinop (ElaBnLt, ElaIdVar (1, 7), ElaIdVar (0, 7))))))));
  ("op>=", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 8)), ElaTyInt (ElaIdVar (0, 8))), ElaTyBool (ElaIdBinop (ElaBnGeq, ElaIdVar (1, 8), ElaIdVar (0, 8))))))));
  ("op>", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 9)), ElaTyInt (ElaIdVar (0, 9))), ElaTyBool (ElaIdBinop (ElaBnGt, ElaIdVar (1, 9), ElaIdVar (0, 9))))))));
  ("op!=", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 10)), ElaTyInt (ElaIdVar (0, 10))), ElaTyBool (ElaIdBinop (ElaBnNeq, ElaIdVar (1, 10), ElaIdVar (0, 10))))))));
  ("op=", (ElaTyDepUni ("a", ElaSrInt, ElaTyDepUni ("b", ElaSrInt, ElaTyArrow (ElaTyProduct (ElaTyInt (ElaIdVar (1, 11)), ElaTyInt (ElaIdVar (0, 11))), ElaTyBool (ElaIdBinop (ElaBnEq, ElaIdVar (1, 11), ElaIdVar (0, 11))))))));
  ("op+.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyFloat)));
  ("op-.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyFloat)));
  ("op*.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyFloat)));
  ("op/.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyFloat)));
  ("op>=.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyDepExi ("b", ElaSrBool, ElaTyBool (ElaIdVar (0, 15))))));
  ("op>.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyDepExi ("b", ElaSrBool, ElaTyBool (ElaIdVar (0, 16))))));
  ("op<=.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyDepExi ("b", ElaSrBool, ElaTyBool (ElaIdVar (0, 17))))));
  ("op<.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyDepExi ("b", ElaSrBool, ElaTyBool (ElaIdVar (0, 18))))));
  ("op!=.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyDepExi ("b", ElaSrBool, ElaTyBool (ElaIdVar (0, 19))))));
  ("op=.", (ElaTyArrow (ElaTyProduct (ElaTyFloat, ElaTyFloat), ElaTyDepExi ("b", ElaSrBool, ElaTyBool (ElaIdVar (0, 20))))));
  ("op&&", (ElaTyDepUni ("a", ElaSrBool, ElaTyDepUni ("b", ElaSrBool, ElaTyArrow (ElaTyProduct (ElaTyBool (ElaIdVar (1, 22)), ElaTyBool (ElaIdVar (0, 22))), ElaTyBool (ElaIdBinop (ElaBnAnd, ElaIdVar (1, 22), ElaIdVar (0, 22))))))));
  ("op||", (ElaTyDepUni ("a", ElaSrBool, ElaTyDepUni ("b", ElaSrBool, ElaTyArrow (ElaTyProduct (ElaTyBool (ElaIdVar (1, 23)), ElaTyBool (ElaIdVar (0, 23))), ElaTyBool (ElaIdBinop (ElaBnOr, ElaIdVar (1, 23), ElaIdVar (0, 23))))))));
]

let ela_prelude_ctx =
  List.fold_left (fun ctx ele -> ela_add_binding ctx (fst ele) (ElaBdVar (snd ele))) ela_empty_ctx ela_prelude

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
    | ElaExIf (ex1, ex2, ex3) -> ElaExIf (walk c ex1, walk c ex2, walk c ex3)
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

let rec ela_find_id free s =
  match free with
  | (s', sr) :: rest -> if s = s' then sr else ela_find_id rest s
  | [] -> raise (Error "ela_find_id")

let rec ela_transform_index ctx id z3ctx free =
  match id with
  | ElaIdId (s) ->
    let sr = ela_find_id free s in
    (match sr with
     | ElaSrInt ->
       Z3.Arithmetic.Integer.mk_const z3ctx (Z3.Symbol.mk_string z3ctx s)
     | ElaSrBool ->
       Z3.Boolean.mk_const z3ctx (Z3.Symbol.mk_string z3ctx s)
     | _ -> raise (Error "ela_transform_index"))
  | ElaIdVar (a, n) ->
    (match ela_get_binding ctx a with
     | ElaBdIndex (sr) ->
       (match sr with
        | ElaSrInt ->
          Z3.Arithmetic.Integer.mk_const
            z3ctx (Z3.Symbol.mk_string z3ctx (ela_index_to_name ctx a))
        | ElaSrBool ->
          Z3.Boolean.mk_const
            z3ctx (Z3.Symbol.mk_string z3ctx (ela_index_to_name ctx a))
        | _ -> raise (Error "ela_transform_index"))
     | _ -> raise (Error "ela_transform_index"))
  | ElaIdInt (i) -> Z3.Arithmetic.Integer.mk_numeral_i z3ctx i
  | ElaIdBool (b) ->
    if b then Z3.Boolean.mk_true z3ctx else Z3.Boolean.mk_false z3ctx
  | ElaIdBinop (bop, id1, id2) ->
    let res1 = ela_transform_index ctx id1 z3ctx free in
    let res2 = ela_transform_index ctx id2 z3ctx free in
    (match bop with
     | ElaBnPlus -> Z3.Arithmetic.mk_add z3ctx [res1; res2]
     | ElaBnMinus -> Z3.Arithmetic.mk_sub z3ctx [res1; res2]
     | ElaBnTimes -> Z3.Arithmetic.mk_mul z3ctx [res1; res2]
     | ElaBnDiv -> Z3.Arithmetic.mk_div z3ctx res1 res2
     | ElaBnLeq -> Z3.Arithmetic.mk_le z3ctx res1 res2
     | ElaBnLt -> Z3.Arithmetic.mk_lt z3ctx res1 res2
     | ElaBnGeq -> Z3.Arithmetic.mk_ge z3ctx res1 res2
     | ElaBnGt -> Z3.Arithmetic.mk_gt z3ctx res1 res2
     | ElaBnNeq -> Z3.Boolean.mk_not z3ctx (Z3.Boolean.mk_eq z3ctx res1 res2)
     | ElaBnEq -> Z3.Boolean.mk_eq z3ctx res1 res2
     | ElaBnAnd -> Z3.Boolean.mk_and z3ctx [res1; res2]
     | ElaBnOr -> Z3.Boolean.mk_or z3ctx [res1; res2])
  | ElaIdUnop (uop, id1) ->
    let res1 = ela_transform_index ctx id1 z3ctx free in
    (match uop with
     | ElaUnNot -> Z3.Boolean.mk_not z3ctx res1)

let rec ela_transform_formula ctx fm z3ctx free =
  match fm with
  | ElaFmTop -> Z3.Boolean.mk_true z3ctx
  | ElaFmBot -> Z3.Boolean.mk_false z3ctx
  | ElaFmProp (pr1) -> ela_transform_index ctx pr1 z3ctx free
  | ElaFmConj (fm1, fm2) ->
    let res1 = ela_transform_formula ctx fm1 z3ctx free in
    let res2 = ela_transform_formula ctx fm2 z3ctx free in
    Z3.Boolean.mk_and z3ctx [res1; res2]
  | ElaFmImply (pr1, fm2) ->
    let res1 = ela_transform_index ctx pr1 z3ctx free in
    let res2 = ela_transform_formula ctx fm2 z3ctx free in
    Z3.Boolean.mk_implies z3ctx res1 res2
  | ElaFmEqv (id1, id2) ->
    let res1 = ela_transform_index ctx id1 z3ctx free in
    let res2 = ela_transform_index ctx id2 z3ctx free in
    Z3.Boolean.mk_eq z3ctx res1 res2
  | ElaFmForall (a, sr1, fm1) ->
    let (_, a') = ela_pick_fresh_name ctx a in
    let ctx' = ela_add_binding ctx a' (ElaBdIndex sr1) in
    let res1 =
      ela_transform_formula
        ctx' fm1 z3ctx
        (List.map (fun (s, sr) -> (s, ela_shift_sort 1 sr)) free) in
    (match sr1 with
     | ElaSrInt ->
       Z3.Quantifier.expr_of_quantifier
         (Z3.Quantifier.mk_forall_const
            z3ctx
            [Z3.Arithmetic.Integer.mk_const
               z3ctx (Z3.Symbol.mk_string z3ctx a')]
            res1 None [] [] None None)
     | ElaSrBool ->
       Z3.Quantifier.expr_of_quantifier
         (Z3.Quantifier.mk_forall_const
            z3ctx
            [Z3.Boolean.mk_const z3ctx (Z3.Symbol.mk_string z3ctx a')]
            res1 None [] [] None None)
     | _ -> raise (Error "ela_transform_formula"))
  | ElaFmExists (s, sr1, fm1) ->
    let res1 = ela_transform_formula ctx fm1 z3ctx ((s, sr1) :: free) in
    (match sr1 with
     | ElaSrInt ->
       Z3.Quantifier.expr_of_quantifier
         (Z3.Quantifier.mk_exists_const
            z3ctx
            [Z3.Arithmetic.Integer.mk_const
               z3ctx (Z3.Symbol.mk_string z3ctx s)]
            res1 None [] [] None None)
     | ElaSrBool ->
       Z3.Quantifier.expr_of_quantifier
         (Z3.Quantifier.mk_exists_const
            z3ctx
            [Z3.Boolean.mk_const
               z3ctx (Z3.Symbol.mk_string z3ctx s)]
            res1 None [] [] None None)
     | _ -> raise (Error "ela_transform_formula"))
  | ElaFmScope (fm1) ->
    ela_transform_formula
      (ela_add_name ctx "%scope")
      fm1
      z3ctx
      (List.map (fun (s, sr) -> (s, ela_shift_sort 1 sr)) free)

let ela_string_of_binop bop =
  match bop with
  | ElaBnPlus -> "+"
  | ElaBnMinus -> "-"
  | ElaBnTimes -> "*"
  | ElaBnDiv -> "/"
  | ElaBnLeq -> "<="
  | ElaBnLt -> "<"
  | ElaBnGeq -> ">="
  | ElaBnGt -> ">"
  | ElaBnNeq -> "!="
  | ElaBnEq -> "="
  | ElaBnAnd -> "&&"
  | ElaBnOr -> "||"

let ela_string_of_unop uop =
  match uop with
  | ElaUnNot -> "~"

let rec ela_string_of_index ctx id =
  match id with
  | ElaIdId (s) -> s
  | ElaIdVar (a, n) -> ela_index_to_name ctx a
  | ElaIdInt (i) -> string_of_int i
  | ElaIdBool (b) -> if b then "true" else "false"
  | ElaIdBinop (bop, id1, id2) -> "(" ^ (ela_string_of_index ctx id1) ^ " " ^ (ela_string_of_binop bop) ^ " " ^ (ela_string_of_index ctx id2) ^ ")"
  | ElaIdUnop (uop, id1) -> "(" ^ (ela_string_of_unop uop) ^ " " ^ (ela_string_of_index ctx id1) ^ ")"

let rec ela_string_of_sort ctx sr =
  match sr with
  | ElaSrVar (a, n) -> ela_index_to_name ctx a
  | ElaSrInt -> "int"
  | ElaSrBool -> "bool"
  | ElaSrSubset (a, sr1, pr1) -> "{ " ^ a ^ " : " ^ (ela_string_of_sort ctx sr1) ^ " | " ^ (ela_string_of_index (ela_add_name ctx a) pr1) ^ " }"

let rec ela_string_of_type ctx ty =
  match ty with
  | ElaTyVar (a, n) -> ela_index_to_name ctx a
  | ElaTyInt (id1) -> "int(" ^ (ela_string_of_index ctx id1) ^ ")"
  | ElaTyBool (id1) -> "bool(" ^ (ela_string_of_index ctx id1) ^ ")"
  | ElaTyUnit -> "unit"
  | ElaTyFloat -> "float"
  | ElaTyVector (id1) -> "vec(" ^ (ela_string_of_index ctx id1) ^ ")"
  | ElaTyMatrix (id1, id2) -> "mat(" ^ (ela_string_of_index ctx id1) ^ ", " ^ (ela_string_of_index ctx id2) ^ ")"
  | ElaTyProduct (ty1, ty2) -> "(" ^ (ela_string_of_type ctx ty1) ^ " * " ^ (ela_string_of_type ctx ty2) ^ ")"
  | ElaTyArrow (ty1, ty2) -> "(" ^ (ela_string_of_type ctx ty1) ^ " -> " ^ (ela_string_of_type ctx ty2) ^ ")"
  | ElaTyDepUni (a, sr1, ty1) ->
    let (ctx', a') = ela_pick_fresh_name ctx a in
    "(pi " ^ a' ^ ": "  ^ (ela_string_of_sort ctx sr1) ^ ". " ^ (ela_string_of_type ctx' ty1) ^ ")"
  | ElaTyDepExi (a, sr1, ty1) ->
    let (ctx', a') = ela_pick_fresh_name ctx a in
    "(sig " ^ a' ^ ": " ^ (ela_string_of_sort ctx sr1) ^ ". " ^ (ela_string_of_type ctx' ty1) ^ ")"

let rec ela_string_of_expr ctx ex =
  match ex with
  | ElaExVar (x, n) -> ela_index_to_name ctx x
  | ElaExInt (i) -> string_of_int i
  | ElaExBool (b) -> if b then "true" else "false"
  | ElaExUnit -> "()"
  | ElaExFloat (f) -> string_of_float f
  | ElaExPair (ex1, ex2) -> "(" ^ (ela_string_of_expr ctx ex1) ^ ", " ^ (ela_string_of_expr ctx ex2) ^ ")"
  | ElaExIf (ex1, ex2, ex3) -> "(if " ^ (ela_string_of_expr ctx ex1) ^ " then " ^ (ela_string_of_expr ctx ex2) ^ " else " ^ (ela_string_of_expr ctx ex3) ^ ")"
  | ElaExLet (x, ex1, ex2) -> "(let " ^ x ^ " = " ^ (ela_string_of_expr ctx ex1) ^ " in " ^ (ela_string_of_expr (ela_add_name ctx x) ex2) ^ ")"
  | ElaExApp (ex1, ex2) -> "[" ^ (ela_string_of_expr ctx ex1) ^ " " ^ (ela_string_of_expr ctx ex2) ^ "]"
  | ElaExAbs (x, ex1) ->
    let (ctx', x') = ela_pick_fresh_name ctx x in
    "(lam " ^ x' ^ ". " ^ (ela_string_of_expr ctx' ex1) ^ ")"
  | ElaExFix (f, tyf, ex1) -> "(fix " ^ f ^ ": " ^ (ela_string_of_type ctx tyf) ^ ". " ^ (ela_string_of_expr (ela_add_name ctx f) ex1) ^ ")"
  | ElaExDepAbs (a, sr1, ex1) ->
    let (ctx', a') = ela_pick_fresh_name ctx a in
    "(dep " ^ a' ^ ":" ^ (ela_string_of_sort ctx sr1) ^ "." ^ (ela_string_of_expr ctx' ex1) ^ ")"
  | ElaExAs (ex1, ty1) -> "(" ^ (ela_string_of_expr ctx ex1) ^ " : " ^ (ela_string_of_type ctx ty1) ^ ")"

let rec ela_string_of_formula ctx fm =
  match fm with
  | ElaFmTop -> "true"
  | ElaFmBot -> "false"
  | ElaFmProp (pr1) -> ela_string_of_index ctx pr1
  | ElaFmConj (fm1, fm2) -> "(" ^ (ela_string_of_formula ctx fm1) ^ " /\\ " ^ (ela_string_of_formula ctx fm2) ^ ")"
  | ElaFmImply (pr1, fm2) -> "(" ^ (ela_string_of_index ctx pr1) ^ " => " ^ (ela_string_of_formula ctx fm2) ^ ")"
  | ElaFmEqv (id1, id2) -> "(" ^ (ela_string_of_index ctx id1) ^ " = " ^ (ela_string_of_index ctx id2) ^ ")"
  | ElaFmForall (a, sr1, fm1) -> "(forall " ^ a ^ ":" ^ (ela_string_of_sort ctx sr1) ^ ". " ^ (ela_string_of_formula (ela_add_name ctx a) fm1) ^ ")"
  | ElaFmExists (s, sr1, fm1) -> "(exists " ^ s ^ ":" ^ (ela_string_of_sort ctx sr1) ^ ". " ^ (ela_string_of_formula ctx fm1) ^ ")"
  | ElaFmScope (fm1) -> ela_string_of_formula (ela_add_name ctx "%scope") fm1

let ela_string_of_command ctx cmd =
  match cmd with
  | ElaCmdEval (ex) -> (ela_string_of_expr ctx ex) ^ ";"
  | ElaCmdVal (x, ex1) -> "val " ^ x ^ " = " ^ (ela_string_of_expr ctx ex1) ^ ";"
  | ElaCmdVar (x, ty1) -> "declare " ^ x ^ " : " ^ (ela_string_of_type ctx ty1) ^ ";"
  | ElaCmdSortAbb (a, sr1) -> "sort " ^ a ^ " = " ^ (ela_string_of_sort ctx sr1) ^ ";"
  | ElaCmdTypeAbb (a, ty1) -> "type " ^ a ^ " = " ^ (ela_string_of_type ctx ty1) ^ ";"

let ela_gentmp_cnt = ref 0

let ela_gentmp () =
  let s = "%tmp" ^ (string_of_int (!ela_gentmp_cnt)) in
  incr ela_gentmp_cnt;
  s

let rec ela_convert_expr ctx ex =
  match ex with
  | ElaExVar (x, n) -> ex
  | ElaExInt (i) -> ex
  | ElaExBool (b) -> ex
  | ElaExUnit -> ex
  | ElaExFloat (f) -> ex
  | ElaExPair (ex1, ex2) ->
    let x1 = ela_gentmp () in
    let x2 = ela_gentmp () in
    ElaExLet
      (x1,
       ela_convert_expr ctx ex1,
       ElaExLet
         (x2,
          ela_convert_expr (ela_add_name ctx x1) (ela_shift_expr 1 ex2),
          ElaExPair
            (ElaExVar (1, 2 + ela_ctx_length ctx),
             ElaExVar (0, 2 + ela_ctx_length ctx))))
  | ElaExIf (ex1, ex2, ex3) ->
    let x1 = ela_gentmp () in
    ElaExLet
      (x1,
       ela_convert_expr ctx ex1,
       ElaExIf
         (ElaExVar (0, 1 + ela_ctx_length ctx),
          ela_convert_expr (ela_add_name ctx x1) (ela_shift_expr 1 ex2),
          ela_convert_expr (ela_add_name ctx x1) (ela_shift_expr 1 ex3)))
  | ElaExLet (x, ex1, ex2) ->
    ElaExLet
      (x,
       ela_convert_expr ctx ex1,
       ela_convert_expr (ela_add_name ctx x) ex2)
  | ElaExApp (ex1, ex2) ->
    let x1 = ela_gentmp () in
    let x2 = ela_gentmp () in
    ElaExLet
      (x1,
       ela_convert_expr ctx ex1,
       ElaExLet
         (x2,
          ela_convert_expr (ela_add_name ctx x1) (ela_shift_expr 1 ex2),
          ElaExApp
            (ElaExVar (1, 2 + ela_ctx_length ctx),
             ElaExVar (0, 2 + ela_ctx_length ctx))))
  | ElaExAbs (x, ex1) ->
    let x1 = ela_gentmp () in
    ElaExAbs
      (x,
       ElaExLet
         (x1,
          ElaExVar (0, 1 + ela_ctx_length ctx),
          ela_convert_expr
            (ela_add_name (ela_add_name ctx x) x1)
            (ela_shift_expr_above 1 1 ex1)))
  | ElaExFix (f, tyf, ex1) ->
    ElaExFix (f, tyf, ela_convert_expr (ela_add_name ctx f) ex1)
  | ElaExDepAbs (a, sr1, ex1) ->
    ElaExDepAbs (a, sr1, ela_convert_expr (ela_add_name ctx a) ex1)
  | ElaExAs (ex1, ty1) ->
    ElaExAs (ela_convert_expr ctx ex1, ty1)
