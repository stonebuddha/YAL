type index =
  | IdVar of int * int
  | IdInt of int
  | IdAdd of index * index

type prop =
  | PrTrue
  | PrFalse
  | PrNeg of prop
  | PrAnd of prop * prop
  | PrOr of prop * prop
  | PrLe of index * index

type sort =
  | SrInt
  | SrSubset of string * sort * prop

type ty =
  | TyInt of index
  | TyBool
  | TyUnit
  | TyProduct of ty * ty
  | TyArrow of ty * ty
  | TyDepUni of string * sort * ty
  | TyDepExi of string * sort * ty

type pat =
  | PtWild
  | PtVar of int * int
  | PtInt of int
  | PtBool of bool
  | PtUnit
  | PtPair of pat * pat

type term =
  | TmVar of int * int
  | TmInt of int
  | TmBool of bool
  | TmUnit
  | TmPair of term * term
  | TmIf of term * term * term
  | TmCase of term * (pat * int * term) list
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLet of string * term * term
  | TmFix of string * ty * term
  | TmDepAbs of string * sort * term
  | TmDepApp of term * index
  | TmDepPair of index * sort * term
  | TmDepLet of string * string * term * term

type binding =
  | BdType of string * ty
  | BdSort of string * sort
  | BdProp of prop

type context = binding list

let empty_ctx = []

let ctx_length ctx = List.length ctx

let add_binding ctx bind = bind :: ctx

let tmmap onvar ontype onindex onsort c tm =
  let rec walk c tm =
    match tm with
    | TmVar (x, n) -> onvar c x n
    | TmInt (i) as tm -> tm
    | TmBool (b) as tm -> tm
    | TmUnit as tm -> tm
    | TmPair (tm1, tm2) -> TmPair (walk c tm1, walk c tm2)
    | TmIf (tm1, tm2, tm3) -> TmIf (walk c tm1, walk c tm2, walk c tm3)
    | TmCase (tm1, cases) -> TmCase (walk c tm1, List.map (fun (pt1, cnt1, tm1) -> (pt1, cnt1, walk (c + cnt1) tm1)) cases)
    | TmAbs (x, tyx, tm2) -> TmAbs (x, ontype c tyx, walk (c + 1) tm2)
    | TmApp (rator, rand) -> TmApp (walk c rator, walk c rand)
    | TmLet (x, tm1, tm2) -> TmLet (x, walk c tm1, walk (c + 1) tm2)
    | TmFix (f, tyf, tm1) -> TmFix (f, ontype c tyf, walk (c + 1) tm1)
    | TmDepAbs (a, sr, tm1) -> TmDepAbs (a, onsort c sr, walk (c + 1) tm1)
    | TmDepApp (tm1, id) -> TmDepApp (walk c tm1, onindex c id)
    | TmDepPair (id, sr, tm1) -> TmDepPair (onindex c id, onsort c sr, walk c tm1)
    | TmDepLet (a, x, tm1, tm2) -> TmDepLet (a, x, walk c tm1, walk (c + 2) tm2)
  in
    walk c tm

let tymap onindex onsort c ty =
  let rec walk c ty =
    match ty with
    | TyInt (id) -> TyInt (onindex c id)
    | TyBool as ty -> ty
    | TyUnit as ty -> ty
    | TyProduct (ty1, ty2) -> TyProduct (walk c ty1, walk c ty2)
    | TyArrow (ty1, ty2) -> TyArrow (walk c ty1, walk c ty2)
    | TyDepUni (a, sr, ty1) -> TyDepUni (a, onsort c sr, walk (c + 1) ty1)
    | TyDepExi (a, sr, ty1) -> TyDepExi (a, onsort c sr, walk (c + 1) ty1)
  in
    walk c ty

let idmap onvar c id =
  let rec walk c id =
    match id with
    | IdVar (a, n) -> onvar c a n
    | IdInt (i) as id -> id
    | IdAdd (id1, id2) -> IdAdd (walk c id1, walk c id2)
  in
    walk c id

let srmap onprop c sr =
  let rec walk c sr =
    match sr with
    | SrInt as sr -> sr
    | SrSubset (a, sr1, pr) -> SrSubset (a, sr1, onprop (c + 1) pr)
  in
    walk c sr

let prmap onindex c pr =
  let rec walk c pr =
    match pr with
    | PrTrue as pr -> pr
    | PrFalse as pr -> pr
    | PrNeg (pr1) -> PrNeg (walk c pr1)
    | PrAnd (pr1, pr2) -> PrAnd (walk c pr1, walk c pr2)
    | PrOr (pr1, pr2) -> PrOr (walk c pr1, walk c pr2)
    | PrLe (id1, id2) -> PrLe (onindex c id1, onindex c id2)
  in
    walk c pr

let shift_index_above d c id =
  idmap
    (fun c a n -> if a >= n then IdVar (a + d, n + d) else IdVar (a, n + d))
    c id

let shift_prop_above d c pr =
  prmap
    (shift_index_above d)
    c pr

let shift_sort_above d c sr =
  srmap
    (shift_prop_above d)
    c sr

let shift_type_above d c ty =
  tymap
    (shift_index_above d)
    (shift_sort_above d)
    c ty

let shift_term_above d c tm =
  tmmap
    (fun c x n -> if x >= c then TmVar (x + d, n + d) else TmVar (x, n + d))
    (shift_type_above d)
    (shift_index_above d)
    (shift_sort_above d)
    c tm

let shift_term d tm = shift_term_above d 0 tm

let shift_type d ty = shift_type_above d 0 ty

let shift_sort d sr = shift_sort_above d 0 sr

let shift_prop d pr = shift_prop_above d 0 pr

let shift_index d id = shift_index_above d 0 id

let subst_term_in_term j s tm =
  tmmap
    (fun j x n -> if x = j then shift_term j s else TmVar (x, n))
    (fun j ty -> ty)
    (fun j id -> id)
    (fun j sr -> sr)
    j tm

let subst_term_in_term_top s tm =
  shift_term (-1) (subst_term_in_term 0 (shift_term 1 s) tm)

let shift_binding d bd =
  match bd with
  | BdType (x, ty) -> BdType (x, shift_type d ty)
  | BdSort (a, sr) -> BdSort (a, shift_sort d sr)
  | BdProp (pr) -> BdProp (shift_prop d pr)

let get_binding ctx i = shift_binding (i + 1) (List.nth ctx i)
