open Support.Pervasive
open Support.Error
open Format

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
  | NameBind
  | BdType of ty
  | BdSort of sort
  | BdProp of prop

type context = (string * binding) list

let empty_ctx = []

let ctx_length ctx = List.length ctx

let add_binding ctx x bind = (x,bind)::ctx

let add_name ctx x = add_binding ctx x NameBind

let rec is_name_bound ctx x =
  match ctx with
      [] -> false
    | (y,_)::rest ->
        if y=x then true
        else is_name_bound rest x

let rec pick_freshname ctx x =
  if is_name_bound ctx x then pick_freshname ctx (x^"'")
  else ((x,NameBind)::ctx), x

let index2name ctx x =
  try
    let (xn,_) = List.nth ctx x in
    xn
  with Failure _ ->
    let msg =
      Printf.sprintf "Variable lookup failure: offset: %d, ctx size: %d" in
    error (msg x (List.length ctx))

let rec name2index ctx x =
  match ctx with
      [] -> error ("Identifier " ^ x ^ " is unbound")
    | (y,_)::rest ->
        if y=x then 0
        else 1 + (name2index rest x)

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

let subst_index_in_index j s id =
  idmap
    (fun j a n -> if a = j then shift_index j s else IdVar (a, n))
    j id

let subst_index_in_index_top s id =
  shift_index (-1) (subst_index_in_index 0 (shift_index 1 s) id)

let subst_index_in_prop j s pr =
  prmap
    (fun j id -> subst_index_in_index j s id)
    j pr

let subst_index_in_prop_top s pr =
  shift_prop (-1) (subst_index_in_prop 0 (shift_index 1 s) pr)

let subst_index_in_sort j s sr =
  srmap
    (fun j pr -> subst_index_in_prop j s pr)
    j sr

let subst_index_in_sort_top s sr =
  shift_sort (-1) (subst_index_in_sort 0 (shift_index 1 s) sr)

let subst_index_in_type j s ty =
  tymap
    (fun j id -> subst_index_in_index j s id)
    (fun j sr -> subst_index_in_sort j s sr)
    j ty

let subst_index_in_type_top s ty =
  shift_type (-1) (subst_index_in_type 0 (shift_index 1 s) ty)

let subst_index_in_term j s tm =
  tmmap
    (fun j x n -> TmVar (x, n))
    (fun j ty -> subst_index_in_type j s ty)
    (fun j id -> subst_index_in_index j s id)
    (fun j sr -> subst_index_in_sort j s sr)
    j tm

let subst_index_in_term_top s tm =
  shift_term (-1) (subst_index_in_term 0 (shift_index 1 s) tm)

let shift_binding d bd =
  match bd with
  | NameBind -> NameBind
  | BdType (ty) -> BdType (shift_type d ty)
  | BdSort (sr) -> BdSort (shift_sort d sr)
  | BdProp (pr) -> BdProp (shift_prop d pr)

let rec get_binding ctx i =
  try
    let (_,bind) = List.nth ctx i in
    shift_binding (i+1) bind
  with Failure _ ->
    let msg =
      Printf.sprintf "Variable lookup failure: offset: %d, ctx size: %d" in
    error (msg i (List.length ctx))

(* ---------------------------------------------------------------------- *)
(* Printing *)

let obox0() = open_hvbox 0
let obox() = open_hvbox 2
let cbox() = close_box()
let break() = print_break 0 0

let small t =
  match t with
    TmVar(_,_) -> true
  | _ -> false

(* let rec printty_Type outer ctx tyT = match tyT with
      tyT -> printty_ArrowType outer ctx tyT

and printty_ArrowType outer ctx  tyT = match tyT with
    TyArrow(tyT1,tyT2) ->
      obox0();
      printty_AType false ctx tyT1;
      if outer then pr " ";
      pr "->";
      if outer then print_space() else break();
      printty_ArrowType outer ctx tyT2;
      cbox()
  | tyT -> printty_AType outer ctx tyT

and printty_ProductType outer ctx tyT = match tyT with
    TyProduct(tyT1, tyT2) ->


and printty_AType outer ctx tyT = match tyT with
  | TyBool -> pr "Bool"
  | TyUnit -> pr "Unit"
  | TyInt -> pr "Int"
  | tyT -> pr "("; printty_Type outer ctx tyT; pr ")"

let printty ctx tyT = printty_Type true ctx tyT *)

let printty_Type outer ctx tyT = pr "T"

let prints_Sort outer ctx srS = pr "S"

let printty ctx tyT = printty_Type true ctx tyT

let rec printtm_Term outer ctx t = match t with
    TmIf(t1, t2, t3) ->
       obox0();
       pr "if ";
       printtm_Term false ctx t1;
       print_space();
       pr "then ";
       printtm_Term false ctx t2;
       print_space();
       pr "else ";
       printtm_Term false ctx t3;
       cbox()
  | TmAbs(x,tyT1,t2) ->
      (let (ctx',x') = (pick_freshname ctx x) in
         obox(); pr "lambda ";
         pr x'; pr ":"; printty_Type false ctx tyT1; pr ".";
         if (small t2) && not outer then break() else print_space();
         printtm_Term outer ctx' t2;
         cbox())
  | TmLet(x, t1, t2) ->
       obox0();
       pr "let "; pr x; pr " = ";
       printtm_Term false ctx t1;
       print_space(); pr "in"; print_space();
       printtm_Term false (add_name ctx x) t2;
       cbox()
  | TmFix(x,tyT1,t1) ->
       obox();
       pr "fix ";
       pr x;
       pr ":";
       printty_Type false ctx tyT1;
       pr ".";
       printtm_Term false ctx t1;
       cbox()
  | t -> printtm_AppTerm outer ctx t

and printtm_AppTerm outer ctx t = match t with
    TmApp(t1, t2) ->
      obox0();
      printtm_AppTerm false ctx t1;
      print_space();
      printtm_ATerm false ctx t2;
      cbox()
  | t -> printtm_ATerm outer ctx t

and printtm_ATerm outer ctx t = match t with
  | TmBool(true) -> pr "true"
  | TmBool(false) -> pr "false"
  | TmInt(i) -> pr (string_of_int i)
  | TmVar(x,n) ->
      if ctx_length ctx = n then
        pr (index2name ctx x)
      else
        pr ("[bad index: " ^ (string_of_int x) ^ "/" ^ (string_of_int n)
            ^ " in {"
            ^ (List.fold_left (fun s (x,_) -> s ^ " " ^ x) "" ctx)
            ^ " }]")
  | TmUnit -> pr "unit"
  | t -> pr "("; printtm_Term outer ctx t; pr ")"

let printtm ctx t = printtm_Term true ctx t
