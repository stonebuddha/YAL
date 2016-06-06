open Support.Pervasive
open Support.Error
open Format
open Lacaml.D

type index =
  | IdVar of int * int
  | IdInt of int
  | IdAdd of index * index
  | IdSub of index * index
  | IdMul of index * index
  | IdDiv of index * index

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
  | TyFloat
  | TyUnit
  | TyProduct of ty * ty
  | TyArrow of ty * ty
  | TyDepUni of string * sort * ty
  | TyDepExi of string * sort * ty
  | TyVector of index
  | TyMatrix of index * index

type pat =
  | PtWild
  | PtVar of string
  | PtInt of int
  | PtBool of bool
  | PtUnit
  | PtPair of pat * pat

type term =
  | TmVar of int * int
  | TmInt of int
  | TmBool of bool
  | TmFloat of float
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
  | TmDepPair of index * term * ty
  | TmDepLet of string * string * term * term
  | TmVector of term array
  | TmMatrix of term array array

type formula =
  | FmVar of int
  | FmIntConst of int
  | FmAdd of formula * formula
  | FmSub of formula * formula
  | FmMul of formula * formula
  | FmDiv of formula * formula
  | FmTrue
  | FmFalse
  | FmAnd of formula list
  | FmOr of formula list
  | FmNot of formula
  | FmLe of formula * formula
  | FmUni of (int list) * formula
  | FmExi of (int list) * formula
  | FmEq of formula * formula
  | FmImply of formula * formula

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
    | TmFloat(f) as tm -> tm
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
    | TmDepPair (id, tm1, ty) -> TmDepPair (onindex c id, walk c tm1, ontype c ty)
    | TmDepLet (a, x, tm1, tm2) -> TmDepLet (a, x, walk c tm1, walk (c + 2) tm2)
    | TmVector (tms) -> TmVector (Array.map (fun x -> walk c x) tms)
    | TmMatrix (tms) -> TmMatrix (Array.map (fun x -> Array.map (fun y -> walk c y) x) tms)
  in
    walk c tm

let tymap onindex onsort c ty =
  let rec walk c ty =
    match ty with
    | TyInt (id) -> TyInt (onindex c id)
    | TyBool as ty -> ty
    | TyFloat -> ty
    | TyUnit as ty -> ty
    | TyProduct (ty1, ty2) -> TyProduct (walk c ty1, walk c ty2)
    | TyArrow (ty1, ty2) -> TyArrow (walk c ty1, walk c ty2)
    | TyDepUni (x, sr, ty1) -> TyDepUni (x, onsort c sr, walk (c + 1) ty1)
    | TyDepExi (x, sr, ty1) -> TyDepExi (x, onsort c sr, walk (c + 1) ty1)
    | TyVector (id) -> TyVector(onindex c id)
    | TyMatrix (id1, id2) -> TyMatrix(onindex c id1, onindex c id2)
  in
    walk c ty

let idmap onvar c id =
  let rec walk c id =
    match id with
    | IdVar (a, n) -> onvar c a n
    | IdInt (i) as id -> id
    | IdAdd (id1, id2) -> IdAdd (walk c id1, walk c id2)
    | IdSub (id1, id2) -> IdSub (walk c id1, walk c id2)
    | IdMul (id1, id2) -> IdMul (walk c id1, walk c id2)
    | IdDiv (id1, id2) -> IdDiv (walk c id1, walk c id2)
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

let fmmap onvar onargs c fm =
  let rec walk c fm =
    match fm with
    | FmVar(i) -> onvar c i
    | FmIntConst(_) -> fm
    | FmAdd(fm1,fm2) -> FmAdd(walk c fm1, walk c fm2)
    | FmSub(fm1,fm2) -> FmSub(walk c fm1, walk c fm2)
    | FmMul(fm1,fm2) -> FmMul(walk c fm1, walk c fm2)
    | FmDiv(fm1,fm2) -> FmDiv(walk c fm1, walk c fm2)
    | FmTrue -> fm
    | FmFalse -> fm
    | FmAnd(args) -> FmAnd(List.map (fun fm1 -> walk c fm1) args)
    | FmOr(args) -> FmOr(List.map (fun fm1 -> walk c fm1) args)
    | FmNot(fm1) -> FmNot(walk c fm1)
    | FmUni(args,fm1) -> FmUni(List.map (fun x -> onargs (c+1) x) args, walk (c + 1) fm1)
    | FmExi(args,fm1) -> FmExi(List.map (fun x -> onargs (c+1) x) args, walk (c + 1) fm1)
    | FmEq(fm1, fm2) -> FmEq(walk c fm1, walk c fm2)
    | FmImply(fm1, fm2) -> FmImply(walk c fm1, walk c fm2)
    | FmLe(fm1, fm2) -> FmLe(walk c fm1, walk c fm2)
  in
    walk c fm

let shift_index_above d c id =
  idmap
    (fun c a n -> if a >= c then 
      if a + d < 0 then error "wrong format with +,-,*,/. Maybe you use second part of dependent pair without index." else IdVar (a + d, n + d) 
      else IdVar (a, n + d))
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

let shift_formula_above d c fm =
  fmmap
    (fun c a -> if a >= c then FmVar(a + d) else FmVar(a))
    (fun c a -> if a >= c then a + d else a)
    c fm

let shift_term d tm = shift_term_above d 0 tm

let shift_type d ty = shift_type_above d 0 ty

let shift_sort d sr = shift_sort_above d 0 sr

let shift_prop d pr = shift_prop_above d 0 pr

let shift_index d id = shift_index_above d 0 id

let shift_formula d fm = shift_formula_above d 0 fm

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

let get_type_from_context ctx i =
   match get_binding ctx i with
         BdType(tyT) -> tyT
     | _ -> error
       ("get_type_from_context: Wrong kind of binding for variable "
         ^ (index2name ctx i))

(* ---------------------------------------------------------------------- *)
(* Printing *)

(* let obox0() = open_hvbox 0
let obox() = open_hvbox 2
let cbox() = close_box()
let break() = print_break 0 0

let small t =
  match t with
    TmVar(_,_) -> true
  | _ -> false *)

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

(* let printty_Type outer ctx tyT = pr "T"

let printsr_Sort outer ctx srS = pr "S"

let printid_Index outer ctx idI = pr "I"

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
  | TmPair(t1,t2) ->
      obox();
      pr " (";
      printtm_Term false ctx t1;
      pr ",";
      printtm_Term false ctx t2;
      pr ") ";
      cbox();
  | TmDepAbs(x,sr,t1) ->
      (let (ctx',x') = (pick_freshname ctx x) in
         obox(); pr "lambda ";
         pr x'; pr ":"; printsr_Sort false ctx sr; pr ".";
         if (small t1) && not outer then break() else print_space();
         printtm_Term outer ctx' t1;
         cbox())
  | TmDepPair(id,t1,tyT) ->
      obox();
      pr " <";
      printid_Index false ctx id;
      pr ",";
      printtm_Term false ctx t1;
      pr ">:";
      printty_Type false ctx tyT;
      cbox();
  | TmDepLet(x1,x2,t1,t2) ->
      obox0();
      pr "let <"; pr x1; pr ","; pr x2; pr "> = ";
      printtm_Term false ctx t1;
      print_space(); pr "in"; print_space();
      let ctx' = add_name ctx x1 in
      let ctx'' = add_name ctx x2 in
      printtm_Term false ctx'' t2;
      cbox()
  | t -> printtm_AppTerm outer ctx t

and printtm_AppTerm outer ctx t = match t with
    TmApp(t1, t2) ->
      obox0();
      printtm_AppTerm false ctx t1;
      print_space();
      printtm_ATerm false ctx t2;
      cbox()
  | TmDepApp(t1, id) ->
      obox0();
      printtm_AppTerm false ctx t1;
      print_space();
      printid_Index false ctx id;
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

let printtm ctx t = printtm_Term true ctx t *)

let rec printid id = 
  match id with
  | IdVar(x,n) -> pr " [";print_int x;pr ",";print_int n;pr "] "
  | IdInt(i) -> pr " ";print_int i;pr " "
  | IdAdd(id1,id2) -> pr " (";printid id1;pr "+";printid id2;pr ") "
  | IdSub(id1,id2) -> pr " (";printid id1;pr "-";printid id2;pr ") "
  | IdMul(id1,id2) -> pr " (";printid id1;pr "*";printid id2;pr ") "
  | IdDiv(id1,id2) -> pr " (";printid id1;pr "/";printid id2;pr ") "

let rec printpr pro =
  match pro with
  | PrTrue -> pr " true "
  | PrFalse -> pr " false "
  | PrNeg(pro1) -> pr " (! ";printpr pro1;pr ") "
  | PrAnd(pro1, pro2) -> pr " (";printpr pro1;pr " & ";printpr pro2; pr ") "
  | PrOr(pro1, pro2) -> pr " (";printpr pro1;pr " || ";printpr pro2; pr ") "
  | PrLe(id1, id2) -> pr " (";printid id1;pr " <= ";printid id2; pr ") "

let rec printsr sr =
  match sr with
  | SrInt -> pr "int"
  | SrSubset(x,sr1,pro) -> pr " {";pr x;pr ":";printsr sr1;pr "|";printpr pro;pr "} "

let rec printty ty =
  match ty with
  | TyInt(id) -> pr " int(";printid id;pr ") "
  | TyBool -> pr " bool "
  | TyUnit -> pr " unit "
  | TyFloat -> pr " float "
  | TyProduct(ty1,ty2) -> pr " (";printty ty1;pr " * ";printty ty2;pr ") "
  | TyArrow(ty1,ty2) -> pr " (";printty ty1;pr " -> ";printty ty2;pr ") "
  | TyDepUni(x,sr,ty1) -> pr " (Pi ";pr x;pr ":";printsr sr;pr ".";printty ty1;pr ") "
  | TyDepExi(x,sr,ty1) -> pr " (Sigma ";pr x;pr ":";printsr sr;pr ".";printty ty1;pr ") "
  | TyVector(id) -> pr " Vector[";printid id;pr "] "
  | TyMatrix(id1, id2) -> pr " Matrix[";printid id1;pr "][";printid id2;pr "]"

let rec printtm t =
  match t with
  | TmVar(x,n) -> pr " [";print_int x;pr ",";print_int n;pr "] "
  | TmInt(i) -> pr " ";print_int i;pr " "
  | TmBool(b) -> pr " ";print_bool b;pr " "
  | TmFloat(f) -> pr " ";print_float f;pr " "
  | TmUnit -> pr " () "
  | TmPair(t1,t2) -> pr " (";printtm t1;pr ",";printtm t2;pr ") "
  | TmIf(t1,t2,t3) -> pr " if ";printtm t1;pr " then ";printtm t2;pr " else ";printtm t3;pr " "
  | TmCase(_,_) -> ()
  | TmAbs(x,ty,t1) -> pr " fn ";pr x;pr ":";printty ty;pr ".";printtm t1;pr " "
  | TmApp(t1,t2) -> pr " ";printtm t1;pr " ";printtm t2;pr " "
  | TmLet(x,t1,t2) -> pr " let ";pr x;pr " = ";printtm t1;pr " in ";printtm t2;pr " "
  | TmFix(x,ty,t1) -> pr " fix ";pr x;pr ":";printty ty;pr " ";printtm t1;pr " "
  | TmDepAbs(x,sr,t1) -> pr " lambda ";pr x;pr ":";printsr sr;pr ".";printtm t1;pr " "
  | TmDepApp(t1,id) -> pr " ";printtm t1;pr " ";printid id;pr " "
  | TmDepPair(id,t1,ty) -> pr " <";printtm t1;pr "> "
  | TmDepLet(x1,x2,t1,t2) -> pr " let <";pr x1;pr ",";pr x2;pr "> = ";printtm t1;pr " in ";printtm t2;pr " "
  | TmVector(tms) -> pr " [";Array.iter (fun x -> printtm x;pr ";") tms;pr "] "
  | TmMatrix(tms) -> pr " [";Array.iter (fun x -> Array.iter (fun y -> printtm y;pr ";") x;pr "\n") tms;pr "] "

let rec printfm fm =
  match fm with
  | FmVar(i) -> pr "[";pr (string_of_int i);pr "]"
  | FmIntConst(i) -> pr (string_of_int i)
  | FmAdd(fm1,fm2) -> pr "(";printfm fm1;pr " + ";printfm fm2;pr ")"
  | FmSub(fm1,fm2) -> pr "(";printfm fm1;pr " - ";printfm fm2;pr ")"
  | FmMul(fm1,fm2) -> pr "(";printfm fm1;pr " * ";printfm fm2;pr ")"
  | FmDiv(fm1,fm2) -> pr "(";printfm fm1;pr " / ";printfm fm2;pr ")"
  | FmTrue -> pr "true"
  | FmFalse -> pr "false"
  | FmAnd(fms) ->
      pr "(";
      let fst = List.hd fms in
      let last = List.tl fms in
      printfm fst;
      (match last with
      | [] -> error "formula AND should have at least two sub formulas"
      | _ -> List.iter (fun x -> pr " and ";printfm x) last;pr")")
  | FmOr(fms) ->
      pr "(";
      let fst = List.hd fms in
      let last = List.tl fms in
      printfm fst;
      (match last with
      | [] -> error "formula OR should have at least two sub formulas"
      | _ -> List.iter (fun x -> pr " or ";printfm x) last)
  | FmNot(fm1) ->
      pr "(not ";printfm fm1;pr ")"
  | FmLe(fm1,fm2) ->
      pr "(";printfm fm1;pr " <= ";printfm fm2;pr ")"
  | FmUni(l,fm1) ->
      pr "( for any ";
      List.iter (fun x -> pr "[";pr (string_of_int x);pr "]") l;
      pr ".";
      printfm fm1;
      pr ")"
  | FmExi(l,fm1) ->
      pr "( there exits ";
      List.iter (fun x -> pr "[";pr (string_of_int x);pr "]") l;
      pr ".";
      printfm fm1;
      pr ")"
  | FmEq(fm1,fm2) ->
      pr "(";printfm fm1;pr " = ";printfm fm2;pr ")"
  | FmImply(fm1,fm2) ->
      pr "(";printfm fm1;pr " => ";printfm fm2;pr ")"

(*-------------------------debugging--------------------------------*)



let rec print_raw_index id =
  match id with
  | IdVar(x,n) -> pr "IdVar(";print_int x;pr ",";print_int n;pr ")"
  | IdInt(i) -> pr "IdInt(";print_int i;pr ")"
  | IdAdd(id1,id2) -> pr "IdAdd(";print_raw_index id1;pr ",";print_raw_index id2;pr ")"
  | IdSub(id1,id2) -> pr "IdSub(";print_raw_index id1;pr ",";print_raw_index id2;pr ")"
  | IdMul(id1,id2) -> pr "IdMul(";print_raw_index id1;pr ",";print_raw_index id2;pr ")"
  | IdDiv(id1,id2) -> pr "IdDiv(";print_raw_index id1;pr ",";print_raw_index id2;pr ")"

let rec print_raw_prop pro =
  match pro with
  | PrTrue -> pr "PrTrue"
  | PrFalse -> pr "PrFalse"
  | PrNeg(pro1) -> pr "PrNeg(";print_raw_prop pro1;pr ")"
  | PrAnd(pro1, pro2) -> pr "PrAnd(";print_raw_prop pro1;pr ",";print_raw_prop pro2; pr ")"
  | PrOr(pro1, pro2) -> pr "PrOr(";print_raw_prop pro1;pr ",";print_raw_prop pro2; pr ")"
  | PrLe(id1, id2) -> pr "PrLe(";print_raw_index id1;pr ",";print_raw_index id2; pr ")"

let rec print_raw_sort sr =
  match sr with
  | SrInt -> pr "SrInt"
  | SrSubset(x,sr1,pro) -> pr "SrSubset(";pr x;pr ",";print_raw_sort sr1;pr ",";print_raw_prop pro;pr ")"

let rec print_raw_type ty =
  match ty with
  | TyInt(id) -> pr "TyInt(";print_raw_index id;pr ")"
  | TyBool -> pr "TyBool"
  | TyUnit -> pr "TyUnit"
  | TyFloat -> pr "TyFloat"
  | TyProduct(ty1,ty2) -> pr "TyProduct(";print_raw_type ty1;pr ",";print_raw_type ty2;pr ")"
  | TyArrow(ty1,ty2) -> pr "TyArrow(";print_raw_type ty1;pr ",";print_raw_type ty2;pr ")"
  | TyDepUni(x,sr,ty1) -> pr "TyDepUni(";pr x;pr ",";print_raw_sort sr;pr ",";print_raw_type ty1;pr ")"
  | TyDepExi(x,sr,ty1) -> pr "TyDepExi(";pr x;pr ",";print_raw_sort sr;pr ",";print_raw_type ty1;pr ")"
  | TyVector(id) -> pr "TyVector(";print_raw_index id;pr ")"
  | TyMatrix(id1,id2) -> pr "TyMatrix(";print_raw_index id1; pr ",";print_raw_index id2;pr ")"

let rec print_raw t =
  match t with
  | TmVar(x,n) -> pr "TmVar(";print_int x;pr ",";print_int n;pr ")"
  | TmInt(i) -> pr "TmInt(";print_int i; pr ")"
  | TmBool(b) -> pr "TmBool("; print_bool b; pr ")"
  | TmFloat(f) -> pr "TmFloat(";print_float f;pr ")"
  | TmUnit -> pr "TmUnit"
  | TmPair(t1,t2) -> pr "(";print_raw t1;pr ",";print_raw t2;pr ")"
  | TmIf(t1,t2,t3) -> pr "TmIf(";print_raw t1;pr ",";print_raw t2;pr ",";print_raw t3;pr ")"
  | TmCase(_,_) -> ()
  | TmAbs(x,ty,t1) -> pr "TmAbs(";pr x;pr ",";print_raw_type ty;pr ",";print_raw t1;pr ")"
  | TmApp(t1,t2) -> pr "TmApp(";print_raw t1;pr ",";print_raw t2;pr ")"
  | TmLet(x,t1,t2) -> pr "TmLet(";pr x;pr ",";print_raw t1;pr ",";print_raw t2;pr ")"
  | TmFix(x,ty,t1) -> pr "TmFix(";pr x;pr ",";print_raw_type ty;pr ",";print_raw t1;pr ")"
  | TmDepAbs(x,sr,t1) -> pr "TmDepAbs(";pr x;pr ",";print_raw_sort sr;pr ",";print_raw t1;pr ")"
  | TmDepApp(t1,id) -> pr "TmDepApp(";print_raw t1;pr ",";print_raw_index id;pr ")"
  | TmDepPair(id,t1,ty) -> pr "TmDepPair(";print_raw_index id;pr ",";print_raw t1;pr ",";print_raw_type ty;pr ")"
  | TmDepLet(x1,x2,t1,t2) -> pr "TmDepLet(";pr x1;pr ",";pr x2;pr ",";print_raw t1;pr ",";print_raw t2;pr ")"
  | TmVector(tms) -> pr "TmVector(";Array.iter (fun x -> print_raw x;pr ",") tms;pr ")"
  | TmMatrix(tms) -> pr "TmMatrix(";Array.iter (fun x -> pr "[";Array.iter (fun y -> printtm y;pr ",") x;pr "]") tms;pr ")"

let prelude = [
("op+", (TyDepUni ("a", SrInt, TyDepUni ("b", SrInt, TyArrow (TyProduct (TyInt (IdVar (1, 2)), TyInt (IdVar (0, 2))), TyInt (IdAdd (IdVar (1, 2), IdVar (0, 2))))))));
("op-", (TyDepUni ("a", SrInt, TyDepUni ("b", SrInt, TyArrow (TyProduct (TyInt (IdVar (1, 3)), TyInt (IdVar (0, 3))), TyInt (IdSub (IdVar (1, 3), IdVar (0, 3))))))));
("op*", (TyDepUni ("a", SrInt, TyDepUni ("b", SrInt, TyArrow (TyProduct (TyInt (IdVar (1, 4)), TyInt (IdVar (0, 4))), TyInt (IdMul (IdVar (1, 4), IdVar (0, 4))))))));
("op/", (TyDepUni ("a", SrInt, TyDepUni ("b", SrInt, TyArrow (TyProduct (TyInt (IdVar (1, 5)), TyInt (IdVar (0, 5))), TyInt (IdDiv (IdVar (1, 5), IdVar (0, 5))))))));
("iszero", (TyArrow (TyDepExi ("a", SrInt, TyInt (IdVar (0, 5))), TyBool)));
("vector_get", (TyDepUni("a", SrInt, TyDepUni("b", SrSubset("c", SrInt, 
  PrAnd(PrLe(IdInt(0), IdVar(0, 2)), PrNeg(PrLe(IdVar(1, 2), IdVar(0, 2))))), 
  TyArrow(TyProduct(TyVector(IdVar(1, 2)), TyInt(IdVar(0, 2))), TyFloat)))));
("vector_set", (TyDepUni("a", SrInt, TyDepUni("b", SrSubset("c", SrInt, 
  PrAnd(PrLe(IdInt(0), IdVar(0, 2)), PrNeg(PrLe(IdVar(1, 2), IdVar(0, 2))))),
  TyArrow(TyProduct(TyProduct(TyVector(IdVar(1, 2)), TyInt(IdVar(0, 2))), TyFloat), TyVector(IdVar(1, 2)))))));
("vector_append", (TyDepUni("a", SrInt, TyDepUni("b", SrInt, TyArrow(
  TyProduct(TyVector(IdVar(1, 2)), TyVector(IdVar(0, 2))), TyVector(IdAdd(IdVar(1, 2), IdVar(0, 2))))))));
("dot", (TyDepUni("a", SrInt, TyArrow(TyProduct(TyVector(IdVar(0, 1)), TyVector(IdVar(0, 1))), TyFloat))));
("gemv", (TyDepUni("a", SrInt, TyDepUni("b", SrInt, TyArrow(
  TyProduct(TyMatrix(IdVar(1, 2), IdVar(0, 2)), TyVector(IdVar(0, 2))), TyVector(IdVar(1, 2)))))));
("gemm", (TyDepUni("a", SrInt, TyDepUni("b", SrInt, TyDepUni("c", SrInt, TyArrow(
  TyProduct(TyMatrix(IdVar(2, 3), IdVar(1, 3)), TyMatrix(IdVar(1, 3), IdVar(0, 3))), TyMatrix(IdVar(2, 3), IdVar(0, 3))))))));
("transpose", (TyDepUni("a", SrInt, TyDepUni("b", SrInt, TyArrow(
  TyMatrix(IdVar(1, 2), IdVar(0, 2)), TyMatrix(IdVar(0, 2), IdVar(1, 2)))))));
("matrix_get", (TyDepUni("a", SrInt, TyDepUni("b", SrInt, TyDepUni("c", SrSubset("c1", SrInt,
  PrAnd(PrLe(IdInt(0), IdVar(0, 3)), PrNeg(PrLe(IdVar(2, 3), IdVar(0, 3))))), TyDepUni("d", SrSubset("d1", SrInt,
  PrAnd(PrLe(IdInt(0), IdVar(0, 3)), PrNeg(PrLe(IdVar(2, 3), IdVar(0, 3))))), TyArrow(
  TyProduct(TyProduct(TyMatrix(IdVar(3, 4), IdVar(2, 4)), TyInt(IdVar(1, 4))), TyInt(IdVar(0, 4))), TyFloat)))))));
("matrix_set", (TyDepUni("a", SrInt, TyDepUni("b", SrInt, TyDepUni("c", SrSubset("c1", SrInt,
  PrAnd(PrLe(IdInt(0), IdVar(0, 3)), PrNeg(PrLe(IdVar(2, 3), IdVar(0, 3))))), TyDepUni("d", SrSubset("d1", SrInt,
  PrAnd(PrLe(IdInt(0), IdVar(0, 3)), PrNeg(PrLe(IdVar(2, 3), IdVar(0, 3))))), TyArrow(
  TyProduct(TyProduct(TyProduct(TyMatrix(IdVar(3, 4), IdVar(2, 4)), TyInt(IdVar(1, 4))), TyInt(IdVar(0, 4))), TyFloat), 
  TyMatrix(IdVar(3, 4), IdVar(2, 4)))))))));
]

let prelude_ctx =
  List.fold_left (fun ctx ele -> add_binding ctx (fst ele) (BdType (snd ele))) empty_ctx prelude
