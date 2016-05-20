open Syntax

type exp =
  | ExVar of int * int
  | ExInt of int
  | ExBool of bool
  | ExUnit
  | ExPair of exp * exp
  | ExIf of exp * exp * exp
  | ExCase of exp * (pat * exp) list
  | ExAbs of string * ty option * exp
  | ExApp of exp * exp
  | ExLet of string * exp * exp
  | ExFix of string * ty option * exp
  | ExAs of exp * ty

exception TODO
exception CannotSynthesize
exception CannotCheck

let shift_exp d ex = raise TODO

let eqtype ctx ty1 ty2 = raise TODO

let rec

synthesize ctx ex =

  match ex with
  | ExVar (x, n) ->
    (match get_binding ctx x with
    | BdType ty -> (ty, TmVar (x, n))
    | _ -> raise CannotSynthesize)
  | ExInt (i) -> (TyInt (IdInt (i)), TmInt (i))
  | ExBool (b) -> (TyBool, TmBool (b))
  | ExUnit -> (TyUnit, TmUnit)
  | ExPair (ex1, ex2) ->
    let syn1 = synthesize ctx ex1 in
    let syn2 = synthesize ctx ex2 in
      (TyProduct (fst syn1, fst syn2), TmPair (snd syn1, snd syn2))
  | ExIf (ex1, ex2, ex3) -> raise TODO
  | ExCase (ex1, cases) -> raise TODO
  | ExAbs (x, tyx, ex1) -> raise CannotSynthesize
  | ExApp (ex1, ex2) ->
    let syn1 = synthesize ctx ex1 in
    let syn2 = synthesize ctx ex2 in
      (match fst syn1 with
      | TyArrow (ty11, ty12) -> if ty11 = fst syn2 then (ty12, TmApp (snd syn1, snd syn2)) else raise CannotSynthesize
      | _ -> raise CannotSynthesize)
  | ExLet (x, ex1, ex2) ->
    let syn1 = synthesize ctx ex1 in
    let syn2 = synthesize (add_binding ctx x (BdType (fst syn1))) ex2 in
      (fst syn2, TmLet (x, snd syn1, snd syn2))
  | ExFix (f, tyf, ex1) -> raise TODO
  | ExAs (ex1, ty1) ->
    let tm1 = check ctx ex1 ty1 in
      (ty1, tm1)

and

check ctx ex ty =
  match ty with
  | TyDepUni (a, sr, ty1) ->
    let ch = check (add_binding ctx a (BdSort sr)) (shift_exp 1 ex) ty1 in
      TmDepAbs (a, sr, ch)
  | TyDepExi (_, _, _) -> raise TODO
  | _ ->
    match ex with
    | ExVar (x, n) ->
      let syn = synthesize ctx ex in
        if eqtype ctx ty (fst syn) then (snd syn) else raise CannotCheck
    | ExInt (i) ->
      let syn = synthesize ctx ex in
        if eqtype ctx ty (fst syn) then (snd syn) else raise CannotCheck
    | ExBool (b) ->
      if ty = TyBool then TmBool (b) else raise CannotCheck
    | ExUnit ->
      if ty = TyUnit then TmUnit else raise CannotCheck
    | ExPair (ex1, ex2) ->
      (match ty with
      | TyProduct (ty1, ty2) ->
        let ch1 = check ctx ex1 ty1 in
        let ch2 = check ctx ex2 ty2 in
          TmPair (ch1, ch2)
      | _ -> raise CannotCheck)
    | ExIf (ex1, ex2, ex3) -> raise TODO
    | ExCase (ex1, cases) -> raise TODO
    | ExAbs (x, None, ex1) ->
      (match ty with
      | TyArrow (ty1, ty2) ->
        let tm1 = check (add_binding ctx x (BdType ty1)) ex1 ty2 in
          TmAbs (x, ty, tm1)
      | _ -> raise CannotCheck)
    | ExAbs (x, Some tyx, ex1) ->
      (match ty with
      | TyArrow (ty1, ty2) -> raise TODO
      | _ -> raise CannotCheck)
    | ExApp (ex1, ex2) ->
      let syn = synthesize ctx ex in
        if eqtype ctx ty (fst syn) then (snd syn) else raise CannotCheck
    | ExLet (x, ex1, ex2) ->
      let syn1 = synthesize ctx ex1 in
      let ch2 = check (add_binding ctx x (BdType (fst syn1))) ex2 ty in
        TmLet (x, snd syn1, ch2)
    | ExFix (f, None, ex1) -> raise TODO
    | ExFix (f, Some tyf, ex1) -> raise TODO
    | ExAs (ex1, ty1) ->
      let syn1 = synthesize ctx ex1 in
        if eqtype ctx ty1 (fst syn1) then snd syn1 else raise CannotCheck
