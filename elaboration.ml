open Elasyntax

exception TODO
exception Error of string

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

let ela_parse_file fn =
  let pi = open_in fn in
  let lexbuf = Lexing.from_channel pi in
  let e = Elaparser.prog Elalexer.read lexbuf in
  e ela_prelude_ctx

let _ = Z3.Log.open_ "z3.log"
let ela_z3cfg = ["timeout", "10000"]
let ela_z3ctx = Z3.mk_context ela_z3cfg
let ela_z3solver = Z3.Solver.mk_solver ela_z3ctx None

let ela_check_formula ctx fm =
  let res = ela_transform_formula ctx fm ela_z3ctx [] in
  print_string (Z3.Expr.to_string res); print_newline ();
  let _ = Z3.Solver.reset ela_z3solver in
  let _ = Z3.Solver.add ela_z3solver [res] in
  let q = Z3.Solver.check ela_z3solver [] in
  print_string "Z3 Solver says: ";
  print_string (Z3.Solver.string_of_status q);
  print_newline ()

let ela_process_cmd ctx cmd =
  print_string (ela_string_of_command ctx cmd); print_newline ();
  match cmd with
  | ElaCmdEval (ex1) ->
    let ex1' = ela_convert_expr ctx ex1 in
    let (ty, free, fm) = ela_synthesize ctx ex1' in
    let fm' =
      List.fold_right
        (fun (s, sr) acc ->
           let (ssr, pr) = ela_split_sort ctx sr in
           ElaFmExists
             (s, ssr,
              ElaFmConj
                (ElaFmProp
                   (ela_subst_index_in_index_top (ElaIdId (s)) pr),
                 acc)))
        free fm in
    let (fm'', subst) = ela_eleminate ctx fm' in
    let ty' =
      List.fold_right
        (fun (s, id) acc ->
           ela_subst_index_in_type_top
             id
             (ela_unsubst_id_in_type_top
                (ela_ctx_length ctx)
                0
                s
                (ela_shift_type 1 acc)))
        subst ty in
    print_string (ela_string_of_type ctx ty'); print_newline ();
    ela_check_formula ctx fm'';
    ctx
  | ElaCmdVal (x, ex1) ->
    let ex1' = ela_convert_expr ctx ex1 in
    let (ty, free, fm) = ela_synthesize ctx ex1' in
    let fm' =
      List.fold_right
        (fun (s, sr) acc ->
           let (ssr, pr) = ela_split_sort ctx sr in
           ElaFmExists
             (s, ssr,
              ElaFmConj
                (ElaFmProp
                  (ela_subst_index_in_index_top (ElaIdId (s)) pr),
                acc)))
        free fm in
    let (fm'', subst) = ela_eleminate ctx fm' in
    let ty' =
      List.fold_right
        (fun (s, id) acc ->
           ela_subst_index_in_type_top
             id
             (ela_unsubst_id_in_type_top
                (ela_ctx_length ctx)
                0
                s
                (ela_shift_type 1 acc)))
        subst ty in
    print_string (ela_string_of_type ctx ty'); print_newline ();
    ela_check_formula ctx fm'';
    ela_add_binding ctx x (ElaBdVar ty')
  | ElaCmdVar (x, ty1) -> ela_add_binding ctx x (ElaBdVar ty1)
  | ElaCmdSortAbb (a, sr1) -> ela_add_binding ctx a (ElaBdSortAbb sr1)
  | ElaCmdTypeAbb (a, ty1) -> ela_add_binding ctx a (ElaBdTypeAbb ty1)

let main () =
  let (cmds, _) = ela_parse_file "elab.f" in
  let _ = List.fold_left ela_process_cmd ela_prelude_ctx cmds in
  ()

let () = main ()
