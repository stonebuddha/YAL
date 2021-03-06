open Syntax
open Z3
open Z3.Boolean
open Z3.Arithmetic
open Z3.Solver
open Z3.Quantifier

let rec fm_to_z3 ctx names formula =
	match formula with
		| FmVar(i) ->
			let raw_name = (string_of_int) (names - i - 1) in
			let name = String.concat "_" ["x";raw_name] in
			(Integer.mk_const ctx (Symbol.mk_string ctx name))
		| FmIntConst(i) -> (Integer.mk_numeral_i ctx i)
		| FmAdd(fm1, fm2) -> (Arithmetic.mk_add ctx [fm_to_z3 ctx names fm1;fm_to_z3 ctx names fm2])
		| FmSub(fm1, fm2) -> (Arithmetic.mk_sub ctx [fm_to_z3 ctx names fm1;fm_to_z3 ctx names fm2])
		| FmMul(fm1, fm2) -> (Arithmetic.mk_mul ctx [fm_to_z3 ctx names fm1;fm_to_z3 ctx names fm2])
		| FmDiv(fm1, fm2) -> (Arithmetic.mk_div ctx (fm_to_z3 ctx names fm1) (fm_to_z3 ctx names fm2))
		| FmTrue -> (Boolean.mk_true ctx)
		| FmFalse -> (Boolean.mk_false ctx)
		| FmAnd(args) -> (Boolean.mk_and ctx (List.map (fun x -> fm_to_z3 ctx names x) args))
		| FmOr(args) -> (Boolean.mk_or ctx (List.map (fun x -> fm_to_z3 ctx names x) args))
		| FmNot(fm1) -> (Boolean.mk_not ctx (fm_to_z3 ctx names fm1))
		| FmLe(fm1,fm2) -> (Arithmetic.mk_le ctx (fm_to_z3 ctx names fm1) (fm_to_z3 ctx names fm2))
		| FmUni(args,fm1) -> 
			let xs = 
				List.mapi (fun i x -> 
					let len = names + i in
					let name = String.concat "_" ["x";(string_of_int len)] in
					(Integer.mk_const ctx (Symbol.mk_string ctx name)))
					args
			in
			let names' = names + (List.length xs) in
			expr_of_quantifier (Quantifier.mk_forall_const ctx xs (fm_to_z3 ctx names' fm1) (Some 1) [] [] None None)
		| FmExi(args,fm1) ->
			let xs = 
				List.mapi (fun i x ->
					let len = names + i in
					let name = String.concat "_" ["x";(string_of_int len)] in
					(Integer.mk_const ctx (Symbol.mk_string ctx name)))
					args
			in
			let names' = names + (List.length xs) in
			expr_of_quantifier (Quantifier.mk_exists_const ctx xs (fm_to_z3 ctx names' fm1) (Some 1) [] [] None None)
		| FmEq(fm1,fm2) -> (mk_eq ctx (fm_to_z3 ctx names fm1) (fm_to_z3 ctx names fm2))
		| FmImply(fm1,fm2) ->(Boolean.mk_implies ctx (fm_to_z3 ctx names fm1) (fm_to_z3 ctx names fm2))

let fm_solver formula = 
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in
	let z3fm = fm_to_z3 ctx 0 formula in
	(* print_string (Z3.Expr.to_string z3fm);print_newline (); *)
	let solver = (mk_solver ctx None) in
		(Solver.add solver [z3fm]);
	let res = check solver [] in
    if res = SATISFIABLE then
      1
    else if res = UNSATISFIABLE then
      2
    else
      3