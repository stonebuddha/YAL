open Syntax
open Evaluation
open Typecheck
open Support.Error

let searchpath = ref [""]

let argDefs = [
  "-I",
      Arg.String (fun f -> searchpath := f::!searchpath),
      "Append a directory to the search path"]

let parseArgs () =
  let inFile = ref (None : string option) in
  Arg.parse argDefs
     (fun s ->
       match !inFile with
         Some(_) -> error "You must specify exactly one input file"
       | None -> inFile := Some(s))
     "";
  match !inFile with
      None -> error "You must specify an input file"
    | Some(s) -> s

(* let prelude_ctx = [
	("op+", BdType (TyDepUni ("a", SrInt, TyDepUni ("b", SrInt, TyArrow (TyProduct (TyInt (IdVar (1, 2)), TyInt (IdVar (0, 2))), TyInt (IdAdd (IdVar (1, 2), IdVar (0, 2))))))));
] *)

let parse_file fn =
  let pi = open_in fn in
  let lexbuf = Lexing.from_channel pi in
  let t = Parser.term Lexer.read lexbuf in
    t empty_ctx

let process fn ctx =
	let t = parse_file fn in
	print_raw t;print_newline ();
	let tyT = typeof_solved empty_ctx t in
	let t' = eval empty_ctx t in
  	printtm t';print_newline ();printty tyT;print_newline()

let main () =
  (* let t = TmIf(TmBool(true), TmInt(3), TmInt(5)) in process t; *)
(*   let t = TmApp(TmDepApp(TmDepAbs("c",SrInt,TmAbs("x",TyDepExi("a",SrInt,TyInt(IdAdd(IdVar(0,2),IdVar(2,2)))),TmVar(0,2))),IdInt(2)),TmDepPair(IdInt(8),TmInt(9),TyDepExi("b",SrInt,TyInt(IdAdd(IdVar(0,1),IdInt(1)))))) in
  let (ty,fm) = typeof empty_ctx t in
  let t' = eval empty_ctx t in
  printtm t';print_newline ();printty ty;print_newline();printfm fm;print_newline (); *)
  (* let t = TmCase(TmInt(3), [(PtInt(0),0,TmInt(1));(PtInt(3),0,TmInt(2))]) in process t *)
  (* let t = TmCase(TmPair(TmInt(3), TmPair(TmInt(4), TmInt(5))),
  	[(PtPair(PtInt(3),PtPair(PtVar("x"), PtVar("y"))),2,TmInt(3));(PtWild, 0, TmInt(2))]) in process t *)
  (* let t = TmLet("x",TmIf(TmBool(true), TmBool(false), TmBool(true)), TmIf(TmVar(0, 0), TmInt(3), TmInt(4))) in process t *)

  (* let sr_outer = SrSubset("y",SrInt,PrLe(IdVar(0,0),IdInt(1))) in
  let sr = SrSubset("x",sr_outer,PrAnd(PrLe(IdVar(0,0),IdInt(5)), PrLe(IdInt(1),IdVar(0,0)))) in
  let id = IdAdd(IdVar(1,0),IdVar(0,0)) in
  let fm = get_sr_fm empty_ctx sr id in
  print_formula fm *)
	let inFile = parseArgs() in
	let _ = process inFile empty_ctx in
  	()

let () = main ()
