open Syntax
open Core

let process t =
	let t' = eval empty_ctx t in
  	printtm empty_ctx t';print_newline ()

let main () =
  print_string "Hello World!";
  print_newline ();
  (* let t = TmIf(TmBool(true), TmInt(3), TmInt(5)) in process t; *)
  (* let t = TmApp(TmAbs("x",TyBool,TmVar(0,2)),TmBool(true)) in process t; *)
  (* let t = TmCase(TmInt(3), [(PtInt(0),0,TmInt(1));(PtInt(3),0,TmInt(2))]) in process t *)
  (* let t = TmCase(TmPair(TmInt(3), TmPair(TmInt(4), TmInt(5))), 
  	[(PtPair(PtInt(3),PtPair(PtVar("x"), PtVar("y"))),2,TmInt(3));(PtWild, 0, TmInt(2))]) in process t *)
  let t = TmLet("x",TmIf(TmBool(true), TmBool(false), TmBool(true)), TmIf(TmVar(0, 0), TmInt(3), TmInt(4))) in process t

let () = main ()
