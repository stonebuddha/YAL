open Syntax
open Core

let main () =
  print_string "Hello World!";
  print_newline ();
  let t = TmIf(TmBool(true), TmInt(3), TmInt(5)) in 
  let t' = eval empty_ctx t in
  	printtm empty_ctx t'

let () = main ()
