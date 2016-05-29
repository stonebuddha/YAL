open Syntax

val eval : context -> term -> term
val typeof : context -> term -> (ty * formula)

(*------------Debug------------*)
(* val append_uniq : 'a list -> 'a list -> 'a list *)
(* val get_id_fm : context -> index -> (int list * formula) *)
(* val get_prop_fm : context -> prop -> formula *)
val get_sr_fm : context -> sort -> index -> formula
