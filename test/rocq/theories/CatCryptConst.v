From Stdlib Require Import Uint63.

(* CatCrypt fixture: addition with an inline literal constant. Compiles
   to a .regConst binding for 251 plus one .regArith .add binding. *)
Definition addc (x : int) : int := (x + 251)%uint63.

(* Closed variant for `peregrine eval` differential testing: addc 5 = 256. *)
Definition addc_closed : int := addc 5.
