From Stdlib Require Import Uint63.

(* CatCrypt fixture: chained addition. Compiles to three .regArith .add
   bindings (plus one mask-and per add when catcrypt_mask63 is on). *)
Definition add3 (x y z : int) : int := (x + y + z)%uint63.

(* Closed variant for `peregrine eval` differential testing against the
   CatCrypt cross-check: add3 5 7 9 = 21. *)
Definition add3_closed : int := add3 5 7 9.
