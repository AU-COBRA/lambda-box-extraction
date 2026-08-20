From Stdlib Require Import Uint63.

(* CatCrypt fixture: literal-amount right shift combined with land.
   NOTE: the CatCrypt backend only supports shifts by a syntactic
   literal amount (0..63) — `x >> 3` below, NOT a variable shift amount
   such as `x >> y`. Variable shift amounts are rejected by the
   backend (see translation-design.md §3, "Shifts:" emit_op rule). *)
Definition mix (x y : int) : int := ((x >> 3) land (y * y))%uint63.

(* Closed variant for `peregrine eval` differential testing:
   mix 40 5 = (40 >> 3) land (5 * 5) = 5 land 25 = 1. *)
Definition mix_closed : int := mix 40 5.
