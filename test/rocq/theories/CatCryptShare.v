From Stdlib Require Import Uint63.

(* CatCrypt fixture: a let-bound subterm shared by both operands of the
   final add. The `let` binder should alias the multiplication's SSA
   level rather than duplicating the .regArith .mul binding. *)
Definition sq2 (x y : int) : int :=
  let a := (x * y)%uint63 in
  (a + a)%uint63.

(* Closed variant for `peregrine eval` differential testing:
   sq2 3 4 = let a := 3 * 4 = 12 in a + a = 24. *)
Definition sq2_closed : int := sq2 3 4.
