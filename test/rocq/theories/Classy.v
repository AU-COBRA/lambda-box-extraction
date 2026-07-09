(* Typeclass-heavy example: dictionaries dragged through operations,
   mirroring Lean's HAdd/OfNat plumbing for [1 + 1].
   Uses non-recursive operations to keep the whole box pipeline wellformed. *)

Definition op1 (x y : nat) : nat := x.
Definition op2 (x y : nat) : nat := y.

Class Add (A : Type) := { add : A -> A -> A }.
#[export] Instance addNat : Add nat := { add := op1 }.

Class Mul (A : Type) := { mul : A -> A -> A }.
#[export] Instance mulNat : Mul nat := { mul := op2 }.

(* A polymorphic function taking two dictionaries. *)
Definition poly {A} `{Add A} `{Mul A} (x y z : A) : A :=
  add (mul x y) z.

Definition test : nat := poly 2 3 4.
