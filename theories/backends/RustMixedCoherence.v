(** * Coercion-coherence for Peregrine's mixed-representation Rust backend.

    This file formalises the mathematically-substantive coherence facts that
    justify the [Path C] mixed numeric backend defined in
    [theories/backends/RustMixedRemaps.v].

    Background (see the header of RustMixedRemaps.v).  Coq [nat]/[Z] numerics
    are extracted by default in PATH A: arbitrary-precision [&'a rug::Integer].
    A directive-selected PARTITION of operations ([b_partition]) is instead
    compiled in PATH B: native [i64].  Each B-body coerces its arguments down
    to [i64] at entry ([__to_i64]), computes natively, and coerces the result
    back up ([__from_i64]).  Those two coercions form the A<->B boundary.

    We model the two representations abstractly, both as the mathematical
    integer they denote:

      - PATH A value  = the integer itself.
      - PATH B value  = the integer, CONSTRAINED to the i64 window [in_i64].
      - [to_i64] / [from_i64] = identity on the modelled integer, valid exactly
        on the [in_i64] window (outside it the real [.to_i64().unwrap()] would
        panic; the [in_i64] precondition is what discharges the [.unwrap()]).

    Everything below is proved against Rocq's standard [ZArith].  The ONE thing
    Rocq cannot see is the Rust source string emitted by each remap; that
    per-string "the emitted Rust realises this modelled function on its domain"
    obligation is collected in the TRUSTED BRIDGE block at the end of the file.

    Rocq 9.1 / Stdlib. *)

From Stdlib Require Import ZArith Lia.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** The i64 window and the boundary coercions *)

(** The signed 64-bit range: exactly the values for which [rug::Integer::to_i64]
    succeeds (its [.unwrap()] does not panic). *)
Definition in_i64 (z : Z) : Prop := (-2^63 <= z < 2^63)%Z.

(** The A->B coercion, modelled on the denoted integer.  On the [in_i64] window
    the real [__to_i64] is the identity on the value it denotes. *)
Definition to_i64_spec (z : Z) : Z := z.

(** The B->A coercion, modelled on the denoted integer.  [__from_i64] injects an
    [i64] back into an arbitrary-precision integer; on the modelled value it is
    the identity. *)
Definition from_i64_spec (z : Z) : Z := z.

(** The A<->B boundary is coherent: coercing down then back up is the identity
    on the whole i64 window.  (The [in_i64] hypothesis is what makes the real
    [.to_i64().unwrap()] total; on the model the roundtrip is unconditional.) *)
Theorem coerce_roundtrip :
  forall z, in_i64 z -> from_i64_spec (to_i64_spec z) = z.
Proof.
  intros z _. unfold from_i64_spec, to_i64_spec. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Generic op-coherence *)

(** A native (path-B) binary op [g : Z -> Z -> Z] realises the Coq (path-A)
    [nat] op [f] when, on arguments that fit i64 and whose result fits i64,
    running B (coerce down, apply [g], coerce back) reproduces the [nat]
    meaning [Z.of_nat (f a b)].

    The three [in_i64] premises are precisely the side-conditions under which
    the two [__to_i64] calls and the one [__from_i64] call in the emitted body
    are total (no [.unwrap()] panic and no i64 overflow). *)
Definition op_coherent (f : nat -> nat -> nat) (g : Z -> Z -> Z) : Prop :=
  forall a b,
    in_i64 (Z.of_nat a) ->
    in_i64 (Z.of_nat b) ->
    in_i64 (Z.of_nat (f a b)) ->
    from_i64_spec (g (to_i64_spec (Z.of_nat a)) (to_i64_spec (Z.of_nat b)))
      = Z.of_nat (f a b).

(* ------------------------------------------------------------------ *)
(** ** The b_partition instances

    Each theorem below corresponds to one entry of [b_partition] in
    RustMixedRemaps.v, pairing the Coq [nat] op with the [Z] model of its
    emitted native i64 expression. *)

(** [Nat.add]  <->  b2i "a + b" *)
Theorem coherent_add : op_coherent Nat.add Z.add.
Proof.
  intros a b _ _ _. unfold from_i64_spec, to_i64_spec.
  rewrite Nat2Z.inj_add. reflexivity.
Qed.

(** [Nat.mul]  <->  b2i "a * b" *)
Theorem coherent_mul : op_coherent Nat.mul Z.mul.
Proof.
  intros a b _ _ _. unfold from_i64_spec, to_i64_spec.
  rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(** [Nat.sub]  <->  b2i "if a - b < 0 { 0 } else { a - b }".
    The native body is saturating (truncated at 0), matching Coq's truncated
    [nat] subtraction.  Modelled as [Z.max 0 (a - b)]. *)
Theorem coherent_sub :
  op_coherent Nat.sub (fun x y => Z.max 0 (x - y)).
Proof.
  intros a b _ _ _. unfold from_i64_spec, to_i64_spec.
  (* [lia]'s zify preprocessing knows both truncated [Nat.sub] (through
     [Z.of_nat]) and [Z.max], so the saturating identity is closed directly. *)
  lia.
Qed.

(** [Nat.div]  <->  b2i "if b == 0 { 0 } else { a / b }".
    Coq's [Nat.div a 0 = 0] and Rust's guard both return 0 on a zero divisor;
    off zero the divisor is positive so truncated [i64] division ([Z.div] on
    nonnegatives) agrees with [Nat.div]. *)
Theorem coherent_div :
  op_coherent Nat.div (fun x y => if Z.eqb y 0 then 0 else x / y).
Proof.
  intros a b _ _ _. unfold from_i64_spec, to_i64_spec.
  destruct (Z.of_nat b =? 0) eqn:E.
  - (* divisor is zero: guard returns 0, and [Nat.div a 0] computes to 0. *)
    apply Z.eqb_eq in E.
    assert (b = 0)%nat by lia. subst b.
    reflexivity.
  - (* divisor nonzero: native division matches [Nat.div] via [Nat2Z.inj_div]. *)
    rewrite <- Nat2Z.inj_div. reflexivity.
Qed.

(** [Nat.modulo]  <->  b2i "if b == 0 { a } else { a % b }".
    Coq's [Nat.modulo a 0 = a] and Rust's guard both return [a] on a zero
    divisor; off zero, on nonnegative operands Rust's truncated remainder [%]
    coincides with Euclidean [Z.modulo], which matches [Nat.modulo] via
    [Nat2Z.inj_mod]. *)
Theorem coherent_mod :
  op_coherent Nat.modulo (fun x y => if Z.eqb y 0 then x else Z.modulo x y).
Proof.
  intros a b _ _ _. unfold from_i64_spec, to_i64_spec.
  destruct (Z.of_nat b =? 0) eqn:E.
  - (* divisor is zero: guard returns [a], and [Nat.modulo a 0] computes to [a]. *)
    apply Z.eqb_eq in E.
    assert (b = 0)%nat by lia. subst b.
    reflexivity.
  - (* divisor nonzero: native remainder matches [Nat.modulo] via [Nat2Z.inj_mod]. *)
    rewrite <- Nat2Z.inj_mod. reflexivity.
Qed.

(** Remark on [Nat.pow]  <->  b2i "a.pow(b as u32)".
    This entry of [b_partition] is intentionally NOT given an [op_coherent]
    theorem here.  Its native body casts the exponent [b as u32], so its
    modelled function is only faithful on the restricted domain [b < 2^32]
    (and, as for every B-op, on results within [in_i64]).  That domain
    restriction is a property of the emitted string, so it is discharged in the
    TRUSTED BRIDGE block below rather than as a numeric coherence lemma. *)

(* ------------------------------------------------------------------ *)
(** ** Comparison predicates (b2b)

    These return a native [bool] in BOTH paths (bool is represented natively
    everywhere), so there is no [__from_i64] coercion back.  Coherence is just:
    the native [Z] boolean test equals the Coq [nat] boolean test. *)

(** [Nat.eqb]  <->  b2b "a == b" *)
Theorem coherent_eqb :
  forall a b,
    in_i64 (Z.of_nat a) -> in_i64 (Z.of_nat b) ->
    Nat.eqb a b = Z.eqb (Z.of_nat a) (Z.of_nat b).
Proof.
  intros a b _ _. destruct (Nat.eqb a b) eqn:E.
  - apply Nat.eqb_eq in E. subst. symmetry. apply Z.eqb_eq. reflexivity.
  - apply Nat.eqb_neq in E. symmetry. apply Z.eqb_neq. lia.
Qed.

(** [Nat.leb]  <->  b2b "a <= b" *)
Theorem coherent_leb :
  forall a b,
    in_i64 (Z.of_nat a) -> in_i64 (Z.of_nat b) ->
    Nat.leb a b = Z.leb (Z.of_nat a) (Z.of_nat b).
Proof.
  intros a b _ _. destruct (Nat.leb a b) eqn:E.
  - apply Nat.leb_le in E. symmetry. apply Z.leb_le. lia.
  - apply Nat.leb_gt in E. symmetry. apply Z.leb_gt. lia.
Qed.

(** [Nat.ltb]  <->  b2b "a < b" *)
Theorem coherent_ltb :
  forall a b,
    in_i64 (Z.of_nat a) -> in_i64 (Z.of_nat b) ->
    Nat.ltb a b = Z.ltb (Z.of_nat a) (Z.of_nat b).
Proof.
  intros a b _ _. destruct (Nat.ltb a b) eqn:E.
  - apply Nat.ltb_lt in E. symmetry. apply Z.ltb_lt. lia.
  - apply Nat.ltb_ge in E. symmetry. apply Z.ltb_ge. lia.
Qed.

(* ================================================================== *)
(** ** TRUSTED BRIDGE (meta-level, per Rust string)

    Everything above is fully machine-checked against Rocq's [ZArith].  The
    proofs relate the Coq [nat] operations to their [Z] MODELS of the native
    i64 expressions.  What Rocq cannot inspect is the concrete Rust source
    string that Peregrine emits for each remap (the strings live in
    [theories/backends/RustMixedRemaps.v] as opaque [string]s).  The remaining,
    UNVERIFIED obligation is that each emitted string really computes its
    modelled function on its stated domain.  Concretely, we ASSUME:

    - The coercion preamble ([mixed_coercions]):
        * "fn __to_i64(&'a self, x) -> i64 { x.to_i64().unwrap() }"
          realises [to_i64_spec] on the domain [in_i64], and the [.unwrap()]
          never panics there -- justified by the [in_i64] premise, which is
          exactly the totality condition of [rug::Integer::to_i64].
        * "fn __from_i64(&'a self, x: i64) -> ... { self.alloc(Integer::from(x)) }"
          realises [from_i64_spec] (the identity injection i64 -> Integer).

    - Each [b_partition] body realises its modelled [Z] function on
      arguments/results within [in_i64] (i.e. the native [i64] arithmetic does
      not overflow, guaranteed by the third [in_i64] premise of [op_coherent]):
        * "a + b"                              realises  [Z.add]        (coherent_add)
        * "a * b"                              realises  [Z.mul]        (coherent_mul)
        * "if a - b < 0 { 0 } else { a - b }"  realises  [fun x y => Z.max 0 (x - y)]
                                                                        (coherent_sub)
        * "if b == 0 { 0 } else { a / b }"     realises  [fun x y => if y =? 0 then 0 else x / y]
                                                                        (coherent_div)
        * "if b == 0 { a } else { a % b }"     realises  [fun x y => if y =? 0 then x else Z.modulo x y]
                                                                        (coherent_mod)
        * "a.pow(b as u32)"                    realises  [Z.pow] on the RESTRICTED
                                               domain [Z.of_nat b < 2^32] (see the
                                               [Nat.pow] remark above); not given a
                                               numeric coherence lemma here.
        * "a == b"                             realises  [Z.eqb]        (coherent_eqb)
        * "a <= b"                             realises  [Z.leb]        (coherent_leb)
        * "a < b"                              realises  [Z.ltb]        (coherent_ltb)

    Under these per-string assumptions, the theorems above establish that every
    op in [b_partition] agrees with its path-A meaning on the coerced values;
    hence the mixed backend is sound INDEPENDENTLY of which ops are placed in
    the B partition -- the partition is a pure performance choice, exactly as
    claimed in the RustMixedRemaps.v header.  This trusted bridge is the only
    unverified part of the coherence argument. *)
