(** Path C: MIXED-representation numeric backend.

    Values live in path A (arbitrary-precision [&'a rug::Integer]) by default, so
    the program is correct for all inputs.  A directive-selected PARTITION of
    operations is compiled in path B (native [i64]): those remap bodies coerce
    their [&'a rug::Integer] arguments down to [i64] at entry ([__to_i64]),
    compute natively, and coerce the result back up ([__from_i64]).  The two
    coercions are the A<->B boundary.

    Correctness is INDEPENDENT of the partition: any operation whose B body
    agrees with its A meaning on the coerced values is sound, so which ops are in
    the B partition is purely a performance choice (the partition is an untrusted
    oracle).  Here the partition is given explicitly ([b_partition]); a static
    analysis or a Rocq attribute could populate it automatically.

    This is the minimal, per-operation realisation of the mixed backend: the two
    representations coexist in one generated crate, joined by coherent coercions.
    A per-function partition (switching the nat REPRESENTATION inside a function,
    not just at op boundaries) is the natural next granularity. *)

From MetaRocq.Common Require Import Kernames.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import RustBackend.
From Peregrine Require Import RustGMPRemaps.
From TypedExtraction Require Import Common.

From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import PArith.
From Stdlib Require Import List.
Import ListNotations.

Local Open Scope bs_scope.

(** A binary op run in path B: coerce both [&'a rug::Integer] args to [i64],
    evaluate the native expression [e] (over locals [a] and [b]), coerce back. *)
Definition b2i (e : string) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { let a = self.__to_i64(a); let b = self.__to_i64(b); self.__from_i64(" ++ e ++ ") }").

(** A binary predicate run in path B: coerce both args, return a native [bool]
    (no coercion back -- [bool] is represented natively in both paths). *)
Definition b2b (e : string) : remapped_constant :=
  mk_const ("fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> bool { let a = self.__to_i64(a); let b = self.__to_i64(b); " ++ e ++ " }").

(** The B partition: the (nat) operations compiled natively.  Placed BEFORE the
    path-A [gmp_const_remaps] so they take precedence in remap lookup. *)
Definition b_partition : constant_remappings := [
  (<%% Nat.add %%>,    b2i "a + b");
  (<%% Nat.mul %%>,    b2i "a * b");
  (<%% Nat.sub %%>,    b2i "if a - b < 0 { 0 } else { a - b }");
  (<%% Nat.div %%>,    b2i "if b == 0 { 0 } else { a / b }");
  (<%% Nat.modulo %%>, b2i "if b == 0 { a } else { a % b }");
  (<%% Nat.pow %%>,    b2i "a.pow(b as u32)");
  (<%% Nat.eqb %%>,    b2b "a == b");
  (<%% Nat.leb %%>,    b2b "a <= b");
  (<%% Nat.ltb %%>,    b2b "a < b")
].

Definition mixed_const_remaps : constant_remappings :=
  (b_partition ++ gmp_const_remaps)%list.

(** The nat/Z/N/positive TYPE stays path A ([Int<'a>]); constructors and
    eliminators are the path-A (GMP) ones. *)
Definition mixed_ind_remaps : inductive_remappings := gmp_ind_remaps.

(** Coercion helpers ([__to_i64]/[__from_i64]) are added to the program preamble,
    alongside the path-A constructor methods. *)
Definition mixed_coercions : string :=
  String.concat MRString.nl [
  "fn __to_i64(&'a self, x: &'a rug::Integer) -> i64 { x.to_i64().unwrap() }";
  "fn __from_i64(&'a self, x: i64) -> &'a rug::Integer { self.alloc(rug::Integer::from(x)) }"
  ].

Definition mixed_program_preamble : string :=
  String.concat MRString.nl [gmp_program_preamble; mixed_coercions].

Definition mixed_rust_config' : rust_config' := {|
  rust_preamble_top'       := Some gmp_top_preamble;
  rust_preamble_program'   := Some mixed_program_preamble;
  rust_term_box_symbol'    := None;
  rust_type_box_symbol'    := None;
  rust_any_type_symbol'    := None;
  rust_print_full_names'   := None;
  rust_default_attributes' := None;
|}.
