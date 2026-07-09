(** Path B: the LOW-LEVEL / native numeric representation for the Rust backend.

    Where [RustGMPRemaps.v] (path A) represents nat/positive/N/Z as an
    arena-allocated [&'a rug::Integer] (arbitrary precision, idiomatic, but every
    op allocates and every eliminator [Box::leak]s a predecessor), this module
    represents them as a NATIVE [i64].  [i64] is [Copy], needs no arena and no
    lifetime, and its eliminators produce the predecessor as a plain [Copy]
    value (no leak, no allocation).  This is the fast representation for values
    that fit in 64 bits -- exactly the recursion-on-nat kernels (e.g. a [divmod]
    defined by structural recursion) that make path A pathologically slow.

    It is the B half of the mixed-representation backend: correctness holds for
    inputs within [i64] range; the coercions in [RustMixedRemaps.v] mediate
    between this and the arbitrary-precision A representation. *)

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

(** Numeric inductives map to the native Rust [i64].  Constructors are emitted
    as [self.]-methods (matching the backend's call convention) that just compute
    an [i64] -- no arena, no allocation.  Eliminators are [macro_rules!] whose
    predecessor is a plain [i64] (Copy), so structural recursion on nat costs one
    integer subtraction per step instead of a GMP allocation + [Box::leak]. *)
Definition native_ind_remaps : inductive_remappings := [
  ind_remap {| inductive_mind := <%% bool %%>; inductive_ind := 0 |}
    "bool" ["true"; "false"] (Some "__bool_elim!");
  ind_remap {| inductive_mind := <%% nat %%>; inductive_ind := 0 |}
    "i64" ["self.__nat_zero()"; "self.__nat_succ"] (Some "__nat_elim!");
  ind_remap {| inductive_mind := <%% positive %%>; inductive_ind := 0 |}
    "i64" ["self.__pos_onebit"; "self.__pos_zerobit"; "self.__pos_one()"]
    (Some "__pos_elim!");
  ind_remap {| inductive_mind := <%% N %%>; inductive_ind := 0 |}
    "i64" ["self.__N_zero()"; "self.__N_frompos"] (Some "__N_elim!");
  ind_remap {| inductive_mind := <%% Z %%>; inductive_ind := 0 |}
    "i64" ["self.__Z_zero()"; "self.__Z_frompos"; "self.__Z_fromneg"]
    (Some "__Z_elim!")
].

Definition native_const_remaps : constant_remappings := [
  (* positive *)
  (<%% Pos.add %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a + b }");
  (<%% Pos.succ %%>, mk_const "fn ##name##(&'a self, a: i64) -> i64 { a + 1 }");
  (<%% Pos.pred %%>, mk_const "fn ##name##(&'a self, a: i64) -> i64 { if a <= 1 { 1 } else { a - 1 } }");
  (<%% Pos.sub %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a - b < 1 { 1 } else { a - b } }");
  (<%% Pos.mul %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a * b }");
  (<%% Pos.min %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a <= b { a } else { b } }");
  (<%% Pos.max %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a >= b { a } else { b } }");
  (<%% Pos.eqb %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }");
  (<%% Pos.compare %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> std::cmp::Ordering { a.cmp(&b) }");

  (* N *)
  (<%% N.add %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a + b }");
  (<%% N.succ %%>, mk_const "fn ##name##(&'a self, a: i64) -> i64 { a + 1 }");
  (<%% N.pred %%>, mk_const "fn ##name##(&'a self, a: i64) -> i64 { if a <= 0 { 0 } else { a - 1 } }");
  (<%% N.sub %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a - b < 0 { 0 } else { a - b } }");
  (<%% N.mul %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a * b }");
  (<%% N.div %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if b == 0 { 0 } else { a / b } }");
  (<%% N.modulo %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if b == 0 { a } else { a % b } }");
  (<%% N.min %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a <= b { a } else { b } }");
  (<%% N.max %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a >= b { a } else { b } }");
  (<%% N.eqb %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }");
  (<%% N.compare %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> std::cmp::Ordering { a.cmp(&b) }");

  (* Z *)
  (<%% Z.add %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a + b }");
  (<%% Z.succ %%>, mk_const "fn ##name##(&'a self, a: i64) -> i64 { a + 1 }");
  (<%% Z.pred %%>, mk_const "fn ##name##(&'a self, a: i64) -> i64 { a - 1 }");
  (<%% Z.sub %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a - b }");
  (<%% Z.mul %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a * b }");
  (<%% Z.opp %%>, mk_const "fn ##name##(&'a self, a: i64) -> i64 { -a }");
  (<%% Z.min %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a <= b { a } else { b } }");
  (<%% Z.max %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a >= b { a } else { b } }");
  (<%% Z.eqb %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }");
  (<%% Z.div %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if b == 0 { 0 } else { a.div_euclid(b) } }");
  (<%% Z.modulo %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if b == 0 { a } else { a.rem_euclid(b) } }");
  (<%% Z.compare %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> std::cmp::Ordering { a.cmp(&b) }");
  (<%% Z.of_N %%>, mk_const "fn ##name##(&'a self, a: i64) -> i64 { a }");
  (<%% Z.abs_N %%>, mk_const "fn ##name##(&'a self, a: i64) -> i64 { a.abs() }");

  (* nat *)
  (<%% Nat.add %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a + b }");
  (<%% Nat.mul %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a * b }");
  (<%% Nat.sub %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a - b < 0 { 0 } else { a - b } }");
  (<%% Nat.eqb %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> bool { a == b }");
  (<%% Nat.leb %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> bool { a <= b }");
  (<%% Nat.ltb %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> bool { a < b }");
  (<%% Nat.compare %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> std::cmp::Ordering { a.cmp(&b) }");
  (<%% Nat.max %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a >= b { a } else { b } }");
  (<%% Nat.min %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if a <= b { a } else { b } }");
  (<%% Nat.div %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if b == 0 { 0 } else { a / b } }");
  (<%% Nat.modulo %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { if b == 0 { a } else { a % b } }");
  (<%% Nat.pow %%>, mk_const "fn ##name##(&'a self, a: i64, b: i64) -> i64 { a.pow(b as u32) }")
].

(** Top-of-file preamble (outside [impl<'a> Program]): the eliminator and bool
    macros over native [i64].  Unlike the GMP eliminators, the predecessor is a
    plain [i64] (Copy) -- no [Box::leak], no allocation. *)
Definition native_top_preamble : string :=
  String.concat MRString.nl [
  "macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }";
  "macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }";
  "macro_rules! __bool_elim { ($tcase:expr, $fcase:expr, $val:expr) => { if $val { $tcase } else { $fcase } } }";
  "";
  "macro_rules! __nat_elim {";
  "  ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {";
  "    { let v: i64 = $val;";
  "      if v == 0 { $zcase }";
  "      else { let $pred: i64 = v - 1; $scase } }";
  "  }";
  "}";
  "";
  "macro_rules! __pos_elim {";
  "  ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {";
  "    { let n: i64 = $val;";
  "      if n == 1 { $onecase }";
  "      else if n % 2 == 1 { let $p: i64 = n / 2; $onebcase }";
  "      else { let $p2: i64 = n / 2; $zerobcase } }";
  "  }";
  "}";
  "";
  "macro_rules! __N_elim {";
  "  ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {";
  "    { let $p: i64 = $val; if $p == 0 { $zero_case } else { $pos_case } }";
  "  }";
  "}";
  "";
  "macro_rules! __Z_elim {";
  "  ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {";
  "    { let n: i64 = $val;";
  "      if n == 0 { $zero_case }";
  "      else if n < 0 { let $p2: i64 = -n; $neg_case }";
  "      else { let $p: i64 = n; $pos_case } }";
  "  }";
  "}"
  ].

(** Program preamble (inside [impl<'a> Program]): constructor methods returning
    native [i64].  No arena, no allocation -- just arithmetic. *)
Definition native_program_preamble : string :=
  String.concat MRString.nl [
  "fn __nat_zero(&'a self) -> i64 { 0 }";
  "fn __nat_succ(&'a self, x: i64) -> i64 { x + 1 }";
  "fn __pos_one(&'a self) -> i64 { 1 }";
  "fn __pos_onebit(&'a self, x: i64) -> i64 { x * 2 + 1 }";
  "fn __pos_zerobit(&'a self, x: i64) -> i64 { x * 2 }";
  "fn __N_zero(&'a self) -> i64 { 0 }";
  "fn __N_frompos(&'a self, z: i64) -> i64 { z }";
  "fn __Z_zero(&'a self) -> i64 { 0 }";
  "fn __Z_frompos(&'a self, z: i64) -> i64 { z }";
  "fn __Z_fromneg(&'a self, z: i64) -> i64 { -z }"
  ].

Definition native_rust_config' : rust_config' := {|
  rust_preamble_top'       := Some native_top_preamble;
  rust_preamble_program'   := Some native_program_preamble;
  rust_term_box_symbol'    := None;
  rust_type_box_symbol'    := None;
  rust_any_type_symbol'    := None;
  rust_print_full_names'   := None;
  rust_default_attributes' := None;
|}.

Definition native_rust_config_full : rust_config := {|
  rust_preamble_top       := native_top_preamble;
  rust_preamble_program   := native_program_preamble;
  rust_term_box_symbol    := "()";
  rust_type_box_symbol    := "()";
  rust_any_type_symbol    := "()";
  rust_print_full_names   := true;
  rust_default_attributes := "#[derive(Debug, Clone)]";
|}.
