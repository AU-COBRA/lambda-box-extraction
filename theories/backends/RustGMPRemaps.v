(** Config-path (CLI) equivalent of the plugin's ExtrRustGMP.v numeric remap,
    using an ARENA-ALLOCATED SHARED-REFERENCE representation.

    The Rust backend stores every extracted value under a pervasive [<A: Copy>]
    bound: inductives are [&'a Enum] references and closures are [&'a dyn Fn],
    all [Copy] references into a [bumpalo] arena.  An OWNED [rug::Integer] is not
    [Copy], so the moment a number is placed in a [list]/pair/tree the generic
    machinery fails to compile (E0277).  We therefore represent the GMP numeric
    types as [&'a rug::Integer] (a shared reference, hence [Copy]), matching the
    backend's architecture.  A number lives in the same arena as everything else.

    Representation summary:
      - [nat]/[positive]/[N]/[Z]  ==>  [&'a rug::Integer]  (alias [Int<'a>]).
      - Constructors are emitted as [self.]-methods that arena-allocate the
        result (they are spliced inside [impl] method bodies where [self] is in
        scope), e.g. ctor strings ["self.__nat_zero()"], ["self.__nat_succ"].
      - Arithmetic ops are [&'a self] methods that arena-allocate their result.
      - Eliminators are [macro_rules!] (no [self] available); the predecessor,
        which must be an [&'a rug::Integer], is produced with
        [Box::leak(Box::new(..))] (a [&'static] that coerces to [&'a]).  Leaks
        are bounded by the recursion depth and GMP ints are compact; the arena
        itself never frees either.

    The matching runtime preamble is split in two: [gmp_top_preamble] (outside
    the [impl]: [use]s, the [Int] alias, the eliminator/bool macros) and
    [gmp_program_preamble] (inside [impl<'a> Program]: the constructor methods).
    Cargo dependencies: [rug = "1"], [bumpalo = "3"].

    NOTE: the eliminator match strings carry the [!] macro-invocation suffix
    (e.g. "__nat_elim!") because the Rust backend emits [eliminator ^ "("]
    verbatim (RustExtract.print_remapped_case) and the preamble defines these
    as [macro_rules!]. *)

From MetaRocq.Common Require Import Kernames.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import RustBackend.
From TypedExtraction Require Import Common.

From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import PArith.
From Stdlib Require Import List.
Import ListNotations.

Local Open Scope bs_scope.

(** Smart constructor for a Rust constant remap: only [re_const_inl] (false =
    emit as a definition) and [re_const_s] (the Rust body, with [##name##]
    replaced by the mangled function name) are consulted by the Rust backend;
    the other fields are C/Wasm-only and left at defaults. *)
Definition mk_const (s : string) : remapped_constant := {|
  re_const_ext   := None;
  re_const_arity := 0;
  re_const_gc    := false;
  re_const_inl   := false;
  re_const_s     := s;
|}.

Definition mk_ind (name : string) (ctors : list string) (m : option string)
  : remapped_inductive :=
  {| re_ind_name  := name;
     re_ind_ctors := ctors;
     re_ind_match := m |}.

Definition ind_remap (i : inductive) (name : string) (ctors : list string)
                     (m : option string) : remap_inductive :=
  StringIndRemap i (mk_ind name ctors m).

(** The numeric type name spliced wherever a [nat]/[N]/[Z]/[positive] appears as
    a Rust type ([RustExtract.print_type_aux], [TInd] branch).  [Int<'a>] keeps
    the arena lifetime in scope; it is a type alias for [&'a rug::Integer] (see
    [gmp_top_preamble]).  Constructor strings are emitted either as a bare 0-arg
    method call ([self.__nat_zero()]) or as a method head applied to arguments
    ([self.__nat_succ(x)]). *)
Definition gmp_ind_remaps : inductive_remappings := [
  (* [bool] -> native Rust [bool].  Coq constructor order is [true] (0) then
     [false] (1); a match becomes [__bool_elim!(tcase, fcase, discr)]. *)
  ind_remap {| inductive_mind := <%% bool %%>; inductive_ind := 0 |}
    "bool" ["true"; "false"] (Some "__bool_elim!");
  ind_remap {| inductive_mind := <%% nat %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__nat_zero()"; "self.__nat_succ"] (Some "__nat_elim!");
  ind_remap {| inductive_mind := <%% positive %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__pos_onebit"; "self.__pos_zerobit"; "self.__pos_one()"]
    (Some "__pos_elim!");
  ind_remap {| inductive_mind := <%% N %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__N_zero()"; "self.__N_frompos"] (Some "__N_elim!");
  ind_remap {| inductive_mind := <%% Z %%>; inductive_ind := 0 |}
    "Int<'a>" ["self.__Z_zero()"; "self.__Z_frompos"; "self.__Z_fromneg"]
    (Some "__Z_elim!")
].

Definition gmp_const_remaps : constant_remappings := [
  (* --- positive --- *)
  (<%% Pos.add %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a + b)) }");
  (<%% Pos.succ %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a + 1)) }");
  (<%% Pos.pred %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a - 1).max(rug::Integer::from(1))) }");
  (<%% Pos.sub %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a - b)) }");
  (<%% Pos.mul %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a * b)) }");
  (<%% Pos.min %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if a <= b { a } else { b } }");
  (<%% Pos.max %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if a >= b { a } else { b } }");
  (<%% Pos.eqb %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> bool { a == b }");
  (<%% Pos.compare %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> std::cmp::Ordering { a.cmp(b) }");

  (* --- N --- *)
  (<%% N.add %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a + b)) }");
  (<%% N.succ %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a + 1)) }");
  (<%% N.pred %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a - 1).max(rug::Integer::new())) }");
  (<%% N.sub %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a - b).max(rug::Integer::new())) }");
  (<%% N.mul %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a * b)) }");
  (<%% N.div %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if *b == 0 { self.alloc(rug::Integer::new()) } else { self.alloc(rug::Integer::from(a / b)) } }");
  (<%% N.modulo %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if *b == 0 { a } else { self.alloc(rug::Integer::from(a % b)) } }");
  (<%% N.min %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if a <= b { a } else { b } }");
  (<%% N.max %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if a >= b { a } else { b } }");
  (<%% N.eqb %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> bool { a == b }");
  (<%% N.compare %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> std::cmp::Ordering { a.cmp(b) }");

  (* --- Z --- *)
  (<%% Z.add %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a + b)) }");
  (<%% Z.succ %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a + 1)) }");
  (<%% Z.pred %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a - 1)) }");
  (<%% Z.sub %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a - b)) }");
  (<%% Z.mul %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a * b)) }");
  (<%% Z.opp %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(-a)) }");
  (<%% Z.min %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if a <= b { a } else { b } }");
  (<%% Z.max %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if a >= b { a } else { b } }");
  (<%% Z.eqb %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> bool { a == b }");
  (<%% Z.div %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if *b == 0 { self.alloc(rug::Integer::new()) } else { self.alloc(rug::Integer::from(a).div_floor(rug::Integer::from(b))) } }");
  (<%% Z.modulo %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if *b == 0 { a } else { self.alloc(rug::Integer::from(a).rem_floor(rug::Integer::from(b))) } }");
  (<%% Z.compare %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> std::cmp::Ordering { a.cmp(b) }");
  (<%% Z.of_N %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer) -> &'a rug::Integer { a }");
  (<%% Z.abs_N %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a.abs_ref())) }");

  (* --- nat --- *)
  (<%% Nat.add %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a + b)) }");
  (<%% Nat.mul %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a * b)) }");
  (<%% Nat.sub %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a - b).max(rug::Integer::new())) }");
  (<%% Nat.eqb %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> bool { a == b }");
  (<%% Nat.leb %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> bool { a <= b }");
  (<%% Nat.ltb %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> bool { a < b }");
  (<%% Nat.compare %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> std::cmp::Ordering { a.cmp(b) }");
  (<%% Nat.max %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if a >= b { a } else { b } }");
  (<%% Nat.min %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if a <= b { a } else { b } }");
  (<%% Nat.div %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if *b == 0 { self.alloc(rug::Integer::new()) } else { self.alloc(rug::Integer::from(a / b)) } }");
  (<%% Nat.modulo %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { if *b == 0 { a } else { self.alloc(rug::Integer::from(a % b)) } }");
  (* Nat.pow remaps to GMP exponentiation (exponent fits u32 for benchmark
     inputs), avoiding an extracted recursive nat closure. *)
  (<%% Nat.pow %%>, mk_const "fn ##name##(&'a self, a: &'a rug::Integer, b: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(a).pow(b.to_u32().unwrap())) }")
].

(** Top-of-file preamble (outside [impl<'a> Program]): imports, the [Int] type
    alias, the eliminator macros over [&'a rug::Integer], and the bool macros.
    The eliminators dereference the reference for comparisons and [Box::leak] the
    predecessor (a [&'static] that coerces to [&'a]). *)
Definition gmp_top_preamble : string :=
  String.concat MRString.nl [
  "use rug::Integer;";
  "use rug::ops::{DivRounding, RemRounding, Pow};";
  "type Int<'a> = &'a rug::Integer;";
  "";
  "macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }";
  "macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }";
  "macro_rules! __bool_elim { ($tcase:expr, $fcase:expr, $val:expr) => { if $val { $tcase } else { $fcase } } }";
  "";
  "macro_rules! __nat_elim {";
  "  ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {";
  "    { let v: &rug::Integer = $val;";
  "      if *v == 0 { $zcase }";
  "      else { let $pred: &rug::Integer = Box::leak(Box::new(rug::Integer::from(v - 1))); $scase } }";
  "  }";
  "}";
  "";
  "macro_rules! __pos_elim {";
  "  ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {";
  "    { let n: &rug::Integer = $val;";
  "      if *n == 1 { $onecase }";
  "      else if n.is_odd() { let $p: &rug::Integer = Box::leak(Box::new(rug::Integer::from(n >> 1u32))); $onebcase }";
  "      else { let $p2: &rug::Integer = Box::leak(Box::new(rug::Integer::from(n >> 1u32))); $zerobcase } }";
  "  }";
  "}";
  "";
  "macro_rules! __N_elim {";
  "  ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {";
  "    { let $p: &rug::Integer = $val; if *$p == 0 { $zero_case } else { $pos_case } }";
  "  }";
  "}";
  "";
  "macro_rules! __Z_elim {";
  "  ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {";
  "    { let n: &rug::Integer = $val;";
  "      if *n == 0 { $zero_case }";
  "      else if *n < 0 { let $p2: &rug::Integer = Box::leak(Box::new(rug::Integer::from(-n))); $neg_case }";
  "      else { let $p = n; $pos_case } }";
  "  }";
  "}"
  ].

(** Program preamble (inside [impl<'a> Program], after [alloc]/[closure]): the
    constructor methods.  Each arena-allocates its result and returns
    [&'a rug::Integer], so a constructor produces the same [Copy] reference shape
    the backend expects.  [__N_frompos]/[__Z_frompos]/[Z.of_N] are identities on
    the reference. *)
Definition gmp_program_preamble : string :=
  String.concat MRString.nl [
  "fn __nat_zero(&'a self) -> &'a rug::Integer { self.alloc(rug::Integer::new()) }";
  "fn __nat_succ(&'a self, x: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(x + 1)) }";
  "fn __pos_one(&'a self) -> &'a rug::Integer { self.alloc(rug::Integer::from(1)) }";
  "fn __pos_onebit(&'a self, x: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(x * 2) + 1) }";
  "fn __pos_zerobit(&'a self, x: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(x * 2)) }";
  "fn __N_zero(&'a self) -> &'a rug::Integer { self.alloc(rug::Integer::new()) }";
  "fn __N_frompos(&'a self, z: &'a rug::Integer) -> &'a rug::Integer { z }";
  "fn __Z_zero(&'a self) -> &'a rug::Integer { self.alloc(rug::Integer::new()) }";
  "fn __Z_frompos(&'a self, z: &'a rug::Integer) -> &'a rug::Integer { z }";
  "fn __Z_fromneg(&'a self, z: &'a rug::Integer) -> &'a rug::Integer { self.alloc(rug::Integer::from(-z)) }"
  ].

(** Optional Rust config (CLI path) with the GMP preambles wired in.  Slots into
    [ConfigUtils.Rust'] for the [peregrine] binary; all other fields fall through
    to [default_rust_config]. *)
Definition gmp_rust_config' : rust_config' := {|
  rust_preamble_top'       := Some gmp_top_preamble;
  rust_preamble_program'   := Some gmp_program_preamble;
  rust_term_box_symbol'    := None;
  rust_type_box_symbol'    := None;
  rust_any_type_symbol'    := None;
  rust_print_full_names'   := None;
  rust_default_attributes' := None;
|}.

(** Full (non-optional) Rust config for driving [extract_rust] directly (test
    harness path).  Mirrors [gmp_rust_config] (RustBackend.v) but with the
    reference-representation preambles. *)
Definition gmp_rust_config_full : rust_config := {|
  rust_preamble_top       := gmp_top_preamble;
  rust_preamble_program   := gmp_program_preamble;
  rust_term_box_symbol    := "()";
  rust_type_box_symbol    := "()";
  rust_any_type_symbol    := "()";
  rust_print_full_names   := true;
  rust_default_attributes := "#[derive(Debug, Clone)]";
|}.
