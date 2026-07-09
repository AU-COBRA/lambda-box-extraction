From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From TypedExtraction Require Import PrettyPrinterMonad.
From TypedExtraction Require Import Printing.
From TypedExtraction Require Import RustExtract.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_rust_config := {|
  rust_preamble_top       := "";
  rust_preamble_program   := "";
  rust_term_box_symbol    := "()";
  rust_type_box_symbol    := "()";
  rust_any_type_symbol    := "()";
  rust_print_full_names   := true;
  rust_default_attributes := "#[derive(Debug, Clone)]";
|}.

(** GMP runtime preamble: helpers + eliminator macros over [rug::Integer],
    the GMP analogue of the u64 helpers hardcoded in PluginExtract.v.  Place
    this in [rust_preamble_top] (see [gmp_rust_config]).  Requires the [rug]
    crate: add [rug = "1"] to the generated Cargo.toml.  Validate against a
    real build — the eliminator/predecessor paths are the least-tested. *)
Definition rust_gmp_preamble : string :=
  String.concat MRString.nl [
  "use rug::Integer;";
  "";
  "fn __nat_succ(x: Integer) -> Integer { x + 1 }";
  "macro_rules! __nat_elim {";
  "  ($zcase:expr, $pred:ident, $scase:expr, $val:expr) => {";
  "    { let v = $val; if v == 0 { $zcase } else { let $pred = Integer::from(&v - 1); $scase } }";
  "  }";
  "}";
  "macro_rules! __andb { ($b1:expr, $b2:expr) => { $b1 && $b2 } }";
  "macro_rules! __orb { ($b1:expr, $b2:expr) => { $b1 || $b2 } }";
  "";
  "fn __pos_onebit(x: Integer) -> Integer { x * 2 + 1 }";
  "fn __pos_zerobit(x: Integer) -> Integer { x * 2 }";
  "macro_rules! __pos_elim {";
  "  ($p:ident, $onebcase:expr, $p2:ident, $zerobcase:expr, $onecase:expr, $val:expr) => {";
  "    { let n = $val;";
  "      if n == 1 { $onecase }";
  "      else if Integer::from(&n & Integer::from(1)) == 0 { let $p2 = Integer::from(&n >> 1u32); $zerobcase }";
  "      else { let $p = Integer::from(&n >> 1u32); $onebcase } }";
  "  }";
  "}";
  "";
  "fn __N_frompos(z: Integer) -> Integer { z }";
  "macro_rules! __N_elim {";
  "  ($zero_case:expr, $p:ident, $pos_case:expr, $val:expr) => {";
  "    { let $p = $val; if $p == 0 { $zero_case } else { $pos_case } }";
  "  }";
  "}";
  "";
  "fn __Z_frompos(z: Integer) -> Integer { z }";
  "fn __Z_fromneg(z: Integer) -> Integer { -z }";
  "macro_rules! __Z_elim {";
  "  ($zero_case:expr, $p:ident, $pos_case:expr, $p2:ident, $neg_case:expr, $val:expr) => {";
  "    { let n = $val;";
  "      if n == 0 { $zero_case }";
  "      else if n < 0 { let $p2 = Integer::from(-&n); $neg_case }";
  "      else { let $p = n; $pos_case } }";
  "  }";
  "}"
  ].

(** As [default_rust_config] but with the GMP numeric preamble wired into the
    top preamble.  Pair this with the GMP constant/inductive remaps (the config
    counterparts of ExtrRustGMP.v) to make [compile_rust] emit GMP arithmetic. *)
Definition gmp_rust_config := {|
  rust_preamble_top       := rust_gmp_preamble;
  rust_preamble_program   := "";
  rust_term_box_symbol    := "()";
  rust_type_box_symbol    := "()";
  rust_any_type_symbol    := "()";
  rust_print_full_names   := true;
  rust_default_attributes := "#[derive(Debug, Clone)]";
|}.

Definition rust_phases := {|
  implement_box_c  := Compatible false;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible true;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
|}.



Definition rust_top_preamble := [
  "#![allow(dead_code)]";
  "#![allow(non_camel_case_types)]";
  "#![allow(unused_imports)]";
  "#![allow(non_snake_case)]";
  "#![allow(unused_variables)]";
  "";
  "use std::marker::PhantomData;";
  "";
  "fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {";
  "  f";
  "}"
].

Definition rust_program_preamble := [
  "fn alloc<T>(&'a self, t: T) -> &'a T {";
  "  self.__alloc.alloc(t)";
  "}";
  "";
  "fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {";
  "  self.__alloc.alloc(F)";
  "}"
].

Definition mk_preamble (o : rust_config) : Preamble := {|
  top_preamble := rust_top_preamble ++ [o.(rust_preamble_top)];
  program_preamble := rust_program_preamble ++ [o.(rust_preamble_program)];
|}.

Definition mk_attributes (attrs : custom_attributes) (o : rust_config) : Kernames.inductive -> string :=
  match attrs with
  | nil => fun _ => o.(rust_default_attributes)
  | _ =>
    fun ind =>
      match List.find (fun '(kn', _) => Kernames.eq_kername ind.(Kernames.inductive_mind) kn') attrs with
      | Some (_, a) => a
      | None => o.(rust_default_attributes)
      end
  end.

Definition mk_remaps (rs : constant_remappings) (is : inductive_remappings) : remaps :=
  let re_inds := filter_map (fun x =>
    match x with
    | StringIndRemap ind r => Some (ind, {|
      re_ind_name  := r.(Config.re_ind_name);
      re_ind_ctors := r.(Config.re_ind_ctors);
      re_ind_match := r.(Config.re_ind_match);
    |})
    | _ => None
    end
  ) is in
  let re_const := filter_map (fun '(kn, r) =>
    if r.(re_const_inl) then None
    else Some (kn, r.(re_const_s))
  ) rs in
  let re_in_const := filter_map (fun '(kn, r) =>
    if r.(re_const_inl) then Some (kn, r.(re_const_s))
    else None
  ) rs in
  {|
  remap_inductive :=
    match re_inds with
    | nil => fun ind => None
    | _ => fun ind =>
      option_map (fun '(_,r) => r)
        (List.find (fun '(ind', _) => Kernames.eq_inductive ind ind') re_inds)
    end;

  remap_constant :=
    match re_const with
    | nil => fun kn => None
    | _ => fun kn =>
      option_map (fun '(_,s) => s)
        (List.find (fun '(kn', _) => Kernames.eq_kername kn kn') re_const)
    end;

  remap_inline_constant :=
    match re_in_const with
    | nil => fun kn => None
    | _ => fun kn =>
      option_map (fun '(_,s) => s)
        (List.find (fun '(kn', _) => Kernames.eq_kername kn kn') re_in_const)
    end;
|}.
(* TODO: support external remapping in Rust backend *)

Definition mk_config (o : rust_config) : RustPrintConfig := {|
  term_box_symbol := o.(rust_term_box_symbol);
  type_box_symbol := o.(rust_type_box_symbol);
  any_type_symbol := o.(rust_any_type_symbol);
  print_full_names := o.(rust_print_full_names);
|}.



Definition extract_rust (const_remaps : constant_remappings)
                        (ind_remaps : inductive_remappings)
                        (custom_attr : custom_attributes)
                        (opts : rust_config)
                        (file_name : string)
                        (p : ExAst.global_env)
                        : result' (list string) :=
  let remaps := mk_remaps const_remaps ind_remaps in
  let attrs := mk_attributes custom_attr opts in
  let config := mk_config opts in
  let preamble := mk_preamble opts in
  let p := @print_program p remaps config attrs preamble in
  '(_, s) <- finish_print_lines p;;
  Ok s.
