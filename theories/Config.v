From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From MetaRocq.Erasure Require EProgram.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Kernames.
From Malfunction Require Serialize.

Local Open Scope bs_scope.



Section BackendConfig.

  Record rust_config := {
    rust_preamble_top       : string;
    rust_preamble_program   : string;
    rust_term_box_symbol    : string;
    rust_type_box_symbol    : string;
    rust_any_type_symbol    : string;
    rust_print_full_names   : bool;
    rust_default_attributes : string;
  }.

  Record elm_config := {
    elm_preamble         : string;
    elm_module_name      : option string;
    elm_term_box_symbol  : string;
    elm_type_box_symbol  : string;
    elm_any_type_symbol  : string;
    elm_false_elim_def   : string;
    elm_print_full_names : bool;
  }.

  Record certirocq_config := {
    direct    : bool;
    c_args    : nat;
    o_level   : nat;
    anf_conf  : nat;
    prefix    : string;
    body_name : string;
  }.

  Definition c_config : Type := certirocq_config.

  Definition wasm_config : Type := certirocq_config.

  Record ocaml_config := {
    program_type : Malfunction.Serialize.program_type;
  }.

  Definition cakeml_config : Type := unit.

  Record eval_config := {
    copts    : certirocq_config;
    fuel     : nat;
    eval_anf : bool;
  }.

  Variant ASTType :=
  | LambdaBox
  | LambdaBoxTyped
  | LambdaBoxMut   : certirocq_config -> ASTType
  | LambdaBoxLocal : certirocq_config -> ASTType
  | LambdaANF      : certirocq_config -> ASTType
  | LambdaANFC     : certirocq_config -> ASTType.

  Record ast_config := {
    ast_type : ASTType;
  }.

  Inductive backend_config :=
  | Rust   : rust_config -> backend_config
  | Elm    : elm_config -> backend_config
  | C      : c_config -> backend_config
  | Wasm   : wasm_config -> backend_config
  | OCaml  : ocaml_config -> backend_config
  | CakeML : cakeml_config -> backend_config
  | Eval   : eval_config -> backend_config
  | AST    : ast_config -> backend_config.

End BackendConfig.



Section GeneralConfig.

  Record remapped_inductive := build_remapped_inductive {
      (* Name of the type to remap to *)
      re_ind_name  : string;
      (* Constructor functions for the new type,
         corresponding to the costructors of the remapped type *)
      re_ind_ctors : list string;
      (* Eliminator, needed if the new type is not an inductive type *)
      re_ind_match : option string;
    }.

  Record remapped_constant := {
      (* Remap to a definition defined externally *)
      re_const_ext : option string;
      (* Arity of the remapped constant *)
      re_const_arity : nat;
      (* Set if the function needs access to GC, only needed for C/Wasm backends *)
      re_const_gc : bool;
      (* Inline the remapping *)
      re_const_inl : bool;
      (* What to remap the constant to *)
      re_const_s : string;
    }.

  Inductive remap_inductive :=
  (* Remap inductives to defined constants *)
  (* Supported by untyped targets *)
  | KnIndRemap : Kernames.kername -> list EProgram.extract_inductive -> remap_inductive
  (* Remap inductives to arbitrary strings *)
  (* Supported by typed targets *)
  | StringIndRemap : Kernames.inductive -> remapped_inductive -> remap_inductive.

  Definition custom_attribute : Type := (Kernames.kername * string).

  Definition inlinings : Type := list Kernames.kername.
  Definition constant_remappings : Type := list (Kernames.kername * remapped_constant).
  Definition inductive_remappings : Type := list remap_inductive.
  Definition custom_attributes : Type := list custom_attribute.

  Inductive phases_config :=
  | Required : phases_config
  | Compatible (default : bool) : phases_config
  | Incompatible : phases_config.

  Record erasure_phases_config := {
      implement_box_c  : phases_config;
      implement_lazy_c : phases_config;
      cofix_to_laxy_c  : phases_config;
      betared_c        : phases_config;
      unboxing_c       : phases_config;
      dearg_ctors_c    : phases_config;
      dearg_consts_c   : phases_config;
      specialize_instances_c : phases_config;
    }.

  Record erasure_phases := {
      implement_box  : bool;
      implement_lazy : bool;
      cofix_to_laxy  : bool;
      betared        : bool;
      unboxing       : bool;
      dearg_ctors    : bool;
      dearg_consts   : bool;
      (* Instance/dictionary specialization (Peregrine-local unsafe pass,
         see erasure/EInstanceSpecialize.v). *)
      specialize_instances : bool;
    }.

  Record config := {
      backend_opts           : backend_config;
      erasure_opts           : erasure_phases;
      inlinings_opts         : inlinings;
      const_remappings_opts  : constant_remappings;
      ind_remappings_opts    : inductive_remappings;
      cstr_reorders_opts     : EProgram.inductives_mapping;
      custom_attributes_opts : custom_attributes;
    }.

  Record attributes_config := {
      inlinings_opt         : inlinings;
      const_remappings_opt  : constant_remappings;
      ind_remappings_opt    : inductive_remappings;
      cstr_reorders_opt     : EProgram.inductives_mapping;
      custom_attributes_opt : custom_attributes;
    }.

End GeneralConfig.
