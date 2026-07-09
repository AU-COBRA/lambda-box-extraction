From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure Require Import EProgram.
From Malfunction Require Serialize.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import SerializeCommon.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.

Import ListNotations.
Local Open Scope bs_scope.



(** * Serializers *)

(** ** Backend Config *)

Instance Serialize_rust_config : Serialize rust_config :=
  fun o =>
    [Atom "rust_config";
     to_sexp (rust_preamble_top o);
     to_sexp (rust_preamble_program o);
     to_sexp (rust_term_box_symbol o);
     to_sexp (rust_type_box_symbol o);
     to_sexp (rust_any_type_symbol o);
     to_sexp (rust_print_full_names o);
     to_sexp (rust_default_attributes o)
    ]%sexp.

Instance Serialize_rust_config' : Serialize rust_config' :=
  fun o =>
    [Atom "rust_config";
     to_sexp (rust_preamble_top' o);
     to_sexp (rust_preamble_program' o);
     to_sexp (rust_term_box_symbol' o);
     to_sexp (rust_type_box_symbol' o);
     to_sexp (rust_any_type_symbol' o);
     to_sexp (rust_print_full_names' o);
     to_sexp (rust_default_attributes' o)
    ]%sexp.

Instance Serialize_elm_config : Serialize elm_config :=
  fun o =>
    [Atom "elm_config";
     to_sexp (elm_preamble o);
     to_sexp (elm_module_name o);
     to_sexp (elm_term_box_symbol o);
     to_sexp (elm_type_box_symbol o);
     to_sexp (elm_any_type_symbol o);
     to_sexp (elm_false_elim_def o);
     to_sexp (elm_print_full_names o)
    ]%sexp.

Instance Serialize_elm_config' : Serialize elm_config' :=
  fun o =>
    [Atom "elm_config";
     to_sexp (elm_preamble' o);
     to_sexp (elm_module_name' o);
     to_sexp (elm_term_box_symbol' o);
     to_sexp (elm_type_box_symbol' o);
     to_sexp (elm_any_type_symbol' o);
     to_sexp (elm_false_elim_def' o);
     to_sexp (elm_print_full_names' o)
    ]%sexp.

Instance Serialize_certirocq_config : Serialize certirocq_config :=
  fun o =>
    [Atom "certirocq_config";
     to_sexp (direct o);
     to_sexp (c_args o);
     to_sexp (o_level o);
     to_sexp (anf_conf o);
     to_sexp (prefix o);
     to_sexp (body_name o)
    ]%sexp.

Instance Serialize_certirocq_config' : Serialize certirocq_config' :=
  fun o =>
    [Atom "certirocq_config";
     to_sexp (direct' o);
     to_sexp (c_args' o);
     to_sexp (o_level' o);
     to_sexp (anf_conf' o);
     to_sexp (prefix' o);
     to_sexp (body_name' o)
    ]%sexp.

Instance Serialize_program_type : Serialize Serialize.program_type :=
  fun n =>
    match n with
    | Serialize.Standalone => Atom "Standalone"
    | Serialize.Shared_lib m r => [ Atom "Shared_lib"; to_sexp m; to_sexp r ]
    end%sexp.

Instance Serialize_ocaml_config : Serialize ocaml_config :=
  fun o =>
    [Atom "ocaml_config";
     to_sexp (program_type o)
    ]%sexp.

Instance Serialize_ocaml_config' : Serialize ocaml_config' :=
  fun o =>
    [Atom "ocaml_config";
     to_sexp (program_type' o)
    ]%sexp.

Instance Serialize_cakeml_config : Serialize cakeml_config :=
  fun o =>
    @to_sexp _ Serialize_unit o.

Instance Serialize_cakeml_config' : Serialize cakeml_config' :=
  fun o =>
    @to_sexp _ Serialize_unit o.

Instance Serialize_lean_config : Serialize lean_config :=
  fun o =>
    [Atom "lean_config";
     to_sexp (lean_namespace o);
     to_sexp (lean_print_full_names o)
    ]%sexp.

Instance Serialize_lean_config' : Serialize lean_config' :=
  fun o =>
    [Atom "lean_config";
     to_sexp (lean_namespace' o);
     to_sexp (lean_print_full_names' o)
    ]%sexp.

Instance Serialize_eval_config : Serialize eval_config :=
  fun o =>
    [Atom "eval_config";
     to_sexp (copts o);
     to_sexp (fuel o);
     to_sexp (eval_anf o)
    ]%sexp.

Instance Serialize_eval_config' : Serialize eval_config' :=
  fun o =>
    [Atom "eval_config";
     to_sexp (copts' o);
     to_sexp (fuel' o);
     to_sexp (eval_anf' o)
    ]%sexp.

Instance Serialize_ASTType : Serialize ASTType :=
  fun o =>
    match o with
    | LambdaBox => Atom "LambdaBox"
    | LambdaBoxTyped => Atom "LambdaBoxTyped"
    | LambdaBoxMut c => [Atom "LambdaBoxMut"; to_sexp c]
    | LambdaBoxLocal c => [Atom "LambdaBoxLocal"; to_sexp c]
    | LambdaANF c => [Atom "LambdaANF"; to_sexp c]
    | LambdaANFC c => [Atom "LambdaANFC"; to_sexp c]
    end%sexp.

Instance Serialize_ASTType' : Serialize ASTType' :=
  fun o =>
    match o with
    | LambdaBox' => Atom "LambdaBox"
    | LambdaBoxTyped' => Atom "LambdaBoxTyped"
    | LambdaBoxMut' c => [Atom "LambdaBoxMut"; to_sexp c]
    | LambdaBoxLocal' c => [Atom "LambdaBoxLocal"; to_sexp c]
    | LambdaANF' c => [Atom "LambdaANF"; to_sexp c]
    | LambdaANFC' c => [Atom "LambdaANFC"; to_sexp c]
    end%sexp.

Instance Serialize_ast_config : Serialize ast_config :=
  fun o =>
    [Atom "ast_config";
     to_sexp (ast_type o)
    ]%sexp.

Instance Serialize_ast_config' : Serialize ast_config' :=
  fun o =>
    [Atom "ast_config";
     to_sexp (ast_type' o)
    ]%sexp.

Instance Serialize_backend_config : Serialize backend_config :=
  fun b =>
    match b with
    | Rust o => [Atom "Rust"; to_sexp o ]
    | Elm o => [Atom "Elm"; to_sexp o ]
    | C o => [Atom "C"; to_sexp o ]
    | Wasm o => [Atom "Wasm"; to_sexp o ]
    | OCaml o => [Atom "OCaml"; to_sexp o ]
    | CakeML o => [Atom "CakeML"; to_sexp o ]
    | Lean o => [Atom "Lean"; to_sexp o ]
    | Eval o => [Atom "Eval"; to_sexp o ]
    | AST o => [Atom "AST"; to_sexp o ]
    end%sexp.

Instance Serialize_backend_config' : Serialize backend_config' :=
  fun b =>
    match b with
    | Rust' o => [Atom "Rust"; to_sexp o ]
    | Elm' o => [Atom "Elm"; to_sexp o ]
    | C' o => [Atom "C"; to_sexp o ]
    | Wasm' o => [Atom "Wasm"; to_sexp o ]
    | OCaml' o => [Atom "OCaml"; to_sexp o ]
    | CakeML' o => [Atom "CakeML"; to_sexp o ]
    | Lean' o => [Atom "Lean"; to_sexp o ]
    | Eval' o => [Atom "Eval"; to_sexp o ]
    | AST' o => [Atom "AST"; to_sexp o ]
    end%sexp.



(** ** Config Serializers *)

Instance Serialize_remapped_inductive : Serialize remapped_inductive :=
  fun o =>
    [Atom "remapped_inductive";
     to_sexp (re_ind_name o);
     to_sexp (re_ind_ctors o);
     to_sexp (re_ind_match o)
    ]%sexp.

Instance Serialize_remapped_constant : Serialize remapped_constant :=
  fun o =>
    [Atom "remapped_constant";
     to_sexp (re_const_ext o);
     to_sexp (re_const_arity o);
     to_sexp (re_const_gc o);
     to_sexp (re_const_inl o);
     to_sexp (re_const_s o)
    ]%sexp.

Instance Serialize_inductive_mapping : Serialize EProgram.inductive_mapping :=
  fun r =>
    let '(kn, (s, n)) := r in
    [Atom "inductive_mapping";
     to_sexp kn;
     to_sexp s;
     to_sexp n
    ]%sexp.

Instance Serialize_extract_inductive : Serialize extract_inductive :=
  fun r =>
    [Atom "extract_inductive";
     to_sexp (cstrs r);
     to_sexp (elim r)
    ]%sexp.

Instance Serialize_remap_inductive : Serialize remap_inductive :=
  fun r =>
    match r with
    | KnIndRemap kn r => [Atom "KnIndRemap"; to_sexp kn; to_sexp r]
    | StringIndRemap ind r => [Atom "StringIndRemap"; to_sexp ind; to_sexp r ]
    end%sexp.

Instance Serialize_custom_attribute : Serialize custom_attribute :=
  fun o =>
    to_sexp o.

Instance Serialize_inlinings : Serialize inlinings :=
  fun o =>
    to_sexp o.

Instance Serialize_constant_remappings : Serialize constant_remappings :=
  fun o =>
    to_sexp o.

Instance Serialize_inductive_remappings : Serialize inductive_remappings :=
  fun o =>
    to_sexp o.

Instance Serialize_custom_attributes : Serialize custom_attributes :=
  fun o =>
    to_sexp o.

Instance Serialize_erasure_phases : Serialize erasure_phases :=
  fun o =>
    [Atom "erasure_phases";
     to_sexp (implement_box o);
     to_sexp (implement_lazy o);
     to_sexp (cofix_to_laxy o);
     to_sexp (betared o);
     to_sexp (unboxing o);
     to_sexp (dearg_ctors o);
     to_sexp (dearg_consts o);
     to_sexp (specialize_instances o)
    ]%sexp.

Instance Serialize_erasure_phases' : Serialize erasure_phases' :=
  fun o =>
    [Atom "erasure_phases";
     to_sexp (implement_box' o);
     to_sexp (implement_lazy' o);
     to_sexp (cofix_to_laxy' o);
     to_sexp (betared' o);
     to_sexp (unboxing' o);
     to_sexp (dearg_ctors' o);
     to_sexp (dearg_consts' o);
     to_sexp (specialize_instances' o)
    ]%sexp.

Instance Serialize_config : Serialize config :=
  fun o =>
    [Atom "config";
     to_sexp (backend_opts o);
     to_sexp (erasure_opts o);
     to_sexp (inlinings_opts o);
     to_sexp (const_remappings_opts o);
     to_sexp (ind_remappings_opts o);
     to_sexp (cstr_reorders_opts o);
     to_sexp (custom_attributes_opts o)
    ]%sexp.

Instance Serialize_config' : Serialize config' :=
  fun o =>
    [Atom "config";
     to_sexp (backend_opts' o);
     to_sexp (erasure_opts' o);
     to_sexp (inlinings_opts' o);
     to_sexp (const_remappings_opts' o);
     to_sexp (ind_remappings_opts' o);
     to_sexp (cstr_reorders_opts' o);
     to_sexp (custom_attributes_opts' o)
    ]%sexp.

Instance Serialize_attributes_config : Serialize attributes_config :=
  fun o =>
    [Atom "attributes_config";
     to_sexp (inlinings_opt o);
     to_sexp (const_remappings_opt o);
     to_sexp (ind_remappings_opt o);
     to_sexp (cstr_reorders_opt o);
     to_sexp (custom_attributes_opt o)
    ]%sexp.



(** * Main serialization functions *)

(** ** Backend Config *)

Definition string_of_rust_config (x : rust_config) : string :=
  @to_string rust_config Serialize_rust_config x.

Definition string_of_rust_config' (x : rust_config') : string :=
  @to_string rust_config' Serialize_rust_config' x.

Definition string_of_elm_config (x : elm_config) : string :=
  @to_string elm_config Serialize_elm_config x.

Definition string_of_elm_config' (x : elm_config') : string :=
  @to_string elm_config' Serialize_elm_config' x.

Definition string_of_certirocq_config (x : certirocq_config) : string :=
  @to_string certirocq_config Serialize_certirocq_config x.

Definition string_of_certirocq_config' (x : certirocq_config') : string :=
  @to_string certirocq_config' Serialize_certirocq_config' x.

Definition string_of_program_type (x : Serialize.program_type) : string :=
  @to_string Serialize.program_type Serialize_program_type x.

Definition string_of_ocaml_config (x : ocaml_config) : string :=
  @to_string ocaml_config Serialize_ocaml_config x.

Definition string_of_ocaml_config' (x : ocaml_config') : string :=
  @to_string ocaml_config' Serialize_ocaml_config' x.

Definition string_of_cakeml_config (x : cakeml_config) : string :=
  @to_string cakeml_config Serialize_cakeml_config x.

Definition string_of_cakeml_config' (x : cakeml_config') : string :=
  @to_string cakeml_config' Serialize_cakeml_config' x.

Definition string_of_lean_config (x : lean_config) : string :=
  @to_string lean_config Serialize_lean_config x.

Definition string_of_lean_config' (x : lean_config') : string :=
  @to_string lean_config' Serialize_lean_config' x.

Definition string_of_eval_config (x : eval_config) : string :=
  @to_string eval_config Serialize_eval_config x.

Definition string_of_eval_config' (x : eval_config') : string :=
  @to_string eval_config' Serialize_eval_config' x.

Definition string_of_ASTType (x : ASTType) : string :=
  @to_string ASTType Serialize_ASTType x.

Definition string_of_ASTType' (x : ASTType') : string :=
  @to_string ASTType' Serialize_ASTType' x.

Definition string_of_ast_config (x : ast_config) : string :=
  @to_string ast_config Serialize_ast_config x.

Definition string_of_ast_config' (x : ast_config') : string :=
  @to_string ast_config' Serialize_ast_config' x.

Definition string_of_backend_config (x : backend_config) : string :=
  @to_string backend_config Serialize_backend_config x.

Definition string_of_backend_config' (x : backend_config') : string :=
  @to_string backend_config' Serialize_backend_config' x.



(** ** Config *)

Definition string_of_remapped_inductive (x : remapped_inductive) : string :=
  @to_string remapped_inductive Serialize_remapped_inductive x.

Definition string_of_remapped_constant (x : remapped_constant) : string :=
  @to_string remapped_constant Serialize_remapped_constant x.

Definition string_of_inductive_mapping (x : inductive_mapping) : string :=
  @to_string inductive_mapping Serialize_inductive_mapping x.

Definition string_of_extract_inductive (x : extract_inductive) : string :=
  @to_string extract_inductive Serialize_extract_inductive x.

Definition string_of_remap_inductive (x : remap_inductive) : string :=
  @to_string remap_inductive Serialize_remap_inductive x.

Definition string_of_custom_attribute (x : custom_attribute) : string :=
  @to_string custom_attribute Serialize_custom_attribute x.

Definition string_of_inlinings (x : inlinings) : string :=
  @to_string inlinings Serialize_inlinings x.

Definition string_of_constant_remappings (x : constant_remappings) : string :=
  @to_string constant_remappings Serialize_constant_remappings x.

Definition string_of_inductive_remappings (x : inductive_remappings) : string :=
  @to_string inductive_remappings Serialize_inductive_remappings x.

Definition string_of_custom_attributes (x : custom_attributes) : string :=
  @to_string custom_attributes Serialize_custom_attributes x.

Definition string_of_erasure_phases (x : erasure_phases) : string :=
  @to_string erasure_phases Serialize_erasure_phases x.

Definition string_of_erasure_phases' (x : erasure_phases') : string :=
  @to_string erasure_phases' Serialize_erasure_phases' x.

Definition string_of_config (x : config) : string :=
  @to_string config Serialize_config x.

Definition string_of_config' (x : config') : string :=
  @to_string config' Serialize_config' x.

Definition string_of_attributes_config (x : attributes_config) : string :=
  @to_string attributes_config Serialize_attributes_config x.
