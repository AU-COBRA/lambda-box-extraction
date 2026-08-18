From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure Require Import EProgram.
From Malfunction Require Serialize.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import DeserializeCommon.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.

Import ListNotations.
Local Open Scope bs_scope.



(** * Deserializers *)

(** ** Backend Config *)

Instance Deserialize_rust_config : Deserialize rust_config :=
  fun l e =>
    Deser.match_con "rust_config" []
      [ ("rust_config", Deser.con7_ Build_rust_config) ]
      l e.

Instance Deserialize_rust_config' : Deserialize rust_config' :=
  fun l e =>
    Deser.match_con "rust_config" []
      [ ("rust_config", Deser.con7_ Build_rust_config') ]
      l e.

Instance Deserialize_elm_config : Deserialize elm_config :=
  fun l e =>
    Deser.match_con "elm_config" []
      [ ("elm_config", Deser.con7_ Build_elm_config) ]
      l e.

Instance Deserialize_elm_config' : Deserialize elm_config' :=
  fun l e =>
    Deser.match_con "elm_config" []
      [ ("elm_config", Deser.con7_ Build_elm_config') ]
      l e.

Instance Deserialize_certirocq_config : Deserialize certirocq_config :=
  fun l e =>
    Deser.match_con "certirocq_config" []
      [ ("certirocq_config", Deser.con6_ Build_certirocq_config) ]
      l e.

Instance Deserialize_certirocq_config' : Deserialize certirocq_config' :=
  fun l e =>
    Deser.match_con "certirocq_config" []
      [ ("certirocq_config", Deser.con6_ Build_certirocq_config') ]
      l e.

Instance Deserialize_program_type : Deserialize Serialize.program_type :=
  fun l e =>
    Deser.match_con "program_type"
      [ ("Standalone", Serialize.Standalone) ]
      [ ("Shared_lib", Deser.con2_ Serialize.Shared_lib) ]
      l e.

Instance Deserialize_ocaml_config : Deserialize ocaml_config :=
  fun l e =>
    Deser.match_con "ocaml_config" []
      [ ("ocaml_config", Deser.con1_ Build_ocaml_config) ]
      l e.

Instance Deserialize_ocaml_config' : Deserialize ocaml_config' :=
  fun l e =>
    Deser.match_con "ocaml_config" []
      [ ("ocaml_config", Deser.con1_ Build_ocaml_config') ]
      l e.

Instance Deserialize_cakeml_config : Deserialize cakeml_config :=
  fun l e =>
    @_from_sexp _ Deserialize_unit l e.

Instance Deserialize_cakeml_config' : Deserialize cakeml_config' :=
  fun l e =>
    @_from_sexp _ Deserialize_unit l e.

Instance Deserialize_fsharp_config : Deserialize fsharp_config :=
  fun l e =>
    Deser.match_con "fsharp_config" []
      [ ("fsharp_config", Deser.con2_ Build_fsharp_config) ]
      l e.

Instance Deserialize_fsharp_config' : Deserialize fsharp_config' :=
  fun l e =>
    Deser.match_con "fsharp_config" []
      [ ("fsharp_config", Deser.con2_ Build_fsharp_config') ]
      l e.

Instance Deserialize_eval_config : Deserialize eval_config :=
  fun l e =>
    Deser.match_con "eval_config" []
      [ ("eval_config", Deser.con3_ Build_eval_config) ]
      l e.

Instance Deserialize_eval_config' : Deserialize eval_config' :=
  fun l e =>
    Deser.match_con "eval_config" []
      [ ("eval_config", Deser.con3_ Build_eval_config') ]
      l e.

Instance Deserialize_ASTType : Deserialize ASTType :=
  fun l e =>
    Deser.match_con "ASTType"
      [ ("LambdaBox", LambdaBox);
        ("LambdaBoxTyped", LambdaBoxTyped)
      ]
      [ ("LambdaBoxMut", Deser.con1_ LambdaBoxMut);
        ("LambdaBoxLocal", Deser.con1_ LambdaBoxLocal);
        ("LambdaANF", Deser.con1_ LambdaANF);
        ("LambdaANFC", Deser.con1_ LambdaANFC)
      ]
      l e.

Instance Deserialize_ASTType' : Deserialize ASTType' :=
  fun l e =>
    Deser.match_con "ASTType"
      [ ("LambdaBox", LambdaBox');
        ("LambdaBoxTyped", LambdaBoxTyped')
      ]
      [ ("LambdaBoxMut", Deser.con1_ LambdaBoxMut');
        ("LambdaBoxLocal", Deser.con1_ LambdaBoxLocal');
        ("LambdaANF", Deser.con1_ LambdaANF');
        ("LambdaANFC", Deser.con1_ LambdaANFC')
      ]
      l e.

Instance Deserialize_ast_config : Deserialize ast_config :=
  fun l e =>
    Deser.match_con "ast_config" []
      [ ("ast_config", Deser.con1_ Build_ast_config) ]
      l e.

Instance Deserialize_ast_config' : Deserialize ast_config' :=
  fun l e =>
    Deser.match_con "ast_config" []
      [ ("ast_config", Deser.con1_ Build_ast_config') ]
      l e.

Instance Deserialize_backend_config : Deserialize backend_config :=
  fun l e =>
    Deser.match_con "backend_config" []
      [ ("Rust", Deser.con_ Rust);
        ("Elm", Deser.con_ Elm);
        ("C", Deser.con_ C);
        ("Wasm", Deser.con_ Wasm);
        ("OCaml", Deser.con_ OCaml);
        ("CakeML", Deser.con_ CakeML);
        ("FSharp", Deser.con_ FSharp);
        ("Eval", Deser.con_ Eval);
        ("AST", Deser.con_ AST)
      ]
      l e.

Instance Deserialize_backend_config' : Deserialize backend_config' :=
  fun l e =>
    Deser.match_con "backend_config" []
      [ ("Rust", Deser.con_ Rust');
        ("Elm", Deser.con_ Elm');
        ("C", Deser.con_ C');
        ("Wasm", Deser.con_ Wasm');
        ("OCaml", Deser.con_ OCaml');
        ("CakeML", Deser.con_ CakeML');
        ("FSharp", Deser.con_ FSharp');
        ("Eval", Deser.con_ Eval');
        ("AST", Deser.con_ AST')
      ]
      l e.



(** ** Config *)

Instance Deserialize_remapped_inductive : Deserialize remapped_inductive :=
  fun l e =>
    Deser.match_con "remapped_inductive" []
      [ ("remapped_inductive", Deser.con3_ build_remapped_inductive) ]
      l e.

Instance Deserialize_inductive_mapping : Deserialize EProgram.inductive_mapping :=
  fun l e =>
    Deser.match_con "inductive_mapping" []
      [ ("inductive_mapping", Deser.con3_ (fun kn s n => (kn, (s, n)))) ]
      l e.

Instance Deserialize_remapped_constant : Deserialize remapped_constant :=
  fun l e =>
    Deser.match_con "remapped_constant" []
      [ ("remapped_constant", Deser.con5_ Build_remapped_constant) ]
      l e.

Instance Deserialize_extract_inductive : Deserialize extract_inductive :=
  fun l e =>
    Deser.match_con "extract_inductive" []
      [ ("extract_inductive", Deser.con2_ Build_extract_inductive) ]
      l e.

Instance Deserialize_remap_inductive : Deserialize remap_inductive :=
  fun l e =>
    Deser.match_con "remap_inductive" []
      [ ("KnIndRemap", Deser.con2_ KnIndRemap);
        ("StringIndRemap", Deser.con2_ StringIndRemap)
      ]
      l e.

Instance Deserialize_custom_attribute : Deserialize custom_attribute :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_inlinings : Deserialize inlinings :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_constant_remappings : Deserialize constant_remappings :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_inductive_remappings : Deserialize inductive_remappings :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_custom_attributes : Deserialize custom_attributes :=
  fun l e =>
    _from_sexp l e.

Instance Deserialize_erasure_phases : Deserialize erasure_phases :=
  fun l e =>
    Deser.match_con "erasure_phases" []
      [ ("erasure_phases", Deser.con7_ Build_erasure_phases) ]
      l e.

Instance Deserialize_erasure_phases' : Deserialize erasure_phases' :=
  fun l e =>
    Deser.match_con "erasure_phases" []
      [ ("erasure_phases", Deser.con7_ Build_erasure_phases') ]
      l e.

Instance Deserialize_config : Deserialize config :=
  fun l e =>
    Deser.match_con "config" []
      [ ("config", Deser.con7_ Build_config) ]
      l e.

Instance Deserialize_config' : Deserialize config' :=
  fun l e =>
    Deser.match_con "config" []
      [ ("config", Deser.con7_ Build_config') ]
      l e.

Instance Deserialize_attributes_config : Deserialize attributes_config :=
  fun l e =>
    Deser.match_con "attributes_config" []
      [ ("attributes_config", Deser.con5_ Build_attributes_config) ]
      l e.



(** * Main deserialization functions *)

(** ** Backend Config *)

Definition rust_config_of_string (s : string) : error + rust_config :=
  @from_string rust_config Deserialize_rust_config s.

Definition rust_config'_of_string (s : string) : error + rust_config' :=
  @from_string rust_config' Deserialize_rust_config' s.

Definition elm_config_of_string (s : string) : error + elm_config :=
  @from_string elm_config Deserialize_elm_config s.

Definition elm_config'_of_string (s : string) : error + elm_config' :=
  @from_string elm_config' Deserialize_elm_config' s.

Definition certirocq_config_of_string (s : string) : error + certirocq_config :=
  @from_string certirocq_config Deserialize_certirocq_config s.

Definition certirocq_config'_of_string (s : string) : error + certirocq_config' :=
  @from_string certirocq_config' Deserialize_certirocq_config' s.

Definition program_type_of_string (s : string) : error + Serialize.program_type :=
  @from_string Serialize.program_type Deserialize_program_type s.

Definition ocaml_config_of_string (s : string) : error + ocaml_config :=
  @from_string ocaml_config Deserialize_ocaml_config s.

Definition ocaml_config'_of_string (s : string) : error + ocaml_config' :=
  @from_string ocaml_config' Deserialize_ocaml_config' s.

Definition cakeml_config_of_string (s : string) : error + cakeml_config :=
  @from_string cakeml_config Deserialize_cakeml_config s.

Definition cakeml_config'_of_string (s : string) : error + cakeml_config' :=
  @from_string cakeml_config' Deserialize_cakeml_config' s.

Definition fsharp_config_of_string (s : string) : error + fsharp_config :=
  @from_string fsharp_config Deserialize_fsharp_config s.

Definition fsharp_config'_of_string (s : string) : error + fsharp_config' :=
  @from_string fsharp_config' Deserialize_fsharp_config' s.

Definition eval_config_of_string (s : string) : error + eval_config :=
  @from_string eval_config Deserialize_eval_config s.

Definition eval_config'_of_string (s : string) : error + eval_config' :=
  @from_string eval_config' Deserialize_eval_config' s.

Definition ASTType_of_string (s : string) : error + ASTType :=
  @from_string ASTType Deserialize_ASTType s.

Definition ASTType'_of_string (s : string) : error + ASTType' :=
  @from_string ASTType' Deserialize_ASTType' s.

Definition ast_config_of_string (s : string) : error + ast_config :=
  @from_string ast_config Deserialize_ast_config s.

Definition ast_config'_of_string (s : string) : error + ast_config' :=
  @from_string ast_config' Deserialize_ast_config' s.

Definition backend_config_of_string (s : string) : error + backend_config :=
  @from_string backend_config Deserialize_backend_config s.

Definition backend_config'_of_string (s : string) : error + backend_config' :=
  @from_string backend_config' Deserialize_backend_config' s.



(** ** Config *)

Definition remapped_inductive_of_string (s : string) : error + remapped_inductive :=
  @from_string remapped_inductive Deserialize_remapped_inductive s.

Definition inductive_mapping_of_string (s : string) : error + EProgram.inductive_mapping :=
  @from_string inductive_mapping Deserialize_inductive_mapping s.

Definition remapped_constant_of_string (s : string) : error + remapped_constant :=
  @from_string remapped_constant Deserialize_remapped_constant s.

Definition extract_inductive_of_string (s : string) : error + extract_inductive :=
  @from_string extract_inductive Deserialize_extract_inductive s.

Definition remap_inductive_of_string (s : string) : error + remap_inductive :=
  @from_string remap_inductive Deserialize_remap_inductive s.

Definition custom_attribute_of_string (s : string) : error + custom_attribute :=
  @from_string custom_attribute Deserialize_custom_attribute s.

Definition inlinings_of_string (s : string) : error + inlinings :=
  @from_string inlinings Deserialize_inlinings s.

Definition constant_remappings_of_string (s : string) : error + constant_remappings :=
  @from_string constant_remappings Deserialize_constant_remappings s.

Definition inductive_remappings_of_string (s : string) : error + inductive_remappings :=
  @from_string inductive_remappings Deserialize_inductive_remappings s.

Definition custom_attributes_of_string (s : string) : error + custom_attributes :=
  @from_string custom_attributes Deserialize_custom_attributes s.

Definition erasure_phases_of_string (s : string) : error + erasure_phases :=
  @from_string erasure_phases Deserialize_erasure_phases s.

Definition erasure_phases'_of_string (s : string) : error + erasure_phases' :=
  @from_string erasure_phases' Deserialize_erasure_phases' s.

Definition config_of_string (s : string) : error + config :=
  @from_string config Deserialize_config s.

Definition config'_of_string (s : string) : error + config' :=
  @from_string config' Deserialize_config' s.

Definition attributes_config_of_string (s : string) : error + attributes_config :=
  @from_string attributes_config Deserialize_attributes_config s.
