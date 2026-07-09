From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require EProgram.
From Malfunction Require Serialize.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import DeserializeCommon.
From Peregrine Require Import SerializeCommon.
From Peregrine Require Import DeserializeConfig.
From Peregrine Require Import SerializeConfig.
From Peregrine Require Import SerializeCommonComplete.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.


Import ListNotations.
Local Open Scope bs_scope.



(** ** Backend Config *)


Instance Complete_rust_config : CompleteClass rust_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident].
  simpl_bytes.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_rust_config' : CompleteClass rust_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident].
  simpl_bytes.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_elm_config : CompleteClass elm_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident].
  simpl_bytes.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_elm_config' : CompleteClass elm_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident].
  simpl_bytes.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_certirocq_config : CompleteClass certirocq_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident Deserialize_SemiIntegral].
  simpl_bytes.
  rewrite 6!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_certirocq_config' : CompleteClass certirocq_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool Deserialize_ident Deserialize_SemiIntegral Deserialize_option].
  simpl_bytes.
  rewrite 6!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_program_type : CompleteClass Serialize.program_type.
Proof.
  unfold CompleteClass, Complete.
  intros l a.
  destruct a.
  - reflexivity.
  - cbn -[Deserialize_ident].
    simpl_bytes.
    rewrite 2!complete_class.
    reflexivity.
Qed.

Instance Complete_ocaml_config : CompleteClass ocaml_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_program_type].
  simpl_bytes.
  rewrite 1!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_ocaml_config' : CompleteClass ocaml_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_program_type].
  simpl_bytes.
  rewrite 1!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_cakeml_config : CompleteClass cakeml_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn.
  destruct o.
  reflexivity.
Qed.

Instance Complete_cakeml_config' : CompleteClass cakeml_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn.
  destruct o.
  reflexivity.
Qed.

Instance Complete_eval_config : CompleteClass eval_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_certirocq_config Deserialize_bool Deserialize_SemiIntegral].
  simpl_bytes.
  rewrite 3!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_eval_config' : CompleteClass eval_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_certirocq_config' Deserialize_bool Deserialize_SemiIntegral].
  simpl_bytes.
  rewrite 3!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_ASTType : CompleteClass ASTType.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  destruct o.
  - cbn -[Deserialize_certirocq_config].
    simpl_bytes.
    reflexivity.
  - cbn -[Deserialize_certirocq_config].
    simpl_bytes.
    reflexivity.
  - cbn -[Deserialize_certirocq_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
Qed.

Instance Complete_ASTType' : CompleteClass ASTType'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  destruct o.
  - cbn -[Deserialize_certirocq_config' Deserialize_option].
    simpl_bytes.
    reflexivity.
  - cbn -[Deserialize_certirocq_config' Deserialize_option].
    simpl_bytes.
    reflexivity.
  - cbn -[Deserialize_certirocq_config' Deserialize_option].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config' Deserialize_option].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config' Deserialize_option].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config' Deserialize_option].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
Qed.

Instance Complete_ast_config : CompleteClass ast_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_certirocq_config].
  simpl_bytes.
  rewrite complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_ast_config' : CompleteClass ast_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_certirocq_config' Deserialize_option].
  simpl_bytes.
  rewrite complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_backend_config : CompleteClass backend_config.
Proof.
  unfold CompleteClass, Complete.
  intros l b.
  destruct b.
  - cbn -[Deserialize_rust_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_elm_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_ocaml_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_cakeml_config'].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_eval_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_ast_config].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
Qed.

Instance Complete_backend_config' : CompleteClass backend_config'.
Proof.
  unfold CompleteClass, Complete.
  intros l b.
  destruct b.
  - cbn -[Deserialize_rust_config'].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_elm_config'].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config'].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_certirocq_config'].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_ocaml_config'].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_cakeml_config'].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_eval_config'].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
  - cbn -[Deserialize_ast_config'].
    simpl_bytes.
    rewrite complete_class.
    reflexivity.
Qed.



(** ** Config *)

Instance Complete_remapped_inductive : CompleteClass remapped_inductive.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_ident Deserialize_list Deserialize_option].
  simpl_bytes.
  rewrite 3!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_remapped_constant : CompleteClass remapped_constant.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_ident Deserialize_list Deserialize_option Deserialize_bool Deserialize_SemiIntegral].
  simpl_bytes.
  rewrite 5!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_inductive_mapping : CompleteClass EProgram.inductive_mapping.
Proof.
  unfold CompleteClass, Complete.
  intros l a.
  destruct a, p.
  cbn -[Deserialize_ident Deserialize_list Deserialize_inductive].
  simpl_bytes.
  rewrite 3!complete_class.
  reflexivity.
Qed.

Instance Complete_extract_inductive : CompleteClass EProgram.extract_inductive.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_kername Deserialize_list].
  simpl_bytes.
  rewrite 2!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_remap_inductive : CompleteClass remap_inductive.
Proof.
  unfold CompleteClass, Complete.
  intros l r.
  destruct r.
  - cbn -[Deserialize_extract_inductive Deserialize_kername Deserialize_list].
    simpl_bytes.
    rewrite 2!complete_class.
    reflexivity.
  - cbn -[Deserialize_remapped_inductive Deserialize_inductive].
    simpl_bytes.
    rewrite 2!complete_class.
    reflexivity.
Qed.

Instance Complete_custom_attribute : CompleteClass custom_attribute.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_inlinings : CompleteClass inlinings.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_constant_remappings : CompleteClass constant_remappings.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_inductive_remappings : CompleteClass inductive_remappings.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_custom_attributes : CompleteClass custom_attributes.
Proof.
  typeclasses eauto.
Qed.

Instance Complete_erasure_phases : CompleteClass erasure_phases.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool].
  simpl_bytes.
  rewrite 8!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_erasure_phases' : CompleteClass erasure_phases'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_bool].
  simpl_bytes.
  rewrite 8!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_config : CompleteClass config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_backend_config Deserialize_erasure_phases Deserialize_option Deserialize_list Deserialize_inlinings Deserialize_inductive_mapping Deserialize_constant_remappings Deserialize_inductive_remappings Deserialize_custom_attributes].
  simpl_bytes.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_config' : CompleteClass config'.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_backend_config' Deserialize_erasure_phases' Deserialize_option Deserialize_list Deserialize_inlinings Deserialize_inductive_mapping Deserialize_constant_remappings Deserialize_inductive_remappings Deserialize_custom_attributes].
  simpl_bytes.
  rewrite 7!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.

Instance Complete_attributes_config : CompleteClass attributes_config.
Proof.
  unfold CompleteClass, Complete.
  intros l o.
  cbn -[Deserialize_list Deserialize_inlinings Deserialize_inductive_mapping Deserialize_constant_remappings Deserialize_inductive_remappings Deserialize_custom_attributes].
  simpl_bytes.
  rewrite 5!complete_class.
  destruct o; cbn.
  reflexivity.
Qed.
