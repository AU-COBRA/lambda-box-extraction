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
From Peregrine Require Import SerializeCommonSound.
From Stdlib Require Import List.
From CeresBS Require Import Ceres.


Import ListNotations.
Local Open Scope bs_scope.



(** ** Backend Config *)

Instance Sound_rust_config : SoundClass rust_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_rust_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_rust_config' : SoundClass rust_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_rust_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_elm_config : SoundClass elm_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_elm_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_elm_config' : SoundClass elm_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_elm_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_certirocq_config : SoundClass certirocq_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  unfold to_sexp, Serialize_certirocq_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, Ea5.
  reflexivity.
Qed.

Instance Sound_certirocq_config' : SoundClass certirocq_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  unfold to_sexp, Serialize_certirocq_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5.
  reflexivity.
Qed.

Instance Sound_program_type : SoundClass Serialize.program_type.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [-> ->].
    cbn.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea0.
    apply sound_class in Ea1.
    cbn.
    rewrite <- Ea0, <- Ea1.
    reflexivity.
Qed.

Instance Sound_ocaml_config : SoundClass ocaml_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea1.
  unfold to_sexp, Serialize_ocaml_config.
  cbn.
  rewrite <- Ea1.
  reflexivity.
Qed.

Instance Sound_ocaml_config' : SoundClass ocaml_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea1.
  unfold to_sexp, Serialize_ocaml_config'.
  cbn.
  rewrite <- Ea1.
  reflexivity.
Qed.

Instance Sound_cakeml_config : SoundClass cakeml_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  destruct a.
  apply (@sound_class _ Serialize_unit Deserialize_unit _)  in He.
  exact He.
Qed.

Instance Sound_cakeml_config' : SoundClass cakeml_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  destruct a.
  apply (@sound_class _ Serialize_unit Deserialize_unit _)  in He.
  exact He.
Qed.

Instance Sound_eval_config : SoundClass eval_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  unfold to_sexp, Serialize_eval_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  reflexivity.
Qed.

Instance Sound_eval_config' : SoundClass eval_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  unfold to_sexp, Serialize_eval_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  reflexivity.
Qed.

Instance Sound_ASTType : SoundClass ASTType.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [es ?]; subst.
    reflexivity.
  - destruct He as [es ?]; subst.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
Qed.

Instance Sound_ASTType' : SoundClass ASTType'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [es ?]; subst.
    reflexivity.
  - destruct He as [es ?]; subst.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
Qed.

Instance Sound_ast_config : SoundClass ast_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea1.
  rewrite <- Ea1.
  cbn.
  reflexivity.
Qed.

Instance Sound_ast_config' : SoundClass ast_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea1.
  rewrite <- Ea1.
  cbn.
  reflexivity.
Qed.

Instance Sound_backend_config : SoundClass backend_config.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
Qed.

Instance Sound_backend_config' : SoundClass backend_config'.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea1.
    rewrite <- Ea1.
    reflexivity.
Qed.



(** ** Config *)

Instance Sound_remapped_inductive : SoundClass remapped_inductive.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  unfold to_sexp, Serialize_remapped_inductive.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  reflexivity.
Qed.

Instance Sound_remapped_constant : SoundClass remapped_constant.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  unfold to_sexp, Serialize_remapped_constant.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4.
  reflexivity.
Qed.

Instance Sound_inductive_mapping : SoundClass EProgram.inductive_mapping.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  destruct a, p.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  unfold to_sexp, Serialize_inductive_mapping.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2.
  reflexivity.
Qed.

Instance Sound_extract_inductive : SoundClass EProgram.extract_inductive.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  destruct a.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  unfold to_sexp, Serialize_extract_inductive.
  cbn.
  rewrite <- Ea0, <- Ea1.
  reflexivity.
Qed.

Instance Sound_remap_inductive : SoundClass remap_inductive.
Proof.
  unfold SoundClass, Sound.
  intros l e n He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea0.
    apply sound_class in Ea1.
    rewrite <- Ea0, <- Ea1.
    reflexivity.
  - destruct He as [es [<- He]].
    sound_field He.
    apply sound_class in Ea0.
    apply sound_class in Ea1.
    rewrite <- Ea0, <- Ea1.
    reflexivity.
Qed.

Instance Sound_custom_attribute : SoundClass custom_attribute.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_inlinings : SoundClass inlinings.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_constant_remappings : SoundClass constant_remappings.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_inductive_remappings : SoundClass inductive_remappings.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_custom_attributes : SoundClass custom_attributes.
Proof.
  typeclasses eauto.
Qed.

Instance Sound_erasure_phases : SoundClass erasure_phases.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  apply sound_class in Ea7.
  unfold to_sexp, Serialize_erasure_phases.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6, <- Ea7.
  reflexivity.
Qed.

Instance Sound_erasure_phases' : SoundClass erasure_phases'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  apply sound_class in Ea7.
  unfold to_sexp, Serialize_erasure_phases'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6, <- Ea7.
  reflexivity.
Qed.

Instance Sound_config : SoundClass config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_config' : SoundClass config'.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  apply sound_class in Ea5.
  apply sound_class in Ea6.
  unfold to_sexp, Serialize_config'.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4, <- Ea5, <- Ea6.
  reflexivity.
Qed.

Instance Sound_attributes_config : SoundClass attributes_config.
Proof.
  unfold SoundClass, Sound.
  intros l e a He.
  apply sound_match_con in He.
  destruct He as [He | He]; elim_Exists He.
  destruct He as [es [<- He]].
  sound_field He.
  apply sound_class in Ea0.
  apply sound_class in Ea1.
  apply sound_class in Ea2.
  apply sound_class in Ea3.
  apply sound_class in Ea4.
  unfold to_sexp, Serialize_attributes_config.
  cbn.
  rewrite <- Ea0, <- Ea1, <- Ea2, <- Ea3, <- Ea4.
  reflexivity.
Qed.
