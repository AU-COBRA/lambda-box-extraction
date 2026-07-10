From Stdlib Require Import Program ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Transform config.
From MetaRocq.Template Require Import EtaExpand TemplateProgram.
From MetaRocq.PCUIC Require PCUICAst PCUICAstUtils PCUICProgram.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnvImpl.
From MetaRocq.Erasure Require EAstUtils ErasureFunction ErasureCorrectness EPretty Extract.
From MetaRocq.Erasure Require Import EProgram EInlining EBeta EWellformed.
From MetaRocq.ErasurePlugin Require Import ETransform Erasure.
From MetaRocq.Erasure Require EImplementBox.
From Peregrine Require EImplementLazyForce.
From Peregrine Require Import EInstanceSpecialize.
From Peregrine Require Import ECommonSubexpr.
From Malfunction Require Pipeline.

Import PCUICProgram.
Import PCUICTransform (template_to_pcuic_transform, pcuic_expand_lets_transform).

Import bytestring.
Local Open Scope bs.
Local Open Scope string_scope2.

Import Common.Transform.Transform.

#[local] Existing Instance extraction_checker_flags.
#[local] Existing Instance PCUICSN.extraction_normalizing.

Local Obligation Tactic := idtac.



Program Definition implement_box_transformation
  (efl := EConstructorsAsBlocks.switch_cstr_as_blocks
  (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params all_env_flags))) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram EImplementBox.block_wcbv_flags) (eval_eprogram EImplementBox.block_wcbv_flags) :=
  {| name := "implementing box";
    transform p _ := EImplementBox.implement_box_program p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram (EImplementBox.switch_off_box efl) p ;
    obseq p hp p' v v' := v' = EImplementBox.implement_box v |}.
Next Obligation.
  intros. cbn in *.
  split.
  - eapply EImplementBox.implement_box_env_wf_glob; eauto. apply p.
  - eapply EImplementBox.transform_wellformed'. all: try reflexivity. all: apply p.
Qed.
Final Obligation.
  red. intros. destruct pr. destruct H.
  eexists. split; [ | eauto].
  econstructor.
  eapply EImplementBox.implement_box_eval; cbn; eauto.
  all: try reflexivity.
Admitted.

Program Definition implement_lazy_force_transformation
  (efl := EConstructorsAsBlocks.switch_cstr_as_blocks
  (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params all_env_flags))) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram final_wcbv_flags) (eval_eprogram final_wcbv_flags) :=
  {| name := "implementing lazy/force";
    transform p _ := EImplementLazyForce.implement_lazy_force_program p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram (EImplementLazyForce.switch_off_thunk efl) p ;
    obseq p hp p' v v' := v' = EImplementLazyForce.implement_lazy_force v |}.
Next Obligation.
  intros. cbn in *.
  split.
  - eapply EImplementLazyForce.implement_lazy_force_env_wf_glob; eauto. apply p.
  - eapply EImplementLazyForce.transform_wellformed'. all: try reflexivity. all: apply p.
Qed.
Final Obligation.
  red. intros. destruct pr. destruct H.
  eexists. split; [ | eauto].
  econstructor.
  eapply EImplementLazyForce.implement_lazy_force_eval; cbn; eauto.
  all: try reflexivity.
Admitted.

Definition switch_off_box_wf env t l :
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params all_env_flags)) in
  wellformed (EImplementBox.switch_off_box efl) env l t ->
  wellformed efl env l t.
Proof.
  cbn.
  generalize dependent l.
  induction t using EInduction.term_forall_list_ind; auto; try discriminate; intro l'; try (simpl; rtoProp; solve_all).
  - unfold wf_fix in *.
    rtoProp.
    solve_all.
  - unfold wf_fix in *.
    rtoProp.
    solve_all.
  - inversion X; auto; subst.
    destruct X0.
    cbn in *. unfold EPrimitive.test_array_model in *.
    rtoProp. solve_all.
Qed.

Definition switch_off_box_wf_glob env :
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params all_env_flags)) in
  wf_glob (EImplementBox.switch_off_box efl) env ->
  wf_glob efl env.
Proof.
  cbn.
  induction env.
  - constructor.
  - destruct a. cbn.
    intros.
    inversion H; subst.
    constructor; auto.
    destruct g.
    + destruct c, cst_body0; auto.
      apply switch_off_box_wf. assumption.
    + cbn.
      assumption.
Qed.

Definition switch_off_box_wf_eprogram p :
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params all_env_flags)) in
  wf_eprogram (EImplementBox.switch_off_box efl) p ->
  wf_eprogram efl p.
Proof.
  intros.
  destruct H.
  split.
  - apply switch_off_box_wf_glob.
    assumption.
  - apply switch_off_box_wf.
    assumption.
Qed.


Program Definition extra_unsafe_transforms (spec_inst cse impl_box impl_lazy_force : bool) :=
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
  (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
  (* Instance/dictionary specialization runs first, in the same
     constructors-as-blocks lambda-box regime as [implement_box], so that the
     subsequent betared (in [optional_unsafe_transforms]) and dead-argument
     elimination can clean up the exposed dictionary plumbing. Common-
     subexpression elimination runs next, in the same regime, restoring the
     sharing that erasure drops. *)
  ETransform.optional_self_transform spec_inst
    (specialize_instances_transformation efl EImplementBox.block_wcbv_flags) ▷
  ETransform.optional_self_transform cse
    (cse_transformation efl EImplementBox.block_wcbv_flags) ▷
  ETransform.optional_self_transform impl_box implement_box_transformation ▷
  ETransform.optional_self_transform impl_lazy_force implement_lazy_force_transformation.
Next Obligation.
  cbn. intros.
  destruct spec_inst, cse, impl_box, impl_lazy_force; cbn in *;
    try assumption; try (apply switch_off_box_wf_eprogram; assumption).
Qed.
Next Obligation.
  cbn. intros.
  destruct spec_inst, cse, impl_box, impl_lazy_force; cbn in *;
    try assumption; try (apply switch_off_box_wf_eprogram; assumption).
Qed.
Next Obligation.
  cbn. intros.
  destruct spec_inst, cse, impl_box, impl_lazy_force; cbn in *;
    try assumption; try (apply switch_off_box_wf_eprogram; assumption).
Qed.



Program Definition untyped_transform_pipeline {guard : abstract_guard_impl}
  (efl := all_env_flags) econf spec_inst cse impl_box impl_lazy_force
  : Transform.t _ _ _ EAst.term _ _
   (* Standard evaluation, with cases on prop, guarded fixpoints, applied constructors *)
   (eval_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (* Target evaluation, with no more cases on prop, unguarded fixpoints, constructors as block *)
   (EProgram.eval_eprogram final_wcbv_flags) :=
  rebuild_wf_env_transform_mapping true true ▷
  verified_lambdabox_pipeline_mapping ▷
  optional_unsafe_transforms econf ▷
  extra_unsafe_transforms spec_inst cse impl_box impl_lazy_force.
Next Obligation.
  cbn. intros.
  destruct H as [? [? ?]].
  destruct enable_unsafe as [[] ? ? ?]=> //.
  split; auto.
  split; auto.
Qed.
Next Obligation.
  cbn. intros.
  destruct enable_unsafe as [[] ? ? ?]=> //.
Qed.
Final Obligation.
  cbn. intros.
  destruct enable_unsafe.
  cbn in H.
  destruct betared, spec_inst, cse, impl_box, impl_lazy_force; auto.
Qed.


Section Dearging.
  Import Optimize OptimizeCorrectness.

  Definition dearg (p : (option dearg_set × ExAst.global_env) * EAst.term) : ExAst.global_env * EAst.term :=
    match p.1.1 with
    | Some masks => ((dearg_env masks p.1.2), dearg_term masks p.2)
    | None => (p.1.2, p.2)
    end.

  Program Definition dearging_transform (efl := EWellformed.all_env_flags) cf :
    Transform.t _ _  EAst.term EAst.term _ _ (eval_typed_eprogram_masks EWcbvEval.opt_wcbv_flags) (eval_typed_eprogram EWcbvEval.opt_wcbv_flags) :=
    {| name := "dearging";
      transform p _ := dearg p ;
      pre p := post_dearging_checks efl cf p;
      post p := wf_eprogram efl (ExAst.trans_env p.1, p.2) /\ EEtaExpandedFix.expanded_eprogram (ExAst.trans_env p.1, p.2) ;
      obseq p hp p' v v' := v' = (dearg (p.1, v)).2 |}.
  Next Obligation.
  Proof.
    cbn. intros.
    unfold dearg.
    destruct p. rewrite H.
    destruct check_dearging_precond eqn:eqp; cbn -[ExAst.trans_env] => //.
    destruct input as [[masks env] t]. cbn -[ExAst.trans_env Optimize.dearg_env] in *.
    subst masks. destruct H0 as [wf exp].
    eapply check_dearging_precond_spec in eqp. intuition.
    - split; cbn.
      unfold dearg_env.
      eapply wf_glob_debox.
      eapply wf_glob_dearg; eauto.
      eapply wf.
      rewrite /dearg_env. rewrite -trans_env_debox.
      eapply wellformed_dearg; eauto.
      eapply wf.
    - rewrite /dearg_env -trans_env_debox. split; cbn.
      eapply expanded_dearg_env; tea. apply exp.
      eapply EEtaExpandedFix.isEtaExp_expanded, expanded_dearg; eauto.
      apply EEtaExpandedFix.expanded_isEtaExp, exp.
  Qed.
  Final Obligation.
    cbn. intros. red.
    intros p v [he [wfe exp]]. unfold eval_typed_eprogram_masks.
    intros [ev].
    unfold dearg. rewrite he.
    destruct (check_dearging_precond) as [masks|] eqn:cpre.
    * eapply (ExtractionCorrectness.extract_correct_gen' _ _ _ masks cf.(overridden_masks) cf.(do_trim_const_masks) cf.(do_trim_ctor_masks)) in ev as ev'.
      destruct ev' as [ev'].
      eexists. split. red. sq. cbn. exact ev'. auto.
      - destruct wfe. now eapply EWellformed.wellformed_closed_env.
      - destruct wfe. now eapply EWellformed.wellformed_closed.
      - move: cpre. unfold check_dearging_precond. destruct EGlobalEnv.closed_env => //.
        destruct ExtractionCorrectness.compute_masks => //.
        destruct (_ && _) => //. congruence.
      - move: cpre. rewrite /check_dearging_precond.
        destruct EGlobalEnv.closed_env => //.
        destruct ExtractionCorrectness.compute_masks => //.
        destruct valid_cases eqn:vc => //. cbn.
        destruct is_expanded => //. now intros [= ->].
      - move: cpre. rewrite /check_dearging_precond.
        destruct EGlobalEnv.closed_env => //.
        destruct ExtractionCorrectness.compute_masks => //.
        destruct valid_cases eqn:vc => //. cbn.
        destruct is_expanded eqn:ise => //. now intros [= ->].
    * exists v. cbn. split => //.
  Qed.
End Dearging.

Program Definition dearging_transform_mapping (cf : ETransform.dearging_config) :
  Transform.t _ _ _ _ _ _ (eval_typed_eprogram_masks_mapping EWcbvEval.opt_wcbv_flags) (eval_typed_eprogram_mapping EWcbvEval.opt_wcbv_flags)  :=
  let tr := (dearging_transform cf) in
 {| name := name tr;
    pre p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1.2) p.1 /\ pre tr p.2 ;
    transform p hp := let nhs := proj2 hp in (p.1, transform tr p.2 nhs) ;
    post p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ post tr p.2;
    obseq p hp p' := obseq tr p.2 (proj2 hp) p'.2 |}.
Next Obligation.
Proof.
  cbn.
  split => //.
  2:{ now unshelve eapply (correctness (dearging_transform cf)). }
  destruct p.
  move: H; rewrite /EReorderCstrs.wf_inductives_mapping; solve_all.
  move: H; rewrite /EReorderCstrs.wf_inductive_mapping. destruct x as [ind [na tags]].
  rewrite /dearg. destruct input.2.1.1 => //.
  rewrite /OptimizeCorrectness.dearg_env.
  rewrite /EGlobalEnv.lookup_inductive /EGlobalEnv.lookup_minductive /=.
  rewrite !OptimizeCorrectness.lookup_env_trans_env.
  rewrite OptimizeCorrectness.lookup_env_debox_env_types option_map_two /=.
  rewrite OptimizeCorrectness.lookup_env_dearg_env option_map_two /=.
  destruct ExAst.lookup_env => //=; destruct g => //=.
  rewrite !nth_error_map option_map_two /=.
  rewrite /Optimize.dearg_mib /=. destruct Optimize.get_mib_masks => //=.
  rewrite !nth_error_mapi.
  1-2:destruct nth_error eqn:hnth => //=; len.
  intros _. destruct o => //=. destruct p => //.
Qed.
Final Obligation.
Proof.
  intros cf p v pr ev. cbn.
  now unshelve eapply (preservation (dearging_transform cf)).
Qed.

Program Definition typed_transform_pipeline {guard : abstract_guard_impl}
  (efl := EWellformed.all_env_flags) econf
  : Transform.t _ _ _ _ _ _
   (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (eval_typed_eprogram_mapping EWcbvEval.opt_wcbv_flags) :=

   remove_match_on_box_typed_transform_mapping (wcon := eq_refl) (hastrel := eq_refl) (hastbox := eq_refl)
    (fl := EWcbvEval.default_wcbv_flags) ▷
   (* Check if the preconditions for dearging are valid, otherwise dearging will be the identity *)
   dearging_checks_transform_mapping econf.(dearging_config) (hastrel := eq_refl) (hastbox := eq_refl) ▷
   dearging_transform_mapping econf.(dearging_config).
Next Obligation.
  program_simpl.
Qed.
Next Obligation.
  program_simpl.
Qed.
Next Obligation.
  program_simpl.
Qed.
Next Obligation.
  program_simpl.
Qed.
Next Obligation.
  intros. cbn.
  apply H.
Qed.
Final Obligation.
  cbn. intros.
  apply H.
Qed.




Program Definition trans_env_transform {fl : EWcbvEval.WcbvFlags} {efl : EWellformed.EEnvFlags} :
  Transform.t _ _  _ _ _ _ (eval_typed_eprogram_mapping fl) (eval_eprogram_mapping fl) :=
  {| name := "typed to untyped transform";
    pre p := EReorderCstrs.wf_inductives_mapping (ExAst.trans_env p.2.1) p.1 /\ wf_eprogram efl (ExAst.trans_env p.2.1, p.2.2) /\ EEtaExpandedFix.expanded_eprogram (ExAst.trans_env p.2.1, p.2.2);
    transform p hp := (p.1, (ExAst.trans_env p.2.1, p.2.2)) ;
    post p := EReorderCstrs.wf_inductives_mapping p.2.1 p.1 /\ wf_eprogram efl p.2 /\ EEtaExpandedFix.expanded_eprogram p.2 ;
    obseq p hp p' v v' := v' = v |}.
Next Obligation.
  intros ? ? ? H.
  cbn in *.
  move: H; rewrite /EReorderCstrs.wf_inductives_mapping; solve_all.
Qed.
Final Obligation.
  intros ? ? ? ? ? ?.
  unfold eval_typed_eprogram_mapping, eval_typed_eprogram in H.
  exists v.
  unfold eval_eprogram_mapping, eval_eprogram.
  cbn.
  split; auto.
Qed.


Program Definition typed_to_untyped_transform_pipeline {guard : abstract_guard_impl}
  (efl := EWellformed.all_env_flags) econf spec_inst cse impl_box impl_lazy_force
  : Transform.t _ _ _ _ _ _
   (eval_typed_eprogram_mapping EWcbvEval.default_wcbv_flags)
   (EProgram.eval_eprogram final_wcbv_flags) :=

   typed_transform_pipeline econf ▷
   trans_env_transform ▷
   rebuild_wf_env_transform_mapping true true ▷
   verified_lambdabox_typed_pipeline econf ▷
   extra_unsafe_transforms spec_inst cse impl_box impl_lazy_force.
Next Obligation.
  intros.
  cbn in *.
  destruct H as [? [? ?]].
  split; auto.
Qed.
Next Obligation.
  intros.
  cbn in *.
  destruct H as [? [? ?]].
  split; auto.
Qed.
Next Obligation.
  intros.
  cbn in *.
  destruct H as [? [? ?]].
  split; auto.
Qed.
Final Obligation.
  cbn. intros.
  destruct enable_unsafe.
  cbn in H.
  destruct betared, spec_inst, cse, impl_box, impl_lazy_force; auto.
Qed.


Program Definition run_untyped_transforms econf ind_reorder spec_inst cse impl_box impl_lazy_force p :=
  run (untyped_transform_pipeline econf spec_inst cse impl_box impl_lazy_force) (ind_reorder, p) _.
Final Obligation.
Admitted. (* assumed for now, check_wf should ensure this *)

Program Definition run_typed_transforms econf ind_reorder p :=
  run (typed_transform_pipeline econf) (ind_reorder, p) _.
Final Obligation.
Admitted. (* assumed for now, check_wf should ensure this *)

Program Definition run_typed_to_untyped_transforms econf ind_reorder spec_inst cse impl_box impl_lazy_force p :=
  run (typed_to_untyped_transform_pipeline econf spec_inst cse impl_box impl_lazy_force) (ind_reorder, p) _.
Final Obligation.
Admitted. (* assumed for now, check_wf should ensure this *)
