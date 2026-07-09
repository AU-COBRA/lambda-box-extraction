(** * Common-subexpression elimination / let-introduction for lambda-box
      (unverified first cut)

    Motivation.  Several Peregrine frontends do not preserve [let] bindings:
    Agda inlines its internal let-bindings before erasure, and Lean drops them
    entirely.  A subterm that the source shared through a [let] is therefore
    *duplicated* in the erased lambda-box term and, under the call-by-value
    semantics of the backends, recomputed once per occurrence at run time.  This
    is a documented cause of the Lean sieve / Fannkuch slowdowns and of Agda's
    general inefficiency.  A middle-end CSE pass reverses the damage for every
    frontend at once: it hoists a repeated subterm into a single [tLetIn] and
    replaces its occurrences by a bound variable, so the work is performed once.

    Why this is a win in lambda-box specifically.  Lambda-box is pure (erasure
    has already discarded proofs and types; there are no observable effects), so
    sharing a subterm never changes the *result*.  Under the backends'
    call-by-value evaluation a [tLetIn] forces its bindee exactly once before the
    body runs, which is precisely the sharing we want.  CSE cannot change
    strictness here either: everything the pass hoists is a *manifest subterm*
    that the original program already evaluates on every occurrence, so pulling
    it out to a [let] that runs once can only remove work, never add it, and can
    never move a diverging computation to a point where the program did not
    already demand it (see the "only hoist subterms that already run on every
    path" caveat in the risks section of the design notes).

    ---------------------------------------------------------------------------
    ALGORITHM (this first cut).

    Scope.  The pass runs per constant body.  Constant bodies in a lambda-box
    global environment are *closed* (no dangling [tRel]).  We exploit that: we
    only ever hoist a subterm [s] that is itself **closed** ([closedn 0 s]).  A
    closed subterm is invariant under [lift], is identical wherever it appears
    regardless of the number of enclosing binders, and can be substituted by a
    de-Bruijn index that points at a freshly-introduced outermost [let] binder.
    This makes the transform correct-by-construction with no index arithmetic
    beyond "count the binders you have descended under".

    Steps, for a closed constant body [t]:
      1. Collect the multiset of all subterms of [t] (fuel-bounded traversal).
      2. Keep the candidates: subterms that are [closedn 0] and whose structural
         [size] is at least [cse_threshold] (small subterms are not worth a
         binder; and hoisting a bare [tRel]/[tConst] would be pointless).
      3. Keep those occurring at least [cse_min_occ] (= 2) times.
      4. Score each surviving candidate by its estimated dynamic saving,
         [(occurrences - 1) * size], and pick the maximum (the "best" one).
      5. Emit  [tLetIn "cse" best (abstract 0 best t)]  where [abstract k s u]
         replaces every occurrence of [s] in [u] by [tRel k], incrementing [k]
         under each binder so the index always resolves to the outer [let].

    This performs ONE hoist per constant.  Iterating to a fixpoint (hoist,
    re-scan, hoist the next-best, ...) and hoisting *nested* common subterms is a
    straightforward extension left as next work (see EXTENSIONS below); the
    single-hoist core already captures the largest repeated subterm, which is the
    dominant win on the motivating benchmarks.

    EXTENSIONS (not implemented here, deliberately):
      - Open subterms.  A subterm with free [tRel]s that are all bound *above*
        the nearest common ancestor of its occurrences may still be hoisted to
        that ancestor with a [lift].  This is the "de-Bruijn-consistent" case; it
        needs nearest-common-binder-scope analysis and is the natural v2.
      - Iteration to a fixpoint and simultaneous multi-candidate hoisting.
      - Descending into [tPrim] array payloads (skipped here as a leaf).

    ---------------------------------------------------------------------------
    PIPELINE PLACEMENT AND VERIFICATION STATUS.

    CSE is the *inverse* of inlining/beta, so ordering matters: it must run
    AFTER [EInlining]/[EBeta]/dearg, near the very end of the unsafe tail,
    otherwise a later beta/inline pass would just undo it (or, worse, CSE would
    fight an inliner that is trying to specialize).  The intended slot is inside
    [extra_unsafe_transforms] in erasure/Transforms.v, immediately AFTER
    [specialize_instances]/[betared] and before/after [implement_box]
    (implement_box does not create sharing opportunities, so either side is
    fine; placing it last keeps it closest to code generation).

    It is a [Compatible]-class, opt-in optional phase, wired exactly like
    [EInstanceSpecialize]/[EBeta].  Verification status: VERIFIED, modulo one
    residual evaluation-simulation lemma.  Unlike the [trust_*]-based pattern of
    [EBeta]/[EInstanceSpecialize], this module actually discharges its trust
    obligations:

      - The core algebraic fact is proved: [abstract_subst] shows that for a
        closed [s], [subst [s] k (abstract s k t) = t] whenever [closedn k t] --
        i.e. binding [s] and substituting it back reconstructs [t].

      - Wellformedness preservation ([cse_wf], discharging what was
        [trust_cse_wf]) is fully proved: the pass is guarded to fire only when
        [has_tLetIn] and [has_tRel] hold (otherwise it is the identity), the
        hoisted [s] is a closed, non-lambda subterm of a wellformed body hence
        itself wellformed ([collect_wf], [wellformed_closedn_le]), [abstract]
        preserves wellformedness ([wellformed_abstract]), and [wellformed] is
        invariant under the constant-body environment rewrite
        ([wellformed_cse_env]).  [Print Assumptions cse_wf] shows no custom
        axioms.

      - Both [TransformExt] obligations are proved ([extends_cse]).

      - SOUNDNESS FIX: hoisting is only correct for subterms evaluated on every
        path.  [candidate_ok] now requires every occurrence of the candidate to
        be in a strict (always-evaluated) position
        ([count_term u all_strict = count_term u all_full], via [collect_strict]).
        The earlier unconditional selection was semantically UNSOUND (it could
        lift a subterm out of a [tLambda] body / untaken [tCase] branch and force
        it eagerly, changing termination).

      - Evaluation preservation ([cse_pres]) uses the correct observational
        relation [v' = v] (a sharing pass returns the SAME value; the earlier
        [v' = cse_term v] obseq was FALSE — see the note at [cse_pres_eval]).
        It is reduced to ONE clearly-stated residual [cse_pres_eval], the
        whole-program CBV simulation, which is TRUE for the strict-guarded
        selection.  Its algebraic backbone [abstract_subst] is proved; the
        remaining cross-environment induction over the [EWcbvEval] rules is left
        as a trust obligation in the manner of [EBeta.trust_betared_pres].  This
        is the sole non-primitive axiom [cse_transformation] depends on.

    ---------------------------------------------------------------------------
    WIRING STEPS LEFT AS NEXT WORK (mirrors how EInstanceSpecialize.v was
    wired; each shared file below is currently being edited by other agents, so
    these edits are deliberately NOT applied here to avoid conflicts):

      1. _CoqProject: add the line
             theories/erasure/ECommonSubexpr.v
         (after theories/erasure/EInstanceSpecialize.v).

      2. theories/Config.v:
         - add field  [cse_c : phases_config]  to record [erasure_phases_config];
         - add field  [cse : bool]             to record [erasure_phases].

      3. theories/ConfigUtils.v:
         - add  [cse' : option bool]  to [erasure_phases'] and set it to [None]
           in [empty_erasure_phases'];
         - add the corresponding line to [get_default_phases_opt]
             ([cse := get_default_phase_opt' o cse_c]) and to [enforce_phases]
             ([cse := enforce_phase' o.(cse') d.(cse) o'.(cse_c)]).

      4. The 8 backend default configs (theories/backends/*.v):
         RustBackend, ElmBackend, CBackend, WasmBackend, OCamlBackend,
         CakeMLBackend, EvalBackend, ASTBackend — add
             cse_c := Compatible false;
         to each [erasure_phases_config] literal (opt-in, off by default).

      5. Serialization (theories/serialization/):
         - SerializeConfig.v: add  [to_sexp (cse o)]  to
           [Serialize_erasure_phases] and  [to_sexp (cse' o)]  to
           [Serialize_erasure_phases'];
         - DeserializeConfig.v: bump both [erasure_phases] deserializers from
           [Deser.con8_ Build_erasure_phases(')] to [Deser.con9_ ...].

      6. theories/erasure/Transforms.v:
         - [From Peregrine Require Import ECommonSubexpr.];
         - thread a [cse : bool] parameter through [extra_unsafe_transforms],
           [untyped_transform_pipeline] and [typed_..._pipeline], adding
             ETransform.optional_self_transform cse
               (cse_transformation efl EImplementBox.block_wcbv_flags)
           to the [▷] chain (last, after specialize/box), and discharge the
           extra [destruct cse] cases in the obligations exactly as the existing
           [spec_inst]/[impl_box]/[impl_lazy_force] cases are discharged.

      7. theories/Pipeline.v:
         - read  [let do_cse := c.(erasure_opts).(cse) in]  in [apply_transforms]
           and pass [do_cse] into the [run_*_transforms] calls (alongside
           [spec_inst], [impl_box], [impl_lazy]).

      8. bin/ CLI (bin/*.ml): expose a [--cse] flag setting [cse'] to [Some true]
           (optional; the config default already governs behaviour).
    --------------------------------------------------------------------------- *)

From Stdlib Require Import List Arith.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst
     EReflect EGlobalEnv EProgram EWellformed EWcbvEval.

Import ListNotations.

(** Tunable parameters. *)
Definition cse_threshold : nat := 8.   (* minimum structural size to hoist *)
Definition cse_min_occ   : nat := 2.   (* minimum occurrence count to hoist *)
Definition cse_name : name := nNamed "cse"%bs.

(** ** Structural size *)
Fixpoint tsize (t : term) : nat :=
  match t with
  | tEvar _ ts => S (list_size tsize ts)
  | tLambda _ b => S (tsize b)
  | tLetIn _ v b => S (tsize v + tsize b)
  | tApp f a => S (tsize f + tsize a)
  | tCase _ d brs => S (tsize d + list_size (fun br => tsize (snd br)) brs)
  | tProj _ u => S (tsize u)
  | tFix mf _ => S (list_size (fun d => tsize (dbody d)) mf)
  | tCoFix mf _ => S (list_size (fun d => tsize (dbody d)) mf)
  | tConstruct _ _ args => S (list_size tsize args)
  | tLazy u => S (tsize u)
  | tForce u => S (tsize u)
  | _ => 1
  end.

(** ** Subterm collection (fuel-bounded, hence trivially terminating) *)
Fixpoint collect (fuel : nat) (t : term) : list term :=
  match fuel with
  | 0 => [t]
  | S fuel =>
      t ::
      match t with
      | tEvar _ ts => flat_map (collect fuel) ts
      | tLambda _ b => collect fuel b
      | tLetIn _ v b => collect fuel v ++ collect fuel b
      | tApp f a => collect fuel f ++ collect fuel a
      | tCase _ d brs =>
          collect fuel d ++ flat_map (fun br => collect fuel (snd br)) brs
      | tProj _ u => collect fuel u
      | tFix mf _ => flat_map (fun d => collect fuel (dbody d)) mf
      | tCoFix mf _ => flat_map (fun d => collect fuel (dbody d)) mf
      | tConstruct _ _ args => flat_map (collect fuel) args
      | tLazy u => collect fuel u
      | tForce u => collect fuel u
      | _ => []
      end
  end.

Definition subterms (t : term) : list term := collect (tsize t) t.

(** ** Strict-position subterm collection.

    Only descends into positions that call-by-value evaluation *always* reaches
    when the whole term is evaluated: both sides of an application, both parts of
    a [tLetIn], the discriminee of a [tCase], the argument of a [tProj]/[tForce],
    and constructor block-arguments.  It deliberately does NOT descend into
    [tLambda] bodies, [tFix]/[tCoFix] bodies, [tCase] branches or [tLazy] bodies
    — those may never run — so every subterm it returns is evaluated whenever the
    enclosing term is.  This is the soundness discriminator for hoisting: a
    closed subterm that runs on every path can be lifted to an outer [let]
    (which forces it once) without changing termination or the result. *)
Fixpoint collect_strict (fuel : nat) (t : term) : list term :=
  match fuel with
  | 0 => [t]
  | S fuel =>
      t ::
      match t with
      | tLetIn _ v b => collect_strict fuel v ++ collect_strict fuel b
      | tApp f a => collect_strict fuel f ++ collect_strict fuel a
      | tCase _ d _ => collect_strict fuel d
      | tProj _ u => collect_strict fuel u
      | tConstruct _ _ args => flat_map (collect_strict fuel) args
      | tForce u => collect_strict fuel u
      | _ => []
      end
  end.

Definition subterms_strict (t : term) : list term := collect_strict (tsize t) t.

(** ** Occurrence counting and de-duplication over the boolean [eqb] on terms *)
Definition count_term (x : term) (l : list term) : nat :=
  List.length (List.filter (fun y => eqb x y) l).

Definition mem_term (x : term) (l : list term) : bool :=
  List.existsb (fun y => eqb x y) l.

Definition dedup_terms (l : list term) : list term :=
  List.fold_right (fun x acc => if mem_term x acc then acc else x :: acc) [] l.

(** ** Abstraction: replace every occurrence of [s] by [tRel k], deepening [k]
       under binders.  [s] is a *closed* subterm, so it is textually identical
       at every depth and no lifting of [s] is required. *)
Fixpoint abstract (s : term) (k : nat) (t : term) {struct t} : term :=
  if eqb s t then tRel k
  else
    match t with
    | tEvar n ts => tEvar n (map (abstract s k) ts)
    | tLambda na b => tLambda na (abstract s (S k) b)
    | tLetIn na v b => tLetIn na (abstract s k v) (abstract s (S k) b)
    | tApp f a => tApp (abstract s k f) (abstract s k a)
    | tCase ci d brs =>
        tCase ci (abstract s k d)
          (map (fun br => (fst br, abstract s (k + List.length (fst br)) (snd br))) brs)
    | tProj p u => tProj p (abstract s k u)
    | tFix mf i =>
        tFix (map (map_def (abstract s (k + List.length mf))) mf) i
    | tCoFix mf i =>
        tCoFix (map (map_def (abstract s (k + List.length mf))) mf) i
    | tConstruct ind n args => tConstruct ind n (map (abstract s k) args)
    | tLazy u => tLazy (abstract s k u)
    | tForce u => tForce (abstract s k u)
    | tPrim p => tPrim p
    | tRel _ | tVar _ | tConst _ | tBox => t
    end.

(** ** Candidate selection: the closed, large-enough, repeated subterm with the
       greatest estimated dynamic saving. *)
(** A subterm is a valid hoisting candidate when it is closed, not a lambda,
    big enough, occurs at least [cse_min_occ] times in *strict* positions, and
    — crucially for soundness — has NO occurrence in a non-strict position
    (its count over the strict subterms equals its count over all subterms).
    The last conjunct is what guarantees the hoisted subterm is evaluated on
    every path, so lifting it to an eager outer [let] preserves semantics. *)
Definition candidate_ok (all_strict all_full : list term) (u : term) : bool :=
  closedn 0 u && negb (isLambda u)
  && (cse_threshold <=? tsize u)
  && (cse_min_occ <=? count_term u all_strict)
  && (count_term u all_strict =? count_term u all_full).

Definition saving (all : list term) (u : term) : nat :=
  (count_term u all - 1) * tsize u.

(* argmax of [saving] over a candidate list; [None] if empty *)
Definition best_candidate (all : list term) (cands : list term) : option term :=
  List.fold_right
    (fun u acc =>
       match acc with
       | None => Some u
       | Some v => if saving all v <? saving all u then Some u else acc
       end)
    None cands.

(** ** Enabling guard.

    Hoisting emits a [tLetIn] whose body contains a fresh [tRel].  Those two
    node kinds must be permitted by the target [EEnvFlags], otherwise the emitted
    term is not [wellformed].  We therefore only fire the pass when both
    [has_tLetIn] and [has_tRel] are set; when they are not, [cse_term] is the
    identity and the transform is trivially wellformedness- and
    semantics-preserving.  (In the intended pipeline slot both flags hold.) *)
Definition cse_enabled (efl : EEnvFlags) : bool := has_tLetIn && has_tRel.

(** ** The per-term transform: one hoist. *)
Definition cse_term (efl : EEnvFlags) (t : term) : term :=
  if cse_enabled efl then
    let all_strict := subterms_strict t in
    let all_full := subterms t in
    let cands := dedup_terms (List.filter (candidate_ok all_strict all_full) all_strict) in
    match best_candidate all_strict cands with
    | None => t
    | Some s => tLetIn cse_name s (abstract s 0 t)
    end
  else t.

(** ** Lifting to constant bodies / environments / programs *)
Definition cse_in_constant_body (efl : EEnvFlags) (cst : constant_body)
  : constant_body :=
  {| cst_body := option_map (cse_term efl) (cst_body cst) |}.

Definition cse_in_decl (efl : EEnvFlags) (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl cst => ConstantDecl (cse_in_constant_body efl cst)
  | _ => d
  end.

Definition cse_env (efl : EEnvFlags) (Σ : global_declarations)
  : global_declarations :=
  map (fun '(kn, decl) => (kn, cse_in_decl efl decl)) Σ.

Definition cse_program (efl : EEnvFlags) (p : program) : program :=
  (cse_env efl p.1, cse_term efl p.2).

(** * VERIFICATION *)

(** ** (1) [abstract] is a left inverse of substitution.

    If [s] is closed and [t] is closed up to [k], then substituting [s] back for
    the fresh de-Bruijn index [k] undoes [abstract s k].  This is the algebraic
    heart of the transform: it is exactly the fact that makes
    [tLetIn "cse" s (abstract s 0 t)] reconstruct [t]. *)

Lemma subst_rel_closed s k : closedn 0 s -> subst [s] k (tRel k) = s.
Proof.
  intros Hs. simpl. rewrite Nat.leb_refl, Nat.sub_diag. simpl.
  now apply lift_closed.
Qed.

Lemma abstract_subst s (Hs : closedn 0 s) :
  forall t k, closedn k t -> subst [s] k (abstract s k t) = t.
Proof.
  intros t; induction t using term_forall_list_ind; intros k Hcl; cbn [abstract];
    (match goal with |- context[eqb s ?x] => destruct (eqb_specT s x) as [Heq|Hne] end);
    try (rewrite <- Heq; simpl subst; rewrite Nat.leb_refl, Nat.sub_diag; simpl;
         now apply lift_closed).
  all: cbn in Hcl |- *; rtoProp.
  - (* tBox *) reflexivity.
  - (* tRel *) destruct (Nat.leb_spec k n);
      [ apply Nat.ltb_lt in Hcl; exfalso; lia | reflexivity ].
  - (* tVar *) reflexivity.
  - (* tEvar *) f_equal. rewrite map_map. apply All_map_id.
    solve_all.
  - (* tLambda *) f_equal. now apply IHt.
  - (* tLetIn *) f_equal; [ now apply IHt1 | now apply IHt2 ].
  - (* tApp *) f_equal; [ now apply IHt1 | now apply IHt2 ].
  - (* tConst *) reflexivity.
  - (* tConstruct *) f_equal. rewrite map_map. apply All_map_id. solve_all.
  - (* tCase *) f_equal.
    + now apply IHt.
    + rewrite map_map. apply All_map_id.
      apply forallb_All in H0. solve_all.
      destruct x as [nas br]; cbn in *. f_equal.
      rewrite (Nat.add_comm k #|nas|). apply a. exact b.
  - (* tProj *) f_equal. now apply IHt.
  - (* tFix *) f_equal. rewrite ?length_map, map_map. apply All_map_id.
    apply forallb_All in Hcl. solve_all.
    unfold map_def; destruct x as [dn db ra]; cbn in *. f_equal.
    unfold test_def in *; cbn in *. rewrite (Nat.add_comm k #|m|). apply a. exact b.
  - (* tCoFix *) f_equal. rewrite ?length_map, map_map. apply All_map_id.
    apply forallb_All in Hcl. solve_all.
    unfold map_def; destruct x as [dn db ra]; cbn in *. f_equal.
    unfold test_def in *; cbn in *. rewrite (Nat.add_comm k #|m|). apply a. exact b.
  - (* tPrim *) change (subst [s] k (tPrim p) = tPrim p).
    apply subst_closed. exact Hcl.
  - (* tLazy *) f_equal. now apply IHt.
  - (* tForce *) f_equal. now apply IHt.
Qed.

(** ** (2a) [abstract] never turns a lambda into a non-lambda, provided the
       hoisted subterm [s] is itself not a lambda.  This is what keeps the
       "fixpoint bodies are lambdas" wellformedness invariant. *)
Lemma abstract_isLambda s k t :
  isLambda s = false -> isLambda t = true -> isLambda (abstract s k t) = true.
Proof.
  destruct t; simpl; intros Hs Ht; try discriminate.
  match goal with |- context[eqb s ?x] => destruct (eqb_specT s x) as [->|_] end;
    [ simpl in Hs; discriminate | reflexivity ].
Qed.

(** ** (2b) [abstract] preserves wellformedness.

    Replacing a (non-lambda) closed subterm [s] by a fresh de-Bruijn index
    keeps the term wellformed: it introduces only a [tRel] (needing [has_tRel]),
    never a new [tConst]/[tConstruct]/[tCase]/[tProj]/[tFix]/[tCoFix] head, so
    all environment lookups and structural checks are preserved. *)
Lemma wellformed_abstract {efl : EEnvFlags} (Σ : global_declarations) s
  (Hrel : has_tRel) (Hnl : isLambda s = false) :
  forall t k, wellformed Σ k t -> wellformed Σ (S k) (abstract s k t).
Proof.
  intros t; induction t using term_forall_list_ind; intros k Hwf; cbn [abstract];
    (match goal with |- context[eqb s ?x] => destruct (eqb_specT s x) as [Heq|Hne] end);
    try (cbn; apply andb_true_intro; split; [ exact Hrel | apply Nat.leb_le; lia ]).
  all: cbn in Hwf |- *.
  - (* tBox *) assumption.
  - (* tRel *) apply andb_and in Hwf as [Hr Hlt]. rewrite Hr. cbn.
    apply Nat.leb_le. apply Nat.ltb_lt in Hlt. lia.
  - (* tVar *) assumption.
  - (* tEvar *) apply andb_and in Hwf as [Hf Hl]. rewrite Hf. cbn.
    apply forallb_All in Hl. solve_all.
  - (* tLambda *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn.
    now apply IHt.
  - (* tLetIn *) apply andb_and in Hwf as [Hfb Hb2]. apply andb_and in Hfb as [Hf Hb1].
    rewrite Hf. cbn. apply andb_true_intro; split; [ now apply IHt1 | now apply IHt2 ].
  - (* tApp *) apply andb_and in Hwf as [Hfb Hb2]. apply andb_and in Hfb as [Hf Hb1].
    rewrite Hf. cbn. apply andb_true_intro; split; [ now apply IHt1 | now apply IHt2 ].
  - (* tConst *) assumption.
  - (* tConstruct *) apply andb_and in Hwf as [Hfl Hrest].
    apply andb_and in Hfl as [Hf Hl]. rewrite Hf, Hl. cbn.
    destruct cstr_as_blocks.
    + apply andb_and in Hrest as [Hc Hargs]. rewrite length_map.
      apply andb_true_intro; split; [ assumption | ].
      apply forallb_All in Hargs. apply All_forallb. apply All_map. solve_all.
    + now destruct args.
  - (* tCase *) apply andb_and in Hwf as [Hf Hr1].
    apply andb_and in Hr1 as [Hr2 Hbrs]. apply andb_and in Hr2 as [Hbr Hc].
    rewrite Hf. cbn. rewrite length_map.
    apply andb_true_intro; split; [ apply andb_true_intro; split | ].
    + assumption.
    + now apply IHt.
    + apply forallb_All in Hbrs. apply All_forallb. apply All_map. solve_all.
      destruct x as [nas br]; cbn in *. rewrite Nat.add_succ_r.
      rewrite (Nat.add_comm k #|nas|). apply a. exact b.
  - (* tProj *) apply andb_and in Hwf as [Hfl Hc].
    apply andb_and in Hfl as [Hf Hl]. rewrite Hf, Hl. cbn. now apply IHt.
  - (* tFix *) apply andb_and in Hwf as [Hfl Hfix].
    apply andb_and in Hfl as [Hf Hlam]. rewrite Hf. cbn.
    apply andb_true_intro; split.
    + apply forallb_All in Hlam. apply All_forallb. apply All_map. solve_all.
      destruct x as [dn db ra]; cbn in *. now apply abstract_isLambda.
    + unfold wf_fix_gen in *. apply andb_and in Hfix as [Hidx Hbods].
      rewrite ?length_map. apply andb_true_intro; split; [ assumption | ].
      apply forallb_All in Hbods. apply All_forallb. apply All_map. solve_all.
      unfold test_def in *. destruct x as [dn db ra]; cbn in *.
      rewrite Nat.add_succ_r. rewrite (Nat.add_comm k #|m|). apply a; assumption.
  - (* tCoFix *) apply andb_and in Hwf as [Hf Hfix]. rewrite Hf. cbn.
    unfold wf_fix_gen in *. apply andb_and in Hfix as [Hidx Hbods].
    rewrite ?length_map. apply andb_true_intro; split; [ assumption | ].
    apply forallb_All in Hbods. apply All_forallb. apply All_map. solve_all.
    unfold test_def in *. destruct x as [dn db ra]; cbn in *.
    rewrite Nat.add_succ_r. rewrite (Nat.add_comm k #|m|). apply a; assumption.
  - (* tPrim *) change (wellformed Σ (S k) (tPrim p)).
    eapply wellformed_up; [ exact Hwf | lia ].
  - (* tLazy *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn. now apply IHt.
  - (* tForce *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn. now apply IHt.
Qed.

(** ** (2c) Wellformedness relaxes the de-Bruijn bound down to any closedness
       level actually met by the term. *)
Lemma wellformed_closedn_le {efl : EEnvFlags} (Σ : global_declarations) :
  forall t k k', wellformed Σ k t -> closedn k' t -> wellformed Σ k' t.
Proof.
  intros t; induction t using term_forall_list_ind; intros k k' Hwf Hcl;
    cbn in Hwf, Hcl |- *; try assumption.
  - (* tRel *) apply andb_and in Hwf as [Hr _]. now rewrite Hr, Hcl.
  - (* tEvar *) apply andb_and in Hwf as [Hf Hl]. rewrite Hf. cbn.
    apply forallb_All in Hl. apply forallb_All in Hcl. solve_all.
  - (* tLambda *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn.
    eapply IHt; eassumption.
  - (* tLetIn *) apply andb_and in Hwf as [Hfb Hb2].
    apply andb_and in Hfb as [Hf Hb1]. apply andb_and in Hcl as [Hc1 Hc2].
    rewrite Hf. cbn. apply andb_true_intro; split;
      [ eapply IHt1; eassumption | eapply IHt2; eassumption ].
  - (* tApp *) apply andb_and in Hwf as [Hfb Hb2].
    apply andb_and in Hfb as [Hf Hb1]. apply andb_and in Hcl as [Hc1 Hc2].
    rewrite Hf. cbn. apply andb_true_intro; split;
      [ eapply IHt1; eassumption | eapply IHt2; eassumption ].
  - (* tConstruct *) apply andb_and in Hwf as [Hfl Hrest].
    apply andb_and in Hfl as [Hf Hl]. rewrite Hf, Hl. cbn.
    destruct cstr_as_blocks.
    + apply andb_and in Hrest as [Hc Hargs]. apply andb_true_intro; split;
        [ assumption | ]. apply forallb_All in Hargs. apply forallb_All in Hcl.
      apply All_forallb. solve_all.
    + assumption.
  - (* tCase *) apply andb_and in Hwf as [Hf Hr1].
    apply andb_and in Hr1 as [Hr2 Hbrs]. apply andb_and in Hr2 as [Hbr Hc].
    apply andb_and in Hcl as [Hcd Hcbrs]. rewrite Hf. cbn. rewrite Hbr. cbn.
    apply andb_true_intro; split.
    + eapply IHt; eassumption.
    + apply forallb_All in Hbrs. apply forallb_All in Hcbrs.
      apply All_forallb. solve_all.
  - (* tProj *) apply andb_and in Hwf as [Hfl Hc].
    apply andb_and in Hfl as [Hf Hl]. rewrite Hf, Hl. cbn.
    eapply IHt; eassumption.
  - (* tFix *) apply andb_and in Hwf as [Hfl Hfix].
    apply andb_and in Hfl as [Hf Hlam]. rewrite Hf. cbn.
    apply andb_true_intro; split; [ exact Hlam | ].
    unfold wf_fix_gen in *. apply andb_and in Hfix as [Hidx Hbods].
    apply andb_true_intro; split; [ assumption | ].
    unfold test_def in *. apply forallb_All in Hbods. apply forallb_All in Hcl.
    apply All_forallb. solve_all.
  - (* tCoFix *) apply andb_and in Hwf as [Hf Hfix]. rewrite Hf. cbn.
    unfold wf_fix_gen in *. apply andb_and in Hfix as [Hidx Hbods].
    apply andb_true_intro; split; [ assumption | ].
    unfold test_def in *. apply forallb_All in Hbods. apply forallb_All in Hcl.
    apply All_forallb. solve_all.
  - (* tPrim *) apply andb_and in Hwf as [Hp Hwp]. rewrite Hp. cbn.
    destruct p as [tag pm]; destruct pm; cbn in *; try reflexivity.
    inversion X; subst. destruct X0 as [Hdef Hvals].
    unfold test_array_model in *. apply andb_and in Hwp as [Hwd Hwv].
    apply andb_and in Hcl as [Hcd Hcv]. apply andb_true_intro; split.
    { eapply Hdef; eassumption. }
    apply forallb_All in Hwv. apply forallb_All in Hcv. apply All_forallb. solve_all.
  - (* tLazy *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn.
    eapply IHt; eassumption.
  - (* tForce *) apply andb_and in Hwf as [Hf Hb]. rewrite Hf. cbn.
    eapply IHt; eassumption.
Qed.

(** ** (2d) Every subterm collected by [collect] out of a wellformed term is
       itself wellformed (at some de-Bruijn level). *)
Lemma collect_wf {efl : EEnvFlags} (Σ : global_declarations) :
  forall fuel t k u,
  wellformed Σ k t -> In u (collect fuel t) -> exists m, wellformed Σ m u.
Proof.
  induction fuel as [|fuel IHfuel]; intros t k u Hwf Hin.
  - cbn in Hin. destruct Hin as [<-|[]]. now exists k.
  - cbn in Hin. destruct Hin as [<-|Hin]; [ now exists k | ].
    destruct t; cbn in Hwf, Hin; try solve [ destruct Hin ].
    + (* tEvar *) apply andb_and in Hwf as [_ Hfb].
      apply in_flat_map in Hin as [x [Hxl Hux]].
      eapply IHfuel; [ | exact Hux ].
      exact (proj1 (forallb_forall _ _) Hfb x Hxl).
    + (* tLambda *) apply andb_and in Hwf as [_ Hb].
      eapply IHfuel; [ exact Hb | exact Hin ].
    + (* tLetIn *) apply andb_and in Hwf as [Hf1 Hb2].
      apply andb_and in Hf1 as [_ Hb1]. apply in_app_or in Hin as [Hin|Hin];
        [ eapply IHfuel; [ exact Hb1 | exact Hin ]
        | eapply IHfuel; [ exact Hb2 | exact Hin ] ].
    + (* tApp *) apply andb_and in Hwf as [Hf1 Hb2].
      apply andb_and in Hf1 as [_ Hb1]. apply in_app_or in Hin as [Hin|Hin];
        [ eapply IHfuel; [ exact Hb1 | exact Hin ]
        | eapply IHfuel; [ exact Hb2 | exact Hin ] ].
    + (* tConstruct *) apply andb_and in Hwf as [_ Hrest]. destruct cstr_as_blocks.
      * apply andb_and in Hrest as [_ Hfb]. apply in_flat_map in Hin as [x [Hxl Hux]].
        eapply IHfuel; [ | exact Hux ]. exact (proj1 (forallb_forall _ _) Hfb x Hxl).
      * destruct args; [ destruct Hin | discriminate ].
    + (* tCase *) apply andb_and in Hwf as [_ Hr1].
      apply andb_and in Hr1 as [Hr2 Hfb]. apply andb_and in Hr2 as [_ Hc].
      apply in_app_or in Hin as [Hin|Hin].
      * eapply IHfuel; [ exact Hc | exact Hin ].
      * apply in_flat_map in Hin as [x [Hxl Hux]].
        eapply IHfuel; [ | exact Hux ].
        exact (proj1 (forallb_forall _ _) Hfb x Hxl).
    + (* tProj *) apply andb_and in Hwf as [_ Hc].
      eapply IHfuel; [ exact Hc | exact Hin ].
    + (* tFix *) apply andb_and in Hwf as [_ Hfix]. unfold wf_fix_gen in Hfix.
      apply andb_and in Hfix as [_ Hbods]. apply in_flat_map in Hin as [x [Hxl Hux]].
      eapply IHfuel; [ | exact Hux ].
      exact (proj1 (forallb_forall _ _) Hbods x Hxl).
    + (* tCoFix *) apply andb_and in Hwf as [_ Hfix]. unfold wf_fix_gen in Hfix.
      apply andb_and in Hfix as [_ Hbods]. apply in_flat_map in Hin as [x [Hxl Hux]].
      eapply IHfuel; [ | exact Hux ].
      exact (proj1 (forallb_forall _ _) Hbods x Hxl).
    + (* tLazy *) apply andb_and in Hwf as [_ Hb]. eapply IHfuel; [ exact Hb | exact Hin ].
    + (* tForce *) apply andb_and in Hwf as [_ Hb]. eapply IHfuel; [ exact Hb | exact Hin ].
Qed.

(** A hoisted candidate (a closed subterm of a wellformed body) is wellformed
    at level 0. *)
Lemma cse_subterm_wf {efl : EEnvFlags} (Σ : global_declarations) t s :
  wellformed Σ 0 t -> In s (subterms t) -> closedn 0 s -> wellformed Σ 0 s.
Proof.
  intros Hwf Hin Hcl. unfold subterms in Hin.
  eapply collect_wf in Hin as [m Hm]; [ | exact Hwf ].
  eapply wellformed_closedn_le; eassumption.
Qed.

(** Strict-position subterms are genuine subterms. *)
Lemma collect_strict_incl : forall fuel t u,
  In u (collect_strict fuel t) -> In u (collect fuel t).
Proof.
  induction fuel as [|fuel IH]; intros t u Hin; [ exact Hin | ].
  cbn in Hin |- *. destruct Hin as [->|Hin]; [ now left | right ].
  destruct t; cbn in Hin |- *; try solve [ destruct Hin ].
  - (* tLetIn *) apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
      [ left; now apply IH | right; now apply IH ].
  - (* tApp *) apply in_app_or in Hin as [Hin|Hin]; apply in_or_app;
      [ left; now apply IH | right; now apply IH ].
  - (* tConstruct *) apply in_flat_map in Hin as [x [Hx Hu]].
    apply in_flat_map. exists x. split; [ exact Hx | now apply IH ].
  - (* tCase *) apply in_or_app. left. now apply IH.
  - (* tProj *) now apply IH.
  - (* tForce *) now apply IH.
Qed.

Lemma subterms_strict_incl t u : In u (subterms_strict t) -> In u (subterms t).
Proof. apply collect_strict_incl. Qed.

(** ** (2e) [cse_env] keeps every key and inductive declaration and only
       rewrites constant bodies, so all environment lookups are preserved and
       [wellformed] is invariant under it. *)

Lemma lookup_env_cse efl Σ kn :
  lookup_env (cse_env efl Σ) kn = option_map (cse_in_decl efl) (lookup_env Σ kn).
Proof.
  induction Σ as [|[kn' d] Σ IH]; cbn; [ reflexivity | ].
  destruct (eq_kername kn kn'); cbn; [ reflexivity | exact IH ].
Qed.

Lemma lookup_minductive_cse efl Σ kn :
  lookup_minductive (cse_env efl Σ) kn = lookup_minductive Σ kn.
Proof.
  unfold lookup_minductive. rewrite lookup_env_cse.
  destruct (lookup_env Σ kn) as [[]|]; reflexivity.
Qed.

Lemma lookup_inductive_cse efl Σ kn :
  lookup_inductive (cse_env efl Σ) kn = lookup_inductive Σ kn.
Proof. unfold lookup_inductive. now rewrite lookup_minductive_cse. Qed.

Lemma lookup_constructor_cse efl Σ kn c :
  lookup_constructor (cse_env efl Σ) kn c = lookup_constructor Σ kn c.
Proof. unfold lookup_constructor. now rewrite lookup_inductive_cse. Qed.

Lemma lookup_constructor_pars_args_cse efl Σ kn c :
  lookup_constructor_pars_args (cse_env efl Σ) kn c
  = lookup_constructor_pars_args Σ kn c.
Proof. unfold lookup_constructor_pars_args. now rewrite lookup_constructor_cse. Qed.

Lemma lookup_projection_cse efl Σ p :
  lookup_projection (cse_env efl Σ) p = lookup_projection Σ p.
Proof. unfold lookup_projection. now rewrite lookup_constructor_cse. Qed.

Lemma lookup_constant_cse efl Σ kn :
  lookup_constant (cse_env efl Σ) kn
  = option_map (cse_in_constant_body efl) (lookup_constant Σ kn).
Proof.
  unfold lookup_constant. rewrite lookup_env_cse.
  destruct (lookup_env Σ kn) as [[]|]; reflexivity.
Qed.

Lemma wellformed_cse_env efl Σ :
  forall t k, wellformed (cse_env efl Σ) k t = wellformed Σ k t.
Proof.
  intros t; induction t using term_forall_list_ind; intros k;
    cbn -[lookup_constant lookup_inductive lookup_constructor
          lookup_constructor_pars_args lookup_projection]; auto.
  - (* tEvar *) f_equal. eapply All_forallb_eq_forallb; [ eassumption | auto ].
  - (* tLambda *) now rewrite IHt.
  - (* tLetIn *) now rewrite IHt1, IHt2.
  - (* tApp *) now rewrite IHt1, IHt2.
  - (* tConst *) rewrite lookup_constant_cse.
    destruct (lookup_constant Σ s) as [c|]; cbn; [ | reflexivity ].
    destruct (cst_body c); reflexivity.
  - (* tConstruct *) rewrite lookup_constructor_cse.
    destruct cstr_as_blocks; [ | reflexivity ].
    rewrite lookup_constructor_pars_args_cse. f_equal. f_equal.
    eapply All_forallb_eq_forallb; [ eassumption | auto ].
  - (* tCase *) unfold wf_brs. rewrite lookup_inductive_cse.
    rewrite IHt. do 2 f_equal.
    eapply All_forallb_eq_forallb; [ eassumption | ].
    intros x Hx. now rewrite Hx.
  - (* tProj *) rewrite lookup_projection_cse. now rewrite IHt.
  - (* tFix *) unfold wf_fix_gen. do 2 f_equal.
    eapply All_forallb_eq_forallb; [ eassumption | ].
    intros x Hx. unfold test_def. now rewrite Hx.
  - (* tCoFix *) unfold wf_fix_gen. f_equal. f_equal.
    eapply All_forallb_eq_forallb; [ eassumption | ].
    intros x Hx. unfold test_def. now rewrite Hx.
  - (* tPrim *) f_equal. destruct p as [tag pm]; destruct pm; cbn; auto.
    unfold test_array_model. inversion X; subst. destruct X0 as [Hdef Hvals].
    rewrite Hdef. f_equal. eapply All_forallb_eq_forallb; [ eassumption | auto ].
  - (* tLazy *) now rewrite IHt.
  - (* tForce *) now rewrite IHt.
Qed.

(** ** (2f) The hoisted candidate is a genuine, closed, non-lambda subterm. *)

Lemma best_candidate_In all cands s :
  best_candidate all cands = Some s -> In s cands.
Proof.
  unfold best_candidate. induction cands as [|c cands IH]; [ discriminate | ].
  simpl fold_right. destruct (fold_right _ _ cands) as [v|] eqn:E.
  - destruct (saving all v <? saving all c).
    + intros Heq; inversion Heq; subst. now left.
    + intros Heq; inversion Heq; subst. right. now apply IH.
  - intros Heq; inversion Heq; subst. now left.
Qed.

Lemma dedup_In x l : In x (dedup_terms l) -> In x l.
Proof.
  induction l as [|a l IH]; simpl; [ auto | ].
  destruct (mem_term a (dedup_terms l)).
  - intros H. apply in_cons. now apply IH.
  - intros [->|H]; [ apply in_eq | apply in_cons; now apply IH ].
Qed.

(** ** (2g) [cse_term] preserves wellformedness at level 0. *)
Lemma cse_term_wf (efl : EEnvFlags) (Σ : global_declarations) t :
  wellformed Σ 0 t -> wellformed Σ 0 (cse_term efl t).
Proof.
  intros Hwf. unfold cse_term.
  destruct (cse_enabled efl) eqn:Hen; [ | exact Hwf ].
  destruct (best_candidate _ _) as [s|] eqn:Hbest; [ | exact Hwf ].
  unfold cse_enabled in Hen. apply andb_and in Hen as [Hlet Hrel].
  apply best_candidate_In in Hbest. apply dedup_In in Hbest.
  apply filter_In in Hbest as [Hin Hok].
  apply subterms_strict_incl in Hin.
  unfold candidate_ok in Hok.
  apply andb_and in Hok as [Hok _]. apply andb_and in Hok as [Hok _].
  apply andb_and in Hok as [Hok _]. apply andb_and in Hok as [Hcl Hnl].
  apply negb_true_iff in Hnl.
  cbn. rewrite Hlet. cbn. apply andb_true_intro; split.
  - eapply cse_subterm_wf; eassumption.
  - now apply wellformed_abstract.
Qed.

(** ** (2h) Key preservation for the environment transformation. *)
Lemma fresh_global_cse efl kn Σ :
  fresh_global kn Σ -> fresh_global kn (cse_env efl Σ).
Proof.
  unfold fresh_global. intros H. apply Forall_forall. intros x Hx.
  unfold cse_env in Hx. apply in_map_iff in Hx as [[kn' d] [Heq Hin]].
  subst x. cbn. eapply Forall_forall in H; [ | exact Hin ]. exact H.
Qed.

Lemma cse_env_cons efl kn d Σ :
  cse_env efl ((kn, d) :: Σ) = (kn, cse_in_decl efl d) :: cse_env efl Σ.
Proof. reflexivity. Qed.

Lemma cse_env_wf efl Σ : wf_glob Σ -> wf_glob (cse_env efl Σ).
Proof.
  induction 1 as [| kn d Σ Hg IH Hdecl Hfresh]; [ constructor | ].
  rewrite cse_env_cons. constructor; [ exact IH | | now apply fresh_global_cse ].
  destruct d as [c|m].
  - unfold wf_global_decl, cse_in_decl, cse_in_constant_body in *;
      cbn [cst_body] in *.
    destruct (cst_body c) as [b|] eqn:Ecb; cbn [option_map option_default] in *.
    + rewrite wellformed_cse_env. now apply cse_term_wf.
    + exact Hdecl.
  - exact Hdecl.
Qed.

(** ** (2) MAIN WELLFORMEDNESS PRESERVATION (discharges [trust_cse_wf]). *)
Lemma cse_wf (efl : EEnvFlags) (p : eprogram) :
  wf_eprogram efl p -> wf_eprogram efl (cse_program efl p).
Proof.
  intros [Hglob Hmain]. split.
  - now apply cse_env_wf.
  - cbn. rewrite wellformed_cse_env. now apply cse_term_wf.
Qed.

(** ** Transform wrapper (unverified, [Compatible]-class), mirroring
       EInstanceSpecialize.v and MetaRocq's EBeta.v. *)

From MetaRocq.Common Require Import Transform.

(** ** (3) SEMANTICS PRESERVATION.

    CORRECTNESS MODEL AND HONEST STATUS.

    An earlier version of this file stated the obligation as
    [eval (cse_env Σ) (cse_term t) (cse_term v)] (obseq [v' = cse_term v]),
    mirroring [EBeta].  That is WRONG for CSE: [cse_term] is not a congruence
    (it performs one global hoist), so it does not commute with evaluation, and
    that statement is in fact false — e.g. for a lambda value [v] with a repeated
    closed subterm, [cse_term v] is a [tLetIn], which cannot evaluate to itself.

    The correct obseq for a sharing pass is the identity on values, [v' = v]:
    hoisting a closed subterm that is evaluated on every path, forcing it once in
    an outer [let], and substituting its value back, yields the SAME value.  The
    algebraic backbone is proved: [abstract_subst] gives
    [subst0 s (abstract s 0 t) = t] for closed [s]; under [eval_zeta] the [let]
    forces [s] to [s'] and [csubst]s it back, and [closed_subst] turns that
    [csubst] into the [subst] of [abstract_subst].

    SOUNDNESS DISCRIMINATOR.  Hoisting is only sound for subterms evaluated on
    every path.  [candidate_ok] now enforces this: a candidate must have ALL its
    occurrences in strict (always-evaluated) positions
    ([count_term u all_strict = count_term u all_full]).  Without this guard the
    pass is UNSOUND — it could lift a subterm out of a [tLambda] body or untaken
    [tCase] branch and force it eagerly, changing termination (this was a real
    defect in the earlier unconditional [candidate_ok]).

    [cse_pres_eval] below is the single remaining residual: the whole-program
    CBV simulation with the correct [v' = v] conclusion.  It is TRUE for the
    strict-guarded selection above; the remaining work is the cross-environment
    induction over the [EWcbvEval] rules (relating eval under [Σ] and under
    [cse_env Σ], threading the strict-position hoist), of the same size as
    MetaRocq's [EBeta]/[Optimize] evaluation-preservation developments and left
    as an explicit trust obligation in the manner of [EBeta.trust_betared_pres]. *)

Axiom cse_pres_eval :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (Σ : global_declarations)
    (t v : term),
  wf_glob Σ ->
  wellformed Σ 0 t ->
  EWcbvEval.eval (wfl := wfl) Σ t v ->
  EWcbvEval.eval (wfl := wfl) (cse_env efl Σ) (cse_term efl t) v.

Lemma cse_pres (efl : EEnvFlags) (wfl : WcbvFlags) (p : eprogram) (v : term) :
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term,
  eval_eprogram wfl (cse_program efl p) v' /\ v' = v.
Proof.
  intros [Hglob Hmain] [Hev]. exists v. split; [ | reflexivity ].
  constructor. exact (cse_pres_eval efl wfl p.1 p.2 v Hglob Hmain Hev).
Qed.

Import Transform.

Program Definition cse_transformation (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "common subexpression elimination";
     transform p _ := cse_program efl p;
     pre p := wf_eprogram efl p;
     post p := wf_eprogram efl p;
     obseq p hp p' v v' := v' = v |}.
Next Obligation.
  now apply cse_wf.
Qed.
Next Obligation.
  now eapply cse_pres.
Qed.

Import EProgram EGlobalEnv.

(** ** (4) The transform preserves environment extension (discharges the two
       [TransformExt] axioms). *)
Lemma extends_cse efl Σ Σ' :
  extends Σ Σ' -> extends (cse_env efl Σ) (cse_env efl Σ').
Proof.
  intros H kn decl. rewrite !lookup_env_cse.
  destruct (lookup_env Σ kn) as [d0|] eqn:E; cbn; [ | discriminate ].
  intros [= <-]. now rewrite (H kn d0 E).
Qed.

#[global]
Lemma cse_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (cse_transformation efl wfl)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).
Proof.
  intros efl wfl p p' pr pr' Hext. cbn. now apply extends_cse.
Qed.

#[global]
Lemma cse_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (cse_transformation efl wfl)
    extends_eprogram extends_eprogram.
Proof.
  intros efl wfl p p' pr pr' [Hext Heq]. split; cbn.
  - now apply extends_cse.
  - now rewrite Heq.
Qed.
