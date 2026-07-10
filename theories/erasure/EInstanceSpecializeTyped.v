(** * Instance / dictionary specialization on TYPED lambda-box (λ□ᵀ / ExAst)

    This module is the typed variant of the instance-specialization pass, a
    self-contained sibling of the untyped [EInstanceSpecialize.v] that does not
    import it.  It operates on MetaRocq's *typed* erased syntax
    ([MetaRocq.Erasure.Typed.ExAst]) — the layer that still carries [box_type]
    information ([cst_type]) — which is where the pass belongs in the Peregrine
    pipeline: it runs before the Rust / Elm backends, where the dictionary
    plumbing it removes is not re-optimized away by a downstream native
    compiler (unlike the OCaml / C paths).

    ------------------------------------------------------------------------
    WHAT THE PASS DOES (identical algorithm to the untyped module, lifted to
    ExAst so [box_type]s are tracked).

    At a call [f D x1 .. xn] where the head [f] is a [tConst] (its body may be
    a [tFix], unfolded once) and [D] is a *statically-known dictionary* — a
    closed [tConstruct] whose inductive is a single-constructor record, or a
    [tConst] delta-unfolding to one — the pass:

      1. emit a fresh specialized constant [f$specN] whose body is [f]'s body
         with [D] substituted in ([spec_beta]) and the exposed method
         projections collapsed by the local beta/iota reducer
         ([specialize_instances]);
      2. give [f$specN] a [cst_type]: the callee's type scheme is reused
         unchanged, so the dictionary parameter that becomes dead is left in
         place and is dropped by the downstream [dearg] pass — which is why the
         phase order is specialize -> dearg -> betared;
      3. redirect the call site to [f$specN x1 .. xn].

    The reductions that expose then discard the plumbing:

      - δ:  [f D]  δ-unfolds [f] to its body [λdict. body], then
      - β:  β-reduces to [body[dict := D]], which is *exactly* [f$specN]'s body,
            so [eval (f D) = eval (f$specN)];
      - ι:  [match D with C xs => br end] with [D = C a..] projects the method
            ([iota_red]); firing ι here is "read a field out of a known
            dictionary".  ([EBeta]'s plain [betared] does β but never ι, and
            [EInlining] inlines named constants uniformly rather than
            specializing a shared function per call site — so this pass
            subsumes neither.)

    Specializations are memoised by the key [(callee, dicts)] and the whole
    saturation is bounded by [specialize_fuel]; the loop re-scans each freshly
    emitted body so chained dictionary plumbing is specialized too.

    ------------------------------------------------------------------------
    VERIFICATION STRUCTURE.

    [eval] is defined on *untyped* [EAst] via [trans_env].  The typed transform
    [specialize_program_typed] therefore does all of its analysis on the
    translated environment [trans_env Σ] and differs from the purely-untyped
    driver [drive_untyped] only in the [box_type] data that [trans_env] erases:

      * [specialize_commutes] proves that erasing the typed result equals
        running [drive_untyped] on the erased input, i.e.

            trans_env (specialize_program_typed Σ t)  =  drive_untyped (trans_env Σ) t.

        It is proved by [Qed] and reduces every semantic/wellformedness
        question about the *typed* pass to the corresponding question about the
        untyped core, with no blanket trust over the typed layer.
      * [typed_specialize_wf] (wellformedness preservation) and
        [typed_specialize_pres] (semantics preservation) are each proved by
        [Qed], modulo one residual about the untyped core,
        [untyped_drive_correct], which packages the δ/β/ι eval-simulation.
        This residual is the same obligation MetaRocq leaves axiomatized for
        the analogous optional passes ([EBeta.trust_betared_pres] /
        [EBeta.trust_betared_wf], [EInlining]); it is scoped to the untyped
        reducer rather than trusting the typed transform wholesale.

    The typed-specific reasoning (the [trans_env] commutation and the reduction
    of both preservation properties to the untyped core) is machine-checked;
    [Print Assumptions typed_specialize_pres] at the bottom lists exactly
    [untyped_drive_correct].  The untyped δ/β/ι simulation itself is the stated
    residual axiom.

    ------------------------------------------------------------------------
    PIPELINE PLACEMENT (typed pipeline, before Rust/Elm).
    [specialize_program_typed] is an optional phase for the typed extraction
    pipeline (Typed/Optimize.v / Typed/Extraction.v).  The phase order is
    specialize -> dearg -> betared: [dearg] removes the dead dictionary
    parameter this pass leaves, and [betared] mops up cascaded redexes.
*)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils ReflectEq.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EReflect ELiftSubst
     EGlobalEnv EProgram EWellformed EWcbvEval.
From MetaRocq.Erasure.Typed Require Import ExAst.

Import ListNotations.

(** Throughout: [EAst.*] / [EGlobalEnv.*] are the *untyped* names, [ExAst.*]
    the *typed* ones (ExAst re-exports [EAst], so both [ConstantDecl],
    [cst_body], [lookup_constant] etc. exist; both are qualified to
    disambiguate). *)

(* ------------------------------------------------------------------------ *)
(** ** Body-level machinery (on the shared [term] type). *)

(** Generic congruence recursor (cf. [EBeta.map_subterms]); kept local so the
    head-reduction fixpoint below is guarded. *)
Definition spec_map_subterms (f : term -> term) (t : term) : term :=
  match t with
  | tEvar n ts => tEvar n (map f ts)
  | tLambda na body => tLambda na (f body)
  | tLetIn na val body => tLetIn na (f val) (f body)
  | tApp hd arg => tApp (f hd) (f arg)
  | tCase p disc brs => tCase p (f disc) (map (on_snd f) brs)
  | tProj p t => tProj p (f t)
  | tFix def i => tFix (map (map_def f) def) i
  | tCoFix def i => tCoFix (map (map_def f) def) i
  | tPrim p => tPrim (map_prim f p)
  | tLazy t => tLazy (f t)
  | tForce t => tForce (f t)
  | tConstruct ind n args => tConstruct ind n (map f args)
  | tRel n => tRel n
  | tVar na => tVar na
  | tConst kn => tConst kn
  | tBox => tBox
  end.

Section reduce.

  (** Apply an already-reduced [body] to a spine of already-reduced [args],
      firing β as far as [body] is a literal lambda. *)
  Fixpoint spec_beta (body : term) (args : list term) {struct args} : term :=
    match args with
    | [] => body
    | a :: args =>
        match body with
        | tLambda na body => spec_beta (body {0 := a}) args
        | _ => mkApps body (a :: args)
        end
    end.

  (** Bottom-up single pass: reduce children first, then one head β (via the
      collected spine) or ι (case-of-known-constructor). *)
  Fixpoint spec_aux (args : list term) (t : term) : term :=
    match t with
    | tApp hd arg => spec_aux (spec_aux [] arg :: args) hd
    | tLambda na body =>
        let b := spec_aux [] body in
        spec_beta (tLambda na b) args
    | tCase (ind, npar) disc brs =>
        let disc' := spec_aux [] disc in
        let brs' := map (on_snd (spec_aux [])) brs in
        let reduced :=
          match disc' with
          | tConstruct _ c cargs =>
              match nth_error brs' c with
              | Some br => iota_red npar cargs br
              | None => tCase (ind, npar) disc' brs'
              end
          | _ => tCase (ind, npar) disc' brs'
          end in
        mkApps reduced args
    | t => mkApps (spec_map_subterms (spec_aux []) t) args
    end.

  Definition specialize_instances : term -> term := spec_aux [].

End reduce.

(* ------------------------------------------------------------------------ *)
(** ** Dictionary analysis over the UNTYPED environment. *)

Definition dkey : Type := kername × list term.

Fixpoint list_eqb {A} (f : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: l1, b :: l2 => f a b && list_eqb f l1 l2
  | _, _ => false
  end.

Definition eqb_key (k1 k2 : dkey) : bool :=
  eqb (fst k1) (fst k2) && list_eqb (fun a b => eqb a b) (snd k1) (snd k2).

(** Fresh, deterministic name for the [i]-th specialization of [nm]. *)
Definition fresh_name (nm : kername) (i : nat) : kername :=
  (nm.1, (nm.2 ++ "$spec" ++ string_of_nat i)%bs).

(** Single-constructor record (the dictionary shape)? *)
Definition is_record_ind (Σ : EAst.global_context) (ind : inductive) : bool :=
  match EGlobalEnv.lookup_inductive Σ ind with
  | Some (_, oib) => Nat.eqb #|oib.(EAst.ind_ctors)| 1
  | None => false
  end.

(** If [t] is a statically-known dictionary value, return the underlying
    (closed, single-constructor) [tConstruct]; resolves one [tConst] delta. *)
Definition dict_value (Σ : EAst.global_context) (t : term) : option term :=
  match t with
  | tConstruct ind _ _ =>
      if is_record_ind Σ ind && closedn 0 t then Some t else None
  | tConst c =>
      match EGlobalEnv.lookup_constant Σ c with
      | Some cb =>
          match EAst.cst_body cb with
          | Some (tConstruct ind n args) =>
              if is_record_ind Σ ind && closedn 0 (tConstruct ind n args)
              then Some (tConstruct ind n args) else None
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.

(** A spine element accepted in a specialization prefix: an erased type arg
    ([tBox]) or a dictionary value.  The flag records "is a real dictionary". *)
Definition prefix_elt (Σ : EAst.global_context) (t : term) : option (bool * term) :=
  match dict_value Σ t with
  | Some d => Some (true, d)
  | None => match t with tBox => Some (false, tBox) | _ => None end
  end.

Fixpoint split_dicts (Σ : EAst.global_context) (spine : list term)
  : bool * list term * list term :=
  match spine with
  | [] => (false, [], [])
  | a :: rest =>
      match prefix_elt Σ a with
      | Some (isd, v) =>
          let '(d', ds, rr) := split_dicts Σ rest in (orb isd d', v :: ds, rr)
      | None => (false, [], spine)
      end
  end.

Definition callee_body (Σ : EAst.global_context) (nm : kername) : option term :=
  match EGlobalEnv.lookup_constant Σ nm with
  | Some cb => EAst.cst_body cb
  | None => None
  end.

(** Body of a specialized copy: substitute the dictionaries into the callee
    body (unfold a [tFix]-body once first), then locally reduce. *)
Definition spec_body (b : term) (dicts : list term) : term :=
  match b with
  | tFix mfix idx =>
      match cunfold_fix mfix idx with
      | Some (_, fn) => specialize_instances (spec_beta fn dicts)
      | None => specialize_instances (mkApps b dicts)
      end
  | _ => specialize_instances (spec_beta b dicts)
  end.

Definition mk_key (Σ : EAst.global_context) (nm : kername) (spine : list term)
  : option (dkey * list term) :=
  match callee_body Σ nm with
  | Some _ =>
      let '(saw_dict, dicts, rest) := split_dicts Σ spine in
      if saw_dict then Some ((nm, dicts), rest) else None
  | None => None
  end.

Fixpoint collect_keys (Σ : EAst.global_context) (spine : list term) (t : term)
  {struct t} : list dkey :=
  match t with
  | tApp hd arg => collect_keys Σ [] arg ++ collect_keys Σ (arg :: spine) hd
  | tConst nm => match mk_key Σ nm spine with Some (k, _) => [k] | None => [] end
  | tLambda _ b => collect_keys Σ [] b
  | tLetIn _ v b => collect_keys Σ [] v ++ collect_keys Σ [] b
  | tCase _ disc brs =>
      collect_keys Σ [] disc ++ concat (map (fun br => collect_keys Σ [] (snd br)) brs)
  | tProj _ c => collect_keys Σ [] c
  | tFix mfix _ => concat (map (fun d => collect_keys Σ [] (dbody d)) mfix)
  | tCoFix mfix _ => concat (map (fun d => collect_keys Σ [] (dbody d)) mfix)
  | tConstruct _ _ args => concat (map (fun a => collect_keys Σ [] a) args)
  | tEvar _ args => concat (map (fun a => collect_keys Σ [] a) args)
  | tLazy t => collect_keys Σ [] t
  | tForce t => collect_keys Σ [] t
  | _ => []
  end.

(** A generated specialization: [(fresh_name, callee, body)]. *)
Definition gentriple : Type := kername * kername * term.

(** Fuel-bounded saturation: pop a key, and if new, record its fresh name +
    generated body and enqueue the keys newly exposed inside it. *)
Fixpoint saturate (Σ : EAst.global_context) (fuel : nat) (worklist : list dkey)
  (seen : list (dkey × kername)) (gen : list gentriple)
  {struct fuel} : list (dkey × kername) × list gentriple :=
  match fuel with
  | 0 => (seen, gen)
  | S fuel' =>
      match worklist with
      | [] => (seen, gen)
      | k :: rest =>
          if existsb (fun p => eqb_key (fst p) k) seen
          then saturate Σ fuel' rest seen gen
          else
            let '(nm, dicts) := k in
            match callee_body Σ nm with
            | Some b =>
                let body := spec_body b dicts in
                let fn := fresh_name nm #|seen| in
                let new_keys := collect_keys Σ [] body in
                saturate Σ fuel' (new_keys ++ rest) ((k, fn) :: seen)
                         ((fn, nm, body) :: gen)
            | None => saturate Σ fuel' rest seen gen
            end
      end
  end.

Definition lookup_spec (seen : list (dkey × kername)) (k : dkey) : option kername :=
  match find (fun p => eqb_key (fst p) k) seen with
  | Some p => Some (snd p)
  | None => None
  end.

(** Redirect specializable call sites to their emitted copies. *)
Fixpoint redirect (Σ : EAst.global_context) (seen : list (dkey × kername))
  (spine : list term) (t : term) {struct t} : term :=
  match t with
  | tApp hd arg => redirect Σ seen (redirect Σ seen [] arg :: spine) hd
  | tConst nm =>
      match mk_key Σ nm spine with
      | Some (k, rest) =>
          match lookup_spec seen k with
          | Some fn => mkApps (tConst fn) rest
          | None => mkApps (tConst nm) spine
          end
      | None => mkApps (tConst nm) spine
      end
  | _ => mkApps (spec_map_subterms (redirect Σ seen []) t) spine
  end.

Definition specialize_fuel : nat := 1000.

(** Keys reachable from all constant bodies plus the main term. *)
Definition init_keys (Σ : EAst.global_context) (main : term) : list dkey :=
  concat (map (fun '(_, d) =>
                 match d with
                 | EAst.ConstantDecl cb =>
                     match EAst.cst_body cb with
                     | Some b => collect_keys Σ [] b
                     | None => []
                     end
                 | _ => []
                 end) Σ)
  ++ collect_keys Σ [] main.

(** The single analysis both drivers share. *)
Definition analysis (Σ : EAst.global_context) (main : term)
  : list (dkey × kername) × list gentriple :=
  saturate Σ specialize_fuel (init_keys Σ main) [] [].

(** Redirect+reduce an untyped declaration's body. *)
Definition redirect_decl (Σ : EAst.global_context) (seen : list (dkey × kername))
  (d : EAst.global_decl) : EAst.global_decl :=
  match d with
  | EAst.ConstantDecl cb =>
      EAst.ConstantDecl
        {| EAst.cst_body :=
             option_map (fun b => specialize_instances (redirect Σ seen [] b))
                        (EAst.cst_body cb) |}
  | _ => d
  end.

(** ** The UNTYPED reference driver ([drive_untyped]).

    This is the object of the residual correctness lemma below.  The typed
    driver's erasure is proved equal to this. *)
Definition drive_untyped (Σ : EAst.global_context) (main : term) : eprogram :=
  let '(seen, gen) := analysis Σ main in
  let red := map (fun '(kn, d) => (kn, redirect_decl Σ seen d)) Σ in
  let gen_u :=
    map (fun '(fn, _, body) =>
           (fn, EAst.ConstantDecl {| EAst.cst_body := Some body |})) gen in
  (red ++ gen_u, specialize_instances (redirect Σ seen [] main)).

(* ------------------------------------------------------------------------ *)
(** ** The TYPED driver over [ExAst.global_env].

    Identical analysis (run on [trans_env Σ]); the ONLY difference from
    [drive_untyped] is the [box_type] ([cst_type]) data, which [trans_env]
    discards. *)

(** Redirect+reduce a typed declaration's body, preserving its [cst_type]. *)
Definition redirect_decl_typed (Σu : EAst.global_context)
  (seen : list (dkey × kername)) (d : ExAst.global_decl) : ExAst.global_decl :=
  match d with
  | ExAst.ConstantDecl cb =>
      ExAst.ConstantDecl
        {| ExAst.cst_type := ExAst.cst_type cb;
           ExAst.cst_body :=
             option_map (fun b => specialize_instances (redirect Σu seen [] b))
                        (ExAst.cst_body cb) |}
  | _ => d
  end.

(** Typed declaration for a generated specialization.  The [cst_type] reuses
    the callee's type scheme unchanged; the dictionary parameter that becomes
    dead is dropped later by [dearg]. *)
Definition spec_typed_decl (Σ : ExAst.global_env) (callee : kername) (body : term)
  : ExAst.global_decl :=
  ExAst.ConstantDecl
    {| ExAst.cst_type :=
         match ExAst.lookup_constant Σ callee with
         | Some cb => ExAst.cst_type cb
         | None => ([], TBox)
         end;
       ExAst.cst_body := Some body |}.

Definition specialize_program_typed (Σ : ExAst.global_env) (main : term)
  : ExAst.global_env × term :=
  let Σu := trans_env Σ in
  let '(seen, gen) := analysis Σu main in
  let red := map (fun '(kn, b, d) => (kn, b, redirect_decl_typed Σu seen d)) Σ in
  let gen_t :=
    map (fun '(fn, callee, body) => (fn, false, spec_typed_decl Σ callee body)) gen in
  (red ++ gen_t, specialize_instances (redirect Σu seen [] main)).

(** Erase a typed program to the untyped level eval is defined on. *)
Definition typed_erase (r : ExAst.global_env × term) : eprogram :=
  (trans_env r.1, r.2).

(* ------------------------------------------------------------------------ *)
(** ** The commutation theorem (fully Qed). *)

Lemma trans_env_app (Σ1 Σ2 : ExAst.global_env) :
  trans_env (Σ1 ++ Σ2) = trans_env Σ1 ++ trans_env Σ2.
Proof. apply map_app. Qed.

(** Erasing a redirected typed decl = redirecting the erased decl.  The only
    subtle case is [TypeAliasDecl]: [trans_global_decl] turns it into a
    [ConstantDecl] with body [tBox], on which [redirect_decl] then fires; but
    [redirect]/[specialize_instances] fix [tBox], so both sides agree. *)
Lemma trans_redirect_decl_typed (Σu : EAst.global_context)
  (seen : list (dkey × kername)) (kn : kername) (b : bool) (d : ExAst.global_decl) :
  (kn, trans_global_decl (redirect_decl_typed Σu seen d))
  = (kn, redirect_decl Σu seen (trans_global_decl d)).
Proof.
  destruct d as [cb| |o]; cbn.
  - (* ConstantDecl *) reflexivity.
  - (* InductiveDecl *) reflexivity.
  - (* TypeAliasDecl *) destruct o as [p|]; cbn; reflexivity.
Qed.

Lemma trans_env_redirect (Σu : EAst.global_context)
  (seen : list (dkey × kername)) (Σ : ExAst.global_env) :
  trans_env (map (fun '(kn, b, d) => (kn, b, redirect_decl_typed Σu seen d)) Σ)
  = map (fun '(kn, d) => (kn, redirect_decl Σu seen d)) (trans_env Σ).
Proof.
  unfold trans_env.
  rewrite !map_map.
  apply map_ext; intros [[kn b] d]; cbn.
  apply (trans_redirect_decl_typed Σu seen kn b d).
Qed.

Lemma trans_env_gen (Σ : ExAst.global_env) (gen : list gentriple) :
  trans_env (map (fun '(fn, callee, body) =>
                    (fn, false, spec_typed_decl Σ callee body)) gen)
  = map (fun '(fn, _, body) =>
           (fn, EAst.ConstantDecl {| EAst.cst_body := Some body |})) gen.
Proof.
  unfold trans_env.
  rewrite !map_map.
  apply map_ext; intros [[fn callee] body]; cbn.
  reflexivity.
Qed.

(** MAIN VERIFIED CONTENT.  Erasing the typed specialization equals the
    untyped driver on the erased input.  Everything typed-specific is here. *)
Theorem specialize_commutes (Σ : ExAst.global_env) (main : term) :
  typed_erase (specialize_program_typed Σ main) = drive_untyped (trans_env Σ) main.
Proof.
  unfold typed_erase, specialize_program_typed, drive_untyped.
  destruct (analysis (trans_env Σ) main) as [seen gen].
  cbn [fst snd].
  f_equal.
  rewrite trans_env_app.
  f_equal.
  - apply trans_env_redirect.
  - apply trans_env_gen.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The single residual axiom: correctness of the untyped core.

    This packages the δ/β/ι eval-simulation for [drive_untyped], mirroring
    [EBeta.trust_betared_pres] / [trust_betared_wf] and the [EInlining]
    correctness argument. *)
Axiom untyped_drive_correct :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (Σu : EAst.global_context) (t : term),
    wf_eprogram efl (Σu, t) ->
    wf_eprogram efl (drive_untyped Σu t)
    /\ (forall v, eval_eprogram wfl (Σu, t) v ->
          exists v', eval_eprogram wfl (drive_untyped Σu t) v'
                     /\ v' = specialize_instances v).

(* ------------------------------------------------------------------------ *)
(** ** Preservation for the typed pass (Qed, modulo the single residual). *)

(** (a) Wellformedness preservation. *)
Theorem typed_specialize_wf
  (efl : EEnvFlags) (wfl : WcbvFlags) (Σ : ExAst.global_env) (t : term) :
  wf_eprogram efl (trans_env Σ, t) ->
  wf_eprogram efl (typed_erase (specialize_program_typed Σ t)).
Proof.
  intros Hwf.
  rewrite specialize_commutes.
  exact (proj1 (untyped_drive_correct efl wfl (trans_env Σ) t Hwf)).
Qed.

(** (b) Semantics preservation.  Since [eval] is defined post-[trans_env], the
    statement is about the erased typed program; the specialized value is the
    locally-reduced original value (the [obseq] used by [EBeta]/[EInlining]). *)
Theorem typed_specialize_pres
  (efl : EEnvFlags) (wfl : WcbvFlags) (Σ : ExAst.global_env) (t v : term) :
  wf_eprogram efl (trans_env Σ, t) ->
  eval_eprogram wfl (trans_env Σ, t) v ->
  exists v', eval_eprogram wfl (typed_erase (specialize_program_typed Σ t)) v'
             /\ v' = specialize_instances v.
Proof.
  intros Hwf Hev.
  rewrite specialize_commutes.
  exact (proj2 (untyped_drive_correct efl wfl (trans_env Σ) t Hwf) v Hev).
Qed.

(** Assumptions of the top semantic-preservation lemma: exactly the one
    scoped residual [untyped_drive_correct] (plus ambient logical axioms, if
    any, from the imported libraries). *)
Print Assumptions typed_specialize_pres.
