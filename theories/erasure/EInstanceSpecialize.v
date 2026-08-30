(** * Instance / dictionary specialization for untyped lambda-box

    This module implements the instance-specialization pass on untyped
    lambda-box terms ([EAst]); its sibling [EInstanceSpecializeTyped] provides
    the typed ([ExAst]) variant.  Correctness and wellformedness preservation
    are provided as trust axioms, matching the other [Compatible]-class
    optional transforms in this toolchain.

    Motivation.  Typeclass-heavy frontends (notably Lean) erase to lambda-box
    in which even trivial arithmetic drags in dictionary values: [1 + 1] is
    elaborated to [HAdd.add instHAdd 1 1] where [instHAdd] is a *statically
    known* record/constructor value.  Lean's own compiler removes this cost
    with instance / typeclass-instance specialization.  This module is the
    Peregrine middle-end analogue, so every frontend benefits.

    What this pass does.  It is a *local, terminating partial evaluator* over
    lambda-box terms performing the two reductions that expose and then discard
    dictionary plumbing but that plain beta reduction ([EBeta]) does not on its
    own complete:

      - beta:  [(fun x => b) a]                          ==>  b[x := a]
      - iota:  [match C a0 .. an with | .. | C xs => br | .. end]
                                                          ==>  br[xs := a..]
               i.e. case-of-known-constructor.  In post-[verified_lambdabox]
               lambda-box, record projections have been compiled to [tCase]
               with constructors-as-blocks, so a dictionary field access is a
               [tCase] on a literal [tConstruct]; firing iota here is exactly
               the "read a field out of a known dictionary" step.

    Cloning driver (implemented below, [drive_env]).
    On top of the local reducer, the pass *clones* a function at call sites
    where a leading argument is a statically-known dictionary value: for [f d x]
    with [d] a closed dictionary [tConstruct] (or a [tConst] whose body unfolds
    to one), it emits a specialized copy [f$specN] whose body is [f]'s body with
    [d] substituted in (via [spec_beta]; for a [tConst] whose body is a [tFix],
    the fixpoint is unfolded once first), so the beta/iota reductions above fire
    *inside* [f]'s body across the call boundary; the call site is redirected to
    [f$specN x].  After this, existing dead-argument elimination ([Optimize]/
    dearg) drops the unused [d] parameter.  A dictionary argument is
    recognised by the heuristic "closed constructor whose inductive is a
    single-constructor record" ([dict_value]/[is_record_ind]), which excludes
    ordinary data (nat, list, bool, ...).  Specializations are memoised in a map
    keyed by [(callee, dicts)] so each is emitted once, and the whole search is
    bounded by a fuel budget ([specialize_fuel]) to guarantee termination and
    avoid code blow-up.  The saturation loop re-scans each freshly emitted body
    so chained dictionary plumbing (a method that itself projects another
    dictionary) is specialized too.  The local reducer below is the cleanup that
    the cloning relies on, and is independently useful after user-directed
    constant inlining ([inlinings_opts] / [EInlining]) brings an instance
    definition to a call site.

    Composition with existing passes.
      - It is meant to run just before [betared] (which the pipeline already
        runs twice); [betared] mops up any cascading redexes this single
        bottom-up pass leaves behind.
      - It feeds dead-argument elimination: after specialization a dictionary
        parameter becomes unused and [Optimize]'s mask analysis removes it.
      - It does NOT subsume any of them: dearg removes *dead* args (it cannot
        touch a dictionary that is still projected), betared does beta but not
        iota-on-constructor, and [EInlining] inlines *named constants* uniformly
        rather than specializing a shared function per call site.

    Verification status.  Correctness and wellformedness preservation are
    stated as trust axioms, following the pattern of the other optional
    [Compatible]-class transforms in this toolchain (cf.
    [EBeta.betared_transformation], justified by the [trust_betared_*]
    axioms). *)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils ReflectEq.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EReflect ELiftSubst EGlobalEnv EProgram.

Import ListNotations.

(** Generic congruence recursor (identical in spirit to [EBeta.map_subterms]);
    kept local so the head-reduction fixpoint below is guarded. *)
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

Section specialize.

  (** Apply an already-reduced [body] to a spine of already-reduced [args],
      firing beta as far as [body] is a literal lambda. *)
  Fixpoint spec_beta (body : term) (args : list term) {struct args} : term :=
    match args with
    | [] => body
    | a :: args =>
        match body with
        | tLambda na body => spec_beta (body {0 := a}) args
        | _ => mkApps body (a :: args)
        end
    end.

  (** Bottom-up single pass: reduce children first, then attempt one head
      beta (via the collected spine) or iota (case-of-known-constructor). *)
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

End specialize.

(** ** Cloning driver

    Detect [tConst nm] applied to a leading run of closed dictionary
    constructors, emit a specialized copy of [nm] with those dictionaries
    substituted into its body, and redirect the call site to the copy. *)

Definition dkey : Type := kername × list term.

(** Boolean equality on specialization keys, built from the [ReflectEq]
    instances for [kername] and [term]; used for memoisation. *)
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

(** Is [ind] a single-constructor record (the typeclass/dictionary shape)? *)
Definition is_record_ind (Σ : global_declarations) (ind : inductive) : bool :=
  match lookup_inductive Σ ind with
  | Some (_, oib) => Nat.eqb #|oib.(ind_ctors)| 1
  | None => false
  end.

(** If [t] is a statically-known dictionary value, return the underlying
    (closed, single-constructor) [tConstruct].  Resolves one level of [tConst]
    delta so that a dictionary supplied as a named instance still qualifies. *)
Definition dict_value (Σ : global_declarations) (t : term) : option term :=
  match t with
  | tConstruct ind _ _ =>
      if is_record_ind Σ ind && closedn 0 t then Some t else None
  | tConst c =>
      match lookup_constant Σ c with
      | Some cb =>
          match cst_body cb with
          | Some (tConstruct ind n args) =>
              if is_record_ind Σ ind && closedn 0 (tConstruct ind n args)
              then Some (tConstruct ind n args) else None
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.

(** A spine element that belongs in a specialization prefix: either an erased
    type argument ([tBox], which typically precedes the dictionaries after
    erasure) or a statically-known dictionary value.  The boolean flags whether
    it is an actual dictionary (so only prefixes that contain at least one
    dictionary are specialized). *)
Definition prefix_elt (Σ : global_declarations) (t : term) : option (bool * term) :=
  match dict_value Σ t with
  | Some d => Some (true, d)
  | None => match t with tBox => Some (false, tBox) | _ => None end
  end.

(** Split a spine into its leading prefix of erased-type/dictionary arguments
    (resolved to the values to substitute) and the remaining ordinary
    arguments; the boolean reports whether the prefix contains a dictionary. *)
Fixpoint split_dicts (Σ : global_declarations) (spine : list term)
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

Definition callee_body (Σ : global_declarations) (nm : kername) : option term :=
  match lookup_constant Σ nm with
  | Some cb => cst_body cb
  | None => None
  end.

(** Body of a specialized copy: substitute the dictionaries into the callee
    body (for a [tFix]-bodied constant, unfold the fixpoint once first), then
    run the local beta/iota reducer to collapse the exposed projections. *)
Definition spec_body (b : term) (dicts : list term) : term :=
  match b with
  | tFix mfix idx =>
      match cunfold_fix mfix idx with
      | Some (_, fn) => specialize_instances (spec_beta fn dicts)
      | None => specialize_instances (mkApps b dicts)
      end
  | _ => specialize_instances (spec_beta b dicts)
  end.

(** Key of a specializable [tConst nm] call [nm @ spine], with the ordinary
    (non-dictionary) remainder of the spine. *)
Definition mk_key (Σ : global_declarations) (nm : kername) (spine : list term)
  : option (dkey * list term) :=
  match callee_body Σ nm with
  | Some _ =>
      let '(saw_dict, dicts, rest) := split_dicts Σ spine in
      if saw_dict then Some ((nm, dicts), rest) else None
  | None => None
  end.

(** Collect every specialization key reachable in a term (spine accumulator in
    the head position, exactly as [spec_aux]). *)
Fixpoint collect_keys (Σ : global_declarations) (spine : list term) (t : term)
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

(** Fuel-bounded saturation: pop a key, and if not already specialized, emit its
    specialized declaration and enqueue the keys newly exposed inside it. *)
Fixpoint saturate (Σ : global_declarations) (fuel : nat) (worklist : list dkey)
  (seen : list (dkey × kername)) (decls : list (kername × global_decl))
  {struct fuel} : list (dkey × kername) × list (kername × global_decl) :=
  match fuel with
  | 0 => (seen, decls)
  | S fuel' =>
      match worklist with
      | [] => (seen, decls)
      | k :: rest =>
          if existsb (fun p => eqb_key (fst p) k) seen
          then saturate Σ fuel' rest seen decls
          else
            let '(nm, dicts) := k in
            match callee_body Σ nm with
            | Some b =>
                let body := spec_body b dicts in
                let fn := fresh_name nm #|seen| in
                let new_keys := collect_keys Σ [] body in
                saturate Σ fuel' (new_keys ++ rest) ((k, fn) :: seen)
                         ((fn, ConstantDecl {| cst_body := Some body |}) :: decls)
            | None => saturate Σ fuel' rest seen decls
            end
      end
  end.

Definition lookup_spec (seen : list (dkey × kername)) (k : dkey) : option kername :=
  match find (fun p => eqb_key (fst p) k) seen with
  | Some p => Some (snd p)
  | None => None
  end.

(** Redirect specializable call sites to their emitted copies (pure rewrite;
    the memo table [seen] is fixed). *)
Fixpoint redirect (Σ : global_declarations) (seen : list (dkey × kername))
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

(** Whole-program driver: gather keys, saturate to a memo table + fresh
    declarations, then redirect every body and the main term and locally
    reduce. *)
Definition drive_env (Σ : global_declarations) (main : term)
  : global_declarations × term :=
  let body_keys :=
    fun d => match d with
             | ConstantDecl cb => match cst_body cb with
                                  | Some b => collect_keys Σ [] b
                                  | None => [] end
             | _ => [] end in
  let init_keys :=
    concat (map (fun '(_, d) => body_keys d) Σ) ++ collect_keys Σ [] main in
  let '(seen, gen_decls) := saturate Σ specialize_fuel init_keys [] [] in
  let Σ' := Σ ++ List.rev gen_decls in
  let red_decl :=
    fun '(kn, d) =>
      match d with
      | ConstantDecl cb =>
          (kn, ConstantDecl {| cst_body :=
                 option_map (fun b => specialize_instances (redirect Σ seen [] b))
                            (cst_body cb) |})
      | _ => (kn, d)
      end in
  (map red_decl Σ', specialize_instances (redirect Σ seen [] main)).

Definition specialize_instances_in_constant_body (cst : constant_body) : constant_body :=
  {| cst_body := option_map specialize_instances (cst_body cst) |}.

Definition specialize_instances_in_decl (d : global_decl) : global_decl :=
  match d with
  | ConstantDecl cst => ConstantDecl (specialize_instances_in_constant_body cst)
  | _ => d
  end.

Definition specialize_instances_env (Σ : global_declarations) : global_declarations :=
  map (fun '(kn, decl) => (kn, specialize_instances_in_decl decl)) Σ.

Definition specialize_instances_program (p : program) : program :=
  drive_env p.1 p.2.

(** ** Transform wrapper (unverified, [Compatible]-class) *)

From MetaRocq.Erasure Require Import EWellformed EWcbvEval.
From MetaRocq.Common Require Import Transform.

Axiom trust_specialize_instances_wf :
  forall efl : EEnvFlags,
  WcbvFlags ->
  forall (input : Transform.program _ term),
  wf_eprogram efl input -> wf_eprogram efl (specialize_instances_program input).

Axiom trust_specialize_instances_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : Transform.program _ term)
    (v : term),
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term,
  eval_eprogram wfl (specialize_instances_program p) v' /\ v' = specialize_instances v.

Import Transform.

Program Definition specialize_instances_transformation (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "instance specialization";
     transform p _ := specialize_instances_program p;
     pre p := wf_eprogram efl p;
     post p := wf_eprogram efl p;
     obseq p hp p' v v' := v' = specialize_instances v |}.
Next Obligation.
  now apply trust_specialize_instances_wf.
Qed.
Next Obligation.
  now eapply trust_specialize_instances_pres.
Qed.

Import EProgram EGlobalEnv.

#[global]
Axiom specialize_instances_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (specialize_instances_transformation efl wfl)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).

#[global]
Axiom specialize_instances_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (specialize_instances_transformation efl wfl)
    extends_eprogram extends_eprogram.
