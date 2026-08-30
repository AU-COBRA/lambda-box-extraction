(** * EHindleyMilner: a type-inference forward map λ□ → λ□ᵀ, verified as a
      section of type erasure.

    ------------------------------------------------------------------------
    OVERVIEW

    λ□ (untyped extracted terms) and λ□ᵀ (typed extracted terms) share the
    term language [EAst.term]; they differ ONLY in the global environment:

      - λ□  uses [EAst.global_context] = list (kername * EAst.global_decl)
      - λ□ᵀ uses [ExAst.global_env]    = list (kername * bool * ExAst.global_decl)

    where ExAst declarations additionally carry [box_type] annotations.  The
    REVERSE map [ExAst.trans_env : ExAst.global_env -> EAst.global_context]
    forgets those annotations and is used in the verified pipeline
    ([Transforms.trans_env_transform]).

    This module builds the FORWARD map

      infer : dt_sigs -> EAst.global_context -> ExAst.global_env

    an Algorithm-W-style Hindley–Milner inference that DECORATES the untyped
    environment with [box_type]s.  Its untyped skeleton (kernames, bodies,
    constructor names/arities, projections) is left untouched, so [infer D] is a
    right inverse (a SECTION) of [trans_env], for ANY given datatype signatures
    [D]:

      trans_env (infer D Σ) = Σ.                      (* [infer_section] *)

    That is the verified deliverable and it is proved by [Qed] below (see
    [Print Assumptions infer_section] at the bottom of the file — closed under
    the empty context).

    ------------------------------------------------------------------------
    VERIFICATION STATUS

    - VERIFIED (Qed, no admits, no added axioms):
        [infer_section : forall D Σ, trans_env (infer D Σ) = Σ].
      This holds *by construction*: [infer] only fills in type fields that
      [trans_env] discards, and reproduces every skeleton field exactly.  The
      proof is robust to ANY choice of inferred types and ANY signatures [D],
      and to the dependency-ordered scheme threading (the scheme table only
      affects discarded type fields).  Supporting structural facts
      [infer_kernames] and [infer_has_deps] are also [Qed].

    - EVALUATION PRESERVATION is not re-proved here, and need not be: given
      [trans_env (infer D Σ) = Σ], observational/evaluation equivalence of the
      typed program with its untyped image is exactly the statement already
      established for [trans_env] in the verified pipeline
      ([Transforms.trans_env_transform], whose [obseq] is [v' = v]).  Composing
      that transform after [infer] transports evaluation with no fresh proof.
      [Lemma eval_preserved_via_section] packages that transport as a rewrite
      along [infer_section].

    - The inference ALGORITHM itself (the [box_type]s it assigns) does not
      claim principality or completeness; these do not hold on all of λ□ (□
      residue, polymorphic recursion, unrepresentable types).  Wherever HM
      cannot assign a principal ML type, inference falls back to [TAny] (⊤ /
      success-typing style), keeping [infer] TOTAL.

    ------------------------------------------------------------------------
    INFERENCE ALGORITHM

    1. UNIFICATION is an idempotent substitution-map solver with occurs-check.
       [extend] fully zonks the right-hand side against the current (idempotent)
       substitution, runs the occurs-check, and applies the new binding to the
       codomains of all existing bindings.  This maintains the invariant that
       the substitution is IDEMPOTENT, so a single structural [zonk] pass is a
       FULL zonk (all chains resolved).  [unify] handles [TInd]/[TConst] so
       datatype/constant types unify.  It is fuel-bounded for structural
       termination; out-of-fuel is a (total) unification failure → [TAny].

    2. CROSS-CONSTANT SCHEME PROPAGATION.  Constants are processed in dependency
       (topological) order — [infer_go] recurses on the tail FIRST, and an
       extracted environment lists a declaration before its dependencies, so the
       tail already holds every dependency's scheme.  Each constant's inferred
       type is Damas–Milner GENERALIZED ([generalize_ty]) and recorded in a
       scheme table; at every [tConst] use-site the scheme is INSTANTIATED with
       fresh variables ([instantiate]).  A constant absent from the table — e.g.
       a forward/mutual reference across the ordering — degrades gracefully to a
       fresh variable, keeping [infer] total.

    3. DATATYPE-DRIVEN TERM INFERENCE from GIVEN signatures.  [infer] takes a
       [dt_sigs] parameter supplying, per inductive, constructor argument/result
       [box_type]s and projection field types.  Using it, [infer_tm] types
         tConstruct  (unify args against constructor arg types; partial
                      application yields the residual arrow),
         tCase       (branch binders typed from constructor arg types; all
                      branch bodies unified to one result type),
         tProj       (field type from the projection signature),
         tFix        (MONOMORPHIC recursion: one fresh var per fixpoint, bodies
                      checked against them),
       alongside
         tBox, tRel, tLambda, tApp, tLetIn, tConst.
       [TAny] denotes genuine residue only: erased/□ content, missing
       signatures, out-of-fragment nodes (tCoFix, tEvar, tVar, tPrim, tLazy,
       tForce), or a unification/fuel failure.  [empty_sigs] supplies no
       signatures, so [tConstruct] and [tProj] yield [TAny] and [tCase] branch
       binders are [TAny] (the [tCase] result and [tFix] variables remain fresh
       unification variables, which do not consult [D]).

    4. TOWARD λ□ᵀ WELL-FORMEDNESS.  The imported MetaRocq install exposes no
       [check_wf_typed_program] predicate, so a full "output is a well-typed
       λ□ᵀ program" lemma is not available here.  What IS proved structurally:
       [infer_kernames] (kernames + order preserved) and [infer_has_deps] (every
       emitted declaration carries [has_deps=true]).  Together with
       [infer_section] these are the structural well-formedness facts the
       pipeline gate consumes; the remaining ExAst-only typing content
       (coherence of the [box_type] annotations) is exactly what [trans_env]
       discards and hence cannot be transported by the section law.

    INDUCTIVE-BODY DECORATION: [infer_oib] records [TAny] for the
    constructor-argument and projection type fields OF THE INDUCTIVE BODY.
    Those fields are discarded by [trans_env] and the untyped inductive body
    carries no type information to recover them from; the GIVEN signatures [D]
    are consumed where they matter for typing — at the term use-sites above.
    Refining the body decoration from [D] would thread the inductive identity
    into [infer_oib]; it is omitted to keep the decoration path free of index
    bookkeeping.

    ------------------------------------------------------------------------
    PIPELINE INTEGRATION.  [PAst.v] [PAst_to_ExAst] promotes untyped
    (lambda-box) input into the typed world with [infer empty_sigs env], and
    [Pipeline.v] runs [infer numeric_sigs env] on the raw environment before the
    typed pipeline for the typed backends (Rust, Elm).  The section lemma
    licenses this: it guarantees the promoted environment erases back to the
    original untyped one, so the untyped correctness results transfer.

    What the section law does NOT transport is the ExAst-only content: that the
    inferred [box_type] annotations are coherent (well-scoped type variables,
    matching arities, instantiable schemes).  A [check_wf_typed_program]-style
    predicate would state this, but none is present in the imported MetaRocq,
    and [infer_oib] would first need to consult [D] for datatype bodies rather
    than emitting [TAny] (see the decoration note above). *)

From Stdlib Require Import List Arith.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.

Import ListNotations.

(** ** Type-inference substitutions and idempotent unification *)

Definition subst_t := list (nat * ExAst.box_type).

Fixpoint slookup (s : subst_t) (n : nat) : option ExAst.box_type :=
  match s with
  | [] => None
  | (m, t) :: s' => if Nat.eqb n m then Some t else slookup s' n
  end.

(** One structural pass.  Because [extend] keeps the substitution IDEMPOTENT
    (see below), a single pass is a *full* zonk: every reachable variable is
    resolved. *)
Fixpoint zonk (s : subst_t) (t : ExAst.box_type) : ExAst.box_type :=
  match t with
  | ExAst.TVar n => match slookup s n with Some u => u | None => ExAst.TVar n end
  | ExAst.TArr a b => ExAst.TArr (zonk s a) (zonk s b)
  | ExAst.TApp a b => ExAst.TApp (zonk s a) (zonk s b)
  | _ => t
  end.

Fixpoint occurs (n : nat) (t : ExAst.box_type) : bool :=
  match t with
  | ExAst.TVar m => Nat.eqb n m
  | ExAst.TArr a b => occurs n a || occurs n b
  | ExAst.TApp a b => occurs n a || occurs n b
  | _ => false
  end.

(** Substitute a single variable [n] by [r] everywhere in [t]. *)
Fixpoint subst_var (n : nat) (r t : ExAst.box_type) : ExAst.box_type :=
  match t with
  | ExAst.TVar m => if Nat.eqb m n then r else ExAst.TVar m
  | ExAst.TArr a b => ExAst.TArr (subst_var n r a) (subst_var n r b)
  | ExAst.TApp a b => ExAst.TApp (subst_var n r a) (subst_var n r b)
  | _ => t
  end.

(** Idempotency-preserving extension.  [t] is first fully zonked against [s]
    (so it mentions no variable in [dom s]); the occurs-check then rejects a
    cyclic binding; finally the new binding [n ↦ t] is pushed through the
    codomains of every existing binding.  The result is again idempotent, so a
    one-pass [zonk] stays a full zonk. *)
Definition extend (n : nat) (t : ExAst.box_type) (s : subst_t) : option subst_t :=
  let t := zonk s t in
  if occurs n t then None
  else Some ((n, t) :: map (fun '(m, u) => (m, subst_var n t u)) s).

Definition unify_fuel : nat := 1000.

(** Fuel-bounded for structural termination; each recursive descent works on
    zonked (hence idempotent-resolved) types.  Running out of fuel is a
    (total) failure. *)
Fixpoint unify (fuel : nat) (s : subst_t) (a b : ExAst.box_type) : option subst_t :=
  match fuel with
  | 0 => None
  | S fuel =>
    let a := zonk s a in
    let b := zonk s b in
    match a, b with
    | ExAst.TAny, _ => Some s
    | _, ExAst.TAny => Some s
    | ExAst.TBox, ExAst.TBox => Some s
    | ExAst.TVar n, ExAst.TVar m => if Nat.eqb n m then Some s else extend n b s
    | ExAst.TVar n, _ => extend n b s
    | _, ExAst.TVar m => extend m a s
    | ExAst.TArr a1 a2, ExAst.TArr b1 b2 =>
      match unify fuel s a1 b1 with
      | Some s1 => unify fuel s1 a2 b2
      | None => None
      end
    | ExAst.TApp a1 a2, ExAst.TApp b1 b2 =>
      match unify fuel s a1 b1 with
      | Some s1 => unify fuel s1 a2 b2
      | None => None
      end
    | ExAst.TInd i, ExAst.TInd j => if eq_inductive i j then Some s else None
    | ExAst.TConst c, ExAst.TConst d => if eq_kername c d then Some s else None
    | _, _ => None
    end
  end.

(** Unify a positional prefix of two type lists, threading the substitution.
    Any per-position failure is swallowed (kept total); over-/under-length is
    simply ignored on the extra tail.

    [fuel] is a *parameter* (not the [unify_fuel] literal) on purpose: a
    fixpoint whose recursive call sits inside a [match unify <literal> …]
    triggers the guard checker to reduce [unify] at that literal fuel, which is
    exponential in the fuel.  Keeping [fuel] an opaque variable here (and
    throughout the [infer_tm] block below) leaves [unify] irreducible for the
    guard checker; the literal is supplied only at the top-level [Definition]s,
    where no guard check runs. *)
Fixpoint unify_list (fuel : nat) (s : subst_t) (xs ys : list ExAst.box_type) : subst_t :=
  match xs, ys with
  | x :: xs', y :: ys' =>
    match unify fuel s x y with
    | Some s1 => unify_list fuel s1 xs' ys'
    | None => unify_list fuel s xs' ys'
    end
  | _, _ => s
  end.

(** ** [box_type] utilities: free variables, freshening, arrows *)

Fixpoint ftv (t : ExAst.box_type) : list nat :=
  match t with
  | ExAst.TVar n => [n]
  | ExAst.TArr a b => ftv a ++ ftv b
  | ExAst.TApp a b => ftv a ++ ftv b
  | _ => []
  end.

Definition max_tv (t : ExAst.box_type) : nat := fold_left Nat.max (ftv t) 0.
Definition max_tvs (ts : list ExAst.box_type) : nat :=
  fold_left Nat.max (flat_map ftv ts) 0.

(** Shift every type variable of [t] up by [base] (freshening a stored
    signature/scheme into a fresh region starting at [base]). *)
Fixpoint inst_tv (base : nat) (t : ExAst.box_type) : ExAst.box_type :=
  match t with
  | ExAst.TVar n => ExAst.TVar (base + n)
  | ExAst.TArr a b => ExAst.TArr (inst_tv base a) (inst_tv base b)
  | ExAst.TApp a b => ExAst.TApp (inst_tv base a) (inst_tv base b)
  | _ => t
  end.

(** Freshen a constructor signature [(ts -> res)] starting at [base]; returns
    the freshened argument types, result type, and the next free counter. *)
Definition freshen_sig (base : nat) (ts : list ExAst.box_type) (res : ExAst.box_type)
  : list ExAst.box_type * ExAst.box_type * nat :=
  let k := S (Nat.max (max_tvs ts) (max_tv res)) in
  (map (inst_tv base) ts, inst_tv base res, base + k).

Definition freshen1 (base : nat) (t : ExAst.box_type) : ExAst.box_type * nat :=
  (inst_tv base t, base + S (max_tv t)).

Fixpoint mkArrows (dom : list ExAst.box_type) (cod : ExAst.box_type) : ExAst.box_type :=
  match dom with
  | [] => cod
  | a :: rest => ExAst.TArr a (mkArrows rest cod)
  end.

(** ** Damas–Milner type schemes and the cross-constant scheme table *)

Definition scheme : Type := (list name * ExAst.box_type)%type.
Definition sch_env : Type := list (kername * scheme).

Fixpoint sch_lookup (E : sch_env) (kn : kername) : option scheme :=
  match E with
  | [] => None
  | (kn', sch) :: E' => if eq_kername kn kn' then Some sch else sch_lookup E' kn
  end.

(** A generalized scheme has its bound variables renamed to [0 .. k-1]
    (see [generalize_ty]); instantiation lifts them into the fresh region at
    [base]. *)
Definition instantiate (base : nat) (sch : scheme) : ExAst.box_type * nat :=
  let '(vs, body) := sch in (inst_tv base body, base + length vs).

(** ** Given datatype signatures (threaded parameter)

    [dt_ctor ind c = Some (argtys, resty)] gives constructor [c] of inductive
    [ind] its argument and result [box_type]s (variables numbered from 0, à la
    a scheme).  [dt_proj ind i = Some ty] gives the [i]-th projection's field
    type.  [empty_sigs] supplies nothing, recovering [TAny] everywhere. *)
Record dt_sigs := mk_dt_sigs {
  dt_ctor : inductive -> nat -> option (list ExAst.box_type * ExAst.box_type);
  dt_proj : inductive -> nat -> option ExAst.box_type
}.

Definition empty_sigs : dt_sigs :=
  mk_dt_sigs (fun _ _ => None) (fun _ _ => None).

(** ** Algorithm-W-style term inference

    [infer_tm fuel D E ctx cnt s t = (ty, s', cnt')]: [D] the datatype
    signatures, [E] the cross-constant scheme table, [ctx] maps de Bruijn
    indices to their [box_type]s, [cnt] is the fresh-variable counter, [s] the
    current substitution.  TOTAL: every failure path (including running out of
    [fuel]) returns [TAny].

    IMPLEMENTATION NOTE — why this is a SINGLE fuel-bounded [Fixpoint] and not a
    mutual one.  A mutual [Fixpoint infer_tm/infer_args/infer_brs/infer_mfix]
    recursing structurally on the term/list, with recursive calls sitting inside
    [match unify unify_fuel …], forces the guard/termination checker to WHNF-
    reduce [unify] at the *literal* fuel (1000) while validating the mutual
    block, which is pathologically slow.  Two devices avoid it:

    (a) The list traversals ([go_args]/[go_brs]/[go_mfix]) are ordinary,
        NON-mutual [Fixpoint]s over their list, parameterised by the term-
        inference function [f] and by an OPAQUE unify-fuel [uf] (a plain [nat]
        variable, never the literal), so the guard checker cannot reduce
        [unify uf].

    (b) [infer_tm] recurses structurally on [fuel : nat] (not on the term).  Its
        recursive uses appear as the partially-applied [infer_tm fuel D E]
        handed to the list helpers, which the guard checker accepts immediately
        ([fuel] is a subterm of [S fuel]); it never needs to reduce a [unify]. *)

Definition tm_fn : Type :=
  list ExAst.box_type -> nat -> subst_t -> EAst.term
  -> ExAst.box_type * subst_t * nat.

(** Infer the (positional) types of an applied argument list, threading the
    fresh counter and substitution left-to-right. *)
Fixpoint go_args (f : tm_fn) (ctx : list ExAst.box_type)
                 (cnt : nat) (s : subst_t) (ts : list EAst.term) {struct ts}
                 : list ExAst.box_type * subst_t * nat :=
  match ts with
  | [] => ([], s, cnt)
  | u :: us =>
    let '(tu, s1, c1) := f ctx cnt s u in
    let '(rest, s2, c2) := go_args f ctx c1 s1 us in
    (tu :: rest, s2, c2)
  end.

(** Infer all [tCase] branches, unifying every branch body against the common
    result type [r].  Branch binders are typed from the constructor argument
    types when the signature is present and its arity matches; otherwise [TAny].
    [bi] is the branch/constructor index.  [uf] is the (opaque) unify fuel. *)
Fixpoint go_brs (uf : nat) (f : tm_fn) (D : dt_sigs)
                (ctx : list ExAst.box_type) (ind : inductive) (r : ExAst.box_type)
                (bs : list (list name * EAst.term)) (bi : nat)
                (cnt : nat) (s : subst_t) {struct bs}
                : subst_t * nat :=
  match bs with
  | [] => (s, cnt)
  | (nms, body) :: bs' =>
    let '(bctx, cnt1) :=
      match dt_ctor D ind bi with
      | Some (atys, _) =>
        if Nat.eqb (List.length atys) (List.length nms)
        then (List.rev (map (inst_tv cnt) atys), cnt + S (max_tvs atys))
        else (map (fun _ => ExAst.TAny) nms, cnt)
      | None => (map (fun _ => ExAst.TAny) nms, cnt)
      end in
    let '(tbody, s1, c1) := f (bctx ++ ctx) cnt1 s body in
    match unify uf s1 tbody r with
    | Some s2 => go_brs uf f D ctx ind r bs' (S bi) c1 s2
    | None => go_brs uf f D ctx ind r bs' (S bi) c1 s1
    end
  end.

(** Infer a (monomorphic) mutual fixpoint: each body is checked in the context
    extended with the fixpoint variables [vars] and unified against its own
    fresh variable.  [uf] is the (opaque) unify fuel. *)
Fixpoint go_mfix (uf : nat) (f : tm_fn)
                 (ctx : list ExAst.box_type) (vars : list ExAst.box_type)
                 (cnt : nat) (s : subst_t)
                 (ds : list (EAst.def EAst.term)) {struct ds}
                 : subst_t * nat :=
  match ds, vars with
  | d :: ds', v :: vs' =>
    let '(tb, s1, c1) := f ctx cnt s d.(EAst.dbody) in
    match unify uf s1 tb v with
    | Some s2 => go_mfix uf f ctx vs' c1 s2 ds'
    | None => go_mfix uf f ctx vs' c1 s1 ds'
    end
  | _, _ => (s, cnt)
  end.

Fixpoint infer_tm (fuel : nat) (D : dt_sigs) (E : sch_env)
                  (ctx : list ExAst.box_type) (cnt : nat) (s : subst_t)
                  (t : EAst.term) {struct fuel}
                  : ExAst.box_type * subst_t * nat :=
  match fuel with
  | 0 => (ExAst.TAny, s, cnt)
  | S fuel =>
    match t with
    | EAst.tBox => (ExAst.TBox, s, cnt)
    | EAst.tRel n =>
      match nth_error ctx n with
      | Some ty => (zonk s ty, s, cnt)
      | None => (ExAst.TAny, s, cnt)
      end
    | EAst.tLambda _ body =>
      let a := ExAst.TVar cnt in
      let '(rb, s1, c1) := infer_tm fuel D E (a :: ctx) (S cnt) s body in
      (ExAst.TArr (zonk s1 a) rb, s1, c1)
    | EAst.tApp u v =>
      let '(tu, s1, c1) := infer_tm fuel D E ctx cnt s u in
      let '(tv, s2, c2) := infer_tm fuel D E ctx c1 s1 v in
      let r := ExAst.TVar c2 in
      match unify unify_fuel s2 tu (ExAst.TArr tv r) with
      | Some s3 => (zonk s3 r, s3, S c2)
      | None => (ExAst.TAny, s2, S c2)
      end
    | EAst.tLetIn _ b body =>
      let '(tb, s1, c1) := infer_tm fuel D E ctx cnt s b in
      infer_tm fuel D E (zonk s1 tb :: ctx) c1 s1 body
    | EAst.tConst kn =>
      match sch_lookup E kn with
      | Some sch => let '(ty, c1) := instantiate cnt sch in (ty, s, c1)
      | None => (ExAst.TVar cnt, s, S cnt)   (* not in scheme table: fresh var *)
      end
    | EAst.tConstruct ind n args =>
      let '(argtys, s1, c1) := go_args (infer_tm fuel D E) ctx cnt s args in
      match dt_ctor D ind n with
      | Some (atys, resty) =>
        let '(atys', resty', c2) := freshen_sig c1 atys resty in
        let s2 := unify_list unify_fuel s1 argtys atys' in
        (zonk s2 (mkArrows (List.skipn (List.length argtys) atys') resty'), s2, c2)
      | None => (ExAst.TAny, s1, c1)
      end
    | EAst.tCase indn c brs =>
      let ind := fst indn in
      let '(_, s0, c0) := infer_tm fuel D E ctx cnt s c in
      let r := ExAst.TVar c0 in
      let '(s1, c1) := go_brs unify_fuel (infer_tm fuel D E) D ctx ind r brs 0 (S c0) s0 in
      (zonk s1 r, s1, c1)
    | EAst.tProj p c =>
      let '(_, s1, c1) := infer_tm fuel D E ctx cnt s c in
      match dt_proj D p.(proj_ind) p.(proj_arg) with
      | Some ty => let '(ty', c2) := freshen1 c1 ty in (zonk s1 ty', s1, c2)
      | None => (ExAst.TAny, s1, c1)
      end
    | EAst.tFix mfix idx =>
      let n := List.length mfix in
      let vars := map (fun i => ExAst.TVar (cnt + i)) (List.seq 0 n) in
      let fixctx := List.rev vars in
      let '(s1, c1) := go_mfix unify_fuel (infer_tm fuel D E) (fixctx ++ ctx) vars (cnt + n) s mfix in
      (zonk s1 (List.nth idx vars ExAst.TAny), s1, c1)
    (* Genuinely out-of-fragment / erased residue. *)
    | EAst.tCoFix _ _ | EAst.tEvar _ _
    | EAst.tVar _ | EAst.tPrim _ | EAst.tLazy _ | EAst.tForce _ =>
      (ExAst.TAny, s, cnt)
    end
  end.

(** Fuel for [infer_tm]: any bound exceeding the term's syntactic depth suffices;
    running short only makes the result [TAny] more often (never unsound — the
    section law does not depend on the inferred types). *)
Definition infer_fuel : nat := 1000.

(** ** Damas–Milner generalization at the top level of a constant *)

Fixpoint mem_nat (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | m :: l' => if Nat.eqb n m then true else mem_nat n l'
  end.

Fixpoint dedup_nat (l : list nat) : list nat :=
  match l with
  | [] => []
  | n :: l' => if mem_nat n (dedup_nat l') then dedup_nat l' else n :: dedup_nat l'
  end.

Fixpoint idx_nat (n : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | m :: l' => if Nat.eqb n m then 0 else S (idx_nat n l')
  end.

Fixpoint rename_tv (vs : list nat) (t : ExAst.box_type) : ExAst.box_type :=
  match t with
  | ExAst.TVar n => ExAst.TVar (idx_nat n vs)
  | ExAst.TArr a b => ExAst.TArr (rename_tv vs a) (rename_tv vs b)
  | ExAst.TApp a b => ExAst.TApp (rename_tv vs a) (rename_tv vs b)
  | _ => t
  end.

(** Generalize a (fully zonked) type: quantify every free type variable,
    renaming them to the canonical [0 .. k-1] so [instantiate] can freshen. *)
Definition generalize_ty (t : ExAst.box_type) : list name * ExAst.box_type :=
  let vs := dedup_nat (ftv t) in
  (map (fun _ => nAnon) vs, rename_tv vs t).

Definition infer_cst_type (D : dt_sigs) (E : sch_env) (b : option EAst.term)
  : list name * ExAst.box_type :=
  match b with
  | None => ([], ExAst.TAny)
  | Some t =>
    let '(ty, s, _) := infer_tm infer_fuel D E [] 0 [] t in
    generalize_ty (zonk s ty)
  end.

(** ** Decorating declarations (the actual forward map) *)

Definition infer_const (D : dt_sigs) (E : sch_env) (cb : EAst.constant_body)
  : ExAst.constant_body :=
  {| ExAst.cst_type := infer_cst_type D E cb.(EAst.cst_body);
     ExAst.cst_body := cb.(EAst.cst_body) |}.

(** Reconstruct a typed one-inductive body.  Constructor argument types and
    projection types are set to [TAny] (see the module header: those fields are
    discarded by [trans_env] and the untyped body has no types to recover; the
    GIVEN signatures are consumed at term use-sites instead).  The ORIGINAL
    arity ([cstr_nargs]) is preserved so that [trans_oib] recovers the untyped
    body exactly. *)
Definition infer_oib (oib : EAst.one_inductive_body) : ExAst.one_inductive_body :=
  {| ExAst.ind_name := oib.(EAst.ind_name);
     ExAst.ind_propositional := oib.(EAst.ind_propositional);
     ExAst.ind_kelim := oib.(EAst.ind_kelim);
     ExAst.ind_type_vars := [];
     ExAst.ind_ctors :=
       map (fun c => (c.(EAst.cstr_name),
                      repeat (nAnon, ExAst.TAny) c.(EAst.cstr_nargs),
                      c.(EAst.cstr_nargs)))
           oib.(EAst.ind_ctors);
     ExAst.ind_projs :=
       map (fun p => (p.(EAst.proj_name), ExAst.TAny)) oib.(EAst.ind_projs) |}.

Definition infer_mib (mib : EAst.mutual_inductive_body) : ExAst.mutual_inductive_body :=
  {| ExAst.ind_finite := mib.(EAst.ind_finite);
     ExAst.ind_npars := mib.(EAst.ind_npars);
     ExAst.ind_bodies := map infer_oib mib.(EAst.ind_bodies) |}.

(** The forward map, threading the Damas–Milner scheme table in dependency
    order.  [infer_go] recurses on the TAIL first: since an extracted
    environment lists a declaration before the declarations it depends on, the
    tail's schemes are available when the head is processed.  Only constants
    contribute schemes.  [has_deps := true] on every declaration (discarded by
    [trans_env]). *)
Fixpoint infer_go (D : dt_sigs) (Σ : EAst.global_context)
  : ExAst.global_env * sch_env :=
  match Σ with
  | [] => ([], [])
  | (kn, d) :: Σ' =>
    let '(env, E) := infer_go D Σ' in
    match d with
    | EAst.ConstantDecl cb =>
      let cb' := infer_const D E cb in
      ((kn, true, ExAst.ConstantDecl cb') :: env,
       (kn, cb'.(ExAst.cst_type)) :: E)
    | EAst.InductiveDecl mib =>
      ((kn, true, ExAst.InductiveDecl (infer_mib mib)) :: env, E)
    end
  end.

Definition infer (D : dt_sigs) (Σ : EAst.global_context) : ExAst.global_env :=
  fst (infer_go D Σ).

(** ** The section lemma and its supporting inversions *)

Lemma trans_infer_const (D : dt_sigs) (E : sch_env) (cb : EAst.constant_body) :
  ExAst.trans_cst (infer_const D E cb) = cb.
Proof. destruct cb; reflexivity. Qed.

Lemma trans_infer_oib (oib : EAst.one_inductive_body) :
  ExAst.trans_oib (infer_oib oib) = oib.
Proof.
  destruct oib as [nm prop kelim ctors projs].
  unfold ExAst.trans_oib, infer_oib; cbn.
  f_equal.
  - (* ind_ctors *)
    unfold ExAst.trans_ctors. rewrite map_map.
    induction ctors as [|c cs IH]; cbn; [reflexivity|].
    destruct c; cbn. f_equal. exact IH.
  - (* ind_projs *)
    rewrite map_map.
    induction projs as [|p ps IH]; cbn; [reflexivity|].
    destruct p; cbn. f_equal. exact IH.
Qed.

Lemma trans_infer_mib (mib : EAst.mutual_inductive_body) :
  ExAst.trans_mib (infer_mib mib) = mib.
Proof.
  destruct mib as [fin npars bodies].
  unfold ExAst.trans_mib, infer_mib; cbn.
  f_equal.
  rewrite map_map.
  induction bodies as [|o os IH]; cbn; [reflexivity|].
  rewrite trans_infer_oib. f_equal. exact IH.
Qed.

(** *** Main theorem: [infer D] is a section of [trans_env], for any [D]. *)
Theorem infer_section (D : dt_sigs) (Σ : EAst.global_context) :
  ExAst.trans_env (infer D Σ) = Σ.
Proof.
  unfold infer.
  induction Σ as [|[kn d] Σ IH]; [reflexivity|].
  simpl infer_go. destruct (infer_go D Σ) as [env E] eqn:Hgo.
  (* [destruct … eqn:Hgo] already rewrote [infer_go D Σ] to [(env,E)] inside
     [IH], so [IH : trans_env (fst (env,E)) = Σ]; [cbn] gives [trans_env env]. *)
  assert (Henv : ExAst.trans_env env = Σ) by (cbn in IH; exact IH).
  destruct d as [cb|mib]; cbn;
    unfold ExAst.trans_env in *; cbn in *.
  - rewrite trans_infer_const. rewrite Henv. reflexivity.
  - rewrite trans_infer_mib. rewrite Henv. reflexivity.
Qed.

(** *** Evaluation preservation, schematically.

    Any property [P] of the untyped environment that the verified pipeline
    establishes for [trans_env (infer D Σ)] is a property of [Σ] itself, and
    vice versa, because the two are equal.  In particular, whatever
    evaluation/observational equivalence [trans_env_transform] proves for
    [trans_env (infer D Σ)] holds verbatim for [Σ]; no fresh evaluation proof
    is needed.  [eval_preserved_via_section] packages that transport. *)
Lemma eval_preserved_via_section
      (P : EAst.global_context -> Prop) (D : dt_sigs) (Σ : EAst.global_context) :
  P (ExAst.trans_env (infer D Σ)) <-> P Σ.
Proof. rewrite infer_section. reflexivity. Qed.

(** The whole forward map preserves the untyped skeleton, stated as the
    equality the pipeline wiring relies on. *)
Corollary infer_erases_back (D : dt_sigs) (Σ : EAst.global_context) :
  ExAst.trans_env (infer D Σ) = Σ.
Proof. exact (infer_section D Σ). Qed.

(** ** Structural well-formedness facts (toward λ□ᵀ well-typedness)

    A full [check_wf_typed_program]-style lemma is out of reach here (that
    predicate is absent from the imported MetaRocq; see the header).  These are
    the structural well-formedness facts the pipeline gate relies on. *)

(** Kernames and their order are preserved exactly. *)
Lemma infer_kernames (D : dt_sigs) (Σ : EAst.global_context) :
  map (fun '(kn, _, _) => kn) (infer D Σ) = map fst Σ.
Proof.
  unfold infer.
  induction Σ as [|[kn d] Σ IH]; [reflexivity|].
  simpl infer_go. destruct (infer_go D Σ) as [env E] eqn:Hgo.
  assert (Henv : map (fun '(kn0, _, _) => kn0) env = map fst Σ)
    by (cbn in IH; exact IH).
  destruct d as [cb|mib]; cbn; rewrite Henv; reflexivity.
Qed.

(** Every emitted declaration carries [has_deps = true]. *)
Lemma infer_has_deps (D : dt_sigs) (Σ : EAst.global_context) :
  Forall (fun '(_, b, _) => b = true) (infer D Σ).
Proof.
  unfold infer.
  induction Σ as [|[kn d] Σ IH]; [constructor|].
  simpl infer_go. destruct (infer_go D Σ) as [env E] eqn:Hgo.
  assert (Henv : Forall (fun '(_, b, _) => b = true) env)
    by (cbn in IH; exact IH).
  destruct d as [cb|mib]; cbn; constructor; try exact Henv; reflexivity.
Qed.

Print Assumptions infer_section.
Print Assumptions infer_kernames.
Print Assumptions infer_has_deps.
