From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import FSharpIR.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  EAst (λ_□) → FSharpIR translation                                 *)
(*                                                                    *)
(*  The context [ctx] maps de Bruijn indices to the [fterm] that      *)
(*  should be emitted for [tRel n].  Ordinary binders push [FVar id]; *)
(*  a recursive top-level [tFix] self-reference pushes [FConst kn].   *)
(* ------------------------------------------------------------------ *)

Definition ctx := list fterm.

Definition lookup_rel (c : ctx) (n : nat) : fterm :=
  nth n c (FPanic ("free de Bruijn index " ++ string_of_nat n)).

(* Produce an ident from a binder name.  Anonymous binders get a name
   derived from the current depth so they remain unique within scope. *)
Definition ident_of_name (depth : nat) (n : name) : ident :=
  match n with
  | nNamed s => s ++ "_" ++ string_of_nat depth
  | nAnon    => "_p" ++ string_of_nat depth
  end.

(* Peel top-level [tLambda]s off [t], collecting the binder names. *)
Fixpoint peel_lambdas (t : EAst.term) : list name * EAst.term :=
  match t with
  | EAst.tLambda na body =>
    let (nas, body') := peel_lambdas body in
    (na :: nas, body')
  | _ => ([], t)
  end.

(* Allocate fresh idents for a [list name], assigning each binder the
   depth it ends up at after the (left-to-right) sequence of pushes
   onto the existing context of depth [base]. *)
Fixpoint generate_ids (base : nat) (ns : list name) : list ident :=
  match ns with
  | [] => []
  | n :: rest => ident_of_name base n :: generate_ids (S base) rest
  end.

(* Push a list of idents (in left-to-right binding order) as [FVar]s onto
   the context.  The leftmost binder ends up deepest. *)
Fixpoint push_vars (ids : list ident) (c : ctx) : ctx :=
  match ids with
  | [] => c
  | id :: rest => push_vars rest (FVar id :: c)
  end.

(* [implement_box] replaces each erased proof/type [□] with a canonical
   self-looping fixpoint [fix f x1..xn := f] (dname usually "reccall").
   Such a value is never forced — it only occupies an erased argument
   slot — so we keep emitting the cheap [()] placeholder for it instead
   of a real [let rec], which also avoids a [let rec]-per-type-argument
   blowup.  Shape test: a singleton fix whose body, after peeling [n]
   lambdas, is exactly the self-reference [tRel n]. *)
Definition is_selfloop_fix (defs : list (EAst.def EAst.term)) : bool :=
  match defs with
  | [d] =>
    let '(params, body) := peel_lambdas d.(EAst.dbody) in
    match body with
    | EAst.tRel k => Nat.eqb k (List.length params)
    | _ => false
    end
  | _ => false
  end.

Fixpoint compile_term (c : ctx) (t : EAst.term) {struct t} : fterm :=
  match t with
  | EAst.tBox => FPanic "tBox should have been erased by implement_box"
  | EAst.tRel n => lookup_rel c n
  | EAst.tVar i => FVar i
  | EAst.tEvar _ _ => FPanic "tEvar unsupported"
  | EAst.tLambda na body =>
    let id := ident_of_name (List.length c) na in
    FLam id (compile_term (FVar id :: c) body)
  | EAst.tLetIn na b body =>
    let id := ident_of_name (List.length c) na in
    FLet id (compile_term c b) (compile_term (FVar id :: c) body)
  | EAst.tApp u v =>
    FApp (compile_term c u) (compile_term c v)
  | EAst.tConst kn => FConst kn
  | EAst.tConstruct ind n args =>
    FCtor ind n (List.map (compile_term c) args)
  | EAst.tCase indn discr brs =>
    let ind := fst indn in
    let discr' := compile_term c discr in
    let brs' := List.map (fun '(ns, body) =>
      let ids := generate_ids (List.length c) ns in
      let c' := push_vars ids c in
      (ids, compile_term c' body)
    ) brs in
    FCase discr' ind brs'
  | EAst.tProj p discr =>
    FProj p (compile_term c discr)
  | EAst.tFix defs idx =>
    if is_selfloop_fix defs then
      (* erased [□]; never inspected *)
      FPanic "erased box (self-loop fix)"
    else
    (* Nested fixpoint (a fix appearing as a subterm — typically an
       inlined recursive helper).  Compile it to an [FFix], which the
       printer emits as a term-mode [let rec].  Each mutual binder maps
       to [FVar name]; MetaCoq orders them so [tRel 0] is the *last*
       def, hence [mut_ctx] reverses [names].  Enclosing binders are
       captured by F#'s expression-level let rec directly, so no closure
       lifting is needed. *)
    let base := List.length c in
    let names := List.map (fun d => ident_of_name base d.(EAst.dname)) defs in
    let mut_ctx := List.rev (List.map (fun nm => FVar nm) names) in
    let c1 := List.app mut_ctx c in
    let entries := List.map (fun d =>
      (ident_of_name base d.(EAst.dname), compile_term c1 d.(EAst.dbody))) defs in
    FFix entries idx
  | EAst.tCoFix _ _ =>
    FPanic "tCoFix unsupported"
  | EAst.tPrim _ =>
    FPanic "tPrim unsupported"
  | EAst.tLazy _ =>
    FPanic "tLazy should have been removed by implement_lazy"
  | EAst.tForce _ =>
    FPanic "tForce should have been removed by implement_lazy"
  end.

(* Partial η-strip: walk outermost-in across [t], peeling [tApp _
   (tRel k)] wrappers as long as the rel index matches the expected
   one (outermost arg = [tRel 0], next = [tRel 1], ...).  Returns
   [(n_stripped, leftover)].

   Common shape from Rocq: [λx_0..x_{m-1}. tApp* (fix m. ...) (tRel 0)..(tRel j)]
   for some [j < m].  The [j+1] innermost outer params are η-applied
   to the fix; the remaining [m-j-1] outer params stay as closure
   variables for the lifted top-level definition.

   Soundness relies on [leftover] not free-referencing the dropped
   binders; this is true for the [tFix] uses we target (the fix's
   body uses the *closure* outer params, not the η-stripped ones),
   but is not checked here. *)
Fixpoint eta_strip_max (max_n : nat) (k : nat) (t : EAst.term) : nat * EAst.term :=
  match max_n with
  | O => (0, t)
  | S max_n' =>
    match t with
    | EAst.tApp f (EAst.tRel idx) =>
      if Nat.eqb idx k then
        let '(n', t') := eta_strip_max max_n' (S k) f in
        (S n', t')
      else (0, t)
    | _ => (0, t)
    end
  end.

(* Compile the body of a single top-level constant.

   Common shapes handled specially:
   - [tLambda x .. body]: peel into [ffun_params]
   - [tFix [d] 0]: self-recursive singleton; bind the fix variable to
     [FConst kn] so recursive calls re-enter through the global name
   - [tLambda x .. (tApp .. (tFix [d] 0) (tRel ..) ..)]: Rocq's
     standard η-expanded form for top-level fixpoints; η-contract the
     outer wrap, then handle as [tFix [d] 0]. *)
(* Build the kername of a sibling fix def from the current constant's
   kname.  Mutually-recursive constants share a [modpath]; only the
   ident differs, taken from each [dname] in the [tFix] block. *)
Definition sibling_kname (kn : kername) (d : EAst.def EAst.term) : kername :=
  let s :=
    match d.(EAst.dname) with
    | nNamed s => s
    | nAnon    => "anon"
    end in
  (fst kn, s).

Definition compile_constant_body (kn : kername) (t : EAst.term) : ffun :=
  let (outer_params, body1) := peel_lambdas t in
  let n_outer := List.length outer_params in
  let '(n0, body0) := eta_strip_max n_outer 0 body1 in
  (* Only commit the η-strip when the leftover is a [tFix] — that's
     the shape Rocq's extraction produces for top-level fixpoints
     ([λ x. fix ... x]).  For non-fix bodies (e.g. [λ x y. f x y]
     for an arbitrary [f]), stripping would silently shift the
     body's de Bruijn indices and silently lose binders. *)
  let '(n_stripped, body1') :=
    match body0 with
    | EAst.tFix _ _ => (n0, body0)
    | _             => (0, body1)
    end in
  match body1' with
  | EAst.tFix defs k =>
    match nth_error defs k with
    | None =>
      let ids := generate_ids 0 outer_params in
      let c := push_vars ids [] in
      {| ffun_params := ids;
         ffun_body   := compile_term c body1' |}
    | Some d =>
      let inner := d.(EAst.dbody) in
      let (inner_params, body2) := peel_lambdas inner in
      let n_inner := List.length inner_params in
      (* The last [n_stripped] outer lambdas are η-applied to the fix,
         so the fix's first [n_stripped] inner params alias them — same
         Lean variable.  Any further inner params become additional
         ffun params.  Outer lambdas left of the η chunk are closure
         variables that every recursive self-reference must re-pass. *)
      let n_stripped' := if Nat.leb n_stripped n_inner then n_stripped else n_inner in
      let extra_inner := List.skipn n_stripped' inner_params in
      let all_params := List.app outer_params extra_inner in
      let ids := generate_ids 0 all_params in
      let outer_ids := List.firstn n_outer ids in
      let extra_inner_ids := List.skipn n_outer ids in
      let n_closure := n_outer - n_stripped' in
      let closure_ids := List.firstn n_closure outer_ids in
      let eta_ids := List.skipn n_closure outer_ids in
      let c0 : ctx := push_vars outer_ids [] in
      (* Build self-refs for the whole mutual block: each fix binder
         maps to [FConst kn'] applied to the closure vars.  For a
         singleton fix the binder is just the outer constant's [kn];
         for a mutual block, each binder is the corresponding sibling.
         The list is reversed because MetaCoq's [tFix] pushes binders
         so [tRel 0] = last def, [tRel (n-1)] = first def.  Note: we
         use [kn] for singletons because the [dname] there is often a
         generic placeholder like "reccall" (e.g. injected by
         [implement_box]) that does not match the actual constant
         name. *)
      let sibling_terms : list fterm :=
        match defs with
        | [_] =>
          [List.fold_left (fun acc id => FApp acc (FVar id))
                          closure_ids (FConst kn)]
        | _ =>
          List.rev (List.map (fun di =>
            let sib_kn := sibling_kname kn di in
            List.fold_left (fun acc id => FApp acc (FVar id))
                           closure_ids (FConst sib_kn)
          ) defs)
        end in
      let c1 : ctx := List.app sibling_terms c0 in
      (* Push the head def's inner params: η-aliased ones reuse the
         outer ids; the rest are fresh.  Keeps de Bruijn indices in
         the body identical to the un-transformed EAst. *)
      let c2 : ctx := push_vars (List.app eta_ids extra_inner_ids) c1 in
      {| ffun_params := ids;
         ffun_body   := compile_term c2 body2 |}
    end
  | _ =>
    let ids := generate_ids 0 outer_params in
    let c := push_vars ids [] in
    {| ffun_params := ids;
       ffun_body   := compile_term c body1' |}
  end.

(* Generate one [(sibling_kn, ffun)] entry per def in a mutual fix
   block.  Each sibling's body is the synthetic [tFix defs i],
   compiled via [compile_constant_body] which already wires the
   sibling self-references through [sibling_kname]. *)
Definition emit_siblings (kn : kername) (defs : list (EAst.def EAst.term))
    : list (kername * ffun) :=
  let fix aux (i : nat) (ds : list (EAst.def EAst.term)) : list (kername * ffun) :=
    match ds with
    | [] => []
    | d :: rest =>
      let sib_kn := sibling_kname kn d in
      (sib_kn, compile_constant_body sib_kn (EAst.tFix defs i))
      :: aux (S i) rest
    end in
  aux 0 defs.

Definition compile_decl (kn : kername) (gd : EAst.global_decl) : list (kername * fdecl) :=
  match gd with
  | EAst.ConstantDecl cb =>
    match cb.(EAst.cst_body) with
    | None => []  (* axiom; skip *)
    | Some t =>
      let (_, body1) := peel_lambdas t in
      let n_outer := List.length (fst (peel_lambdas t)) in
      let '(_, body1') := eta_strip_max n_outer 0 body1 in
      match body1' with
      | EAst.tFix defs _ =>
        match defs with
        | d0 :: _ :: _ =>
          (* Mutual block.  Multiple constants in the env may expand
             the *same* tFix (e.g. both [oddNat] and [evenNat] are
             top-level), so only the constant whose name matches the
             first def's [dname] actually emits the block; the
             others are silently dropped to avoid Lean's "already
             declared" error. *)
          if eq_kername kn (sibling_kname kn d0) then
            [(kn, FRecGroup (emit_siblings kn defs))]
          else
            []
        | _ =>
          [(kn, FDef (compile_constant_body kn t))]
        end
      | _ =>
        [(kn, FDef (compile_constant_body kn t))]
      end
    end
  | EAst.InductiveDecl mib => [(kn, FInductive mib)]
  end.

Definition compile_env (env : EAst.global_declarations) : list (kername * fdecl) :=
  List.fold_right (fun '(kn, gd) acc =>
    List.app (compile_decl kn gd) acc
  ) [] env.

(* MetaCoq stores the global environment in reverse order of dependency
   (most recently declared first).  F# wants definitions before uses,
   so we reverse. *)
Definition compile_program (p : EAst.program) : fprogram :=
  let env := List.rev (fst p) in
  {| fdecls := compile_env env |}.
