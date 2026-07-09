(** Datatype signatures ([dt_sigs]) for the standard numeric/boolean inductives,
    to sharpen [EHindleyMilner.infer] on untyped (lambda-box) input.

    [infer empty_sigs] leaves a constant whose type is only tied to a
    constructor of, say, [nat] as a bare type variable (the inferencer has no
    signature to concretise it), so the extracted entry gets a generic Rust type
    ([-> a]) that [rustc] rejects against a concrete numeric body.  Supplying the
    constructor argument/result [box_type]s for [nat]/[positive]/[N]/[Z]/[bool]
    lets inference concretise those types.

    This only changes which [box_type] annotations [infer] emits; it does NOT
    affect [infer_section] ([trans_env (infer D Sigma) = Sigma]), which erases
    every [box_type] regardless of [D]. *)

From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import ExAst.
From MetaRocq.Utils Require Import bytestring.
From TypedExtraction Require Import Common.
From Peregrine Require Import EHindleyMilner.
From Stdlib Require Import Arith ZArith NArith PArith List.
Import ListNotations.

Definition i_nat  : inductive := {| inductive_mind := <%% nat %%>;      inductive_ind := 0 |}.
Definition i_pos  : inductive := {| inductive_mind := <%% positive %%>; inductive_ind := 0 |}.
Definition i_N    : inductive := {| inductive_mind := <%% N %%>;        inductive_ind := 0 |}.
Definition i_Z    : inductive := {| inductive_mind := <%% Z %%>;        inductive_ind := 0 |}.
Definition i_bool : inductive := {| inductive_mind := <%% bool %%>;     inductive_ind := 0 |}.

Definition tnat  := TInd i_nat.
Definition tpos  := TInd i_pos.
Definition tN    := TInd i_N.
Definition tZ    := TInd i_Z.
Definition tbool := TInd i_bool.

(* [nat]: O (0) : nat ; S (1) : nat -> nat. *)
Definition sig_nat (c : nat) : option (list box_type * box_type) :=
  match c with
  | 0 => Some ([], tnat)
  | 1 => Some ([tnat], tnat)
  | _ => None
  end.

(* [positive]: xI (0) : positive -> positive ; xO (1) : positive -> positive ;
   xH (2) : positive. *)
Definition sig_pos (c : nat) : option (list box_type * box_type) :=
  match c with
  | 0 => Some ([tpos], tpos)
  | 1 => Some ([tpos], tpos)
  | 2 => Some ([], tpos)
  | _ => None
  end.

(* [N]: N0 (0) : N ; Npos (1) : positive -> N. *)
Definition sig_N (c : nat) : option (list box_type * box_type) :=
  match c with
  | 0 => Some ([], tN)
  | 1 => Some ([tpos], tN)
  | _ => None
  end.

(* [Z]: Z0 (0) : Z ; Zpos (1) : positive -> Z ; Zneg (2) : positive -> Z. *)
Definition sig_Z (c : nat) : option (list box_type * box_type) :=
  match c with
  | 0 => Some ([], tZ)
  | 1 => Some ([tpos], tZ)
  | 2 => Some ([tpos], tZ)
  | _ => None
  end.

(* [bool]: true (0) : bool ; false (1) : bool. *)
Definition sig_bool (c : nat) : option (list box_type * box_type) :=
  match c with
  | 0 => Some ([], tbool)
  | 1 => Some ([], tbool)
  | _ => None
  end.

Definition numeric_dt_ctor (ind : inductive) (c : nat)
  : option (list box_type * box_type) :=
  if eq_inductive_def ind i_nat  then sig_nat  c
  else if eq_inductive_def ind i_pos  then sig_pos  c
  else if eq_inductive_def ind i_N    then sig_N    c
  else if eq_inductive_def ind i_Z    then sig_Z    c
  else if eq_inductive_def ind i_bool then sig_bool c
  else None.

Definition numeric_sigs : dt_sigs :=
  mk_dt_sigs numeric_dt_ctor (fun _ _ => None).
