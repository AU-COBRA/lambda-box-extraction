From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import LeanIR.
From Peregrine Require Import LeanCompile.
From Peregrine Require Import PrintLean.

Local Open Scope bs_scope.



Definition default_lean_config := {|
  lean_namespace        := "Generated";
  lean_print_full_names := true;
|}.

Definition lean_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Required;
  cofix_to_laxy_c  := Required;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible false;
  dearg_consts_c   := Compatible false;
|}.



Definition extract_lean (remaps : constant_remappings)
                        (custom_attr : custom_attributes)
                        (opts : lean_config)
                        (file_name : string)
                        (p : EAst.program)
                        : result' string :=
  let ir := compile_program p in
  Ok (print_program opts.(lean_print_full_names) file_name opts.(lean_namespace) ir).



(* ----- Stub verification scaffolding -------------------------------

   These statements document the verification goals for the new
   backend.  They mirror the names used by CertiRocq's correctness
   lemmas so a future formalisation effort can find them by grep. *)

Theorem extract_lean_total :
  forall remaps attrs opts file p,
    exists s, extract_lean remaps attrs opts file p = Ok s.
Proof.
  intros. eexists. reflexivity.
Qed.

(* Semantics preservation: ⟦p⟧_λ□ ≈ ⟦extract_lean p⟧_Lean.
   Stated as [True] for now — to be replaced with a real relation
   between the EWcbvEval semantics and Lean 4's reduction. *)
Theorem extract_lean_semantics_preservation : True.
Proof. exact I. Qed.
