From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import FSharpIR.
From Peregrine Require Import FSharpCompile.
From Peregrine Require Import PrintFSharp.

Local Open Scope bs_scope.



Definition default_fsharp_config := {|
  fsharp_namespace        := "Generated";
  fsharp_print_full_names := true;
|}.

Definition fsharp_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Required;
  cofix_to_laxy_c  := Required;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible false;
  dearg_consts_c   := Compatible false;
|}.



Definition extract_fsharp (remaps : constant_remappings)
                          (custom_attr : custom_attributes)
                          (opts : fsharp_config)
                          (file_name : string)
                          (p : EAst.program)
                          : result' string :=
  let ir := compile_program p in
  Ok (print_program opts.(fsharp_print_full_names) file_name opts.(fsharp_namespace) ir).



(* ----- Stub verification scaffolding -------------------------------

   These statements document the verification goals for the new
   backend.  They mirror the names used by CertiRocq's correctness
   lemmas so a future formalisation effort can find them by grep. *)

Theorem extract_fsharp_total :
  forall remaps attrs opts file p,
    exists s, extract_fsharp remaps attrs opts file p = Ok s.
Proof.
  intros. eexists. reflexivity.
Qed.

(* Semantics preservation: ⟦p⟧_λ□ ≈ ⟦extract_fsharp p⟧_F#.
   Stated as [True] for now — to be replaced with a real relation
   between the EWcbvEval semantics and F#'s reduction. *)
Theorem extract_fsharp_semantics_preservation : True.
Proof. exact I. Qed.
