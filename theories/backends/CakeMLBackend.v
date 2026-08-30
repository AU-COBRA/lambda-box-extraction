From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.ErasurePlugin Require Import ETransform.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Stdlib Require Import List.
From CeresBS Require Import CeresSerialize.
From CakeML.Backend Require Import Pipeline.
From CakeML.Backend Require Import Serialize.

Import ListNotations.
Import MonadNotation.
Import Common.Transform.Transform.

Local Open Scope bs_scope.



Definition default_cakeml_config := tt.

Definition cakeml_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
  cse_c            := Compatible false;
|}.



Fixpoint extract_names (t : EAst.term) : list ident :=
  match t with
  | EAst.tConst kn => [Kernames.string_of_kername kn]
  | EAst.tApp u v => (extract_names u) ++ extract_names v
  | _ => []
  end.

Program Definition cakeml_pipeline :
  Transform.t _ _ _ _ _ _ (EProgram.eval_eprogram final_wcbv_flags) (fun _ _ => True) :=
  enforce_extraction_conditions ▷
  name_annotation ▷
  compile_to_malfunction.
Final Obligation.
Admitted.

Definition print_program nms p :=
  let serialize p_c := @to_string _ (Serialize_module (rev nms)) p_c in
  let code := serialize p in
  (nms, code).

Axiom trust_coq_kernel : forall p, pre cakeml_pipeline p.

Definition extract_cakeml (remaps : constant_remappings)
                          (custom_attr : custom_attributes)
                          (opts : cakeml_config)
                          (file_name : string)
                          (p : EAst.program)
                          : result' (list string * string) :=
  let nms := extract_names (snd p) in
  let p := run cakeml_pipeline p (trust_coq_kernel p) in
  Ok (print_program nms p).
