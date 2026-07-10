From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import Transform.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.ErasurePlugin Require Import ETransform.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Malfunction Require Import Pipeline.
From Malfunction Require Import Serialize.
From Malfunction Require Import SemanticsSpec.
From Stdlib Require Import List.
From CeresBS Require Import CeresSerialize.

Import ListNotations.
Import MonadNotation.
Import Common.Transform.Transform.

Local Open Scope bs_scope.



Definition default_ocaml_config := {|
  Config.program_type := Malfunction.Serialize.Standalone
|}.

Definition ocaml_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible true;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
|}.



Fixpoint extract_names (t : EAst.term) : list ident :=
  match t with
  | EAst.tConst kn => [Kernames.string_of_kername kn]
  | EAst.tApp u v => (extract_names u) ++ extract_names v
  | _ => []
  end.

Local Existing Instance CanonicalHeap.
Local Existing Instance CanonicalPointer.

Program Definition malfunction_pipeline :
  Transform.t _ _ _ _ _ _ (EProgram.eval_eprogram final_wcbv_flags) (fun _ _ => True) :=
  enforce_extraction_conditions ▷
  name_annotation ▷
  compile_to_malfunction.
Next Obligation.
Admitted.
Final Obligation.
Admitted.

Definition print_program prims pt nms p :=
  let serialize p_c := @to_string _ (Serialize_module prims pt (rev nms)) p_c in
  let code := serialize p in
  (nms, code).

Definition mk_remaps (rs : constant_remappings) : Malfunction.primitives :=
  map (fun '(kn, r) =>
      let '(m, s) := split_name r.(re_const_s) in
      (string_of_kername kn, Malfunction.Global m s)
  ) rs.
(* TODO: support Malfuntion prim_def.Primtive & prim_def.Erased *)
(* TODO: collect list of packages for compiling *)



Axiom trust_coq_kernel : forall p, pre malfunction_pipeline p.

Definition extract_ocaml (remaps : constant_remappings)
                         (custom_attr : custom_attributes)
                         (opts : ocaml_config)
                         (file_name : string)
                         (p : EAst.program)
                         : result' (list string * string) :=
  let nms := extract_names (snd p) in
  let remaps := mk_remaps remaps in
  let p := run malfunction_pipeline p (trust_coq_kernel p) in
  Ok (print_program remaps opts.(Config.program_type) nms p).
