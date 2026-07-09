From ExtLib.Structures Require Import Monad.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From CertiRocq Require Import Compiler.pipeline.
From CertiRocq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import PAst.
From Peregrine Require Import CertiRocqBackend.
From Peregrine Require SerializePAst.
From Peregrine Require SerializeLambdaBoxMut.
From Peregrine Require SerializeLambdaBoxLocal.
From Peregrine Require SerializeLambdaANF.
From MetaRocq.Utils Require Import ResultMonad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_ast_config := {|
  ast_type := LambdaBox;
|}.

Definition default_ast_c_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 0;
  anf_conf  := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition ast_phases := {|
  implement_box_c  := Compatible false;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible false;
  dearg_consts_c   := Compatible false;
  specialize_instances_c := Compatible false;
|}.

Definition extract_untyped_ast (p : EAst.program)
                               : result' string :=
  Ok (SerializePAst.string_of_PAst (Untyped p.1 (Some p.2))).

Definition extract_typed_ast (p : ExAst.global_env)
                             : result' string :=
  Ok (SerializePAst.string_of_PAst (Typed p None)).

Definition extract_mut_ast (remaps : constant_remappings)
                           (opts : certirocq_config)
                           (p : EAst.program)
                           : result' string :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let (res, _) :=
    run_pipeline EAst.program _ config p (mut_pipeline prs) in
  match res with
  | compM.Ret s =>
    Ok (@SerializeLambdaBoxMut.string_of_Program _ SerializeLambdaBoxMut.Serialize_Term s)
  | compM.Err s => Err s
  end.

Definition extract_local_ast (remaps : constant_remappings)
                             (opts : certirocq_config)
                             (p : EAst.program)
                            : result' string :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let (res, _) :=
    run_pipeline EAst.program _ config p (local_pipeline prs) in
  match res with
  | compM.Ret s =>
    Ok (SerializeLambdaBoxLocal.string_of_LambdaBoxLocalTerm s)
  | compM.Err s => Err s
  end.


Definition extract_anf_ast (remaps : constant_remappings)
                           (opts : certirocq_config)
                           (p : EAst.program)
                           : result' string :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let (res, _) :=
    run_pipeline EAst.program _ config p (anf_pipeline' prs) in
  match res with
  | compM.Ret s =>
    Ok (SerializeLambdaANF.string_of_LambdaANF_FullTerm s)
  | compM.Err s => Err s
  end.


Definition extract_anfc_ast (remaps : constant_remappings)
                            (opts : certirocq_config)
                            (p : EAst.program)
                            : result' string :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let (res, _) :=
    run_pipeline EAst.program _ config p (anf_pipeline (fun _ => id_trans) prs) in
  match res with
  | compM.Ret s =>
    Ok (SerializeLambdaANF.string_of_LambdaANF_FullTerm s)
  | compM.Err s => Err s
  end.

Definition extract_ast (remaps : constant_remappings)
                       (custom_attr : custom_attributes)
                       (opts : ast_config)
                       (file_name : string)
                       (p : PAst.PAst)
                       : result' string :=
  match opts.(ast_type) with
  | LambdaBox =>
    (* Cannot use monad notation due to extlib/metarocq clash *)
    match PAst_to_EAst p with
    | Ok p => extract_untyped_ast p
    | Err e => Err e
    end
  | LambdaBoxTyped =>
    match PAst_to_ExAst p with
    | Ok p => extract_typed_ast p
    | Err e => Err e
    end
  | LambdaBoxMut c =>
    match PAst_to_EAst p with
    | Ok p => extract_mut_ast remaps c p
    | Err e => Err e
    end
  | LambdaBoxLocal c =>
    match PAst_to_EAst p with
    | Ok p => extract_local_ast remaps c p
    | Err e => Err e
    end
  | LambdaANF c =>
    match PAst_to_EAst p with
    | Ok p => extract_anf_ast remaps c p
    | Err e => Err e
    end
  | LambdaANFC c =>
    match PAst_to_EAst p with
    | Ok p => extract_anfc_ast remaps c p
    | Err e => Err e
    end
  end.
