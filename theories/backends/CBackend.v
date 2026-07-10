From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From CertiRocq Require Import Compiler.pipeline.
From CertiRocq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CertiRocqBackend.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_c_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 0;
  anf_conf  := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition c_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
|}.



Definition c_pipeline prs (p : EAst.program) :=
  anf_pipeline compile_Clight prs p.

Definition extract_c (remaps : constant_remappings)
                     (custom_attr : custom_attributes)
                     (opts : c_config)
                     (file_name : string)
                     (p : EAst.program)
                     : result' (Cprogram * list string) :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let gc_lib := if opts.(direct) then "gc_stack.h" else "gc.h" in
  let libs := gc_lib :: (Kernames.IdentSetProp.to_list (get_libs remaps)) in
  let (res, _) := run_pipeline EAst.program Cprogram config p (c_pipeline prs) in
  match res with
  | compM.Ret p => Ok (p, libs)
  | compM.Err s => Err s
  end.
