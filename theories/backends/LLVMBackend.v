(* LLVM/VIR backend entry point for the Peregrine CLI: mirrors WasmBackend.v,
   retargeted to certirocq's CodegenLLVM backend (compile_LambdaANF_to_LLVM +
   serialize_program). Requires the installed certirocq to expose
   CertiRocq.CodegenLLVM (and Vellvm). *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From CertiRocq Require Import CodegenLLVM.toplevel.   (* compile_LambdaANF_to_LLVM, serialize_program *)
From CertiRocq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CertiRocqBackend.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_llvm_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 0;
  anf_conf  := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition llvm_phases := {|
  implement_box_c  := Required;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
|}.



Definition llvm_pipeline prs (p : EAst.program) :=
  anf_pipeline compile_LambdaANF_to_LLVM prs p.

Definition print_llvm p : string :=
  String.parse (serialize_program p).

Definition extract_llvm (remaps : constant_remappings)
                        (custom_attr : custom_attributes)
                        (opts : llvm_config)
                        (file_name : string)
                        (p : EAst.program)
                        : result' string :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let (res, _) := run_pipeline EAst.program _ config p (llvm_pipeline prs) in
  match res with
  | compM.Ret m => Ok (print_llvm m)
  | compM.Err s => Err s
  end.
