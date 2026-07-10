From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From CertiRocq Require Import CodegenWasm.toplevel.
From CertiRocq Require Import Common.Pipeline_utils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CertiRocqBackend.
From Wasm Require Import binary_format_printer.
From ExtLib.Structures Require Import Monad.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_wasm_config := {|
  direct    := true;
  c_args    := 5;
  o_level   := 0;
  anf_conf  := 0;
  prefix    := "";
  body_name := "body";
|}.

Definition wasm_phases := {|
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



Definition wasm_pipeline prs (p : EAst.program) :=
  anf_pipeline compile_LambdaANF_to_Wasm prs p.

Definition print_wasm p : string :=
  String.parse (binary_of_module p).

Definition extract_wasm (remaps : constant_remappings)
                        (custom_attr : custom_attributes)
                        (opts : wasm_config)
                        (file_name : string)
                        (p : EAst.program)
                        : result' string :=
  let config := mk_opts opts in
  let prs := mk_prims remaps in
  let (res, _) := run_pipeline EAst.program _ config p (wasm_pipeline prs) in
  match res with
  | compM.Ret m => Ok (print_wasm m)
  | compM.Err s => Err s
  end.
