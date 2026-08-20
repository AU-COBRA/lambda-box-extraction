From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CatCryptIR.
From Peregrine Require Import CatCryptCompile.
From Peregrine Require Import PrintCatCrypt.
From Stdlib Require Import List.

Import ListNotations.
Import MonadNotation.

Local Open Scope bs_scope.



Definition default_catcrypt_config := {|
  catcrypt_namespace := "PeregrineGenerated";
  catcrypt_def_name  := "";
  catcrypt_mask63    := true;
  catcrypt_scaffold  := false;
|}.

(* [betared] normalises the β-redexes erasure leaves behind; every other
   phase either introduces constructs the straight-line fragment
   rejects or is a no-op on it. *)
Definition catcrypt_phases := {|
  implement_box_c  := Compatible false;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible true;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible false;
  dearg_consts_c   := Compatible false;
|}.



Definition extract_catcrypt (remaps : constant_remappings)
                            (custom_attr : custom_attributes)
                            (opts : catcrypt_config)
                            (file_name : string)
                            (p : EAst.program)
                            : result' string :=
  ir <- compile_program (List.app remaps builtin_remaps)
                        opts.(catcrypt_mask63)
                        opts.(catcrypt_def_name)
                        p ;;
  if cc_wf ir then
    Ok (print_program opts.(catcrypt_namespace)
                      opts.(catcrypt_def_name)
                      opts.(catcrypt_mask63)
                      opts.(catcrypt_scaffold)
                      ir)
  else
    Err "internal error: the generated CatCrypt program is not well-formed (SSA level out of scope)".
