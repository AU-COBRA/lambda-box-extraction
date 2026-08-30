From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From TypedExtraction Require Import PrettyPrinterMonad.
From TypedExtraction Require Import ElmExtract.
From TypedExtraction Require Import Common.

Import MonadNotation.

Local Open Scope bs_scope.



Definition default_elm_config := {|
  elm_preamble         := "";
  elm_module_name      := None;
  elm_term_box_symbol  := "()";
  elm_type_box_symbol  := "()";
  elm_any_type_symbol  := "()";
  elm_false_elim_def   := "false_rec ()";
  elm_print_full_names := true;
|}.

Definition elm_phases := {|
  implement_box_c  := Compatible false;
  implement_lazy_c := Compatible false;
  cofix_to_laxy_c  := Compatible false;
  betared_c        := Compatible false;
  unboxing_c       := Compatible false;
  dearg_ctors_c    := Compatible true;
  dearg_consts_c   := Compatible true;
  specialize_instances_c := Compatible false;
  cse_c            := Compatible false;
|}.



Definition mk_preamble (o : elm_config) f : string :=
  let mod_name :=
    match o.(elm_module_name) with
    | Some s => s
    | None => f
    end in
  "module " ++ mod_name ++ " exposing (..)" ++ nl ++ o.(elm_preamble) ++ nl ++ o.(elm_false_elim_def).

Definition mk_config (o : elm_config) : ElmPrintConfig := {|
  term_box_symbol   := o.(elm_term_box_symbol);
  type_box_symbol   := o.(elm_type_box_symbol);
  any_type_symbol   := o.(elm_any_type_symbol);
  false_elim_def    := o.(elm_false_elim_def);
  print_full_names  := o.(elm_print_full_names);
|}.

Definition mk_remaps (rs : constant_remappings) : Kernames.kername -> option string :=
  let re_const := map (fun '(kn, r) =>
    (kn, r.(re_const_s))
  ) rs in
  match re_const with
  | nil => fun _ => None
  | _ => fun kn =>
      option_map (fun '(_,s) => s)
        (List.find (fun '(kn', _) => Kernames.eq_kername kn kn') re_const)
  end.
(* TODO: support external remapping in Elm backend *)
(* TODO: support inline constant remapping in Elm backend *)
(* TODO: support inductive remapping in Elm backend *)



Definition extract_elm (remaps : constant_remappings)
                       (custom_attr : custom_attributes)
                       (opts : elm_config)
                       (file_name : string)
                       (p : ExAst.global_env)
                       : result' string :=
  let remaps    := mk_remaps remaps in
  let config    := mk_config opts in
  let preamble  := mk_preamble opts file_name in
  let p := @print_env p remaps config in
  '(_, s) <- finish_print p;;
  @Ok string string (preamble ++ nl ++ s ++ nl).
