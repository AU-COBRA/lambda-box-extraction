From Peregrine Require Import Deserialize.
From Peregrine Require Import PAst.
From Peregrine Require Import Config.
From Peregrine Require Import ConfigUtils.
From Peregrine Require Import Transforms.
From Peregrine Require Import EHindleyMilner.
From Peregrine Require Import EHMNumericSigs.
From Peregrine Require Import Erasure.
From Peregrine Require Import CheckWf.
From Peregrine Require RustBackend.
From Peregrine Require ElmBackend.
From Peregrine Require OCamlBackend.
From Peregrine Require CBackend.
From Peregrine Require WasmBackend.
From Peregrine Require EvalBackend.
From Peregrine Require ASTBackend.
From Peregrine Require NameSanitize.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Utils.

Import MonadNotation.

Local Open Scope bs_scope.



Definition parse_ast (s : string) : result' PAst :=
  match PAst_of_string s with
  | inr p => Ok p
  | inl e => Err ("Failed parsing input program\n" ++ string_of_error true true e)
  end.

Definition parse_config (s : string) : result' config :=
  match config_of_string s with
  | inr p => Ok (mk_config p)
  | inl e => Err ("Failed parsing configuration file\n" ++ string_of_error true true e)
  end.

Definition parse_attribute (s : string) : result' attributes_config :=
  match attributes_config_of_string s with
  | inr p => Ok p
  | inl e => Err ("Failed parsing configuration file\n" ++ string_of_error true true e)
  end.

Definition parse_attributes (attrs : list string) : result' (list attributes_config) :=
  monad_map parse_attribute attrs.

Definition get_config (c : string + config') (attrs : list string) : result' config :=
  c <- match c with
      | inl s => parse_config s
      | inr c' => Ok (mk_config c')
      end;;
  attrs <- parse_attributes attrs;;
  if 0 <? length attrs then Ok (merge_attributes_config c attrs) else Ok c.

Definition check_wf (p : PAst) : result' unit :=
  map_error (fun e => "Program not wellformed\n" ++ e)
  match p with
  | Untyped env (Some t) =>
      @check_wf_program EWellformed.all_env_flags (env, t)
  | Untyped env None =>
      @check_wf_glob EWellformed.all_env_flags env
  | Typed env (Some t) =>
      _ <- @CheckWfExAst.check_wf_typed_program EWellformed.all_env_flags env;;
      @wellformed EWellformed.all_env_flags (ExAst.trans_env env) 0 t
  | Typed env None =>
      @CheckWfExAst.check_wf_typed_program EWellformed.all_env_flags env
  end.

Definition validate_ast_type (c : config) (p : PAst) : result' unit :=
  match c.(backend_opts) with
  (* Untyped (lambda-box) input is accepted for the typed backends: [PAst_to_ExAst]
     bridges it to lambda-box-typed via the verified HM section [infer]. *)
  | Rust _ => Ok tt
  | Elm _ => Ok tt
  | C _ | Wasm _ | OCaml _ | CakeML _ | Eval _ => Ok tt
  | AST c =>
    match c.(ast_type) with
    | LambdaBoxTyped => Ok tt
    | _ => Ok tt
    end
  end.

Definition needs_typed (c : config) : bool :=
  match c.(backend_opts) with
  | Rust _ | Elm _ => true
  | C _ | Wasm _ | OCaml _ | CakeML _ | Eval _ => false
  | AST c =>
    match c.(ast_type) with
    | LambdaBoxTyped => true
    | _ => false
    end
  end.

Definition apply_transforms (c : config) (p : PAst) (typed : bool) : result' PAst :=
  let econf := mk_opts c typed in
  let cstr_reorder := mk_cstr_reorders c in
  let impl_box := c.(erasure_opts).(implement_box) in
  let impl_lazy := c.(erasure_opts).(implement_lazy) in
  let spec_inst := c.(erasure_opts).(specialize_instances) in
  match p, typed with
  | Untyped env (Some t), true =>
      (* Typed backend on untyped (lambda-box) input: bridge to typed via the
         verified HM section [infer] on the *raw* env (before the untyped
         pipeline turns constructors into blocks, which the typed backends do
         not consume), then run the typed pipeline, which preserves applied
         constructors.  [infer_section] gives [trans_env (infer env) = env]. *)
      let '(_, (env', t')) := run_typed_transforms econf cstr_reorder (infer numeric_sigs env, t) in
      Ok (Typed env' (Some t'))
  | Untyped env None, true =>
      let '(_, (env', _)) := run_typed_transforms econf cstr_reorder (infer numeric_sigs env, EAst.tBox) in
      Ok (Typed env' None)
  | Untyped env (Some t), false =>
      let (env', t') := run_untyped_transforms econf cstr_reorder spec_inst impl_box impl_lazy (env, t) in
      Ok (Untyped env' (Some t'))
  | Untyped env None, false =>
      let (env', _) := run_untyped_transforms econf cstr_reorder spec_inst impl_box impl_lazy (env, EAst.tBox) in
      Ok (Untyped env' None)
  | Typed env (Some t), true =>
      let '(_, (env', t')) := run_typed_transforms econf cstr_reorder (env, t) in
      Ok (Typed env' (Some t'))
  | Typed env (Some t), false =>
      let (env', t') := run_typed_to_untyped_transforms econf cstr_reorder spec_inst impl_box impl_lazy (env, t) in
      (Ok (Untyped env' (Some t')))
  | Typed env None, true =>
      let '(_, (env', _)) := run_typed_transforms econf cstr_reorder (env, EAst.tBox) in
      Ok (Typed env' None)
  | Typed env None, false =>
      let (env', _) := run_typed_to_untyped_transforms econf cstr_reorder spec_inst impl_box impl_lazy (env, EAst.tBox) in
      (Ok (Untyped env' None))
  end.



Inductive extracted_program :=
| RustProgram : list string -> extracted_program
| ElmProgram : string -> extracted_program
| CProgram : (CertiRocq.Codegen.toplevel.Cprogram * list string) -> extracted_program
| WasmProgram : string -> extracted_program
| OCamlProgram : (list string * string) -> extracted_program
| CakeMLProgram : (list string * string) -> extracted_program
| EvalProgram : string -> extracted_program
| ASTProgram : string -> extracted_program.

Definition extraction_result : Type := result' extracted_program.

Definition run_backend (c : config) (f : string) (p : PAst) : extraction_result :=
  let const_remaps := c.(const_remappings_opts) in
  let ind_remaps := c.(ind_remappings_opts) in
  let custom_attr := c.(custom_attributes_opts) in
  match c.(backend_opts) with
  | Rust opts =>
    p' <- PAst_to_ExAst p;;
    res <- RustBackend.extract_rust
      const_remaps
      ind_remaps
      custom_attr
      opts
      f
      p';;
    Ok (RustProgram res)

  | Elm opts =>
    p' <- PAst_to_ExAst p;;
    res <- ElmBackend.extract_elm
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (ElmProgram res)

  | OCaml opts =>
    p' <- PAst_to_EAst p;;
    res <- OCamlBackend.extract_ocaml
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (OCamlProgram res)

  | CakeML opts =>
    p' <- PAst_to_EAst p;;
    res <- CakeMLBackend.extract_cakeml
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (CakeMLProgram res)

  | C opts =>
    p' <- PAst_to_EAst p;;
    res <- CBackend.extract_c
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (CProgram res)

  | Wasm opts =>
    p' <- PAst_to_EAst p;;
    res <- WasmBackend.extract_wasm
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (WasmProgram res)

  | Eval opts =>
    p' <- PAst_to_EAst p;;
    res <- EvalBackend.eval
      const_remaps
      custom_attr
      opts
      f
      p';;
    Ok (EvalProgram res)

  | AST opts =>
    res <- ASTBackend.extract_ast
      const_remaps
      custom_attr
      opts
      f
      p;;
    Ok (ASTProgram res)
  end.



Definition peregrine_pipeline (c : string + config') (attrs : list string) (p : string) (f : string) : extraction_result :=
  p <- parse_ast p;; (* Parse input string into AST *)
  c <- get_config c attrs;; (* Parse or construct config *)
  check_wf p;; (* Check that AST is wellformed *)
  validate_ast_type c p;; (* Check that the provided AST is compatible with the chosen backend *)
  p <- NameSanitize.sanitize_PAst (NameSanitize.get_sanitizer c) p;; (* Sanitize names in AST *)
  c <- NameSanitize.sanitize_config (NameSanitize.get_sanitizer c) c;; (* Sanitize names in config *)
  p <- apply_transforms c p (needs_typed c);; (* Apply program transformation *)
  run_backend c f p. (* Run extraction backend *)

Definition peregrine_validate (c : string + config') (attrs : list string) (p : string) : result' unit :=
  p <- parse_ast p;; (* Parse input string into AST *)
  c <- get_config c attrs;; (* Parse or construct config *)
  check_wf p. (* Check that AST is wellformed *)
