From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Utils Require Import bytestring.
From Peregrine Require Import Utils.
From Peregrine Require Import EHindleyMilner.



Definition typed_env := ExAst.global_env.
Definition untyped_env := EAst.global_context.

Inductive PAst :=
| Untyped : untyped_env -> option EAst.term -> PAst
| Typed : typed_env -> option EAst.term -> PAst.



Definition PAst_to_EAst (ast : PAst) : result' EAst.program :=
  match ast with
  | Untyped env (Some t) => Ok (env, t)
  | Untyped env None => Ok (env, EAst.tBox) (* TODO: what should we in this case? *)
  | Typed env (Some t) => Ok (ExAst.trans_env env, t)
  | Typed env None => Ok (ExAst.trans_env env, EAst.tBox)
  end.

Definition PAst_to_ExAst (ast : PAst) : result' ExAst.global_env :=
  match ast with
  (* Untyped (lambda-box) input is bridged to typed (lambda-box-typed) by the
     verified Hindley-Milner section [infer]: [trans_env (infer empty_sigs env)
     = env] (EHindleyMilner.infer_section), so erasure recovers the original
     program.  [empty_sigs] supplies no datatype signatures; inference falls
     back to [TAny] where a type is undetermined, which the section law tolerates
     since the [box_type] annotations are erased away. *)
  | Untyped env _ => Ok (infer empty_sigs env)
  | Typed env (Some t) => Ok env (* TODO: add t to env, with a fresh name or hardcoded main? *)
  | Typed env None => Ok env
  end.

Definition is_typed_ast (p : PAst) : bool :=
  match p with
  | Untyped _ _ => false
  | Typed _ _ => true
  end.

Definition is_untyped_ast (p : PAst) : bool :=
  match p with
  | Untyped _ _ => true
  | Typed _ _ => false
  end.
