From MetaRocq.Utils Require Import bytestring.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import NArith.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  CatCrypt [NamedSSA] intermediate representation                    *)
(*                                                                    *)
(*  A straight-line SSA block over 64-bit registers.  Inputs occupy    *)
(*  levels [0 .. ccp_ninputs-1]; binding [k] defines level             *)
(*  [ccp_ninputs + k].  The operation set is exactly CatCrypt's        *)
(*  [SupportedOp] fragment (ScalarLinDeBruijn.lean) — the ARM/RISC-V   *)
(*  instruction selector silently drops anything outside it.          *)
(* ------------------------------------------------------------------ *)

Variant cc_binop := CCAdd | CCSub | CCMul | CCAnd | CCOr | CCXor.

Variant cc_op :=
| CCArith  (b : cc_binop)
| CCMulHi
| CCShrImm (n : nat)
| CCShlImm (n : nat)
| CCConst  (n : N).

Record cc_binding := mkCCBinding {
  ccb_op   : cc_op;
  ccb_args : list nat;
}.

Record cc_prog := mkCCProg {
  ccp_name     : string;
  ccp_comment  : string;
  ccp_ninputs  : nat;
  ccp_bindings : list cc_binding;
  ccp_ret      : nat;
}.

Definition cc_op_arity (o : cc_op) : nat :=
  match o with
  | CCArith _  => 2
  | CCMulHi    => 2
  | CCShrImm _ => 1
  | CCShlImm _ => 1
  | CCConst _  => 0
  end.

(* The 63-bit mask [2^63 - 1], shared by the compiler and the printer. *)
Definition cc_mask63 : N := N.ones 63.

Definition cc_wf (p : cc_prog) : bool :=
  let fix aux (lvl : nat) (bs : list cc_binding) : bool :=
    match bs with
    | [] => true
    | b :: rest =>
      andb (andb (Nat.eqb (List.length b.(ccb_args)) (cc_op_arity b.(ccb_op)))
                 (forallb (fun a => Nat.ltb a lvl) b.(ccb_args)))
           (aux (S lvl) rest)
    end in
  andb (aux p.(ccp_ninputs) p.(ccp_bindings))
       (Nat.ltb p.(ccp_ret) (p.(ccp_ninputs) + List.length p.(ccp_bindings))).
