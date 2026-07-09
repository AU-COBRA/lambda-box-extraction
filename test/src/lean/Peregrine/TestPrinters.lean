/-
  Peregrine.TestPrinters — universal s-expression printers used by
  the test harness to inspect Obj values emitted by the Lean backend.

  The Lean backend emits each source inductive as an `unsafe inductive
  <Name>_` whose constructor names come from the source frontend
  (rocq, agda, lean, ...).  At runtime, however, those inductives all
  share the same memory layout as any other inductive with the same
  constructor arities in the same order.  The printers below cast an
  `Obj` to a *canonical* inductive of the right shape and pattern-match
  on it, so they work regardless of the source frontend's naming.

  Conventions, fixed across frontends:
    Bool  : false @ 0,  true @ 1
    Nat   : zero  @ 0,  succ @ 1 (1 field)
    List  : nil   @ 0,  cons @ 1 (2 fields)

  Output format matches the OCaml backend's s-expression form, so test
  expectations in `expected_output[0]` stay common.
-/
import Peregrine.Runtime

namespace Peregrine

unsafe inductive PBool : Type where
  | f
  | t

unsafe inductive PNat : Type where
  | zero
  | succ (n : Obj)

unsafe inductive PList : Type where
  | nil
  | cons (h t : Obj)

unsafe def pp_bool (o : Obj) : String :=
  match (Peregrine.cast o : PBool) with
  | .f => "false"
  | .t => "true"

unsafe def pp_nat (o : Obj) : String :=
  match (Peregrine.cast o : PNat) with
  | .zero => "O"
  | .succ n => "(S " ++ pp_nat n ++ ")"

unsafe def pp_list (ppA : Obj -> String) (o : Obj) : String :=
  match (Peregrine.cast o : PList) with
  | .nil => "nil"
  | .cons h t => "(cons " ++ ppA h ++ " " ++ pp_list ppA t ++ ")"

end Peregrine
