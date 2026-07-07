From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require EAst.
From Stdlib Require Import List.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  λ_pure-ish Lean intermediate representation                       *)
(*                                                                    *)
(*  Loosely modelled on the λ_pure IR of Lean 4 (Ullrich & de Moura,  *)
(*  ``Counting Immutable Beans'', IFL 2019).  Not strict ANF: nested  *)
(*  expressions are permitted; the printer emits Lean source where    *)
(*  the structure is naturally supported.  Anonymous lambdas and      *)
(*  fixpoints are lambda-lifted to top-level [LDef]/[LRecGroup]       *)
(*  declarations during compilation, so the IR only carries named     *)
(*  top-level functions.                                              *)
(* ------------------------------------------------------------------ *)

Inductive lterm : Set :=
| LVar    : ident -> lterm
| LConst  : kername -> lterm
| LCtor   : inductive -> nat (* ctor idx *) -> list lterm -> lterm
| LProj   : projection -> lterm -> lterm
| LApp    : lterm -> lterm -> lterm
| LLam    : ident -> lterm -> lterm  (* anonymous lambda fun x => body *)
| LLet    : ident -> lterm -> lterm -> lterm
| LCase   : lterm
            -> inductive (* discriminant inductive *)
            -> list (list ident * lterm) (* branches, indexed by ctor idx *)
            -> lterm
(* A nested (non-top-level) fixpoint.  Each entry is [(name, body)]
   where [body] is the compiled def body *with* its leading lambdas
   (printed as a term-mode [let rec name : Obj := body]).  The [nat]
   selects which mutual component this fix denotes.  Emitted only for
   fixes that appear as subterms; top-level fixpoints are handled by
   [compile_constant_body] and become [LDef]/[LRecGroup]. *)
| LFix    : list (ident * lterm) -> nat -> lterm
| LPanic  : string -> lterm.

Record lfun := mkLFun {
  lfun_params : list ident;
  lfun_body   : lterm;
}.

Inductive ldecl :=
| LInductive : EAst.mutual_inductive_body -> ldecl
| LDef       : lfun -> ldecl
| LRecGroup  : list (kername * lfun) -> ldecl.

Record lprogram := mkLProgram {
  ldecls : list (kername * ldecl);
}.
