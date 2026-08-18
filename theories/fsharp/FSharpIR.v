From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require EAst.
From Stdlib Require Import List.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  λ_pure-ish F# intermediate representation                         *)
(*                                                                    *)
(*  Loosely modelled on the λ_pure IR of Lean 4 (Ullrich & de Moura,  *)
(*  ``Counting Immutable Beans'', IFL 2019).  Not strict ANF: nested  *)
(*  expressions are permitted; the printer emits F# source where      *)
(*  the structure is naturally supported.  Anonymous lambdas and      *)
(*  fixpoints are lambda-lifted to top-level [FDef]/[FRecGroup]       *)
(*  declarations during compilation, so the IR only carries named     *)
(*  top-level functions.                                              *)
(* ------------------------------------------------------------------ *)

Inductive fterm : Set :=
| FVar    : ident -> fterm
| FConst  : kername -> fterm
| FCtor   : inductive -> nat (* ctor idx *) -> list fterm -> fterm
| FProj   : projection -> fterm -> fterm
| FApp    : fterm -> fterm -> fterm
| FLam    : ident -> fterm -> fterm  (* anonymous lambda fun x => body *)
| FLet    : ident -> fterm -> fterm -> fterm
| FCase   : fterm
            -> inductive (* discriminant inductive *)
            -> list (list ident * fterm) (* branches, indexed by ctor idx *)
            -> fterm
(* A nested (non-top-level) fixpoint.  Each entry is [(name, body)]
   where [body] is the compiled def body *with* its leading lambdas
   (printed as a term-mode [let rec name : Obj := body]).  The [nat]
   selects which mutual component this fix denotes.  Emitted only for
   fixes that appear as subterms; top-level fixpoints are handled by
   [compile_constant_body] and become [FDef]/[FRecGroup]. *)
| FFix    : list (ident * fterm) -> nat -> fterm
| FPanic  : string -> fterm.

Record ffun := mkFFun {
  ffun_params : list ident;
  ffun_body   : fterm;
}.

Inductive fdecl :=
| FInductive : EAst.mutual_inductive_body -> fdecl
| FDef       : ffun -> fdecl
| FRecGroup  : list (kername * ffun) -> fdecl.

Record fprogram := mkFProgram {
  fdecls : list (kername * fdecl);
}.
