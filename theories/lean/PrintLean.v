From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import MRString.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import LeanIR.
From Peregrine Require Utils.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  LeanIR → Lean 4 source pretty-printer                             *)
(* ------------------------------------------------------------------ *)

Definition nl : string := String.String "010"%byte String.EmptyString.

Definition concat_with (sep : string) (xs : list string) : string :=
  String.concat sep xs.

(* Use just the last component of a kername.  All emitted definitions
   live inside a single Lean namespace, so collisions only matter
   across modules that happen to share a local name — accepted v1
   limitation, controlled by [lean_print_full_names]. *)
Definition local_name (kn : kername) : string := snd kn.

(* Flat full name: [default_module ++ "_" ++ snd kn].  [default_module]
   is the source file basename, supplied by the CLI driver.  We
   deliberately ignore the kernel modpath: across frontends the
   modpath ranges from empty (lean-to-lambdabox) to deep
   ([Peregrine.Tests.Demo] for rocq extractions), which would
   yield inconsistent emitted names across otherwise-identical
   programs.  Tests expect [<File>_<ident>], so we anchor on the
   file name.  External-module references in the same program are
   currently rare because erasure inlines library types into local
   copies; if collisions ever arise, switch this to fold a
   one-component summary of [fst kn]. *)
Definition full_name (default_module : string) (kn : kername) : string :=
  match default_module with
  | "" => snd kn
  | _ => default_module ++ "_" ++ snd kn
  end.

Definition pick_fun_name (full : bool) (default_module : string) (kn : kername) : string :=
  if full then full_name default_module kn else local_name kn.

(* Suffix inductive / constructor names with [_] so we never collide
   with Lean keywords (e.g. [true], [false], [Nat]). *)
Definition ind_name (s : ident) : string := s ++ "_".
Definition ctor_name (s : ident) : string := s ++ "_".

Fixpoint mk_arg_idents (n : nat) : list string :=
  match n with
  | O => []
  | S k => ("a" ++ string_of_nat (n - 1 - k)) :: mk_arg_idents k
  end.
(* mk_arg_idents 3 = ["a0"; "a1"; "a2"]  (reversed-build, restored order) *)

Definition arg_idents (n : nat) : list string :=
  let fix aux (i max : nat) : list string :=
    match i with
    | O => []
    | S k => ("a" ++ string_of_nat (max - i)) :: aux k max
    end in
  aux n n.
(* arg_idents 3 = ["a0"; "a1"; "a2"] *)

(* Format a parameter group: "(x0 x1 .. xn : Obj)" — empty string if no
   parameters. *)
Definition params_group (ids : list string) : string :=
  match ids with
  | [] => ""
  | _ => "(" ++ concat_with " " ids ++ " : Obj)"
  end.

(* ----- Inductive lookup environment ------------------------------- *)

Definition ind_env := list (kername * EAst.mutual_inductive_body).

Definition build_ind_env (decls : list (kername * ldecl)) : ind_env :=
  Utils.filter_map (fun (x : kername * ldecl) =>
    let '(kn, d) := x in
    match d with
    | LInductive mib => Some (kn, mib)
    | _ => None
    end
  ) decls.

Definition lookup_oib (env : ind_env) (ind : inductive) : option EAst.one_inductive_body :=
  match List.find (fun '(kn, _) => eq_kername kn ind.(inductive_mind)) env with
  | Some (_, mib) => nth_error mib.(EAst.ind_bodies) ind.(inductive_ind)
  | None => None
  end.

Definition lookup_ctor_name (env : ind_env) (ind : inductive) (n : nat) : string :=
  match lookup_oib env ind with
  | Some oib =>
    match nth_error oib.(EAst.ind_ctors) n with
    | Some cb => ctor_name (cb.(EAst.cstr_name))
    | None => "MissingCtor_" ++ string_of_nat n
    end
  | None => "MissingInd_" ++ string_of_nat n
  end.

Definition lookup_ind_name (env : ind_env) (ind : inductive) : string :=
  match lookup_oib env ind with
  | Some oib => ind_name (oib.(EAst.ind_name))
  | None => "MissingInd"
  end.

(* ----- Inductive declaration printer (context-free) --------------- *)

Definition print_ctor (cb : EAst.constructor_body) : string :=
  let nargs := cb.(EAst.cstr_nargs) in
  let ids := arg_idents nargs in
  "  | " ++ ctor_name (cb.(EAst.cstr_name))
    ++ (match ids with [] => "" | _ => " " ++ params_group ids end).

Definition print_one_inductive (oib : EAst.one_inductive_body) : string :=
  "unsafe inductive " ++ ind_name (oib.(EAst.ind_name)) ++ " where" ++ nl
    ++ concat_with nl (List.map print_ctor (oib.(EAst.ind_ctors))).

Definition print_inductive (mib : EAst.mutual_inductive_body) : string :=
  match mib.(EAst.ind_bodies) with
  | [oib] => print_one_inductive oib
  | bodies =>
    "mutual" ++ nl
      ++ concat_with nl (List.map print_one_inductive bodies) ++ nl
      ++ "end"
  end.

(* ----- Term / declaration printer --------------------------------- *)

Section Printer.
  (* Invariant context, shared by every printer below. *)
  Context (full_names : bool) (default_module : string) (env : ind_env)
          (thunks : list kername).

  (* Nullary top-level constants are emitted as memoized [Thunk Obj]
     (see [print_lfun]); references to them must force via [.get]. *)
  Definition is_thunk (kn : kername) : bool :=
    List.existsb (fun k => eq_kername k kn) thunks.

  (* Every recursive call returns a string that names an [Obj]-typed
     Lean expression, achieved by wrapping each emitted term in
     [Peregrine.reflect] (idempotent at runtime). *)
  Fixpoint print_lterm (t : lterm) : string :=
    let reflect s := "(Peregrine.reflect " ++ s ++ ")" in
    match t with
    | LVar id => reflect id
    | LConst kn =>
      let nm := pick_fun_name full_names default_module kn in
      if is_thunk kn then reflect (nm ++ ".get") else reflect nm
    | LCtor ind idx args =>
      let cn := lookup_ctor_name env ind idx in
      let ind_n := lookup_ind_name env ind in
      let body :=
        match args with
        | [] => "(." ++ cn ++ " : " ++ ind_n ++ ")"
        | _ =>
          "((" ++ ind_n ++ "." ++ cn ++ ") "
            ++ concat_with " " (List.map print_lterm args) ++ ")"
        end in
      reflect body
    | LProj p discr =>
      let ind := p.(proj_ind) in
      let arg := p.(proj_arg) in
      let cn := lookup_ctor_name env ind 0 in
      let nargs :=
        match lookup_oib env ind with
        | Some oib =>
          match nth_error oib.(EAst.ind_ctors) 0 with
          | Some cb => cb.(EAst.cstr_nargs)
          | None => 0
          end
        | None => 0
        end in
      let mk_pat (i : nat) :=
        if Nat.eqb i arg then "x" else "_" in
      let pat_args :=
        let fix aux (i : nat) :=
          match i with
          | O => []
          | S k => mk_pat (nargs - i) :: aux k
          end in
        aux nargs in
      reflect ("(match (Peregrine.cast " ++ print_lterm discr
        ++ " : " ++ lookup_ind_name env ind ++ ") with | ." ++ cn ++ " "
        ++ concat_with " " pat_args ++ " => x)")
    | LApp f x =>
      reflect ("(Peregrine.apply " ++ print_lterm f ++ " " ++ print_lterm x ++ ")")
    | LLam id body =>
      reflect ("(fun (" ++ id ++ " : Obj) => " ++ print_lterm body ++ ")")
    | LLet id b body =>
      reflect ("(let " ++ id ++ " : Obj := " ++ print_lterm b ++ "; "
        ++ print_lterm body ++ ")")
    | LCase discr ind brs =>
      let ind_n := lookup_ind_name env ind in
      let print_br (i : nat) (br : list ident * lterm) : string :=
        let '(ids, body) := br in
        let cn := lookup_ctor_name env ind i in
        "  | ." ++ cn
          ++ (match ids with [] => "" | _ => " " ++ concat_with " " ids end)
          ++ " => " ++ print_lterm body in
      let fix print_brs (i : nat) (bs : list (list ident * lterm)) : list string :=
        match bs with
        | [] => []
        | b :: rest => print_br i b :: print_brs (S i) rest
        end in
      match brs with
      | [] =>
        (* Match on an empty inductive (e.g. an [Empty]/[False] left
           over from erasure).  We still elaborate the discriminant for
           its effects, then evaluate to the placeholder [()] — these
           expressions are unreachable in well-typed programs. *)
        reflect ("(let _ : Obj := " ++ print_lterm discr ++ "; ())")
      | _ =>
        reflect ("(match (Peregrine.cast " ++ print_lterm discr ++ " : "
          ++ ind_n ++ ") with" ++ nl
          ++ concat_with nl (print_brs 0 brs) ++ nl ++ ")")
      end
    | LFix entries _ =>
      match entries with
      | [(name, body)] =>
        (* Singleton nested fix → term-mode [let rec].  The block's value
           is the (curried [Obj]-valued) function [name]; callers reach it
           through [Peregrine.apply].  Lean's [let rec] captures enclosing
           binders natively, so no closure parameters are threaded. *)
        reflect ("(let rec " ++ name ++ " : Obj :=" ++ nl
          ++ "     " ++ print_lterm body ++ nl
          ++ "   " ++ name ++ ")")
      | _ =>
        (* Mutual nested fix: term-mode [let rec] has no [and] clause, and
           no current program needs it.  Fail loudly at first touch rather
           than emitting a silent placeholder. *)
        reflect "(panic! ""peregrine: mutual nested fix unsupported"")"
      end
    | LPanic _ =>
      (* Stand-in Obj for computationally irrelevant terms (tBox
         replacements).  A well-typed program should never inspect such a
         value at runtime. *)
      reflect "()"
    end.

  (* Nullary constants become memoized [Thunk Obj]: a plain nullary def
     is evaluated during module initialization, on the process's small
     pre-[main] stack (deep recursion there is a hard SIGSEGV).  As a
     [Thunk] the body runs on first [.get] — inside [main], on the Lean
     runtime's big-stack thread — while preserving evaluate-once sharing. *)
  Definition print_lfun (name : string) (f : lfun) : string :=
    match f.(lfun_params) with
    | [] =>
      "unsafe def " ++ name ++ " : Thunk Obj := Thunk.mk (fun _ =>" ++ nl
        ++ "  " ++ print_lterm f.(lfun_body) ++ ")"
    | params =>
      "unsafe def " ++ name ++ " "
        ++ concat_with " " (List.map (fun id => "(" ++ id ++ " : Obj)") params)
        ++ " : Obj :=" ++ nl
        ++ "  " ++ print_lterm f.(lfun_body)
    end.

  Definition print_decl (kn : kername) (d : ldecl) : string :=
    match d with
    | LInductive mib => print_inductive mib
    | LDef f => print_lfun (pick_fun_name full_names default_module kn) f
    | LRecGroup fs =>
      "mutual" ++ nl
        ++ concat_with nl (List.map (fun '(kn', f) =>
             print_lfun (pick_fun_name full_names default_module kn') f) fs) ++ nl
        ++ "end"
    end.

End Printer.

Definition preamble (ns : string) : string :=
  "-- Generated by Peregrine" ++ nl
    ++ "import Peregrine.Runtime" ++ nl
    ++ "open Peregrine" ++ nl
    (* Closed programs bake in numeric literals as deep [S_] towers;
       elaborating them exceeds Lean's default recursion depth. *)
    ++ "set_option maxRecDepth 1000000" ++ nl
    ++ nl
    ++ "namespace " ++ ns ++ nl.

Definition postamble (ns : string) : string :=
  nl ++ "end " ++ ns ++ nl.

(* Knames of nullary [LDef]s — the constants emitted as [Thunk Obj]
   and therefore referenced via [.get]. *)
Definition thunk_knames (decls : list (kername * ldecl)) : list kername :=
  Utils.filter_map (fun (x : kername * ldecl) =>
    let '(kn, d) := x in
    match d with
    | LDef f => match f.(lfun_params) with [] => Some kn | _ => None end
    | _ => None
    end
  ) decls.

Definition print_program (full_names : bool) (default_module : string) (ns : string) (p : lprogram) : string :=
  let env := build_ind_env p.(ldecls) in
  let thunks := thunk_knames p.(ldecls) in
  preamble ns
    ++ concat_with (nl ++ nl)
         (List.map (fun '(kn, d) => print_decl full_names default_module env thunks kn d) p.(ldecls))
    ++ postamble ns.
