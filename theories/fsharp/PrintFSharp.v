From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import MRString.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require EAst.
From Peregrine Require Import FSharpIR.
From Peregrine Require Utils.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Strings.Byte.

Import ListNotations.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  FSharpIR → F# source pretty-printer                               *)
(*                                                                    *)
(*  Core invariant: every emitted expression has static type [obj],   *)
(*  and every function value boxed into an [obj] is exactly a unary   *)
(*  [FSharpFunc<obj,obj>] — [PG.apply] downcasts to [obj -> obj], and *)
(*  .NET casts are checked at runtime, so [box]ing an n≥2-ary def     *)
(*  directly would crash at the first apply.  Saturated calls to      *)
(*  known n-ary definitions are emitted as direct (uncurried) calls;  *)
(*  under-applied heads are wrapped in a chain of unary closures      *)
(*  ([curry_wrapper]).  Every binding body is printed on a single     *)
(*  line so the offside rule cannot re-associate anything, and every  *)
(*  composite expression is parenthesized.                            *)
(* ------------------------------------------------------------------ *)

Definition nl : string := String.String "010"%byte String.EmptyString.

Definition concat_with (sep : string) (xs : list string) : string :=
  String.concat sep xs.

(* Use just the last component of a kername.  All emitted definitions
   live inside a single F# module, so collisions only matter across
   modules that happen to share a local name — accepted v1 limitation,
   controlled by the full-names printing flag. *)
Definition local_name (kn : kername) : string := snd kn.

(* Inner-module qualifiers of a modpath: everything below the file root.
   [MPfile] contributes nothing (its dirpath is the compilation-unit name,
   already covered by [default_module]); [MPdot]/[MPbound] components are
   folded in order.  Rationale: names anchored only on [snd kn] collide as
   soon as a program uses same-named definitions from different modules
   (e.g. FMap [M.add] vs FSet [S.add] vs [Nat.add] in VeriStar), which
   previously emitted duplicate defs.  Top-level definitions keep their
   historical [<File>_<ident>] names. *)
Fixpoint mp_quals (mp : modpath) : list ident :=
  match mp with
  | MPfile _ => []
  | MPbound _ id _ => [id]
  | MPdot mp id => mp_quals mp ++ [id]
  end.

Definition qualify_mp (mp : modpath) (s : ident) : ident :=
  match mp_quals mp with
  | [] => s
  | qs => concat_with "_" qs ++ "_" ++ s
  end.

(* File root of a modpath (innermost dirpath component = file name),
   used as a last-resort disambiguator when [qualify_mp] alone still
   collides (same-named top-level defs in different files, e.g.
   [Corelib.Init.Nat.add] vs a program's own [add]). *)
Fixpoint mp_root_file (mp : modpath) : list ident :=
  match mp with
  | MPfile dp | MPbound dp _ _ => match dp with f :: _ => [f] | [] => [] end
  | MPdot mp _ => mp_root_file mp
  end.

Definition base_name (kn : kername) : string := qualify_mp (fst kn) (snd kn).

Definition disamb_name (kn : kername) : string :=
  concat_with "_" (mp_root_file (fst kn) ++ mp_quals (fst kn) ++ [snd kn]).

(* Flat full name: [default_module ++ "_" ++ <quals> ++ snd kn], where
   the file root is folded in only for names in [dups] (the base names
   that appear more than once in this program — computed by
   [print_program]).  [default_module] is the source file basename,
   supplied by the CLI driver.  We deliberately ignore the [MPfile] root
   otherwise: across frontends it ranges from empty (lean-to-lambdabox)
   to deep ([Peregrine.Tests.Demo] for rocq extractions), which would
   yield inconsistent emitted names across otherwise-identical programs.
   Tests expect [<File>_<ident>], so we anchor on the file name. *)
Definition full_name (dups : list string) (default_module : string) (kn : kername) : string :=
  let base := base_name kn in
  let base := if List.existsb (String.eqb base) dups then disamb_name kn else base in
  match default_module with
  | "" => base
  | _ => default_module ++ "_" ++ base
  end.

Definition pick_fun_name (dups : list string) (full : bool) (default_module : string) (kn : kername) : string :=
  if full then full_name dups default_module kn else local_name kn.

(* ----- Name casing ------------------------------------------------- *)

(* F# union cases must start with an uppercase letter.  ASCII-only
   capitalization is enough: identifiers reaching this printer have
   been sanitized upstream. *)
Definition byte_upper (b : byte) : byte :=
  match b with
  | x61 => x41
  | x62 => x42
  | x63 => x43
  | x64 => x44
  | x65 => x45
  | x66 => x46
  | x67 => x47
  | x68 => x48
  | x69 => x49
  | x6a => x4a
  | x6b => x4b
  | x6c => x4c
  | x6d => x4d
  | x6e => x4e
  | x6f => x4f
  | x70 => x50
  | x71 => x51
  | x72 => x52
  | x73 => x53
  | x74 => x54
  | x75 => x55
  | x76 => x56
  | x77 => x57
  | x78 => x58
  | x79 => x59
  | x7a => x5a
  | _ => b
  end.

Definition byte_is_lower (b : byte) : bool :=
  match b with
  | x61 | x62 | x63 | x64 | x65 | x66 | x67 | x68 | x69 | x6a | x6b | x6c
  | x6d | x6e | x6f | x70 | x71 | x72 | x73 | x74 | x75 | x76 | x77 | x78
  | x79 | x7a => true
  | _ => false
  end.

Definition byte_is_upper (b : byte) : bool :=
  match b with
  | x41 | x42 | x43 | x44 | x45 | x46 | x47 | x48 | x49 | x4a | x4b | x4c
  | x4d | x4e | x4f | x50 | x51 | x52 | x53 | x54 | x55 | x56 | x57 | x58
  | x59 | x5a => true
  | _ => false
  end.

(* Capitalize the first letter; names not starting with an ASCII letter
   get a "C" prefix instead (still a valid uppercase-led identifier). *)
Definition fs_cap (s : string) : string :=
  match s with
  | String.EmptyString => "C"
  | String.String b rest =>
    if byte_is_lower b then String.String (byte_upper b) rest
    else if byte_is_upper b then s
    else "C" ++ s
  end.

(* Suffix inductive type names with [_] so we never collide with F#
   keywords or built-in types (e.g. [bool], [option], [unit]).  Type
   names keep their source casing — F# accepts lowercase type names —
   but union cases must be capitalized, hence [fs_cap] on ctors. *)
Definition ind_name (s : ident) : string := s ++ "_".
Definition ctor_name (s : ident) : string := fs_cap s ++ "_".

(* [obj_tuple 3 = "obj * obj * obj"] — the payload type of an n-field
   union case. *)
Fixpoint obj_tuple (n : nat) : string :=
  match n with
  | O => ""
  | S O => "obj"
  | S k => "obj * " ++ obj_tuple k
  end.

(* Format a parameter list: ["n_0"; "m_1"] ↦ "(n_0: obj) (m_1: obj)". *)
Definition fs_params (ids : list ident) : string :=
  concat_with " " (List.map (fun id => "(" ++ id ++ ": obj)") ids).

(* ----- Inductive lookup environment ------------------------------- *)

Definition ind_env := list (kername * EAst.mutual_inductive_body).

Definition build_ind_env (decls : list (kername * fdecl)) : ind_env :=
  Utils.filter_map (fun (x : kername * fdecl) =>
    let '(kn, d) := x in
    match d with
    | FInductive mib => Some (kn, mib)
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

(* Inductive type names get the same inner-module qualification as
   definitions: e.g. FMap [M.t] and FSet [S.t] would otherwise both
   print as [t_]. *)
Definition lookup_ind_name (env : ind_env) (ind : inductive) : string :=
  match lookup_oib env ind with
  | Some oib =>
    ind_name (qualify_mp (fst ind.(inductive_mind)) (oib.(EAst.ind_name)))
  | None => "MissingInd"
  end.

(* ----- Inductive declaration printer (context-free) --------------- *)

Definition print_ctor (cb : EAst.constructor_body) : string :=
  let nargs := cb.(EAst.cstr_nargs) in
  "| " ++ ctor_name (cb.(EAst.cstr_name))
    ++ (match nargs with O => "" | _ => " of " ++ obj_tuple nargs end).

(* One union per one_inductive_body, on a single line.
   [<RequireQualifiedAccess>] keeps same-named cases of different
   unions apart (every use site is printed qualified anyway).  An
   inductive with no constructors is elided: F# forbids empty unions,
   and such a type can never be referenced by a well-formed program
   (its only use sites are empty matches, printed without a cast). *)
Definition print_one_inductive (mp : modpath) (oib : EAst.one_inductive_body) : string :=
  let nm := ind_name (qualify_mp mp (oib.(EAst.ind_name))) in
  match oib.(EAst.ind_ctors) with
  | [] =>
    "// empty inductive " ++ nm ++ " elided (F# forbids empty unions; never referenced)"
  | ctors =>
    "[<RequireQualifiedAccess>]" ++ nl
      ++ "type " ++ nm ++ " = " ++ concat_with " " (List.map print_ctor ctors)
  end.

(* Mutual inductives need no [and]-chaining: every field is [obj], so
   the printed unions never refer to each other. *)
Definition print_inductive (kn : kername) (mib : EAst.mutual_inductive_body) : string :=
  concat_with nl (List.map (print_one_inductive (fst kn)) mib.(EAst.ind_bodies)).

(* ----- Arity bookkeeping ------------------------------------------ *)

(* Arity of every top-level function — the printer needs it to decide
   between a direct (uncurried) call and a curried wrapper. *)
Definition fun_arities (decls : list (kername * fdecl)) : list (kername * nat) :=
  List.concat (List.map (fun (x : kername * fdecl) =>
    let '(kn, d) := x in
    match d with
    | FDef f => [(kn, List.length f.(ffun_params))]
    | FRecGroup fs => List.map (fun '(kn', f) => (kn', List.length f.(ffun_params))) fs
    | FInductive _ => []
    end) decls).

(* Locally bound function names (nested [let rec]s from [FFix]) and
   their arities.  Plain [obj]-typed locals are absent from the map. *)
Definition lookup_local (id : ident) (locals : list (ident * nat)) : option nat :=
  match List.find (fun '(id', _) => String.eqb id' id) locals with
  | Some (_, n) => Some n
  | None => None
  end.

(* Drop shadowed names when entering binders.  The compiler suffixes
   every local with its binding depth, so real shadowing cannot occur —
   this is robustness only. *)
Definition remove_locals (ids : list ident) (locals : list (ident * nat)) : list (ident * nat) :=
  List.filter (fun '(id, _) => negb (List.existsb (String.eqb id) ids)) locals.

(* Split a term into its leading lambdas and residual body. *)
Fixpoint peel_flams (t : fterm) : list ident * fterm :=
  match t with
  | FLam id b => let '(ids, body) := peel_flams b in (id :: ids, body)
  | _ => ([], t)
  end.

(* ----- Call-shape helpers ------------------------------------------ *)

(* Apply an [obj]-typed head to already-printed argument strings, one
   generic application at a time. *)
Definition wrap_applies (s : string) (args : list string) : string :=
  List.fold_left (fun acc a => "(PG.apply " ++ acc ++ " " ++ a ++ ")") args s.

(* Turn an n-ary definition into an [obj]: a 1-ary function is already
   an [FSharpFunc<obj,obj>], so it boxes directly; n≥2 needs a chain of
   unary closures.  The [box] between lambda levels is load-bearing —
   without it fsc fuses the nest into an [OptimizedClosures.FSharpFunc]
   whose downcast to [obj -> obj] fails at runtime.  The wrapper
   variables [c0..] cannot collide with program locals (those all carry
   a [_<depth>] suffix). *)
Definition curry_wrapper (name : string) (n : nat) : string :=
  match n with
  | O => name (* unreachable: arity-0 heads never reach the wrapper *)
  | S O => "(box " ++ name ++ ")"
  | _ =>
    let ids :=
      let fix aux (i max : nat) : list string :=
        match i with
        | O => []
        | S k => ("c" ++ string_of_nat (max - i)) :: aux k max
        end in
      aux n n in
    let call := "(" ++ name ++ " " ++ concat_with " " ids ++ ")" in
    let fix wrap (rest : list string) : string :=
      match rest with
      | [] => call
      | id :: rest' => "(box (fun (" ++ id ++ ": obj) -> " ++ wrap rest' ++ "))"
      end in
    wrap ids
  end.

(* Finish printing a spine whose head is a function of known [arity]
   with [pending] printed argument strings:
   - arity 0: the head is already a value (nullary rec-group member);
     apply generically.
   - saturated: direct call on the first [arity] arguments, generic
     applies for the rest.
   - under-applied: curried wrapper, with the available arguments still
     applied NOW via [PG.apply] (preserving call-by-value strictness). *)
Definition finish_call (name : string) (arity : nat) (pending : list string) : string :=
  match arity with
  | O => wrap_applies name pending
  | _ =>
    if Nat.leb arity (List.length pending) then
      wrap_applies
        ("(" ++ name ++ " " ++ concat_with " " (List.firstn arity pending) ++ ")")
        (List.skipn arity pending)
    else
      wrap_applies (curry_wrapper name arity) pending
  end.

(* ----- Term / declaration printer --------------------------------- *)

Section Printer.
  (* Invariant context, shared by every printer below.  [dups] is the set
     of base names that collide in this program (see [full_name]);
     [arities] maps every top-level function to its parameter count. *)
  Context (dups : list string) (full_names : bool) (default_module : string)
          (env : ind_env) (thunks : list kername) (arities : list (kername * nat)).

  (* Nullary top-level constants are emitted as [Lazy<obj>] (see
     [print_ffun]); references to them must force via [.Force()]. *)
  Definition is_thunk (kn : kername) : bool :=
    List.existsb (fun k => eq_kername k kn) thunks.

  Definition lookup_arity (kn : kername) : option nat :=
    match List.find (fun '(kn', _) => eq_kername kn' kn) arities with
    | Some (_, n) => Some n
    | None => None
    end.

  (* Accumulator ("spine") printer: [pending] carries the printed
     argument strings of the application spine enclosing [t], leftmost
     argument first.  Walking [FApp] nodes into the accumulator keeps
     the recursion structural while letting the spine's head see all
     its arguments at once and choose the call shape ([finish_call]).
     Every returned string is a complete [obj]-typed F# expression. *)
  Fixpoint print_fterm_k (locals : list (ident * nat)) (t : fterm) (pending : list string) {struct t} : string :=
    match t with
    | FApp f x =>
      print_fterm_k locals f (print_fterm_k locals x [] :: pending)
    | FVar id =>
      match lookup_local id locals with
      | Some n => finish_call id n pending
      | None => wrap_applies id pending
      end
    | FConst kn =>
      let nm := pick_fun_name dups full_names default_module kn in
      if is_thunk kn then wrap_applies ("(" ++ nm ++ ".Force())") pending
      else
        match lookup_arity kn with
        | Some n => finish_call nm n pending
        (* Unknown arity (axiom / missing decl): print the bare name and
           let the F# compiler reject it, matching the Lean backend. *)
        | None => wrap_applies nm pending
        end
    | FCtor ind idx args =>
      let cn := lookup_ctor_name env ind idx in
      let ind_n := lookup_ind_name env ind in
      let fix print_args (ts : list fterm) : list string :=
        match ts with
        | [] => []
        | a :: rest => print_fterm_k locals a [] :: print_args rest
        end in
      let head :=
        match args with
        | [] => "(box " ++ ind_n ++ "." ++ cn ++ ")"
        | _ =>
          "(box (" ++ ind_n ++ "." ++ cn ++ " ("
            ++ concat_with ", " (print_args args) ++ ")))"
        end in
      wrap_applies head pending
    | FProj p discr =>
      let ind := p.(proj_ind) in
      let arg := p.(proj_arg) in
      let cn := lookup_ctor_name env ind 0 in
      let ind_n := lookup_ind_name env ind in
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
      let pat :=
        match pat_args with
        | [] => ""
        | [p1] => " " ++ p1
        | _ => " (" ++ concat_with ", " pat_args ++ ")"
        end in
      wrap_applies
        ("(match (" ++ print_fterm_k locals discr [] ++ " :?> " ++ ind_n
          ++ ") with | " ++ ind_n ++ "." ++ cn ++ pat ++ " -> x)")
        pending
    | FLam id body =>
      wrap_applies
        ("(box (fun (" ++ id ++ ": obj) -> "
          ++ print_fterm_k (remove_locals [id] locals) body [] ++ "))")
        pending
    | FLet id b body =>
      wrap_applies
        ("(let " ++ id ++ " : obj = " ++ print_fterm_k locals b [] ++ " in "
          ++ print_fterm_k (remove_locals [id] locals) body [] ++ ")")
        pending
    | FCase discr ind brs =>
      let ind_n := lookup_ind_name env ind in
      let print_br (i : nat) (br : list ident * fterm) : string :=
        let '(ids, body) := br in
        let cn := lookup_ctor_name env ind i in
        let pat :=
          match ids with
          | [] => ""
          | [x1] => " " ++ x1
          | _ => " (" ++ concat_with ", " ids ++ ")"
          end in
        "| " ++ ind_n ++ "." ++ cn ++ pat ++ " -> "
          ++ print_fterm_k (remove_locals ids locals) body [] in
      let fix print_brs (i : nat) (bs : list (list ident * fterm)) : list string :=
        match bs with
        | [] => []
        | b :: rest => print_br i b :: print_brs (S i) rest
        end in
      match brs with
      | [] =>
        (* Match on an empty inductive (e.g. an [Empty]/[False] left
           over from erasure).  We still evaluate the discriminant for
           its effects, then produce the placeholder [box ()] — these
           expressions are unreachable in well-typed programs. *)
        wrap_applies
          ("(let _ = " ++ print_fterm_k locals discr [] ++ " in box ())")
          pending
      | _ =>
        wrap_applies
          ("(match (" ++ print_fterm_k locals discr [] ++ " :?> " ++ ind_n
            ++ ") with " ++ concat_with " " (print_brs 0 brs) ++ ")")
          pending
      end
    | FFix entries idx =>
      (* Nested fixpoint.  Only the singleton case has a legal one-line
         F# form ([let rec f (x: obj) … : obj = body in …]); a mutual
         group would need an [and] binding, which F#'s light syntax
         rejects on a single line, and multi-line blocks at a fixed
         column are offside errors once nested.  Mutual nested fixes
         are not produced by any current frontend (the Lean backend
         panics on them too), so we fail loudly rather than miscompile.
         The single entry's leading lambdas become real parameters; the
         fix name is then a known-arity head (direct call when the
         enclosing spine saturates it, curried wrapper otherwise). *)
      match entries with
      | [(nm, body)] =>
        let ps := fst (peel_flams body) in
        match ps with
        | [] =>
          (* A parameterless entry would need value recursion ([let rec
             x = … x …]), which .NET cannot express eagerly.  No
             frontend produces it; fail loudly at runtime. *)
          wrap_applies "(failwith ""peregrine: value-recursive fix"" : obj)" pending
        | _ =>
          let locals' := (nm, List.length ps) :: remove_locals (nm :: ps) locals in
          let fix print_after_lams (u : fterm) : string :=
            match u with
            | FLam _ b => print_after_lams b
            | _ => print_fterm_k locals' u []
            end in
          "(let rec " ++ nm ++ " " ++ fs_params ps ++ " : obj = "
            ++ print_after_lams body
            ++ " in " ++ finish_call nm (List.length ps) pending ++ ")"
        end
      | _ =>
        wrap_applies "(failwith ""peregrine: mutual nested fix unsupported"" : obj)" pending
      end
    | FPanic _ =>
      (* Stand-in [obj] for computationally irrelevant terms (tBox
         replacements).  Must be a benign value — erased argument slots
         are materialized eagerly under call-by-value, so a [failwith]
         here would abort correct programs. *)
      wrap_applies "(box ())" pending
    end.

  (* Nullary standalone constants become memoized [Lazy<obj>]: a plain
     nullary [let] runs inside the module's static initializer, where
     deep recursion overflows the small startup stack and evaluation is
     load-order dependent.  As a [Lazy<obj>] the body runs on first
     [.Force()] — inside [main] — while preserving evaluate-once
     sharing.  [leader] selects [let rec] vs [and] within a rec group;
     a standalone [FDef] is always a leader.  Leaders use [let rec]
     even when non-recursive: self-references are [FConst]s, and F#
     emits no warning for an unused [rec]. *)
  Definition print_ffun (leader : bool) (name : string) (f : ffun) : string :=
    match f.(ffun_params) with
    | [] =>
      if leader then
        "let " ++ name ++ " : Lazy<obj> = lazy ("
          ++ print_fterm_k [] f.(ffun_body) [] ++ ")"
      else
        (* Nullary rec-group member (theoretical): a value binding in a
           [let rec] chain — checked-at-runtime initialization, covered
           by [#nowarn "40"]. *)
        "and " ++ name ++ " : obj = " ++ print_fterm_k [] f.(ffun_body) []
    | params =>
      (if leader then "let rec " else "and ") ++ name ++ " " ++ fs_params params
        ++ " : obj = " ++ print_fterm_k [] f.(ffun_body) []
    end.

  Definition print_decl (kn : kername) (d : fdecl) : string :=
    match d with
    | FInductive mib => print_inductive kn mib
    | FDef f => print_ffun true (pick_fun_name dups full_names default_module kn) f
    | FRecGroup fs =>
      (* Module-level [and] continues the leader's [let rec] at column 0. *)
      match fs with
      | [] => ""
      | (kn1, f1) :: rest =>
        concat_with nl
          (print_ffun true (pick_fun_name dups full_names default_module kn1) f1
            :: List.map (fun '(kn', f) =>
                 print_ffun false (pick_fun_name dups full_names default_module kn') f) rest)
      end
    end.

End Printer.

(* Warnings silenced: 25/26 (incomplete/redundant matches — single-ctor
   projections), 40 (checked value recursion), 49 (uppercase pattern
   variables), 58 (indentation), 64 (construct makes code less generic). *)
Definition preamble (ns : string) : string :=
  "module " ++ ns ++ nl
    ++ "// Generated by Peregrine (F# backend). Self-contained." ++ nl
    ++ "// Build in Release (--tailcalls+): Debug/fsi disable tail calls and may overflow on deep recursion." ++ nl
    ++ "#nowarn ""25""" ++ nl
    ++ "#nowarn ""26""" ++ nl
    ++ "#nowarn ""40""" ++ nl
    ++ "#nowarn ""49""" ++ nl
    ++ "#nowarn ""58""" ++ nl
    ++ "#nowarn ""64""" ++ nl
    ++ "module PG =" ++ nl
    ++ "  let inline apply (f: obj) (x: obj) : obj = (f :?> (obj -> obj)) x" ++ nl
    ++ nl.

(* Knames of nullary standalone [FDef]s — the constants emitted as
   [Lazy<obj>] and therefore referenced via [.Force()]. *)
Definition thunk_knames (decls : list (kername * fdecl)) : list kername :=
  Utils.filter_map (fun (x : kername * fdecl) =>
    let '(kn, d) := x in
    match d with
    | FDef f => match f.(ffun_params) with [] => Some kn | _ => None end
    | _ => None
    end
  ) decls.

(* Kernames of every printed definition (mutual-group members included). *)
Definition printed_knames (decls : list (kername * fdecl)) : list kername :=
  List.concat (List.map (fun (x : kername * fdecl) =>
    let '(kn, d) := x in
    match d with
    | FRecGroup fs => List.map fst fs
    | FInductive _ => []
    | _ => [kn]
    end) decls).

(* Base names occurring more than once — these get the file-root
   disambiguator in [full_name]. *)
Definition dup_base_names (decls : list (kername * fdecl)) : list string :=
  let names := List.map base_name (printed_knames decls) in
  List.filter (fun n =>
    Nat.ltb 1 (List.length (List.filter (String.eqb n) names))) names.

Definition print_program (full_names : bool) (default_module : string) (ns : string) (p : fprogram) : string :=
  let env := build_ind_env p.(fdecls) in
  let thunks := thunk_knames p.(fdecls) in
  let arities := fun_arities p.(fdecls) in
  let dups := dup_base_names p.(fdecls) in
  preamble ns
    ++ concat_with (nl ++ nl)
         (List.map (fun '(kn, d) =>
            print_decl dups full_names default_module env thunks arities kn d) p.(fdecls))
    ++ nl.
