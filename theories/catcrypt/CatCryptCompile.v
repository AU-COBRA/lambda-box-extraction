From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import MRString.
From MetaRocq.Utils Require Import ResultMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require Import EPrimitive.
From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require EAstUtils.
From Peregrine Require Import Config.
From Peregrine Require Import Utils.
From Peregrine Require Import CatCryptIR.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import PrimInt63.
From Stdlib Require Import Uint63.

Import ListNotations.
Import MonadNotation.

Local Open Scope bs_scope.

(* ------------------------------------------------------------------ *)
(*  EAst (λ□) → CatCryptIR                                            *)
(*                                                                    *)
(*  Only the straight-line arithmetic fragment is accepted: leading    *)
(*  lambdas become SSA inputs, [let] aliases an already-computed       *)
(*  level, and every application head must be a remapped PrimInt63     *)
(*  primitive.  Everything else is a hard error — CatCrypt's           *)
(*  [NamedSSA] has no control flow, no closures and no heap.          *)
(* ------------------------------------------------------------------ *)

(* ----- Primitive vocabulary --------------------------------------- *)

Variant cc_prim :=
| CPBin (b : cc_binop) (masks : bool)
| CPMulHi
| CPShl
| CPShr.

Definition cc_supported_prims : string :=
  "add, sub, mul, land, lor, lxor, mulhi, lsl, lsr".

Definition interp_prim (s : string) : option cc_prim :=
  if String.eqb s "add"   then Some (CPBin CCAdd true)
  else if String.eqb s "sub"   then Some (CPBin CCSub true)
  else if String.eqb s "mul"   then Some (CPBin CCMul true)
  else if String.eqb s "land"  then Some (CPBin CCAnd false)
  else if String.eqb s "lor"   then Some (CPBin CCOr false)
  else if String.eqb s "lxor"  then Some (CPBin CCXor false)
  else if String.eqb s "mulhi" then Some CPMulHi
  else if String.eqb s "lsl"   then Some CPShl
  else if String.eqb s "lsr"   then Some CPShr
  else None.

Definition primint63_mp : modpath :=
  MPfile ["PrimInt63"; "Int63"; "Cyclic"; "Numbers"; "Corelib"].

Definition mk_builtin_remap (s : string) : kername * remapped_constant :=
  ((primint63_mp, s),
   {| re_const_ext   := None;
      re_const_arity := 2;
      re_const_gc    := false;
      re_const_inl   := false;
      re_const_s     := s |}).

(* [div], [mod], [asr], the comparisons and the carry/euclid operations
   are deliberately absent: CatCrypt's [SupportedOp] cannot express
   them, so they must surface as "not a remapped primitive". *)
Definition builtin_remaps : constant_remappings :=
  List.map mk_builtin_remap
    ["add"; "sub"; "mul"; "land"; "lor"; "lxor"; "lsl"; "lsr"].

Definition lookup_remap (rs : constant_remappings) (kn : kername)
    : option remapped_constant :=
  match List.find (fun '(kn', _) => eq_kername kn kn') rs with
  | Some (_, r) => Some r
  | None => None
  end.

(* ----- Compiler state --------------------------------------------- *)

Record cstate := mkCState {
  st_rev_bindings : list cc_binding;
  st_next_level   : nat;
  st_mask_level   : option nat;
}.

Definition cc_emit (st : cstate) (o : cc_op) (args : list nat) : nat * cstate :=
  (st.(st_next_level),
   {| st_rev_bindings := {| ccb_op := o; ccb_args := args |} :: st.(st_rev_bindings);
      st_next_level   := S st.(st_next_level);
      st_mask_level   := st.(st_mask_level) |}).

(* At most one [regConst (2^63-1)] binding per program. *)
Definition get_mask (st : cstate) : nat * cstate :=
  match st.(st_mask_level) with
  | Some l => (l, st)
  | None =>
    let '(l, st') := cc_emit st (CCConst cc_mask63) [] in
    (l, {| st_rev_bindings := st'.(st_rev_bindings);
           st_next_level   := st'.(st_next_level);
           st_mask_level   := Some l |})
  end.

Definition apply_mask (mask63 masks : bool) (st : cstate) (l : nat) : nat * cstate :=
  if andb mask63 masks then
    let '(m, st1) := get_mask st in
    cc_emit st1 (CCArith CCAnd) [l; m]
  else (l, st).

(* ----- Term helpers ------------------------------------------------ *)

Fixpoint peel_lambdas (t : EAst.term) : list name * EAst.term :=
  match t with
  | EAst.tLambda na body =>
    let '(nas, body') := peel_lambdas body in
    (na :: nas, body')
  | _ => ([], t)
  end.

(* Bounds the traversal: [compile_expr] only recurses through [tApp]
   and [tLetIn] subterms. *)
Fixpoint term_size (t : EAst.term) : nat :=
  match t with
  | EAst.tApp u v => S (term_size u + term_size v)
  | EAst.tLetIn _ b u => S (term_size b + term_size u)
  | _ => 1
  end.

Definition prim_int_value (p : prim_val EAst.term) : option N :=
  match prim_val_model p with
  | primIntModel i => Some (Z.to_N (Uint63.to_Z i))
  | _ => None
  end.

Definition shift_amount (t : EAst.term) : option nat :=
  match t with
  | EAst.tPrim p =>
    match prim_int_value p with
    | Some n => if N.leb n 63 then Some (N.to_nat n) else None
    | None => None
    end
  | _ => None
  end.

(* ----- Expression compiler ----------------------------------------- *)

Section Compile.
  Context (remaps : constant_remappings) (mask63 : bool).

  Fixpoint compile_expr (fuel : nat) (ctx : list nat) (st : cstate) (t : EAst.term)
      {struct fuel} : result' (nat * cstate) :=
    match fuel with
    | O => Err "internal error: fuel exhausted while compiling"
    | S fuel' =>
      let compile_bin (o : cc_op) (masks : bool) (a1 a2 : EAst.term)
          : result' (nat * cstate) :=
        '(l1, st1) <- compile_expr fuel' ctx st a1 ;;
        '(l2, st2) <- compile_expr fuel' ctx st1 a2 ;;
        let '(l3, st3) := cc_emit st2 o [l1; l2] in
        Ok (apply_mask mask63 masks st3 l3) in
      let compile_shift (mk : nat -> cc_op) (masks : bool) (a1 a2 : EAst.term)
          : result' (nat * cstate) :=
        match shift_amount a2 with
        | None =>
          Err "shift amount must be a literal 0..63; variable shifts unsupported by CatCrypt ARM/RISC-V path"
        | Some k =>
          '(l1, st1) <- compile_expr fuel' ctx st a1 ;;
          let '(l2, st2) := cc_emit st1 (mk k) [l1] in
          Ok (apply_mask mask63 masks st2 l2)
        end in
      let compile_prim (kn : kername) (r : remapped_constant) (args : list EAst.term)
          : result' (nat * cstate) :=
        match interp_prim r.(re_const_s) with
        | None =>
          Err ("the remapping of " ++ string_of_kername kn ++ " targets the unknown CatCrypt primitive '"
               ++ r.(re_const_s) ++ "'; supported primitives are " ++ cc_supported_prims)
        | Some p =>
          match args with
          | [a1; a2] =>
            match p with
            | CPBin b masks => compile_bin (CCArith b) masks a1 a2
            | CPMulHi =>
              if mask63 then
                Err "mulhi is unsupported under 63-bit masking: the 63- and 64-bit high words differ; recompile with mask63 disabled"
              else compile_bin CCMulHi false a1 a2
            | CPShl => compile_shift CCShlImm true a1 a2
            | CPShr => compile_shift CCShrImm false a1 a2
            end
          | _ =>
            Err ("the CatCrypt primitive '" ++ r.(re_const_s) ++ "' takes 2 arguments but the remapping of "
                 ++ string_of_kername kn ++ " declares arity " ++ string_of_nat r.(re_const_arity))
          end
        end in
      let compile_app (hd : EAst.term) (args : list EAst.term)
          : result' (nat * cstate) :=
        match hd with
        | EAst.tConst kn =>
          match lookup_remap remaps kn with
          | None =>
            Err ("constant " ++ string_of_kername kn
                 ++ " is not a remapped primitive; inline it or add a remapping")
          | Some r =>
            if negb (Nat.eqb (List.length args) r.(re_const_arity)) then
              Err ("constant " ++ string_of_kername kn ++ " is applied to "
                   ++ string_of_nat (List.length args) ++ " argument(s) but its remapping declares arity "
                   ++ string_of_nat r.(re_const_arity)
                   ++ "; partial and over-application are unsupported")
            else compile_prim kn r args
          end
        | _ => Err "application head is not a remapped primitive (higher-order application)"
        end in
      match t with
      | EAst.tRel i =>
        match nth_error ctx i with
        | Some l => Ok (l, st)
        | None => Err ("free de Bruijn index " ++ string_of_nat i)
        end
      | EAst.tLetIn _ b u =>
        '(l, st1) <- compile_expr fuel' ctx st b ;;
        compile_expr fuel' (l :: ctx) st1 u
      | EAst.tPrim p =>
        match prim_int_value p with
        | Some n => Ok (cc_emit st (CCConst n) [])
        | None => Err "float/string/array literal unsupported"
        end
      | EAst.tConst _ => compile_app t []
      | EAst.tApp _ _ =>
        let '(hd, args) := EAstUtils.decompose_app t in
        compile_app hd args
      | EAst.tLambda _ _ => Err "lambda in non-prefix position (closure) unsupported"
      | EAst.tCase _ _ _ => Err "match/inductives unsupported (straight-line fragment)"
      | EAst.tConstruct _ _ _ => Err "match/inductives unsupported (straight-line fragment)"
      | EAst.tProj _ _ => Err "match/inductives unsupported (straight-line fragment)"
      | EAst.tFix _ _ => Err "recursion unsupported"
      | EAst.tCoFix _ _ => Err "recursion unsupported"
      | EAst.tBox => Err "erased proof/type in relevant position"
      | EAst.tVar _ => Err "open term"
      | EAst.tEvar _ _ => Err "open term"
      | EAst.tLazy _ => Err "lazy/force unsupported"
      | EAst.tForce _ => Err "lazy/force unsupported"
      end
    end.

End Compile.

(* ----- Entry point -------------------------------------------------- *)

Definition ident_byte_ok (first : bool) (b : Byte.byte) : bool :=
  let n := Byte.to_nat b in
  orb (orb (orb (andb (Nat.leb 97 n) (Nat.leb n 122))
                (andb (Nat.leb 65 n) (Nat.leb n 90)))
           (Nat.eqb n 95))
      (andb (negb first) (andb (Nat.leb 48 n) (Nat.leb n 57))).

Fixpoint sanitize_aux (first : bool) (s : string) : string :=
  match s with
  | String.EmptyString => String.EmptyString
  | String.String b rest =>
    if ident_byte_ok first b
    then String.String b (sanitize_aux false rest)
    else String.String "095"%byte (sanitize_aux false rest)
  end.

Definition sanitize_ident (s : string) : string :=
  match s with
  | String.EmptyString => "f"
  | _ => sanitize_aux true s
  end.

Definition lookup_const (Sigma : EAst.global_declarations) (kn : kername)
    : option EAst.constant_body :=
  match List.find (fun '(kn', _) => eq_kername kn kn') Sigma with
  | Some (_, EAst.ConstantDecl cb) => Some cb
  | _ => None
  end.

(* Returns the body to compile, a provenance string for the header, and
   the def name derived from the source constant. *)
Definition resolve_entry (Sigma : EAst.global_declarations) (main : EAst.term)
    : result' (EAst.term * string * string) :=
  match main with
  | EAst.tConst kn =>
    match lookup_const Sigma kn with
    | None =>
      Err ("entry constant " ++ string_of_kername kn
           ++ " was not found in the global environment")
    | Some cb =>
      match cb.(EAst.cst_body) with
      | Some b => Ok (b, string_of_kername kn, sanitize_ident (snd kn))
      | None =>
        Err ("entry constant " ++ string_of_kername kn ++ " has no body (axiom?)")
      end
    end
  | _ => Ok (main, "(anonymous term)", "f")
  end.

Definition compile_program (remaps : constant_remappings) (mask63 : bool)
                           (name : string) (p : EAst.program) : result' cc_prog :=
  '(entry, prov, derived) <- resolve_entry (fst p) (snd p) ;;
  let '(params, body) := peel_lambdas entry in
  let n := List.length params in
  (* [tRel 0] is the innermost binder, i.e. the last input. *)
  let ctx := List.rev (List.seq 0 n) in
  let st0 := {| st_rev_bindings := []; st_next_level := n; st_mask_level := None |} in
  '(l, st) <- compile_expr remaps mask63 (term_size body) ctx st0 body ;;
  Ok {| ccp_name     := match name with
                        | String.EmptyString => derived
                        | _ => sanitize_ident name
                        end;
        ccp_comment  := prov;
        ccp_ninputs  := n;
        ccp_bindings := List.rev st.(st_rev_bindings);
        ccp_ret      := l |}.
