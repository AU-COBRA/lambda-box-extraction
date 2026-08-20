From MetaRocq.Erasure Require EAst.
From MetaRocq.Erasure Require ExAst.
From MetaRocq.Erasure Require EProgram.
From MetaRocq.ErasurePlugin Require Import ETransform.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Common Require Kernames.
From Malfunction Require Serialize.
From Peregrine Require Import Config.
From Peregrine Require Import RustBackend.
From Peregrine Require Import ElmBackend.
From Peregrine Require Import OCamlBackend.
From Peregrine Require Import CakeMLBackend.
From Peregrine Require Import CatCryptBackend.
From Peregrine Require Import CBackend.
From Peregrine Require Import WasmBackend.
From Peregrine Require Import EvalBackend.
From Peregrine Require Import ASTBackend.

Local Open Scope bs_scope.


Section ErasureConfig.

  Definition mk_cstr_reorders (c : config) := c.(cstr_reorders_opts).

  Definition mk_ind_remaps (c : config) : EProgram.extract_inductives :=
    Utils.filter_map (fun r =>
      match r with
      | KnIndRemap kn r => Some (kn, r)
      | _ => None
      end
    ) c.(ind_remappings_opts).

  Definition mk_opts (c : config) (typed : bool) : erasure_configuration := {|
      enable_unsafe := {|
        Erasure.cofix_to_lazy := c.(erasure_opts).(cofix_to_laxy);
        Erasure.inlining := true;
        Erasure.inductives_extraction := true;
        Erasure.unboxing := c.(erasure_opts).(unboxing);
        Erasure.betared := c.(erasure_opts).(betared);
      |};
      dearging_config := {|
        overridden_masks := fun _ => None;
        do_trim_const_masks := c.(erasure_opts).(dearg_consts);
        do_trim_ctor_masks := c.(erasure_opts).(dearg_ctors);
      |};
      enable_typed_erasure := typed;
      inlined_constants := MetaRocq.Erasure.Typed.Utils.kername_set_of_list c.(inlinings_opts);
      extracted_inductives := mk_ind_remaps c;
    |}.

End ErasureConfig.



Section BackendConfigOptional.
  Definition get_optional {A A' B : Type} (r : A) (r' : A') (p : A -> option B) (p' : A' -> B) : B :=
    match p r with
    | Some x => x
    | None => p' r'
    end.


  (* Rust *)
  Record rust_config' := {
    rust_preamble_top'       : option string;
    rust_preamble_program'   : option string;
    rust_term_box_symbol'    : option string;
    rust_type_box_symbol'    : option string;
    rust_any_type_symbol'    : option string;
    rust_print_full_names'   : option bool;
    rust_default_attributes' : option string;
  }.
  Definition empty_rust_config' : rust_config' := {|
    rust_preamble_top'       := None;
    rust_preamble_program'   := None;
    rust_term_box_symbol'    := None;
    rust_type_box_symbol'    := None;
    rust_any_type_symbol'    := None;
    rust_print_full_names'   := None;
    rust_default_attributes' := None;
  |}.

  Definition mk_rust_config (o : rust_config') : rust_config := {|
    rust_preamble_top       := get_optional o default_rust_config rust_preamble_top' rust_preamble_top;
    rust_preamble_program   := get_optional o default_rust_config rust_preamble_program' rust_preamble_program;
    rust_term_box_symbol    := get_optional o default_rust_config rust_term_box_symbol' rust_term_box_symbol;
    rust_type_box_symbol    := get_optional o default_rust_config rust_type_box_symbol' rust_type_box_symbol;
    rust_any_type_symbol    := get_optional o default_rust_config rust_any_type_symbol' rust_any_type_symbol;
    rust_print_full_names   := get_optional o default_rust_config rust_print_full_names' rust_print_full_names;
    rust_default_attributes := get_optional o default_rust_config rust_default_attributes' rust_default_attributes;
  |}.


  (* Elm *)
  Record elm_config' := {
    elm_preamble'         : option string;
    elm_module_name'      : option string;
    elm_term_box_symbol'  : option string;
    elm_type_box_symbol'  : option string;
    elm_any_type_symbol'  : option string;
    elm_false_elim_def'   : option string;
    elm_print_full_names' : option bool;
  }.
  Definition empty_elm_config' : elm_config' := {|
    elm_preamble'         := None;
    elm_module_name'      := None;
    elm_term_box_symbol'  := None;
    elm_type_box_symbol'  := None;
    elm_any_type_symbol'  := None;
    elm_false_elim_def'   := None;
    elm_print_full_names' := None;
  |}.

  Definition mk_elm_config (o : elm_config') : elm_config := {|
    elm_preamble         := get_optional o default_elm_config elm_preamble' elm_preamble;
    elm_module_name      :=
      match o.(elm_module_name') with
      | None => default_elm_config.(elm_module_name)
      | Some s => Some s
      end;
    elm_term_box_symbol  := get_optional o default_elm_config elm_term_box_symbol' elm_term_box_symbol;
    elm_type_box_symbol  := get_optional o default_elm_config elm_type_box_symbol' elm_type_box_symbol;
    elm_any_type_symbol  := get_optional o default_elm_config elm_any_type_symbol' elm_any_type_symbol;
    elm_false_elim_def   := get_optional o default_elm_config elm_false_elim_def' elm_false_elim_def;
    elm_print_full_names := get_optional o default_elm_config elm_print_full_names' elm_print_full_names;
  |}.

  (* C and Wasm *)
  Record certirocq_config' := {
    direct'    : option bool;
    c_args'    : option nat;
    o_level'   : option nat;
    anf_conf'  : option nat;
    prefix'    : option string;
    body_name' : option string;
  }.
  Definition empty_certirocq_config' : certirocq_config' := {|
    direct'    := None;
    c_args'    := None;
    o_level'   := None;
    anf_conf'  := None;
    prefix'    := None;
    body_name' := None;
  |}.

  Definition mk_certirocq_config default_certirocq_config (o : certirocq_config') : certirocq_config := {|
    direct    := get_optional o default_certirocq_config direct' direct;
    c_args    := get_optional o default_certirocq_config c_args' c_args;
    o_level   := get_optional o default_certirocq_config o_level' o_level;
    anf_conf  := get_optional o default_certirocq_config anf_conf' anf_conf;
    prefix    := get_optional o default_certirocq_config prefix' prefix;
    body_name := get_optional o default_certirocq_config body_name' body_name;
  |}.

  Definition c_config' : Type := certirocq_config'.

  Definition wasm_config' : Type := certirocq_config'.

  (* OCaml *)
  Record ocaml_config' := {
    program_type' : option Malfunction.Serialize.program_type;
  }.
  Definition empty_ocaml_config' : ocaml_config' := {|
    program_type' := None;
  |}.

  Definition mk_ocaml_config (o : ocaml_config') : ocaml_config := {|
    program_type := get_optional o default_ocaml_config program_type' program_type;
  |}.

  (* CatCrypt *)
  Record catcrypt_config' := {
    catcrypt_namespace' : option string;
    catcrypt_def_name'  : option string;
    catcrypt_mask63'    : option bool;
    catcrypt_scaffold'  : option bool;
  }.
  Definition empty_catcrypt_config' : catcrypt_config' := {|
    catcrypt_namespace' := None;
    catcrypt_def_name'  := None;
    catcrypt_mask63'    := None;
    catcrypt_scaffold'  := None;
  |}.

  Definition mk_catcrypt_config (o : catcrypt_config') : catcrypt_config := {|
    catcrypt_namespace := get_optional o default_catcrypt_config catcrypt_namespace' catcrypt_namespace;
    catcrypt_def_name  := get_optional o default_catcrypt_config catcrypt_def_name' catcrypt_def_name;
    catcrypt_mask63    := get_optional o default_catcrypt_config catcrypt_mask63' catcrypt_mask63;
    catcrypt_scaffold  := get_optional o default_catcrypt_config catcrypt_scaffold' catcrypt_scaffold;
  |}.

  Definition cakeml_config' : Type := unit.
  Definition empty_cakeml_config' : cakeml_config' := tt.

  Definition mk_cakeml_config (o : cakeml_config') : cakeml_config := tt.

  Record eval_config' := {
    copts'    : option certirocq_config';
    fuel'     : nat;
    eval_anf' : bool;
  }.
  Definition empty_eval_config' : eval_config' := {|
    copts'    := None;
    fuel'     := (Nat.pow 2 14);
    eval_anf' := true;
  |}.

  Definition mk_eval_config (o : eval_config') : eval_config := {|
    copts    := get_optional o default_eval_config
      (fun c => option_map (mk_certirocq_config default_eval_config.(copts)) (copts' c)) copts;
    fuel     := o.(fuel');
    eval_anf := o.(eval_anf');
  |}.

  Variant ASTType' :=
  | LambdaBox'
  | LambdaBoxTyped'
  | LambdaBoxMut'   : option certirocq_config' -> ASTType'
  | LambdaBoxLocal' : option certirocq_config' -> ASTType'
  | LambdaANF'      : option certirocq_config' -> ASTType'
  | LambdaANFC'     : option certirocq_config' -> ASTType'.

  Record ast_config' := {
    ast_type' : ASTType';
  }.
  Definition empty_ast_config' : ast_config' := {|
    ast_type' := LambdaBox';
  |}.

  Definition mk_ast_config (o : ast_config') : ast_config :=
    let mk c := match c with | Some c => mk_certirocq_config default_ast_c_config c | None => default_ast_c_config end in
    {| ast_type :=
        match o.(ast_type') with
        | LambdaBox' => LambdaBox
        | LambdaBoxTyped' => LambdaBoxTyped
        | LambdaBoxMut' c => LambdaBoxMut (mk c)
        | LambdaBoxLocal' c => LambdaBoxLocal (mk c)
        | LambdaANF' c => LambdaANF (mk c)
        | LambdaANFC' c => LambdaANFC (mk c)
        end
    |}.

  Inductive backend_config' :=
  | Rust'   : rust_config' -> backend_config'
  | Elm'    : elm_config' -> backend_config'
  | C'      : c_config' -> backend_config'
  | Wasm'   : wasm_config' -> backend_config'
  | OCaml'  : ocaml_config' -> backend_config'
  | CakeML' : cakeml_config' -> backend_config'
  | CatCrypt' : catcrypt_config' -> backend_config'
  | Eval'   : eval_config' -> backend_config'
  | AST'    : ast_config' -> backend_config'.
  Definition mk_backend_config (o : backend_config') : backend_config :=
    match o with
    | Rust' o   => Rust (mk_rust_config o)
    | Elm' o    => Elm (mk_elm_config o)
    | C' o      => C (mk_certirocq_config default_c_config o)
    | Wasm' o   => Wasm (mk_certirocq_config default_wasm_config o)
    | OCaml' o  => OCaml (mk_ocaml_config o)
    | CakeML' o => CakeML (mk_cakeml_config o)
    | CatCrypt' o => CatCrypt (mk_catcrypt_config o)
    | Eval' o   => Eval (mk_eval_config o)
    | AST' o    => AST (mk_ast_config o)
    end.

End BackendConfigOptional.



Section GeneralConfigOptional.

  Record erasure_phases' := {
    implement_box'  : option bool;
    implement_lazy' : option bool;
    cofix_to_laxy'  : option bool;
    betared'        : option bool;
    unboxing'       : option bool;
    dearg_ctors'    : option bool;
    dearg_consts'   : option bool;
  }.
  Definition empty_erasure_phases' : erasure_phases' := {|
    implement_box'  := None;
    implement_lazy' := None;
    cofix_to_laxy'  := None;
    betared'        := None;
    unboxing'       := None;
    dearg_ctors'    := None;
    dearg_consts'   := None;
  |}.

  Definition get_default_phase_opt' (o : erasure_phases_config) (p : erasure_phases_config -> phases_config) : bool :=
    match (p o) with
    | Required => true
    | Compatible default => default
    | Incompatible => false
    end.

  Definition get_default_phases_opt (o : erasure_phases_config) := {|
    implement_box  := get_default_phase_opt' o implement_box_c;
    implement_lazy := get_default_phase_opt' o implement_lazy_c;
    cofix_to_laxy  := get_default_phase_opt' o cofix_to_laxy_c;
    betared        := get_default_phase_opt' o betared_c;
    unboxing       := get_default_phase_opt' o unboxing_c;
    dearg_ctors    := get_default_phase_opt' o dearg_ctors_c;
    dearg_consts   := get_default_phase_opt' o dearg_consts_c;
  |}.

  Definition enforce_phase' (b' : option bool) (b : bool) (o : phases_config) : bool :=
    match o with
    | Required => true
    | Incompatible => false
    | _ =>
      match b' with
      | Some x => x
      | None => b
      end
    end.

  Definition enforce_phases (o : erasure_phases') (d : erasure_phases) (o' : erasure_phases_config) : erasure_phases := {|
    implement_box  := enforce_phase' o.(implement_box')  d.(implement_box)  o'.(implement_box_c);
    implement_lazy := enforce_phase' o.(implement_lazy') d.(implement_lazy) o'.(implement_lazy_c);
    cofix_to_laxy  := enforce_phase' o.(cofix_to_laxy')  d.(cofix_to_laxy)  o'.(cofix_to_laxy_c);
    betared        := enforce_phase' o.(betared')        d.(betared)        o'.(betared_c);
    unboxing       := enforce_phase' o.(unboxing')       d.(unboxing)       o'.(unboxing_c);
    dearg_ctors    := enforce_phase' o.(dearg_ctors')    d.(dearg_ctors)    o'.(dearg_ctors_c);
    dearg_consts   := enforce_phase' o.(dearg_consts')   d.(dearg_consts)   o'.(dearg_consts_c);
  |}.

  Definition mk_erasure_phases (b : backend_config') (o : option erasure_phases') : erasure_phases :=
    let def_opt :=
      match b with
      | Rust' _   => get_default_phases_opt rust_phases
      | Elm' _    => get_default_phases_opt elm_phases
      | C' _      => get_default_phases_opt c_phases
      | Wasm' _   => get_default_phases_opt wasm_phases
      | OCaml' _  => get_default_phases_opt ocaml_phases
      | CakeML' _ => get_default_phases_opt cakeml_phases
      | CatCrypt' _ => get_default_phases_opt catcrypt_phases
      | Eval' _   => get_default_phases_opt eval_phases
      | AST' _   => get_default_phases_opt ast_phases
      end in
    match o with
    | Some o =>
      match b with
      | Rust' _   => enforce_phases o def_opt rust_phases
      | Elm' _    => enforce_phases o def_opt elm_phases
      | C' _      => enforce_phases o def_opt c_phases
      | Wasm' _   => enforce_phases o def_opt wasm_phases
      | OCaml' _  => enforce_phases o def_opt ocaml_phases
      | CakeML' _ => enforce_phases o def_opt cakeml_phases
      | CatCrypt' _ => enforce_phases o def_opt catcrypt_phases
      | Eval' _   => enforce_phases o def_opt eval_phases
      | AST' _   => enforce_phases o def_opt ast_phases
      end
    | None => def_opt
    end.

  Definition mk_erasure_config (b : backend_config') (o : option erasure_phases') : erasure_phases :=
    mk_erasure_phases b o.

  Record config' := {
    backend_opts'           : backend_config';
    erasure_opts'           : option erasure_phases';
    inlinings_opts'         : inlinings;
    const_remappings_opts'  : constant_remappings;
    ind_remappings_opts'    : inductive_remappings;
    cstr_reorders_opts'     : EProgram.inductives_mapping;
    custom_attributes_opts' : custom_attributes;
  }.
  Definition empty_config' (b : backend_config') : config' := {|
    backend_opts'           := b;
    erasure_opts'           := None;
    inlinings_opts'         := nil;
    const_remappings_opts'  := nil;
    ind_remappings_opts'    := nil;
    cstr_reorders_opts'     := nil;
    custom_attributes_opts' := nil;
  |}.

  Definition mk_config (o : config') : config := {|
    backend_opts           := mk_backend_config o.(backend_opts');
    erasure_opts           := mk_erasure_config o.(backend_opts') o.(erasure_opts');
    inlinings_opts         := o.(inlinings_opts');
    const_remappings_opts  := o.(const_remappings_opts');
    ind_remappings_opts    := o.(ind_remappings_opts');
    cstr_reorders_opts     := o.(cstr_reorders_opts');
    custom_attributes_opts := o.(custom_attributes_opts');
  |}.

  Definition merge_attributes_config (o : config) (attrs : list attributes_config) : config :=
    let inlinings_o :=
      List.concat (o.(inlinings_opts) :: (List.map inlinings_opt attrs)) in
    let const_remappings_o :=
      List.concat (o.(const_remappings_opts) :: (List.map const_remappings_opt attrs)) in
    let ind_remappings_o :=
      List.concat (o.(ind_remappings_opts) :: (List.map ind_remappings_opt attrs)) in
    let cstr_reorders_o :=
      List.concat (o.(cstr_reorders_opts) :: (List.map cstr_reorders_opt attrs)) in
    let custom_attributes_o :=
      List.concat (o.(custom_attributes_opts) :: (List.map custom_attributes_opt attrs)) in
    {|
      backend_opts           := o.(backend_opts);
      erasure_opts           := o.(erasure_opts);
      inlinings_opts         := inlinings_o;
      const_remappings_opts  := const_remappings_o;
      ind_remappings_opts    := ind_remappings_o;
      cstr_reorders_opts     := cstr_reorders_o;
      custom_attributes_opts := custom_attributes_o;
    |}.



  Definition is_rust_config (o : config) : bool :=
    match o.(backend_opts) with
    | Rust _ => true
    | _ => false
    end.

  Definition is_elm_config (o : config) : bool :=
    match o.(backend_opts) with
    | Elm _ => true
    | _ => false
    end.

  Definition is_ocaml_config (o : config) : bool :=
    match o.(backend_opts) with
    | OCaml _ => true
    | _ => false
    end.

  Definition is_cakeml_config (o : config) : bool :=
    match o.(backend_opts) with
    | CakeML _ => true
    | _ => false
    end.

  Definition is_catcrypt_config (o : config) : bool :=
    match o.(backend_opts) with
    | CatCrypt _ => true
    | _ => false
    end.

  Definition is_c_config (o : config) : bool :=
    match o.(backend_opts) with
    | C _ => true
    | _ => false
    end.

  Definition is_wasm_config (o : config) : bool :=
    match o.(backend_opts) with
    | Wasm _ => true
    | _ => false
    end.

  Definition is_eval_config (o : config) : bool :=
    match o.(backend_opts) with
    | Eval _ => true
    | _ => false
    end.

  Definition is_ast_config (o : config) : bool :=
    match o.(backend_opts) with
    | AST _ => true
    | _ => false
    end.

End GeneralConfigOptional.
