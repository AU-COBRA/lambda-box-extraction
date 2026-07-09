open Common
open Peregrine.Caml_bytestring

module Datatypes = Peregrine.Datatypes
module Config = Peregrine.Config1
module ConfigUtils = Peregrine.ConfigUtils
module RustGMPRemaps = Peregrine.RustGMPRemaps
module RustNativeRemaps = Peregrine.RustNativeRemaps
module RustMixedRemaps = Peregrine.RustMixedRemaps
module Pipeline = Peregrine.Pipeline2
module ResultMonad = Peregrine.ResultMonad
module Cps = Peregrine.Cps



(* String conversion *)
let string_of_cstring = Peregrine.Camlcoq.camlstring_of_coqstring
let cstring_of_string = Peregrine.Camlcoq.coqstring_of_camlstring

let cprint_endline s =
  print_endline (caml_string_of_bytestring s)



(* Extraction output helper functions *)
let get_out_file opts f ext =
  match opts.output_file with
  | Some f -> f
  | None -> (Filename.remove_extension f)^"."^ext

let get_header_file opts f =
  match opts.output_file with
  | Some f -> (Filename.remove_extension f)^".h"
  | None -> (Filename.remove_extension f)^".h"

let write_res f p =
  let f = open_out f in
  p f;
  flush f;
  close_out f

let write_wasm_res opts f p =
  let f = get_out_file opts f "wasm" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_elm_res opts f p =
  let f = get_out_file opts f "elm" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let write_rust_res opts f p =
  let f = get_out_file opts f "rs" in
  write_res f (fun f ->
    List.iter (fun s -> output_string f ((caml_string_of_bytestring s) ^ "\n")) p)

let write_ocaml_res opts f p =
  let f = get_out_file opts f "mlf" in
  write_res f (fun f ->
    output_string f (caml_string_of_bytestring (snd p)))

let write_cakeml_res opts f p =
  let f = get_out_file opts f "cml" in
  write_res f (fun f ->
    output_string f (caml_string_of_bytestring (snd p)))

let write_ast_res opts f p =
  let f = get_out_file opts f "ast" in
  let p = caml_string_of_bytestring p in
  write_res f (fun f -> output_string f p)

let printCProg prog names (dest : string) (imports : import list) =
  let imports' = List.map (fun i -> match i with
    | FromRelativePath s -> "#include \"" ^ s ^ "\""
    | FromLibrary (s, _) -> "#include <" ^ s ^ ">"
    | FromAbsolutePath _ ->
        failwith "Import with absolute path should have been filled") imports in
  Peregrine.PrintClight.print_dest_names_imports prog (Cps.M.elements names) dest imports'

let write_c_res opts f p =
  match p with
  | (((nenv, header), prg), libs) ->
    let runtime_imports = List.map (fun x -> FromLibrary (caml_string_of_bytestring x, None)) libs in
    let imports = runtime_imports in
    let cstr = get_out_file opts f "c" in
    let hstr = get_header_file opts f in
    printCProg prg nenv cstr (imports @ [FromRelativePath hstr]);
    printCProg header nenv hstr (runtime_imports)

let write_program opts f p =
  match p with
  | Pipeline.RustProgram p -> write_rust_res opts f p
  | Pipeline.ElmProgram p -> write_elm_res opts f p
  | Pipeline.OCamlProgram p -> write_ocaml_res opts f p
  | Pipeline.CakeMLProgram p -> write_cakeml_res opts f p
  | Pipeline.CProgram p -> write_c_res opts f p
  | Pipeline.WasmProgram p -> write_wasm_res opts f p
  | Pipeline.EvalProgram p -> cprint_endline p
  | Pipeline.ASTProgram p -> write_ast_res opts f p



let read_file f =
  let c = open_in f in
  let s = really_input_string c (in_channel_length c) in
  close_in c;
  s


let mk_certirocq_config copts = {
  ConfigUtils.direct'    = Some (not copts.cps);
  ConfigUtils.c_args'    = Option.map Peregrine.Caml_nat.nat_of_caml_int copts.c_args;
  ConfigUtils.o_level'   = Option.map Peregrine.Caml_nat.nat_of_caml_int copts.o_level;
  ConfigUtils.anf_conf'  = Option.map Peregrine.Caml_nat.nat_of_caml_int copts.anf_conf;
  ConfigUtils.prefix'    = Option.map bytestring_of_caml_string copts.prefix;
  ConfigUtils.body_name' = Option.map bytestring_of_caml_string copts.body_name;
}

let mk_erasure_config eopts = {
  ConfigUtils.implement_box'  = None;
  ConfigUtils.implement_lazy' = None;
  ConfigUtils.cofix_to_laxy'  = None;
  ConfigUtils.betared'        = eopts.betared;
  ConfigUtils.unboxing'       = eopts.unboxing;
  ConfigUtils.dearg_ctors'    = eopts.dearg_ctors;
  ConfigUtils.dearg_consts'   = eopts.dearg_consts;
  ConfigUtils.specialize_instances' = eopts.specialize_instances;
}

let mk_config ?(const_remaps=[]) ?(ind_remaps=[]) b eopts = {
  ConfigUtils.backend_opts' = b;
  ConfigUtils.erasure_opts' = Some (mk_erasure_config eopts);
  ConfigUtils.inlinings_opts' = [];
  ConfigUtils.const_remappings_opts' = const_remaps;
  ConfigUtils.ind_remappings_opts' = ind_remaps;
  ConfigUtils.cstr_reorders_opts' = [];
  ConfigUtils.custom_attributes_opts' = []
}

let mk_ast_config t copts : ConfigUtils.ast_config' =
    match t with
    | Box -> ConfigUtils.LambdaBox'
    | BoxTyped -> ConfigUtils.LambdaBoxTyped'
    | BoxMut -> ConfigUtils.LambdaBoxMut' (Some (mk_certirocq_config copts))
    | BoxLocal -> ConfigUtils.LambdaBoxLocal' (Some (mk_certirocq_config copts))
    | ANF -> ConfigUtils.LambdaANF' (Some (mk_certirocq_config copts))
    | ANFC -> ConfigUtils.LambdaANFC' (Some (mk_certirocq_config copts))

(* Validate function *)
let validate opts f_prog f_config =
  let prog = f_prog |> read_file |> bytestring_of_caml_string in
  (* backend part of config isn't check so we just use any *)
  let config =
    match f_config with
    | Some f -> Datatypes.Coq_inl (f |> read_file |> bytestring_of_caml_string)
    | None -> Datatypes.Coq_inr (ConfigUtils.empty_config' (ConfigUtils.OCaml' ConfigUtils.empty_ocaml_config')) in
  let attrs = List.map (fun s -> s |> read_file |> bytestring_of_caml_string) opts.attrs in
  print_endline "Validating AST:";
  let res = Pipeline.peregrine_validate config attrs prog in
  match res with
  | ResultMonad.Ok _ ->
    print_endline "AST is valid"
  | ResultMonad.Err e ->
    print_endline "Error validating AST:";
    cprint_endline e;
    exit 1


(* Compile functions *)
let compile_aux opts f prog config =
  let f_name = f |> Filename.basename |> Filename.chop_extension |> bytestring_of_caml_string in
  let attrs = List.map (fun s -> s |> read_file |> bytestring_of_caml_string) opts.attrs in
  print_endline "Compiling:";
  let res = Pipeline.peregrine_pipeline config attrs prog f_name in
  match res with
  | ResultMonad.Ok p ->
    print_endline "Compiled successfully:";
    write_program opts f p
  | ResultMonad.Err e ->
    print_endline "Could not compile:";
    cprint_endline e;
    exit 1

let compile opts f_prog f_config =
  let prog = f_prog |> read_file |> bytestring_of_caml_string in
  let config = f_config |> read_file |> bytestring_of_caml_string in
  compile_aux opts f_prog prog (Datatypes.Coq_inl config)

let compile_backend ?(const_remaps=[]) ?(ind_remaps=[]) backend_opts opts eopts f_prog =
  let prog = f_prog |> read_file |> bytestring_of_caml_string in
  let config = mk_config ~const_remaps ~ind_remaps backend_opts eopts in
  compile_aux opts f_prog prog (Datatypes.Coq_inr config)

let compile_rust opts eopts f_prog =
  (* Wire in the GMP numeric backend: the [rug::Integer] preamble plus the
     nat/positive/N/Z arithmetic remaps (config-path analogue of the plugin's
     ExtrRustGMP.v).  Without these the Rust backend lowers nat/N/Z to unary
     Peano / binary-inductive towers, giving catastrophic arithmetic. *)
  let b_opts = ConfigUtils.Rust' RustGMPRemaps.gmp_rust_config' in
  compile_backend
    ~const_remaps:RustGMPRemaps.gmp_const_remaps
    ~ind_remaps:RustGMPRemaps.gmp_ind_remaps
    b_opts opts eopts f_prog

let compile_rust_native opts eopts f_prog =
  (* Path B: the native-i64 numeric representation (no arena, no Box::leak).
     Fast for values within i64 range; the mixed backend combines it with the
     arbitrary-precision path A via coercions. *)
  let b_opts = ConfigUtils.Rust' RustNativeRemaps.native_rust_config' in
  compile_backend
    ~const_remaps:RustNativeRemaps.native_const_remaps
    ~ind_remaps:RustNativeRemaps.native_ind_remaps
    b_opts opts eopts f_prog

let compile_rust_mixed opts eopts f_prog =
  (* Path C: mixed representation.  Default path A (rug::Integer), with a
     directive-selected partition of ops compiled in path B (native i64) behind
     A<->B coercions. *)
  let b_opts = ConfigUtils.Rust' RustMixedRemaps.mixed_rust_config' in
  compile_backend
    ~const_remaps:RustMixedRemaps.mixed_const_remaps
    ~ind_remaps:RustMixedRemaps.mixed_ind_remaps
    b_opts opts eopts f_prog

let compile_elm opts eopts f_prog =
  let b_opts = ConfigUtils.Elm' ConfigUtils.empty_elm_config' in
  compile_backend b_opts opts eopts f_prog

let compile_ocaml opts eopts f_prog =
  let b_opts = ConfigUtils.OCaml' ConfigUtils.empty_ocaml_config' in
  compile_backend b_opts opts eopts f_prog

let compile_cakeml opts eopts f_prog =
  let b_opts = ConfigUtils.CakeML' ConfigUtils.empty_cakeml_config' in
  compile_backend b_opts opts eopts f_prog

let compile_c opts copts eopts f_prog =
  let b_opts = ConfigUtils.C' (mk_certirocq_config copts) in
  compile_backend b_opts opts eopts f_prog

let compile_wasm opts copts eopts f_prog =
  let b_opts = ConfigUtils.Wasm' (mk_certirocq_config copts) in
  compile_backend b_opts opts eopts f_prog

let compile_ast opts copts eopts t f_prog =
  let b_opts = ConfigUtils.AST' (mk_ast_config t copts) in
  compile_backend b_opts opts eopts f_prog

let compile_eval opts copts eopts fuel anf f_prog =
  let copts = (mk_certirocq_config copts) in
  let b_opts = ConfigUtils.Eval' {
      ConfigUtils.copts'    = Some copts;
      ConfigUtils.fuel'     = Peregrine.Caml_nat.nat_of_caml_int fuel;
      ConfigUtils.eval_anf' = anf;
    } in
  compile_backend b_opts opts eopts f_prog
