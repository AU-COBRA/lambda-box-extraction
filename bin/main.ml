open Cmdliner
open Compile
open Common

let version = "0.0.1"

let copts_t =
  let docs = Manpage.s_common_options in
  let verbose_arg =
    let doc = "Suppress informational output." in
    let quiet = Quiet, Arg.info ["q"; "quiet"] ~docs ~doc in
    let doc = "Give verbose output." in
    let verbose = Verbose, Arg.info ["v"; "verbose"] ~docs ~doc in
    Arg.(last & vflag_all [Normal] [quiet; verbose])
  in
  let debug_arg =
    let doc = "Enable debug information." in
    Arg.(value & flag & info ["d"; "debug"] ~docs ~doc)
  in
  let out_arg =
    let doc = "Output file." in
    Arg.(value & opt (some string) None & info ["o"; "outfile"] ~docs ~doc)
  in
  let attrs_arg =
    let doc = "Attribute config files." in
    Arg.(value & opt (list file) [] & info ["attributes"] ~docs ~doc)
  in
  Term.(const mk_copts $ verbose_arg $ debug_arg $ out_arg $ attrs_arg)

let certirocq_opts_t =
  let cps_arg =
    let doc = "Use CPS translation pipeline." in
    Arg.(value & flag & info ["cps"] ~doc)
  in
  let c_args_arg =
    let doc = "Numbers of C arguments." in
    Arg.(value & opt (some int) None & info ["c-args"] ~doc)
  in
  let o_level_arg =
    let doc = "Optimization level." in
    Arg.(value & opt (some int) None & info ["O"] ~doc)
  in
  let anf_conf_arg =
    let doc = "ANF pipeline config." in
    Arg.(value & opt (some int) None & info ["anf-conf"] ~doc)
  in
  let prefix_arg =
    let doc = "Prefix to generated FFI." in
    Arg.(value & opt (some string) None & info ["prefix"] ~doc)
  in
  let body_name_arg =
    let doc = "Name of the toplevel function." in
    Arg.(value & opt (some string) None & info ["body-name"] ~doc)
  in
  Term.(const mk_certirocq_opts $ cps_arg $ c_args_arg $ o_level_arg $ anf_conf_arg $ prefix_arg $ body_name_arg)

let erasure_opts_t =
  let betared_arg =
    let doc = "Perform beta reduction." in
    Arg.(value & opt (some bool) None & info ["betared"] ~doc)
  in
  let unbox_arg =
    let doc = "Unbox singleton types." in
    Arg.(value & opt (some bool) None & info ["unboxing"] ~doc)
  in
  let dearg_ctors_arg =
    let doc = "Dearg constructors." in
    Arg.(value & opt (some bool) None & info ["dearg-ctors"] ~doc)
  in
  let dearg_consts_arg =
    let doc = "Dearg constants." in
    Arg.(value & opt (some bool) None & info ["dearg-consts"] ~doc)
  in
  Term.(const mk_erasure_opts $ betared_arg $ unbox_arg $ dearg_ctors_arg $ dearg_consts_arg)


let sdocs = Manpage.s_common_options

let help man_format cmds topic = match topic with
| None -> `Help (`Pager, None)
| Some topic ->
  let topics = "topics" :: "errors" :: "warnings" :: "environment" :: cmds in
  let conv = Cmdliner.Arg.enum (List.rev_map (fun s -> (s, s)) topics) in
  let parse = Cmdliner.Arg.Conv.parser conv in
  match parse topic with
  | Error e -> `Error (false, e)
  | Ok t when t = "topics" -> List.iter print_endline topics; `Ok ()
  | Ok t when List.mem t cmds -> `Help (man_format, Some t)
  | Ok t when t = "environment" ->
    let page = (topic, 7, "", "", ""), [`S topic; `P "Not implemented yet";] in
    `Ok (Cmdliner.Manpage.print man_format Format.std_formatter page)
  | Ok _ ->
    let page = (topic, 7, "", "", ""), [`S topic; `P "Not implemented yet";] in
    `Ok (Cmdliner.Manpage.print man_format Format.std_formatter page)

let help_secs = [
  `S Manpage.s_common_options;
  `P "These options are common to all commands.";
  `S "MORE HELP";
  `P "Use $(mname) $(i,COMMAND) --help for help on a single command.";`Noblank;
  `P "Use $(mname) $(b,help environment) for help on environment variables.";
  `S Manpage.s_bugs; `P "Please report bugs at https://github.com/peregrine-project/peregrine-tool/issues.";]

let help_cmd =
  let topic =
    let doc = "The topic to get help on. $(b,topics) lists the topics." in
    Arg.(value & pos 0 (some string) None & info [] ~docv:"TOPIC" ~doc)
  in
  let doc = "display help about commands" in
  let man =
    [`S Manpage.s_description;
     `P "Prints help about commands and other subjects…";
     `Blocks help_secs; ]
  in
  let info = Cmd.info "help" ~doc ~man in
  Cmd.v info
    Term.(ret (const help $ Arg.man_format $ Term.choice_names $ topic))

let exits = Cmd.Exit.defaults @ [
  Cmd.Exit.info 10 ~max:19 ~doc:"on parsing errors.";
  Cmd.Exit.info 20 ~max:29 ~doc:"on compiler errors.";
]

let compile_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"PROGRAM_FILE" ~doc)
  in
  let config_file =
    let doc = "config file" in
    Arg.(required & pos 1 (some file) None & info []
           ~docv:"CONFIG_FILE" ~doc)
  in
  let doc = "Compile lambda box program" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "compile" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile $ copts_t $ program_file $ config_file)

let rust_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box program to Rust" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "rust" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_rust $ copts_t $ erasure_opts_t $ program_file)

let elm_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box program to Elm" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "elm" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_elm $ copts_t $ erasure_opts_t $ program_file)

let ocaml_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box program to OCaml" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "ocaml" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_ocaml $ copts_t $ erasure_opts_t $ program_file)

let cakeml_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box program to CakeML" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "cakeml" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_cakeml $ copts_t $ erasure_opts_t $ program_file)

let catcrypt_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let namespace_arg =
    let doc = "Lean namespace for the generated NamedSSA program." in
    Arg.(value & opt (some string) None & info ["namespace"] ~doc)
  in
  let def_name_arg =
    let doc = "Name of the generated definition (defaults to the source constant name)." in
    Arg.(value & opt (some string) None & info ["def-name"] ~doc)
  in
  let no_mask63_arg =
    let doc = "Disable 63-bit masking of arithmetic operations (masking is on by default)." in
    Arg.(value & flag & info ["no-mask63"] ~doc)
  in
  let scaffold_arg =
    let doc = "Emit scaffolding around the generated definition." in
    Arg.(value & flag & info ["scaffold"] ~doc)
  in
  let doc = "Compile lambda box program to CatCrypt NamedSSA (Lean 4)" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "catcrypt" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_catcrypt $ copts_t $ erasure_opts_t $ namespace_arg $ def_name_arg $ no_mask63_arg $ scaffold_arg $ program_file)

let c_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box program to C" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "c" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_c $ copts_t $ certirocq_opts_t $ erasure_opts_t $ program_file)

let wasm_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Compile lambda box program to WebAssembly" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "wasm" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_wasm $ copts_t $ certirocq_opts_t $ erasure_opts_t $ program_file)

let eval_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let fuel_arg =
    let doc = "evaluator fuel" in
    Arg.(value & opt int 10000 & info ["fuel"] ~doc)
  in
  let anf_arg =
    let doc = "evaluator type" in
    Arg.(value & opt bool true & info ["anf"] ~doc)
  in
  let doc = "Evaluate lambda box program" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "eval" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_eval $ copts_t $ certirocq_opts_t $ erasure_opts_t $ fuel_arg $ anf_arg $ program_file)

let ast_cmd =
  let ast_type =
    let doc = "AST type" in
    Arg.(required & pos 0 (some (enum [("box", Box); ("typed", BoxTyped); ("mut", BoxMut); ("local", BoxLocal); ("anf", ANF); ("anfc", ANFC)])) None & info []
           ~docv:"AST_TYPE" ~doc)
  in
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 1 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let doc = "Get intermediate representations" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "ast" ~doc ~sdocs ~man in
  Cmd.v info Term.(const compile_ast $ copts_t $ certirocq_opts_t $ erasure_opts_t $ ast_type $ program_file)

let validate_cmd =
  let program_file =
    let doc = "lambda box program" in
    Arg.(required & pos 0 (some file) None & info []
           ~docv:"FILE" ~doc)
  in
  let config_file =
    let doc = "config file" in
    Arg.(value & opt (some file) None & info ["config"] ~doc)
  in
  let doc = "Validate program and compile configuration" in
  let man = [
    `S Manpage.s_description;
    `P "";
    `Blocks help_secs; ]
  in
  let info = Cmd.info "validate" ~doc ~sdocs ~man in
  Cmd.v info Term.(const validate $ copts_t $ program_file $ config_file)

let main_cmd =
  let doc = "Verified compiler from LambdaBox to WebAssembly, C, Rust, and OCaml" in
  let man = help_secs in
  let info = Cmd.info "peregrine" ~version ~doc ~sdocs ~man ~exits in
  let default = Term.(ret (const (fun _ -> `Help (`Pager, None)) $ copts_t)) in
  Cmd.group info ~default [compile_cmd; rust_cmd; elm_cmd; ocaml_cmd; cakeml_cmd; catcrypt_cmd; c_cmd; wasm_cmd; eval_cmd; ast_cmd; validate_cmd; help_cmd]

let () = exit (Cmd.eval main_cmd)
