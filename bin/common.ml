type verbose = Normal | Quiet | Verbose

type copts = {
  verbose: verbose;
  debug: bool;
  output_file: string option;
  attrs: string list;
}
let mk_copts verbose debug output_file attrs = {
  verbose;
  debug;
  output_file;
  attrs
}

type erasure_opts = {
  betared             : bool option;
  unboxing            : bool option;
  dearg_ctors         : bool option;
  dearg_consts        : bool option;
  specialize_instances : bool option;
  cse                 : bool option;
}

let mk_erasure_opts betared unboxing dearg_ctors dearg_consts specialize_instances cse = {
  betared;
  unboxing;
  dearg_ctors;
  dearg_consts;
  specialize_instances;
  cse;
}

type certirocq_opts = {
  cps: bool;
  c_args: int option;
  o_level: int option;
  anf_conf: int option;
  prefix: string option;
  body_name: string option;
}

let mk_certirocq_opts cps c_args o_level anf_conf prefix body_name = {
  cps;
  c_args;
  o_level;
  anf_conf;
  prefix;
  body_name;
}

type astType =
    Box
  | BoxTyped
  | BoxMut
  | BoxLocal
  | ANF
  | ANFC

type import =
    FromRelativePath of string
  | FromAbsolutePath of string
  | FromLibrary of string * string option
