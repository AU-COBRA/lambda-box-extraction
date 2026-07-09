export type Timeout = { type: "error", reason: "timeout" };
export type RuntimeError = { type: "error", reason: "runtime error", error: string };
export type CompileError = { type: "error", reason: "compile error", compiler: string, code: number, error: string };
export type IncorrectResult = { type: "error", reason: "incorrect result", expected: string, actual: string };
export type ExecFailure = Timeout | RuntimeError | CompileError | IncorrectResult;
export type ExecSuccess = { type: "success", time: number }
// Result of executing/compiling a test
export type ExecResult = ExecFailure | ExecSuccess;


// Type representing simple types in the test programs
// Used to specify parameter and return types for the main function
export enum SimpleType {
  Nat,
  Bool,
  UInt63,
  Other /* For programs using types not in the list, when using this type the output won't be checked */
}

// Complex types that have type variables
type ComplexType =
| { type: "list", a_t: ProgramType }
| { type: "option", a_t: ProgramType }
| { type: "prod", a_t: ProgramType, b_t: ProgramType }

// Type representing types in the test programs
// Used to specify parameter and return types for the main function
export type ProgramType = SimpleType | ComplexType;


// Languages support by the lambda box compiler
export enum Lang {
  OCaml = "OCaml",
  C = "C",
  Wasm = "WebAssembly",
  Rust = "Rust",
  Elm = "Elm",
  CakeML = "CakeML",
  Lean = "Lean"
}

export type TestCase = {
  // Path to file containing the program lambda box source
  src?: string,
  // Path to file containg the typed lambda box source
  tsrc?: string,
  // Name of the programs main function
  // Only used for typed backends where there isn't an explicit main function
  main: string,
  // The return type of the main function
  // Used to generate printing function for the output
  output_type: ProgramType,
  // The expected output
  expected_output?: string[],
  // Types of the main functions parameters
  parameters?: ProgramType[],
  // Arguments for main function call
  arguments?: string[],
  // Extra flags and args for compiling the test program
  compiler_args?: string,
}

// Test configuration consisting of a target language, testset name, and a set of options
// for the peregrine compiler
export type TestConfiguration = [Lang, string, string]
