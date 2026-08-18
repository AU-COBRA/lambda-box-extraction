# Peregrine Backends

Peregrine backends compiles a $\lambda_\square$ or $\lambda_\square^T$ program down to one of several target languages. The choice of target is encoded in the `backend_config` field of the [configuration](format.md).

The table below summarises supported the backends


| Backend      | Source  | Verified | Verified printer | Target format       | Readability | Memory handling |
|--------------|---------|----------|------------------|---------------------|-------------|-----------------|
| C            | untyped | ✓ | ✗ | C-light                    | ✗ | Verified GC |
| WebAssembly  | untpyed | ✓ | ✓ | Binary format              | ✗ | Bump allocator, no GC |
| OCaml        | untyped | ✓ | ✗ | Malfunction Serialized AST | ✗ | GC |
| CakeML       | untyped | ✓ | ✓ | Serialized AST             | ✗ | GC |
| Rust         | typed   | ✗ | ✗ | Source language            | ✓ | Bump allocator, no GC |
| Elm          | typed   | ✗ | ✗ | Source language            | ✓ | - |
| F#           | untyped | ✗ | ✗ | F# source                  | ✓ | .NET GC |
| AST (debug)  | either  | ✓ | ✓ | Serialized AST             | ✗ | - |
| Eval (debug) | either  | ✓ | ✗ | -                          | ✗ | -  |


## C

C backend extracting to surface level C-light (a subset of C). It accepts both typed and untyped ASTs as input.
Implemented in [CertiRocq](https://github.com/CertiRocq/certirocq/).

Output — a C-light program as a single `.c` and `.h` file. The CLI writes a `.c` file plus a `.h` header; the C must be linked against the CertiRocq runtime and glue code (see the [CertiRocq plugin docs](https://github.com/CertiRocq/certirocq/wiki/The-CertiRocq-plugin#compiling-the-generated-c-code)). The C output can then be compiled with [CompCert](https://compcert.org/) or any standard C compiler.

## WebAssembly

WebAssembly(Wasm) backend extracting to Wasm binary format. It uses the Wasm 2.0 standard with tail-call extension. It accepts both typed and untyped ASTs as input.
Implemented in [CertiRocq](https://github.com/CertiRocq/certirocq/).

Output — a file the binary-encoded Wasm module. The CLI writes a `.wasm` file. The module exports the main function as `main_function`.
The code can be executed by any Wasm 2.0 compatible runtime that supports the [tail-call extension](https://webassembly.org/features/) (e.g. recent Node.js, Wasmtime, modern browsers).

## OCaml

OCaml backend extracting to serialized [malfunction](https://github.com/stedolan/malfunction) AST. It accepts both typed and untyped ASTs as input.
Implemented in [coq-verified-extraction](https://github.com/yforster/coq-verified-extraction).

Output — serialized malfunction AST. The CLI writes a `.mlf` file containing the source; it is compiled with the [malfunction](https://github.com/stedolan/malfunction) tool.

## CakeML

CakeML backend extracting to serialized CakeML AST 

Output — serialized AST. The CLI writes a `.cml` file.
The `.cml` file can be compiled using the [CakeML compiler](https://cakeml.org/) using the flags `--sexp=true --exclude_prelude=true --skip_type_inference=true`.

## Rust

Rust backend extracting to surface level Rust code. The backend requires typed AST.
The backend is located in [`peregrine-project/rocq-typed-extraction`](https://github.com/peregrine-project/rocq-typed-extraction).

Output
* A single file; written to `<file>.rs` by the CLI.
* The generated Rust depends on [bumpalo](https://docs.rs/bumpalo/) v3 or later.
* Is compiled with the [Rust compiler](https://rust-lang.org/tools/install/)

## Elm

ELm backend extracting to surface level Elm code. The backend requires typed AST.
The backend is located in [`peregrine-project/rocq-typed-extraction`](https://github.com/peregrine-project/rocq-typed-extraction).

Output
* A single file; written to `<file>.elm` by the CLI.
* The result has no external dependencies and is compiled with the [Elm compiler](https://guide.elm-lang.org/install/elm).

## F#

F# backend extracting to surface level F# code. The backend requires untyped AST. The printer is unverified.

Output
* A single, self-contained `.fs` file, including an inlined runtime helper, so it has no external dependencies. Note the emitted file cannot run under `dotnet fsi` (scripts reject top-level `module` declarations); compile it inside a .NET project.
* Every value is printed as `obj`; source inductives become `[<RequireQualifiedAccess>]` discriminated unions, and nullary constants are wrapped in `Lazy<obj>` so they are not forced at module-init time.
* Compile and run with [`dotnet`](https://dotnet.microsoft.com/) in `Release` mode — `Debug` builds and `dotnet fsi` disable .NET tail calls. Deep non-tail recursion should run on a large-stack thread (the test harness uses a 512 MiB stack).
* No support for `tPrim`/primitives, and no support for remapping, like the Lean backend.

## Debug backends

Backends used for debugging.

### AST

Output the AST after running the middle-end pipeline.
Useful for debugging the pipeline and for inspecting intermediate steps in the middle-end.
Implemented in [`theories/backends/ASTBackend.v`](/theories/backends/ASTBackend.v); used by `peregrine ast`.

Output — a single file written by the CLI to `<file>.ast` (default extension is preserved across IR choices).

### Eval

Evaluates the $\lambda_\square$ input using an interpreter.
Implemented in [`theories/backends/EvalBackend.v`](/theories/backends/EvalBackend.v); used by `peregrine eval`.

Output — a string containing the printed value. The CLI prints it on stdout.



# Backend support
TODO

# Writing a new backend

Adding a new backend to Peregrine consists of two tasks.

1) Writing the backend
   - Implementing translation from $\lambda_\square$ or $\lambda_\square^T$ to the target language
   - Implementing printing or serialization of the target language. To properly integrate with Peregrine the result of the backend must be a string or list of strings. 
   - Optionally handling optional features such as remapping or split extraction
2) Integrating with Peregrine
   - Declare option format and default options and implement serialization
   - Declare which transformations and optimizations are required, optional, or incompatible with the backend, and provide default options for passes
   - Declare which features are supported by the backend
   - Implement name sanitization for the backend if necessary
   - Add wrapper function calling the backend and add it to `run_backend` in [`Pipeline.v`](/theories/Pipeline.v)
