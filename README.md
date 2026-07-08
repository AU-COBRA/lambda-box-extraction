# Peregrine
[![Build](https://github.com/peregrine-project/peregrine-tool/actions/workflows/build.yml/badge.svg)](https://github.com/peregrine-project/peregrine-tool/actions/workflows/build.yml)
[![GitHub](https://img.shields.io/github/license/peregrine-project/peregrine-tool)](https://github.com/peregrine-project/peregrine-tool/blob/master/LICENSE)

The Peregrine Project provides a unified middle-end for code generation from proof assistants. It supports Agda, Lean, and Rocq and can generate code in CakeML, C, Rust, OCaml, and WebAssembly.

It puts a focus on correct code extraction: The middle end is verified in the Rocq proof assistant, and some of the frontends and backends are. It is based on an intermediate language called $\lambda_\square$ (LambdaBox).

The peregrine middle-end connects frontends (Rocq, Lean, Agda) to code extractions backends (C, Rust, WebAssembly, ...) through the $\lambda_\square$ intermediate language and defines a common interface between the frontends and backends.
Peregrine frontends produce $\lambda_\square$ programs, which can be compiled to various programming languages through the supported backends. The middle-end connects the frontends and backends, validating the programs and performing transformations and optimizations.

For more details on the Peregrine pipeline see [overview.md](doc/overview.md)


## Install
The backend requires OCaml 4.13 or later and [Opam](https://opam.ocaml.org/doc/Install.html).

The backend can be installed using:
```bash
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
opam install rocq-peregrine
```

See [dev.md](doc/dev.md) for instructions on how to build locally from sources.


## Usage
```
peregrine TARGETLANGUAGE FILE [-o FILE]
```
Compiles $\lambda_\square$ to one of the supported languages.
E.g. compiling `prog.ast` file to WebAssembly.
```
peregrine wasm prog.ast -o prog.wasm
```
Valid values for `TARGETLANGUAGE` are:
* `wasm`
* `c`
* `ocaml`
* `cakeml`
* `rust`
* `elm`

For detailed usage on all commands and flags see [cmds.md](/doc/cmds.md) or use `peregrine --help`.

See [frontends.md](/doc/frontends.md) for details on how to generate $\lambda_\square$ from proof assistants.


## Supported Proof Assistants (frontends)
Peregrine supports code extraction from the following proof assistants
* [Rocq](https://rocq-prover.org/)
* [Lean](https://lean-lang.org/)
* [Agda](https://agda.readthedocs.io)

For more information on the frontends and how to use them see [frontends.md](/doc/frontends.md).


## Supported Languages (backends)
Peregrine supports extraction to the following programming languages
* C
* WebAssembly
* Rust
* OCaml
* CakeML
* Elm

For more information on the backends see [backends.md](/doc/backends.md).
