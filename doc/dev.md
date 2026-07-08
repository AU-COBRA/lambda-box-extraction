# Local dev environemnt setup
## Requirements
To install Peregrine dependencies either [opam](http://opam.ocaml.org/) or [Nix](https://nixos.org/) package managers are recommended.

To build the Peregrine Haskell libary GHC and cabal are required.

Additionally, Lean, Node.JS, cargo, rustc, and gcc are required to run the test suite.

## Getting sources
To checkout the Peregrine source code:
```bash
git clone https://github.com/peregrine-project/peregrine-tool.git
cd peregrine-tool
```

## Installing using `opam`
First set up a fresh `opam` environment for Peregrine
```bash
opam switch create peregrine --packages="ocaml-variants.4.14.2+options,ocaml-option-flambda"
eval $(opam env)
opam repo add rocq-released https://rocq-prover.org/opam/released
```

To install dependencies run:
```bash
opam install . --deps-only
```

## Installing using `Nix`
```bash
nix-shell --argstr bundle 9.1 --argstr job Peregrine
```

## Building and running Peregrine
Once dependencies have been installed you can build Peregrine with `make`.
The dev CLI can be launched with `dune exec peregrine -- <ARGS>`.

### Make targets
| | |
|------------------|--------------------------|
| `make`           | Build Rocq sources, CLI, and Rocq frontend |
| `make theory`    | Build Rocq sources |
| `make mllib`     | Build Peregrine CLI |
| `make hs-lib`    | Build Peregrine Haskell library |
| `make test`      | Run test suite |
| `make install`   | Install Peregrine |
| `make uninstall` | Uninstall Peregrine |
| `make clean`     | Clean compiled and generated files |

# Running tests
The test suite is a TypeScript runner that drives peregrine against pre-extracted Rocq, Lean, and Agda fixtures, compiles the output with the relevant external tool, and checks the result. From the repo root:

```bash
make test
```

To generate the test files see [`test/README.md`](/test/README.md).

For benchmark suite see [benchmarks](https://github.com/peregrine-project/benchmarks).


# Project structure
This repository contains:
* The source code for the Peregrine middle-end written in Rocq
* A command-line interface for Peregrine written in OCaml. The interface is a wrapper on top of the extracted middle-end Rocq code.
* A Rocq frontend for Peregrine
* A Haskell library containing Peregrine definitions, printers, and parsers for interfacing with Peregrine
* A test suite for Peregrine

## Directory layout
See the README in each subdirectory for more details.

| Path | Contents |
|------|----------|
| [thories/](/theories/) | Rocq sources for Peregrine |
| [src/](/src/) | Extracted OCaml code from Rocq sources |
| [bin/](/bin/) | OCaml sources defining the Peregrine command-line interface |
| [plugin/](/plugin/) | Peregrine frontend for Rocq |
| [hs-lib/](/hs-lib/) | Haskell library extracted from Rocq sources, contains the $\lambda_\square$ and Peregrine configuration definitions and verified printers/parsers |
| [test/](/test/) | Test suite |
| [doc/](/doc/) | Documentation |
| [.github/](/.github/) | GitHub CI |
| [.nix/](/.nix/) | Nix package configuration for Peregrine |
