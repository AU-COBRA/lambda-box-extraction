# Lean 4 backend for peregrine-tool

`peregrine lean prog.ast -o prog.lean` compiles a λ_□ AST to a
self-contained Lean 4 source file that imports `Peregrine.Runtime`.
End-to-end verified: extracting `Demo.ast` and running the result
under `lake env lean` produces `[tftf]`, matching the source value
`.cons .true (.cons .false (.cons .true (.cons .false .empty)))`.

## Pipeline

```
.ast (PAst)
  ↓ existing parse / check_wf / sanitize / transforms
EAst.program (λ_□)
  ↓ LeanCompile.compile_program       (NEW, Rocq)
LeanIR.lprogram (λ_pure-ish)
  ↓ PrintLean.print_program           (NEW, Rocq)
Lean 4 source string
  ↓ bin/compile.ml:write_lean_res     (NEW, OCaml)
prog.lean
```

## Files added

- `theories/lean/LeanIR.v` — IR datatype (`lterm`, `lfun`, `ldecl`,
  `lprogram`).
- `theories/lean/LeanCompile.v` — `EAst → LeanIR`.  Top-level `tFix`
  with a singleton mutual block is detected and treated as a
  self-recursive `def`.
- `theories/lean/PrintLean.v` — pretty-printer.  Every emitted term is
  wrapped in `Peregrine.reflect` so values uniformly inhabit `Obj`;
  `LApp` goes through `Peregrine.apply` (universal application).
- `theories/backends/LeanBackend.v` — `extract_lean` wrapper with
  `default_lean_config`, `lean_phases` (requires `implement_box`,
  `implement_lazy`, `cofix_to_laxy`), and `Admitted`-stub correctness
  lemmas.
- `lean/Peregrine/Runtime.lean` — `Obj` (unsafe inductive), `cast`,
  `reflect`, `apply`.

## Files modified

- `theories/Config.v`, `theories/ConfigUtils.v` — `lean_config` /
  `lean_config'` records, `Lean` / `Lean'` variants, dispatch arms.
- `theories/Pipeline.v` — `LeanProgram` ctor, `Lean` arm in
  `run_backend`, `Lean _` in `validate_ast_type` / `needs_typed`.
- `theories/NameSanitize.v` — `lean_sanitizer`.
- `theories/serialization/{SerializeConfig,DeserializeConfig,SerializeConfigSound,SerializeConfigComplete}.v`
  — `lean_config{,'}` instances + `Lean{,'}` cases in
  `backend_config{,'}` instances.
- `theories/Extraction.v` — `empty_lean_config'` added to the
  `Separate Extraction` list.
- `_CoqProject` — new files registered.
- `bin/compile.ml` — `compile_lean`, `write_lean_res`, `LeanProgram`
  arm in `write_program`.
- `bin/main.ml` — `lean_cmd`, added to `Cmd.group`.
- `lakefile.toml` — `Peregrine.Runtime` added to roots.

## Design choices

- IR is loosely paper-faithful (no strict ANF, binary `LApp`).  Match
  arms keep their de Bruijn binder names via a `ctx : list lterm` that
  also encodes self-recursion as `LConst kn`.
- All emitted Lean values inhabit `Obj`; per-source `unsafe inductive`
  declarations have all fields typed `Obj`; functions are `unsafe def`
  with `Obj`-typed parameters and return.
- `Peregrine.reflect : α → Obj` and `Peregrine.cast : Obj → α` are
  unsafe identity casts; `Peregrine.apply : Obj → Obj → Obj`
  reinterprets the head as `Obj → Obj`.  All three are zero-cost.
- No RC instrumentation — Lean's own compiler handles RC downstream
  (per §3 of the *Counting Immutable Beans* paper, RC insertion is
  optional for correctness).

## Verification stubs

`theories/backends/LeanBackend.v` declares:

- `extract_lean_total` — proved.
- `extract_lean_semantics_preservation` — `True` placeholder, to be
  replaced with a real relation between `EWcbvEval` and Lean 4
  reduction.

## Known v1 limitations

- Mutual `tFix` blocks spread across multiple top-level constants are
  not merged into a single `mutual` block; sibling references emit
  `Peregrine.reflect ()` placeholders.
- Nested (non-top-level) `tFix` is not lambda-lifted; emits the same
  placeholder.  Reachable mainly from `implement_box`'s replacement of
  computationally irrelevant terms, which a well-typed source program
  should never inspect at runtime.
- No primitive support (`tPrim`, `Uint63`, native strings) — emits the
  placeholder.
- No constant / inductive remapping into the Lean standard library
  (would mirror `RustBackend.v`'s `remap_constant` infrastructure).
- The `lean_sanitizer` reuses the OCaml sanitizer, so emitted names
  contain `_UU2e` escapes for dots and similar mangling.  Readable
  but verbose.

## Usage

```
lake build                                  # build Peregrine.Runtime
test/lean$ lake build                       # produce test/lean/extraction/Demo.ast
dune exec peregrine -- lean test/lean/extraction/Demo.ast -o Demo.lean
lake env lean Demo.lean                     # compile against runtime
```
