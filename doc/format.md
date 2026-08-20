# Peregrine input format

The peregrine middle end takes two input files:

1. a $\lambda_\square$ program formatted as S-expressions, and
2. a pipeline configuration formatted as S-expressions.

Both files use the same lightweight S-expression syntax described below. Parsers and printers live under [theories/serialization/](/theories/serialization/) and are built on top of the Ceres library (`CeresBS`). The Rocq source of record for the configuration types is [theories/Config.v](/theories/Config.v); the AST types come from MetaRocq's `EAst` and `ExAst`.

## Generic S-expression conventions

The S-expression format supports string and integer literals. Both files should be UTF-8 encoded. Non-ASCII characters are only supported in S-expression string literals; the following escape sequences are recognised: `\n`, `\r`, `\t`, `\\`, `\"`. Booleans are serialized as the atoms `true` / `false`.

Rocq lists and pairs are translated to S-expression lists. Records are translated to a list starting with an atom corresponding to the record name (same capitalization as the Rocq type), followed by each field in the order in which they appear in the source. Field names are not included.

```coq
Record foo := { bar : nat; baz : string; }.
Definition s : foo := {| bar := 0; baz := "hello"; |}.
(* In S-expression form: *)
(* (foo 0 "hello") *)
```

Inductives are similarly translated. For an n-ary constructor the constructor application is translated to a list of length `n+1` whose first element is the atom for the constructor name and whose remaining elements are the constructor arguments. Nullary constructors are translated to a single atom.

```coq
Inductive foo :=
| bar : foo
| baz : nat -> foo -> foo.
Definition s : foo := baz 1 (baz 2 bar).
(* In S-expression form: *)
(* (baz 1 (baz 2 bar)) *)
```

`option` values use the same convention: `None` serializes as the atom `None`, and `Some x` serializes as `(Some <x>)`.

## Lambda Box AST

LambdaBox has two variants:

1. untyped lambda box ($\lambda_\square$), defined in MetaRocq's `EAst`;
2. typed lambda box ($\lambda_\square^T$), defined in MetaRocq's `ExAst`.

Peregrine wraps both in a single Rocq inductive `PAst` that tags the variant.

[`PAst` definition](/theories/PAst.v)
```coq
Definition typed_env := ExAst.global_env.
Definition untyped_env := EAst.global_context.

Inductive PAst :=
| Untyped : untyped_env -> option EAst.term -> PAst
| Typed : typed_env -> option EAst.term -> PAst.
```

Both ASTs consist of an environment of constant- and inductive-declarations, and an optional term representing the program's main function. When the optional term is `None` the program is treated as a library (no entry point); for backends that always need a term the missing term is replaced internally by `tBox`.

```
(Untyped (...env...) (Some (...term...)))
(Typed   (...env...) None)
```

The serializers/deserializers for `PAst` live in [SerializePAst.v](/theories/serialization/SerializePAst.v) and [DeserializePAst.v](/theories/serialization/DeserializePAst.v). They delegate to [SerializeEAst.v](/theories/serialization/SerializeEAst.v) and [SerializeExAst.v](/theories/serialization/SerializeExAst.v) for the underlying environments, to [SerializeCommon.v](/theories/serialization/SerializeCommon.v) for shared names/idents/kernames, and to [SerializePrimitives.v](/theories/serialization/SerializePrimitives.v) for `tPrim` payloads.

### Shared building blocks

The following appear inside both ASTs and inside the configuration file.

* `ident` — a bare string atom.
* `name` — `nAnon` for the anonymous name, `(nNamed <ident>)` otherwise.
* `dirpath` — a list of `ident`s (in reverse order, as in MetaRocq).
* `modpath` — one of
  * `(MPfile <dirpath>)`
  * `(MPbound <dirpath> <ident> <nat>)`
  * `(MPdot <modpath> <ident>)`
* `kername` — a pair `(<modpath> . <ident>)`.
* `inductive` — `(inductive <kername> <nat>)`; the `nat` selects the body inside a mutual block.
* `projection` — `(projection <inductive> <npars> <arg>)`.
* `recursivity_kind` — atom: `Finite`, `CoFinite`, or `BiFinite`.
* `allowed_eliminations` — atom: `IntoSProp`, `IntoPropSProp`, `IntoSetPropSProp`, or `IntoAny`.

### Primitives

`tPrim` payloads (defined in `EPrimitive`) are serialised as `(<tag> <value>)`:

* `(primInt <int>)`
* `(primFloat <float>)`
* `(primString <string>)`
* `(primArray (array_model <default> <values>))`

### Untyped $\lambda_\square$ AST

A `program` is a pair `(<global_declarations> . <term>)`. `global_declarations` is a list of `(<kername> . <global_decl>)` pairs.

A `global_decl` is one of:

* `(ConstantDecl (constant_body <option term>))` — the optional body is `None` for axioms.
* `(InductiveDecl (mutual_inductive_body <recursivity_kind> <npars> <ind_bodies>))`.

Each `one_inductive_body` is:
```
(one_inductive_body <ind_name> <ind_propositional> <ind_kelim> <ind_ctors> <ind_projs>)
```
with `ind_ctors` a list of `(constructor_body <cstr_name> <cstr_nargs>)` and `ind_projs` a list of `(projection_body <proj_name>)`.

A `term` is one of the following (matching the constructors of `EAst.term`):
```
tBox
(tRel       <nat>)
(tVar       <ident>)
(tEvar      <nat> (<term> ...))
(tLambda    <name> <term>)
(tLetIn     <name> <term> <term>)
(tApp       <term> <term>)
(tConst     <kername>)
(tConstruct <inductive> <nat> (<term> ...))
(tCase      (<inductive> . <npars>) <term> ((<bcontext> . <bbody>) ...))
(tProj      <projection> <term>)
(tFix       ((def <name> <term> <rarg>) ...) <nat>)
(tCoFix     ((def <name> <term> <rarg>) ...) <nat>)
(tPrim      <prim_val>)
(tLazy      <term>)
(tForce     <term>)
```

`tEvar`, `tConstruct`, `tFix`/`tCoFix` carry plain lists in their argument positions (the `(...)` may itself be empty for nullary cases).

### Typed $\lambda_\square^T$ AST

A typed environment is a list of `(<kername> <has_deps> <global_decl>)` triples where `<has_deps>` is a boolean (the extra field added by `ExAst.global_env`).

`global_decl` in the typed setting is one of:

* `(ConstantDecl (constant_body (<list name> . <box_type>) <option term>))` — the first component of the type pair is the list of type variables binding `TVar` occurrences in `box_type`.
* `(InductiveDecl (mutual_inductive_body <recursivity_kind> <npars> <ind_bodies>))`.
* `(TypeAliasDecl <option (<list type_var_info> . <box_type>)>)` — `None` means an opaque alias.

A `box_type` is one of:
```
TBox
TAny
(TArr   <box_type> <box_type>)
(TApp   <box_type> <box_type>)
(TVar   <nat>)
(TInd   <inductive>)
(TConst <kername>)
```

`type_var_info`:
```
(type_var_info <tvar_name> <tvar_is_logical> <tvar_is_arity> <tvar_is_sort>)
```

A typed `one_inductive_body` adds the type-variable context and per-constructor argument typing:
```
(one_inductive_body
  <ind_name>
  <ind_propositional>
  <ind_kelim>
  (<type_var_info> ...)
  ((<ident> (<name> . <box_type>) ... <nat>) ...)   ; ind_ctors
  ((<ident> . <box_type>) ...))                     ; ind_projs
```
The trailing `nat` in each constructor entry is the original constructor arity (kept around so that the dearger can match against MetaRocq's `erases_one_inductive_body`).

Terms in `Typed` ASTs use exactly the same `EAst.term` grammar as the untyped case; only the environment carries typing information.

## Configuration

The configuration file is a single S-expression of type `config` (defined in [Config.v](/theories/Config.v)). The CLI also accepts additional *attribute* files of type `attributes_config` via `--attributes`; their `inlinings_opt`, `const_remappings_opt`, `ind_remappings_opt`, `cstr_reorders_opt` and `custom_attributes_opt` lists are concatenated onto the corresponding fields of the main config by `merge_attributes_config`.

When the configuration is supplied as an S-expression file it is parsed at the `config'` ("optional") layer defined in [ConfigUtils.v](/theories/ConfigUtils.v), where every defaultable field is wrapped in `option`, and then materialised via `mk_config`. All omitted fields are filled from the backend-specific defaults (`default_rust_config`, `default_elm_config`, `default_c_config`, `default_wasm_config`, `default_ocaml_config`, `default_cakeml_config`, `default_eval_config`, `default_ast_config`). Wherever a field below is "optional" this is the mechanism: send `None` to take the default, or `(Some <value>)` to override.

### General configuration

A `config` is a 7-element record:

```
(config
  <backend_config>
  <erasure_phases>            ; or None at the optional layer
  <inlinings>
  <constant_remappings>
  <inductive_remappings>
  <inductives_mapping>        ; constructor reordering
  <custom_attributes>)
```

Field by field:

* `backend_opts` (`backend_config`) — selects the backend and its options; see below.

* `erasure_opts` (`erasure_phases`) — toggles the optional erasure passes. The seven fields are
  ```
  (erasure_phases
    <implement_box>
    <implement_lazy>
    <cofix_to_laxy>
    <betared>
    <unboxing>
    <dearg_ctors>
    <dearg_consts>)
  ```
  All booleans. Each backend declares an `<name>_phases : erasure_phases_config` value (see [theories/backends/](/theories/backends/)). For each phase the backend marks it `Required`, `Incompatible`, or `(Compatible <default>)`; `Required`/`Incompatible` *enforce* the value (the user's choice is ignored), and `Compatible` uses the user's value when present and otherwise the declared default. When the whole `erasure_opts` field is `None`, every phase takes its declared default.

* `inlinings_opts` (`inlinings`) — a list of `kername`s; constants in this list are inlined by the typed-erasure pass.

* `const_remappings_opts` (`constant_remappings`) — a list of `(<kername> <remapped_constant>)` pairs (see below).

* `ind_remappings_opts` (`inductive_remappings`) — a list of `remap_inductive`s (see below).

* `cstr_reorders_opts` (`inductives_mapping`) — a list of constructor-reorder entries from MetaRocq:
  ```
  (inductive_mapping <kername> <string> <list nat>)
  ```
  Reorders the constructors of the given inductive according to the permutation, and supplies a fresh print name.

* `custom_attributes_opts` (`custom_attributes`) — a list of `(<kername> . <string>)` pairs. Used by the Rust backend to override the default derive attribute (`#[derive(Debug, Clone)]`) on a per-inductive basis.

#### Remappings

`remapped_constant`:
```
(remapped_constant
  <option string>   ; re_const_ext   — name of the external module/library, if any
  <nat>             ; re_const_arity
  <bool>            ; re_const_gc    — needs GC access (C/Wasm primitives)
  <bool>            ; re_const_inl   — inline instead of generating a call
  <string>)         ; re_const_s     — what to remap the constant to
```

`remapped_inductive` (used inside `StringIndRemap`):
```
(remapped_inductive
  <string>          ; re_ind_name
  (<string> ...)    ; re_ind_ctors  — constructor function names, in order
  <option string>)  ; re_ind_match  — eliminator, when the target is not an inductive
```

`remap_inductive` is a tagged union:
```
(KnIndRemap     <kername>   ((extract_inductive <list string> <option string>) ...))
(StringIndRemap <inductive> <remapped_inductive>)
```
`KnIndRemap` targets untyped backends (delegates to MetaRocq's `EProgram.extract_inductive`), `StringIndRemap` targets typed backends.

#### Attribute files

The `attributes_config` payload accepted via `--attributes` is the 5-element subset of `config` that can be merged across files:
```
(attributes_config
  <inlinings>
  <constant_remappings>
  <inductive_remappings>
  <inductives_mapping>
  <custom_attributes>)
```

### Backend configuration

`backend_config` is a tagged union selecting which backend to run:

```
(Rust   <rust_config>)
(Elm    <elm_config>)
(C      <c_config>)
(Wasm   <wasm_config>)
(OCaml  <ocaml_config>)
(CakeML <cakeml_config>)
(CatCrypt <catcrypt_config>)
(Eval   <eval_config>)
(AST    <ast_config>)
```

The `c_config`, `wasm_config`, and the `copts` field of `eval_config` all share the same underlying `certirocq_config` record, since they all drive the CertiRocq pipeline. The defaults below are the values used when a field is omitted in the optional form.

#### Rust (`rust_config`)
```
(rust_config
  <rust_preamble_top>        ; ""
  <rust_preamble_program>    ; ""
  <rust_term_box_symbol>     ; "()"
  <rust_type_box_symbol>     ; "()"
  <rust_any_type_symbol>     ; "()"
  <rust_print_full_names>    ; true
  <rust_default_attributes>) ; "#[derive(Debug, Clone)]"
```
* `rust_preamble_top` is appended to the fixed module-level preamble (allow-lints + `hint_app` helper).
* `rust_preamble_program` is appended to the per-program preamble (the bumpalo allocator and `closure` helpers).
* The three `*_box_symbol`/`*_any_type_symbol` strings are used by the typed printer for erased terms, erased types, and `Any` types respectively.
* `rust_print_full_names` toggles fully-qualified printing of MetaRocq names.
* `rust_default_attributes` is the derive attribute placed in front of each generated `enum`/`struct`, unless overridden by a matching entry in `custom_attributes_opts`.

#### Elm (`elm_config`)
```
(elm_config
  <elm_preamble>           ; ""
  <elm_module_name>        ; None — defaults to the input file's basename
  <elm_term_box_symbol>    ; "()"
  <elm_type_box_symbol>    ; "()"
  <elm_any_type_symbol>    ; "()"
  <elm_false_elim_def>     ; "false_rec ()"
  <elm_print_full_names>)  ; true
```
The generated module starts with `module <elm_module_name> exposing (..)` followed by `elm_preamble` and `elm_false_elim_def`.

#### C / Wasm (`certirocq_config`)
```
(certirocq_config
  <direct>     ; true   — use the direct (ANF) pipeline
  <c_args>     ; 5      — number of C arguments (for CertiRocq)
  <o_level>    ; 0      — optimisation level
  <anf_conf>   ; 0      — ANF pipeline configuration
  <prefix>     ; ""     — prefix prepended to generated FFI symbols
  <body_name>) ; "body" — name of the top-level function
```
The C and Wasm backends use this record verbatim. The C backend additionally selects between `gc_stack.h` (when `direct = true`) and `gc.h` (when `direct = false`) and prepends the GC header to the list of `#include`s.

#### OCaml (`ocaml_config`)
```
(ocaml_config <program_type>)
```
`program_type` is one of
```
Standalone
(Shared_lib <module-name> <reexports>)
```
and is forwarded to the Malfunction printer. Default: `Standalone`.

#### CakeML (`cakeml_config`)
`cakeml_config` is `unit`, serialized as the empty list `()`. CakeML extraction has no user-tunable fields at present.

#### Eval (`eval_config`)
```
(eval_config
  <copts>     ; certirocq_config, defaulting to the C/Wasm defaults
  <fuel>      ; 2^14
  <eval_anf>) ; true  — evaluate the ANF program; false uses the LambdaBoxMut evaluator
```
The `eval` command runs the program in-process using CertiRocq's evaluator (after the relevant prefix of the C pipeline) and prints its result to stdout. `fuel` bounds the number of reduction steps before giving up.

#### AST (`ast_config`)
```
(ast_config <ast_type>)
```
`ast_type` selects which intermediate representation to dump, and (where applicable) carries the CertiRocq options needed to produce it:
```
LambdaBox                                    ; untyped lambda box (PAst)
LambdaBoxTyped                               ; typed lambda box (PAst)
(LambdaBoxMut   <certirocq_config>)          ; CertiRocq's L1g
(LambdaBoxLocal <certirocq_config>)          ; CertiRocq's L4
(LambdaANF      <certirocq_config>)          ; LambdaANF after the standard pipeline
(LambdaANFC     <certirocq_config>)          ; LambdaANF without the final cleanup pass
```
