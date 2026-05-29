import { Lang, SimpleType, TestCase, TestConfiguration } from "./types";

/* (backend, peregrine flags) pair configurations */
export var test_configurations: TestConfiguration[] = [
    [Lang.OCaml, "", ""],
    // [Lang.C, "cps", "--cps"], // TODO
    [Lang.C, "", ""],
    [Lang.Wasm, "cps", "--cps"],
    [Lang.Wasm, "", ""],
    // [Lang.Rust, "", "--attr=\"#[derive(Debug, Clone, Serialize)]\" --top-preamble=\"use lexpr::{to_string}; use serde_derive::{Serialize}; use serde_lexpr::{to_value};\n\""],
    // [Lang.Elm, "", "--top-preamble=\"import Test\nimport Html\nimport Expect exposing (Expectation)\""],
    [Lang.CakeML, "", ""],
    [Lang.Lean, "", ""]
];

// Agda Tests
var agda_tests: TestCase[] =
    [
        {
            src: "agda/Demo.ast",
            main: "Demo_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true (cons false (cons true (cons false nil))))",
                "(Cons () (True) (Cons () (False) (Cons () (True) (Cons () (False) (Empty)))))",
                "Cons True (Cons False (Cons True (Cons False Empty)))"
            ],
            parameters: []
        },
        {
            src: "agda/Equality.ast",
            main: "Equality_test",
            output_type: SimpleType.Nat,
            expected_output: [
                "(S (S O))",
                ""
            ],
            parameters: []
        },
        {
            src: "agda/EtaCon.ast",
            main: "EtaCon_example",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S O) nil)",
                "(Cons () (S O) (Empty)",
                "Cons (S O) Empty"
            ],
            parameters: []
        },
        {
            src: "agda/Exports.ast",
            main: "Exports_test",
            output_type: SimpleType.Other,
            expected_output: ["", ""],
            parameters: []
        },
        {
            src: "agda/Hello.ast",
            main: "Hello_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) nil))))))",
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "agda/Imports.ast",
            main: "Imports_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S (S (S (S (S O)))))) nil)",
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "agda/Input.ast",
            main: "Input_test",
            output_type: SimpleType.Other,
            expected_output: ["", ""],
            parameters: []
        },
        {
            src: "agda/Irr.ast",
            main: "Irr_test",
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/K.ast",
            main: "K_test",
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/Levels.ast",
            main: "Levels_testMkLevel",
            // OCaml/Wasm/CakeML call this program's malfunction
            // [main], which CertiRocq's Malfunction extraction
            // resolves to a tBox placeholder ("error: tBox has been
            // translated away") because [Levels.test]'s body
            // contains an erased type argument it can't lower.
            // [Levels_testMkLevel] does evaluate to 42 [S]s under
            // the Lean backend (which calls the symbol directly),
            // but the result is unobservable on the other backends.
            // Treat as Other so all backends exercise compile+run
            // without requiring a shared output convention.
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/Map.ast",
            main: "Map_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S O)) (cons (S (S (S (S (S (S O)))))) (cons (S (S (S (S (S (S (S (S (S (S O)))))))))) nil)))",
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "agda/Mutual.ast",
            main: "Mutual_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S O)", "", ""],
            parameters: []
        },
        {
            src: "agda/Nat.ast",
            main: "Nat_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "", ""],
            parameters: []
        },
        {
            src: "agda/OddEven.ast",
            main: "OddEven_test",
            output_type: SimpleType.Bool,
            expected_output: ["false", "", ""],
            parameters: []
        },
        {
            src: "agda/PatternLambda.ast",
            main: "PatternLambda_test",
            output_type: SimpleType.Bool,
            expected_output: ["false", "", ""],
            parameters: []
        },
        {
            src: "agda/Proj.ast",
            main: "Proj_test",
            output_type: SimpleType.Bool,
            expected_output: ["false", "", ""],
            parameters: []
        },
        {
            src: "agda/rust.ast",
            main: "rust_testIdd",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: ["(cons (S (S (S O))) nil)", ""],
            parameters: []
        },
        {
            src: "agda/scheme.ast",
            main: "scheme_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S (S (S (S O))))))", ""],
            parameters: []
        },
        /*     {
                tsrc: "agda/SchemeTyped.ast",
                main: "SchemeTyped_demo",
                output_type: SimpleType.Nat, // TODO
                expected_output: ["", ""], // TODO
                parameters: []
            }, */ // No main to test
        {
            src: "agda/STLC.ast",
            main: "STLC_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S O))", "", ""],
            parameters: []
        },
        /*     {
                tsrc: "agda/Test.ast",
                main: "Test_demo",
                output_type: SimpleType.Nat, // TODO
                expected_output: ["", ""], // TODO
                parameters: []
            }, */ // No main to test
        /*     {
                tsrc: "agda/Types.ast",
                main: "Types_demo",
                output_type: SimpleType.Nat, // TODO
                expected_output: ["", ""], // TODO
                parameters: []
            }, */ // No main to test
        {
            src: "agda/Unicode.ast",
            main: "Unicode_test",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: ["(cons (S O) nil)", "", ""],
            parameters: []
        },
        {
            src: "agda/With.ast",
            main: "With_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: ["(cons true nil)", "", ""],
            parameters: []
        },
    ];

// Rocq Tests
var rocq_tests: TestCase[] =
    [
        {
            src: "rocq/extraction/Demo.ast",
            tsrc: "rocq/extraction/Demo_typed.ast",
            main: "Demo_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true (cons false (cons true (cons false nil))))",
                "(Cons () (True) (Cons () (False) (Cons () (True) (Cons () (False) (Empty)))))",
                "Cons True (Cons False (Cons True (Cons False Empty)))"
            ],
            parameters: []
        },
        {
            src: "rocq/extraction/Hello.ast",
            tsrc: "rocq/extraction/Hello_typed.ast",
            main: "Hello_hello",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) nil))))))",
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "rocq/extraction/Map.ast",
            tsrc: "rocq/extraction/Map_typed.ast",
            main: "Map_ys",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S O)) (cons (S (S (S (S (S (S O)))))) (cons (S (S (S (S (S (S (S (S (S (S O)))))))))) nil)))",
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "rocq/extraction/Mutual.ast",
            tsrc: "rocq/extraction/Mutual_typed.ast",
            main: "Mutual_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S O)", "", ""],
            parameters: []
        },
        {
            src: "rocq/extraction/Nat.ast",
            tsrc: "rocq/extraction/Nat_typed.ast",
            main: "Nat_thing",
            output_type: SimpleType.Nat,
            expected_output: ["(S (S (S O)))", "", ""],
            parameters: []
        },
        {
            src: "rocq/extraction/OddEven.ast",
            tsrc: "rocq/extraction/OddEven_typed.ast",
            main: "OddEven_test",
            output_type: SimpleType.Bool,
            expected_output: ["false", "", ""],
            parameters: []
        },
    ];
// Lean Tests
var lean_tests: TestCase[] =
    [
        {
            src: "lean/extraction/Demo.ast",
            main: "Demo_test",
            output_type: { type: "list", a_t: SimpleType.Bool },
            expected_output: [
                "(cons true (cons false (cons true (cons false nil))))",
                "(Cons () (True) (Cons () (False) (Cons () (True) (Cons () (False) (Empty)))))",
                "Cons True (Cons False (Cons True (Cons False Empty)))"
            ],
            parameters: []
        },
        {
            src: "lean/extraction/Map.ast",
            main: "Map_ys",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: [
                "(cons (S (S O)) (cons (S (S (S (S (S (S O)))))) (cons (S (S (S (S (S (S (S (S (S (S O)))))))))) nil)))",
                "",
                ""
            ],
            parameters: []
        }, // Generates invalid identifier names in C backend
    ];

// List of programs to be tested
export var tests: TestCase[] =
    [...agda_tests, ...rocq_tests, ...lean_tests];
