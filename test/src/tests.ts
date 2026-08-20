import { Lang, SimpleType, TestCase, TestConfiguration } from "./types";
import { CatCryptRejectTestCase, CatCryptTestCase } from "./catcrypt";

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
    [Lang.CatCrypt, "", ""]
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
            main: "Exports_main",
            output_type: SimpleType.Other,
            expected_output: ["", ""],
            parameters: []
        },
        {
            src: "agda/Hello.ast",
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
            src: "agda/Imports.ast",
            main: "Imports_test2",
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
            main: "Input_main",
            output_type: SimpleType.Other,
            expected_output: ["", ""],
            parameters: []
        },
        {
            src: "agda/Irr.ast",
            main: "Irr_ys",
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/K.ast",
            main: "K_K",
            output_type: SimpleType.Other,
            expected_output: undefined,
            parameters: []
        },
        {
            src: "agda/Levels.ast",
            main: "Levels_testMkLevel",
            output_type: SimpleType.Nat,
            expected_output: [
                "(S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))",
                "",
                ""
            ],
            parameters: []
        },
        {
            src: "agda/Map.ast",
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
            src: "agda/Mutual.ast",
            main: "Mutual_test",
            output_type: SimpleType.Nat,
            expected_output: ["(S O)", "", ""],
            parameters: []
        },
        {
            src: "agda/Nat.ast",
            main: "Nat_thing",
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
            main: "Proj_second",
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
            main: "scheme_demo",
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
            main: "Unicode_main",
            output_type: { type: "list", a_t: SimpleType.Nat },
            expected_output: ["(cons (S O) nil)", "", ""],
            parameters: []
        },
        {
            src: "agda/With.ast",
            main: "With_ys",
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

// CatCrypt backend tests. These are NOT part of the `tests` list above:
// unlike the other backends, CatCrypt doesn't compile-and-run an
// s-expression-printing executable, it compiles a straight-line
// int-arithmetic fragment to a Lean 4 NamedSSA value, so it needs its
// own CatCryptTestCase shape and its own driver (test/src/catcrypt.ts).
// Fixture sources: test/rocq/theories/CatCrypt*.v.
export var catcrypt_tests: CatCryptTestCase[] =
    [
        {
            // add3 x y z = x + y + z
            // add3 5 7 9 = 5 + 7 + 9 = 21
            name: "CatCryptAdd",
            src: "rocq/extraction/CatCryptAdd.ast",
            closed_src: "rocq/extraction/CatCryptAddClosed.ast",
            def: "add3",
            arguments: ["5", "7", "9"],
            expected_output: "21",
        },
        {
            // addc x = x + 251
            // addc 5 = 5 + 251 = 256
            name: "CatCryptConst",
            src: "rocq/extraction/CatCryptConst.ast",
            closed_src: "rocq/extraction/CatCryptConstClosed.ast",
            def: "addc",
            arguments: ["5"],
            expected_output: "256",
        },
        {
            // sq2 x y = let a := x * y in a + a
            // sq2 3 4 = let a := 3 * 4 = 12 in a + a = 24
            name: "CatCryptShare",
            src: "rocq/extraction/CatCryptShare.ast",
            closed_src: "rocq/extraction/CatCryptShareClosed.ast",
            def: "sq2",
            arguments: ["3", "4"],
            expected_output: "24",
        },
        {
            // mix x y = (x >> 3) land (y * y)
            // mix 40 5 = (40 >> 3) land (5 * 5) = 5 land 25
            //   40 = 0b0101000, 40 >> 3 = 0b00101 = 5
            //   5 * 5 = 25    = 0b11001
            //   5 land 25     = 0b00101 land 0b11001 = 0b00001 = 1
            name: "CatCryptShift",
            src: "rocq/extraction/CatCryptShift.ast",
            closed_src: "rocq/extraction/CatCryptShiftClosed.ast",
            def: "mix",
            arguments: ["40", "5"],
            expected_output: "1",
        },
    ];

// .ast fixtures that use inductives/recursion and so must be REJECTED by
// the CatCrypt backend (straight-line int arithmetic only). Reused from
// the existing Rocq fixtures rather than adding new sources: Map.ast
// (list map, an inductive-heavy program) and OddEven.ast (mutual
// recursion). A successful compile of either is a test failure.
export var catcrypt_reject_tests: CatCryptRejectTestCase[] =
    [
        {
            name: "Map",
            src: "rocq/extraction/Map.ast",
        },
        {
            name: "OddEven",
            src: "rocq/extraction/OddEven.ast",
        },
    ];
