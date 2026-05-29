import { execSync } from "child_process";
import { ExecFailure, ProgramType, SimpleType, TestCase } from "./types";
import { exit } from "process";
import { print_line, replace_ext } from "./utils";

var counter = 0;

// Generate printing function for a given type
// Returns two elements, the first being a list of function and external declarations,
// the second element is the name of the printing function
function get_pp_fun(type: ProgramType): [string[], string] {
  switch (type) {
    case SimpleType.Bool:
      counter += 1;
      return [
        ["extern void print_CertiRocq_bool(value);",
          `void pp_${counter}(value val) { print_CertiRocq_bool(val); }`
        ],
        `pp_${counter}`
      ];
    case SimpleType.Nat:
      counter += 1;
      return [
        ["extern void print_Coq_Init_Datatypes_nat(value);",
          `void pp_${counter}(value val) { print_Coq_Init_Datatypes_nat(val); }`
        ],
        `pp_${counter}`
      ];
    case SimpleType.UInt63:
      // TODO
      break;
    case SimpleType.Other:
      return [
        [],
        ""
      ]
    default:
      switch (type.type) {
        case "list":
          var a = get_pp_fun(type.a_t);
          counter += 1;
          return [
            ["extern void print_Coq_Init_Datatypes_list(value, void (*)(value));",
              ...a[0],
              `void pp_${counter}(value val) { print_Coq_Init_Datatypes_list(val, ${a[1]}); }`
            ],
            `pp_${counter}`
          ];
        case "option":
          var a = get_pp_fun(type.a_t);
          counter += 1;
          return [
            ["extern void print_Coq_Init_Datatypes_option(value, void (*)(value));",
              ...a[0],
              `void pp_${counter}(value val) { print_Coq_Init_Datatypes_option(val, ${a[1]}); }`
            ],
            `pp_${counter}`
          ];
        case "prod":
          var a = get_pp_fun(type.a_t);
          var b = get_pp_fun(type.b_t);
          counter += 1;
          return [
            ["extern void print_Coq_Init_Datatypes_prod(value, void (*)(value), void (*)(value));",
              ...a[0],
              ...b[0],
              `void pp_${counter}(value val) { print_Coq_Init_Datatypes_prod(val, ${a[1]}, ${b[1]}); }`
            ],
            `pp_${counter}`
          ];
        default:
          break;
      }
      break;
  }
}

// Generates a main file that
// 1) sets up garbage collector;
// 2) runs the program
// 3) pretty prints the return value as S-expression
function get_c_main(test: TestCase): string {
  counter = 0;
  const pp_fun = get_pp_fun(test.output_type);
  const pp_def = pp_fun[0].join("\n");
  const pp = `${pp_fun[1]}(val);\nprintf("\\n");`;
  const content =
    `#include <stdio.h>
#include <stdlib.h>
#include "gc_stack.h"
#include <time.h>

extern value body(struct thread_info *);
${pp_def}

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;

  tinfo = make_tinfo();
  val = body(tinfo);
  ${pp}

  return 0;
}
`;
  return content;
}

// Compile a C file using gcc
export function compile_c(file: string, test: TestCase, timeout: number): string | ExecFailure {
  const f_out = replace_ext(file, ".o");
  const f_glue = "src/c/glue.c";
  // GCC 14+ promotes -Wint-conversion / -Wincompatible-pointer-types /
  // -Wimplicit-function-declaration to errors by default; the legacy
  // CertiRocq glue.c relies on the older permissive behaviour, so
  // downgrade them back to warnings (which -w then silences).
  const cmd = `gcc -o ${f_out} -w -Wno-error=int-conversion -Wno-error=incompatible-pointer-types -Wno-error=implicit-function-declaration -O2 -fomit-frame-pointer -I\${C_RUNTIME_PATH} \${C_RUNTIME_PATH}/gc_stack.c ${file} ${f_glue} -xc -`;
  // Generate main file
  const main = get_c_main(test);

  try {
    // Run gcc, main file is given through stdin
    execSync(cmd, { stdio: "pipe", timeout: timeout, input: main });
    return f_out;
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "compile error", compiler: "gcc", code: e.status, error: e.stderr.toString('utf8') };
  }
}

// Set environment variables used when compiling C code
export async function set_c_env(timeout) {
  const cmd = `coqc -where`;

  try {
    const path = execSync(cmd, { stdio: "pipe", timeout: timeout, encoding: 'utf8' });
    process.env.C_RUNTIME_PATH = path.trim() + "/user-contrib/CertiRocq/Plugin/runtime/";
  } catch (e) {
    print_line("error: could not set environment");
    exit(1);
  }
}
