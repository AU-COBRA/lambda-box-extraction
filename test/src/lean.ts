import { execSync } from "child_process";
import { ExecResult, ProgramType, SimpleType, TestCase } from "./types";
import { appendFileSync, copyFileSync, cpSync, existsSync, mkdirSync, readFileSync, writeFileSync } from "fs";
import path from "path";

const template_dir = path.join(process.cwd(), "src/lean/");
const runtime_src = path.join(process.cwd(), "..", "lean", "Peregrine", "Runtime.lean");

// Set up a fresh Lake project in tmpdir that the Lean test driver
// can build & run generated programs against.  Mirrors prepare_cargo
// / prepare_elm_project.  Returns the project root directory.
export function prepare_lean_project(tmpdir: string, timeout: number): string {
  const projectdir = path.join(tmpdir, "lean/");
  if (!existsSync(projectdir)) mkdirSync(projectdir, { recursive: true });

  // Copy static template files (lakefile.toml, lean-toolchain).
  cpSync(template_dir, projectdir, { recursive: true });

  // Pull the live Runtime from the repo root so we always test the
  // current backend's runtime support, not a snapshot.
  const runtime_dst_dir = path.join(projectdir, "Peregrine");
  if (!existsSync(runtime_dst_dir)) mkdirSync(runtime_dst_dir, { recursive: true });
  copyFileSync(runtime_src, path.join(runtime_dst_dir, "Runtime.lean"));

  // Warm the Lake cache so per-test runs don't each rebuild Runtime.
  execSync("lake build Peregrine", { stdio: "pipe", timeout: timeout, cwd: projectdir });

  return projectdir;
}

// Build a Lean expression that prints an `Obj` of `type` via the
// universal printers in Peregrine.TestPrinters.  Those printers cast
// the Obj to canonical inductives (PBool/PNat/PList) whose runtime
// layout matches any source inductive with the same constructor
// arities in the same order — Bool first/then true, Nat zero/then
// succ, List nil/then cons — so they work regardless of which
// frontend produced the .ast (rocq, agda, lean, ...).
function pp_call(type: ProgramType): string | undefined {
  if (type === SimpleType.Bool) return "Peregrine.pp_bool";
  if (type === SimpleType.Nat) return "Peregrine.pp_nat";
  if (type === SimpleType.UInt63) return undefined;
  if (type === SimpleType.Other) return undefined;
  if (typeof type === "number") return undefined;
  switch (type.type) {
    case "list": {
      const a = pp_call(type.a_t);
      return a === undefined ? undefined : `(Peregrine.pp_list ${a})`;
    }
    case "option":
    case "prod":
      // No universal printers for these yet; treat as opaque so the
      // runner just exercises evaluation without checking the result.
      return undefined;
  }
}

// Splice an `import Peregrine.TestPrinters` next to the generated
// file's existing imports, and append a `main` that prints the
// test's entry-point value in the s-expression format
// `expected_output[0]` already encodes.  Imports must precede all
// other declarations in Lean, so we cannot simply `appendFileSync`
// the import.
function append_main(file: string, test: TestCase) {
  const printer = pp_call(test.output_type);
  const original = readFileSync(file, "utf8");

  // Nullary constants are emitted as `Thunk Obj` (evaluated lazily on
  // first `.get`, inside `main`, rather than at module init); force
  // such an entry point with `.get`. A function-valued entry stays as
  // is.
  const isThunk = new RegExp(`def\\s+${test.main}\\s*:\\s*Thunk\\b`).test(original);
  const target = isThunk ? `Generated.${test.main}.get` : `Generated.${test.main}`;

  const main_body = printer === undefined
    ? `let _ := ${target}; pure ()`
    : `IO.println (${printer} ${target})`;

  const patched = original.replace(
    "import Peregrine.Runtime",
    "import Peregrine.Runtime\nimport Peregrine.TestPrinters",
  );

  writeFileSync(file, patched + `

unsafe def main : IO Unit :=
  ${main_body}
`);
}

export function run_lean(file: string, projectdir: string, test: TestCase, timeout: number): ExecResult {
  try {
    append_main(file, test);

    // Build and run a NATIVE executable (compiled mode).  Compiled Lean
    // specializes refcount ops and evaluates nullary constants at module
    // init — behaviors the interpreter (`lake env lean --run`) never
    // exercises, and which previously hid a whole class of backend bugs
    // (unchecked RC on scalar `Obj`, init-time deep recursion).  We copy
    // the generated program to the exe root module `Main.lean`, build the
    // `testexe` target, and run the binary.
    const mainFile = path.join(projectdir, "Main.lean");
    copyFileSync(file, mainFile);

    const start_main = Date.now();
    execSync(`lake build testexe`, {
      stdio: "pipe",
      timeout: timeout,
      cwd: projectdir,
      encoding: "utf8",
    });
    const res = execSync(`./.lake/build/bin/testexe`, {
      stdio: "pipe",
      timeout: timeout,
      cwd: projectdir,
      encoding: "utf8",
    }).trim();
    const stop_main = Date.now();
    const time_main = stop_main - start_main;

    if (test.expected_output === undefined || test.output_type === SimpleType.Other) {
      return { type: "success", time: time_main };
    }

    if (res !== test.expected_output[0]) {
      return { type: "error", reason: "incorrect result", actual: res, expected: test.expected_output[0] };
    }

    return { type: "success", time: time_main };
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    const stderr = e.stderr ? e.stderr.toString("utf8") : "";
    const stdout = e.stdout ? e.stdout.toString("utf8") : "";
    return { type: "error", reason: "compile error", compiler: "lake", code: e.status, error: stderr || stdout };
  }
}
