import { execSync } from "child_process";
import { existsSync, mkdirSync, readFileSync, writeFileSync } from "fs";
import path from "path";
import { ExecResult } from "./types";

// A CatCrypt backend test fixture. Unlike the generic `TestCase` used by
// the other (printing-based) backends, CatCrypt compiles a straight-line
// int-arithmetic program to a Lean 4 `NamedSSA` value rather than an
// executable that prints an s-expression, so it needs its own shape:
// decimal arguments/expected output (one `BitVec 64` per SSA input
// level) instead of `ProgramType`-typed parameters.
export type CatCryptTestCase = {
  // Human-readable fixture name. Used for the golden file
  // (`test/catcrypt/golden/<name>.lean`) and the rendered cross-check
  // driver file name; should match the source constant's file, e.g.
  // "CatCryptAdd" for `test/rocq/theories/CatCryptAdd.v`.
  name: string;
  // Path (relative to `test/`) to the untyped .ast fixture.
  src: string;
  // Path (relative to `test/`) to the closed (zero-argument) variant of
  // the same fixture, if any, used for the layer-4 `peregrine eval`
  // differential. Omit for fixtures without a closed variant.
  closed_src?: string;
  // Lean def name to force via `--def-name` so it's known ahead of
  // compilation (rather than re-deriving Peregrine's default-naming
  // rule here).
  def: string;
  // `--namespace` override; when omitted the backend default
  // ("PeregrineGenerated", per wiring-plan.md) is assumed for the
  // driver's `open`.
  namespace?: string;
  // Decimal argument values, one per NamedSSA input level in order.
  arguments: string[];
  // Expected decimal `NamedSSA.eval` result.
  expected_output: string;
};

// An .ast fixture that CatCrypt must REJECT (inductives, recursion, ...
// are all outside the straight-line int-arithmetic fragment it compiles).
// A successful compile here is a test failure.
export type CatCryptRejectTestCase = {
  name: string;
  src: string;
};

const catcrypt_default_namespace = "PeregrineGenerated";

// Golden files live at test/catcrypt/golden/<name>.lean (test/ is cwd,
// mirrors how e.g. lean.ts resolves `src/lean/` off process.cwd()).
function golden_path(name: string): string {
  return path.join(process.cwd(), "catcrypt", "golden", `${name}.lean`);
}

// Layer 1: compare the generated .lean against the committed golden
// file. With UPDATE_GOLDEN=1, (re)write the golden file instead of
// comparing (record mode). A MISSING golden file outside of record mode
// is NOT silently treated as a pass — the driver has no backend output
// to trust yet, so it fails loudly with the recovery instructions.
function golden_check(name: string, generated: string): string | undefined {
  const gp = golden_path(name);

  if (process.env.UPDATE_GOLDEN === "1") {
    mkdirSync(path.dirname(gp), { recursive: true });
    writeFileSync(gp, generated);
    return undefined;
  }

  if (!existsSync(gp)) {
    return "golden missing, run with UPDATE_GOLDEN=1";
  }

  const golden = readFileSync(gp, "utf8");
  if (golden !== generated) {
    return `golden mismatch for ${name} (${gp}); rerun with UPDATE_GOLDEN=1 if this change is intentional`;
  }

  return undefined;
}

// Layer 2: structural sanity checks on the generated .lean text, parsed
// with regexes rather than a real Lean parser (the printer output shape
// is pinned by translation-design.md §5: `nInputs := N`, `retLevel := N`,
// and one `⟨op, [args]⟩` binding per line).
function structural_check(generated: string, test: CatCryptTestCase): string | undefined {
  const nInputsMatch = generated.match(/nInputs\s*:=\s*(\d+)/);
  if (nInputsMatch === null) {
    return "structural check: `nInputs := N` not found in generated .lean";
  }
  const nInputs = parseInt(nInputsMatch[1], 10);
  if (nInputs !== test.arguments.length) {
    return `structural check: nInputs=${nInputs} but fixture has ${test.arguments.length} argument(s)`;
  }

  const retLevelMatch = generated.match(/retLevel\s*:=\s*(\d+)/);
  if (retLevelMatch === null) {
    return "structural check: `retLevel := N` not found in generated .lean";
  }
  const retLevel = parseInt(retLevelMatch[1], 10);
  if (retLevel < nInputs) {
    return `structural check: retLevel=${retLevel} is below nInputs=${nInputs}`;
  }

  const bindingsCount = (generated.match(/⟨/g) ?? []).length;
  if (bindingsCount <= 0) {
    return "structural check: no `⟨op, [args]⟩` bindings found";
  }

  return undefined;
}

// Layer 3 gate: only attempt the CatCrypt cross-check (and, in turn, the
// layer-4 differential) when both a CatCrypt checkout and `lake` are
// available. CI never has CATCRYPT_DIR set, so this must degrade to
// "skip silently and successfully", never a failure.
function catcrypt_gate(): string | undefined {
  const dir = process.env.CATCRYPT_DIR;
  if (dir === undefined || dir === "" || !existsSync(dir)) {
    return undefined;
  }
  try {
    execSync("which lake", { stdio: "pipe" });
  } catch {
    return undefined;
  }
  return dir;
}

const driver_template_dir = path.join(process.cwd(), "src/catcrypt/");

// Elaborating the driver imports the CatCrypt spine (and, transitively,
// mathlib) from its .oleans. That is a few seconds warm but can be much
// slower cold, so the cross-check gets its own generous budget rather
// than the suite's 30s `compile_timeout`.
const catcrypt_lake_timeout = 600000;

function render_driver(program: string, ns: string, def: string, args: string[]): string {
  const tmpl = readFileSync(path.join(driver_template_dir, "Driver.lean.tmpl"), "utf8");
  const argsStr = args.map((a) => `(${a} : BitVec 64)`).join(", ");
  return tmpl
    .split("{{PROGRAM}}").join(program)
    .split("{{NS}}").join(ns)
    .split("{{DEF}}").join(def)
    .split("{{ARGS}}").join(argsStr)
    .split("{{NINPUTS}}").join(String(args.length));
}

// Run the rendered driver through `lake env lean --run` from inside the
// CatCrypt checkout and parse its two output lines
// (`BUILD_OK`/`BUILD_FAIL`, then the decimal eval result). `--run` (not
// a bare `lake env lean` with `#eval`) is what keeps stdout clean: an
// `#eval` reports through the message log, so every line would arrive
// prefixed with `<file>:<line>:<col>: info:`. Returns the decimal eval
// result on success, or an ExecResult describing the failure.
function run_cross_check(
  test: CatCryptTestCase,
  generated: string,
  ns: string,
  tmpdir: string,
  catcryptDir: string,
): string | ExecResult {
  const driverDir = path.join(tmpdir, "catcrypt/");
  if (!existsSync(driverDir)) mkdirSync(driverDir, { recursive: true });
  const driverFile = path.join(driverDir, `${test.name}Driver.lean`);

  writeFileSync(driverFile, render_driver(generated, ns, test.def, test.arguments));

  let out: string;
  try {
    out = execSync(`lake env lean --run ${driverFile}`, {
      stdio: "pipe",
      timeout: catcrypt_lake_timeout,
      cwd: catcryptDir,
      encoding: "utf8",
    });
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }
    const stderr = e.stderr ? e.stderr.toString("utf8") : "";
    const stdout = e.stdout ? e.stdout.toString("utf8") : "";
    return { type: "error", reason: "compile error", compiler: "lake env lean", code: e.status, error: stderr || stdout };
  }

  const lines = out.trim().split("\n").map((l) => l.trim()).filter((l) => l.length > 0);
  const [buildLine, evalLine] = lines;

  if (buildLine !== "BUILD_OK") {
    // BUILD_FAIL (ComBuilder.build rejected the NamedSSA) or
    // ARITY_MISMATCH (p.nInputs disagrees with the fixture's argument
    // count) — see the stdout contract in src/catcrypt/Driver.lean.tmpl.
    return { type: "error", reason: "runtime error", error: `CatCrypt driver did not report BUILD_OK for ${test.name}:\n${out}` };
  }
  if (evalLine === undefined) {
    return { type: "error", reason: "runtime error", error: `CatCrypt driver produced no eval output for ${test.name}:\n${out}` };
  }
  if (evalLine === "EVAL_NONE") {
    return { type: "error", reason: "runtime error", error: `CatCrypt NamedSSA.eval returned none for ${test.name} (unsupported op or unresolved operand level)` };
  }
  if (evalLine !== test.expected_output) {
    return { type: "error", reason: "incorrect result", expected: test.expected_output, actual: evalLine };
  }

  return evalLine;
}

// Layer 4: differential vs `peregrine eval` on the fixture's closed
// (zero-argument) variant. Informational only — both values are printed
// regardless of outcome, and this only fails the test when both values
// parse cleanly as decimal integers AND disagree. Gated on the same
// CATCRYPT_DIR/lake availability as layer 3, since it compares against
// the layer-3 CatCrypt eval result.
//
// KNOWN LIMITATION: `peregrine eval` cannot currently run any of these
// fixtures — the interpreter has no realization for the PrimInt63
// axioms (`Axioms found, use Extract Constant to realize them in C:
// Corelib.Numbers.Cyclic.Int63.PrimInt63.add`, ...), so every closed
// fixture bails out during eval's own compile step. That is a missing
// eval feature, not a CatCrypt backend defect, so this layer degrades to
// an informational note instead of failing the suite. The correctness
// oracle meanwhile is `expected_output` (Rocq-verified) checked against
// CatCrypt's own `NamedSSA.eval` in layer 3.
function run_eval_differential(
  test: CatCryptTestCase,
  catcryptValue: string,
  peregrineCmd: string,
  exec_timeout: number,
  notes: string[],
): ExecResult | undefined {
  if (test.closed_src === undefined) return undefined;

  let out: string;
  try {
    out = execSync(`${peregrineCmd} eval ${test.closed_src}`, {
      stdio: "pipe",
      timeout: exec_timeout,
      encoding: "utf8",
    }).trim();
  } catch (e) {
    const detail = ((e.stdout ? e.stdout.toString("utf8") : "") + (e.stderr ? e.stderr.toString("utf8") : "")).trim();
    const primint = /PrimInt63|Axioms found/.test(detail);
    notes.push(
      `[skipped] eval differential for ${test.closed_src}: ` +
      (primint
        ? "peregrine eval does not support primitive ints (PrimInt63) yet"
        : `peregrine eval failed: ${detail.split("\n").join(" ")}`),
    );
    return undefined;
  }

  notes.push(`[informational] CatCrypt eval = ${catcryptValue}, peregrine eval = ${out}`);

  const a = Number.parseInt(catcryptValue, 10);
  const b = Number.parseInt(out, 10);
  const a_is_int = !Number.isNaN(a) && String(a) === catcryptValue;
  const b_is_int = !Number.isNaN(b) && String(b) === out;

  if (a_is_int && b_is_int && a !== b) {
    return { type: "error", reason: "incorrect result", expected: catcryptValue, actual: out };
  }

  return undefined;
}

// Run all four layers against an already-compiled CatCrypt fixture.
// `f_lean` is the .lean file `peregrine catcrypt` produced (via the
// generic `compile_box` helper in runner.ts); this function is only
// reached once that compile succeeded. Informational/skip notes are
// appended to `notes` rather than printed, so the caller can emit them
// after the test's own result line.
export function run_catcrypt(
  f_lean: string,
  test: CatCryptTestCase,
  tmpdir: string,
  peregrineCmd: string,
  exec_timeout: number,
  notes: string[],
): ExecResult {
  const start = Date.now();
  const generated = readFileSync(f_lean, "utf8");

  const golden_err = golden_check(test.name, generated);
  if (golden_err !== undefined) {
    return { type: "error", reason: "runtime error", error: golden_err };
  }

  const struct_err = structural_check(generated, test);
  if (struct_err !== undefined) {
    return { type: "error", reason: "runtime error", error: struct_err };
  }

  const catcryptDir = catcrypt_gate();
  if (catcryptDir !== undefined) {
    const ns = test.namespace ?? catcrypt_default_namespace;
    const cross = run_cross_check(test, generated, ns, tmpdir, catcryptDir);
    if (typeof cross !== "string") {
      // Layer 3 failed outright.
      return cross;
    }
    notes.push(`[cross-check] CatCrypt build OK, NamedSSA.eval = ${cross}`);

    const diff = run_eval_differential(test, cross, peregrineCmd, exec_timeout, notes);
    if (diff !== undefined) {
      return diff;
    }
  } else {
    notes.push("[skipped] CATCRYPT_DIR/lake not available; skipping CatCrypt cross-check and eval differential");
  }

  return { type: "success", time: Date.now() - start };
}
