import { execSync } from "child_process";
import { ExecResult, ProgramType, SimpleType, TestCase } from "./types";
import { cpSync, existsSync, mkdirSync, readFileSync, writeFileSync } from "fs";
import path from "path";

const template_dir = path.join(process.cwd(), "src/fsharp/");

// Keep the SDK quiet and reproducible across machines.
const dotnet_env = { ...process.env, DOTNET_CLI_TELEMETRY_OPTOUT: "1", DOTNET_NOLOGO: "1" };

// Set up a fresh .NET project in tmpdir that the F# test driver can
// build & run generated programs against.  Mirrors prepare_cargo /
// prepare_elm_project.  Returns the project root directory.
export function prepare_fsharp_project(tmpdir: string, timeout: number): string {
  const projectdir = path.join(tmpdir, "fsharp/");
  if (!existsSync(projectdir)) mkdirSync(projectdir, { recursive: true });

  // Copy static template files (fsharp_tests.fsproj, TestPrinters.fs,
  // and the stub Main.fs that each test overwrites).
  cpSync(template_dir, projectdir, { recursive: true });

  // Warm build: performs the one (offline, library-packs-backed) restore
  // and compiles TestPrinters + stub Main so per-test builds are incremental.
  execSync("dotnet build -c Release --nologo -v:q", {
    stdio: "pipe",
    timeout: timeout,
    cwd: projectdir,
    env: dotnet_env,
  });

  return projectdir;
}

// Build an F# expression that prints an extracted value of `type` via
// the universal printers in TestPrinters.  Those printers read union
// case tags and fields by reflection, so they match any source
// inductive with the same constructor arities in the same order —
// Bool false/then true, Nat zero/then succ, List nil/then cons — and
// therefore work regardless of which frontend produced the .ast
// (rocq, agda, lean, ...).
function pp_call(type: ProgramType): string | undefined {
  if (type === SimpleType.Bool) return "TestPrinters.pp_bool";
  if (type === SimpleType.Nat) return "TestPrinters.pp_nat";
  if (type === SimpleType.UInt63) return undefined;
  if (type === SimpleType.Other) return undefined;
  if (typeof type === "number") return undefined;
  switch (type.type) {
    case "list": {
      const a = pp_call(type.a_t);
      return a === undefined ? undefined : `(TestPrinters.pp_list ${a})`;
    }
    case "option":
    case "prod":
      // No universal printers for these yet; treat as opaque so the
      // runner just exercises evaluation without checking the result.
      return undefined;
  }
}

// Append a main INSIDE `module Generated` (a top-level module runs to
// EOF).  Nullary constants are emitted as Lazy<obj> and must be forced
// inside the big-stack thread, never at module init on the 1 MiB stack.
function append_main(original: string, test: TestCase): string {
  const isLazy = new RegExp(`let(?:\\s+rec)?\\s+${test.main}\\s*:\\s*Lazy<obj>`).test(original);
  const target = isLazy ? `${test.main}.Force()` : `box ${test.main}`;

  const printer = pp_call(test.output_type);
  const body = printer === undefined
    ? `ignore (${target})`
    : `System.Console.Out.WriteLine(${printer} (${target}))`;

  return original + `

[<EntryPoint>]
let main (_argv: string[]) =
    let run () = ${body}
    let t = System.Threading.Thread(run, 536870912)   // 512 MiB stack
    t.Start()
    t.Join()
    0
`;
}

export function run_fsharp(file: string, projectdir: string, test: TestCase, timeout: number): ExecResult {
  try {
    // The generated program becomes the project's Main.fs, with the
    // entry point appended to it.
    writeFileSync(path.join(projectdir, "Main.fs"), append_main(readFileSync(file, "utf8"), test));

    // Build and run a NATIVE executable; the warm build already
    // restored, so the per-test build is incremental.
    const start_main = Date.now();
    execSync("dotnet build -c Release --no-restore --nologo -v:q", {
      stdio: "pipe",
      timeout: timeout,
      cwd: projectdir,
      encoding: "utf8",
      env: dotnet_env,
    });
    const res = execSync("dotnet bin/Release/net10.0/testexe.dll", {
      stdio: "pipe",
      timeout: timeout,
      cwd: projectdir,
      encoding: "utf8",
      env: dotnet_env,
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
    return { type: "error", reason: "compile error", compiler: "dotnet", code: e.status, error: stderr || stdout };
  }
}
