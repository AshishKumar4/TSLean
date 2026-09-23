#!/usr/bin/env node
// Differential harness for the LCNF → TypeScript lowering (LCNF-COMPILER-PLAN.md, M2).
//
//   node scripts/lcnf-slice.mjs [--out DIR] [--repeat N] [Suite ...]
//
// For each suite tests/lcnf/programs/<Suite>.lean:
//   1. `lake env lean` runs the suite's driver: M1's Extract.closure on the roots, Canon, lower,
//      print; the LCNF semantics checked against `#eval`; the module and a case manifest written.
//   2. `tsc` type-checks every printed module together with the runtime (strict, no `any`).
//   3. Node runs each module on the generated inputs and compares with `#eval`.
// Exits non-zero if any stage fails. Suites default to every file in tests/lcnf/programs.
import { execFileSync, spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readdirSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";

const root = resolve(import.meta.dirname, "..");
const args = process.argv.slice(2);
let out = null;
let repeat = "1";
const suites = [];
for (let i = 0; i < args.length; i++) {
  if (args[i] === "--out") out = resolve(args[++i]);
  else if (args[i] === "--repeat") repeat = args[++i];
  else suites.push(args[i]);
}
out ??= mkdtempSync(join(tmpdir(), "lcnf-slice-"));
mkdirSync(out, { recursive: true });
const programs = join(root, "tests/lcnf/programs");
if (suites.length === 0) {
  for (const f of readdirSync(programs).sort()) if (f.endsWith(".lean")) suites.push(f.slice(0, -5));
}
const runtime = join(root, "src/lcnf-runtime/index.ts");
console.log(`output: ${out}`);

let failed = false;
const ran = [];
for (const suite of suites) {
  console.log(`== ${suite}: lean`);
  // Deep `#eval`s (Lean's own reference runs over 10^6-element inputs) need a large thread stack.
  const lean = spawnSync("lake", ["env", "lean", "--tstack=4000000", join(programs, `${suite}.lean`)], {
    cwd: join(root, "lean"),
    env: { ...process.env, LCNF_OUT: out, LCNF_RUNTIME: runtime },
    stdio: "inherit",
  });
  if (lean.status !== 0) { failed = true; console.log(`== ${suite}: lean FAILED`); continue; }
  ran.push(suite);
}

writeFileSync(join(out, "tsconfig.json"), JSON.stringify({
  extends: join(root, "tests/lcnf/tsconfig.json"),
  compilerOptions: { typeRoots: [join(root, "node_modules/@types")] },
  include: ["*.ts"],
}));
console.log("== tsc");
const tsc = spawnSync(join(root, "node_modules/.bin/tsc"), ["-p", join(out, "tsconfig.json")], { stdio: "inherit" });
if (tsc.status !== 0) { failed = true; console.log("== tsc FAILED"); }

for (const suite of ran) {
  console.log(`== ${suite}: node`);
  const node = spawnSync(process.execPath, [
    "--experimental-strip-types", "--no-warnings",
    join(root, "tests/lcnf/runner.ts"), join(out, `${suite}.json`), "--repeat", repeat,
  ], { stdio: "inherit" });
  if (node.status !== 0) failed = true;
}
console.log(`git: ${execFileSync("git", ["rev-parse", "--short", "HEAD"], { cwd: root }).toString().trim()}${
  execFileSync("git", ["status", "--porcelain"], { cwd: root }).toString().trim() ? " (dirty)" : ""}`);
process.exitCode = failed ? 1 : 0;
