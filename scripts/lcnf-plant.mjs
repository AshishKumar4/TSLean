#!/usr/bin/env node
// Run the LCNF slice harness with a planted defect, then restore the tree.
//
//   node scripts/lcnf-plant.mjs <plant> [--out DIR] [Suite ...]
//
// <plant> names tests/lcnf/plants/<plant>.patch. The patch is applied, the LcnfLower library is
// rebuilt, the harness runs on the given suites, and the patch is reversed and the library rebuilt.
// A plant is shown when the suites it guards FAIL; this script exits 0 when the harness failed.
import { spawnSync } from "node:child_process";
import { join, resolve } from "node:path";

const root = resolve(import.meta.dirname, "..");
const [plant, ...rest] = process.argv.slice(2);
if (plant === undefined) throw new Error("usage: lcnf-plant.mjs <plant> [--out DIR] [Suite ...]");
const patch = join(root, "tests/lcnf/plants", `${plant}.patch`);

function run(cmd, args, cwd = root) {
  const r = spawnSync(cmd, args, { cwd, stdio: "inherit" });
  return r.status ?? 1;
}

function build() {
  if (run("lake", ["build", "LcnfLower"], join(root, "lean")) !== 0) throw new Error("lake build LcnfLower failed");
}

if (run("patch", ["-p1", "--forward", "--no-backup-if-mismatch", "-i", patch]) !== 0) throw new Error(`cannot apply ${patch}`);
let status;
try {
  build();
  status = run(process.execPath, [join(root, "scripts/lcnf-slice.mjs"), ...rest]);
} finally {
  if (run("patch", ["-p1", "-R", "--no-backup-if-mismatch", "-i", patch]) !== 0) throw new Error(`cannot reverse ${patch}`);
  build();
}
console.log(status === 0 ? `plant ${plant}: NOT detected (harness passed)` : `plant ${plant}: detected (harness failed)`);
process.exitCode = status === 0 ? 1 : 0;
