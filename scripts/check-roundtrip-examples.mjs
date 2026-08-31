#!/usr/bin/env node
// Send every checked-in example round, in both directions, and report what held.
//
// The round trip projects each generated module onto the profile, compiles the projection
// back to Lean, elaborates it under the pinned toolchain, and runs both sides over the
// enumerated input domain of every exported function. It reports counterexamples; it states
// no theorem.
//
//   node scripts/check-roundtrip-examples.mjs

import { readFileSync } from 'node:fs';
import process from 'node:process';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { verifyLeanToTypeScriptRoundtrip, verifyTypeScriptToLeanRoundtrip } from '../dist/roundtrip/index.js';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const registry = JSON.parse(readFileSync(join(root, 'examples/lean-to-typescript/roundtrip/registry.json'), 'utf8'));

const manifests = [
  ...registry.map((entry) => join(root, entry.outDir, 'tslean.manifest.json')),
  join(root, 'examples/lean-to-typescript/generated/tslean.manifest.json'),
  join(root, 'examples/lean-to-typescript/package/generated/tslean.manifest.json'),
  join(root, 'examples/agent-core/facets/generated/tslean.manifest.json'),
];

const options = { leanProjectRoot: join(root, 'lean') };
let failed = 0;

for (const manifest of manifests) {
  const report = await verifyLeanToTypeScriptRoundtrip(manifest, options);
  const name = manifest.slice(root.length + 1);
  if (report.holds) {
    const applied = report.behaviour?.coverage.reduce((total, entry) => total + entry.applied, 0) ?? 0;
    const sampled = report.behaviour?.coverage.filter((entry) => !entry.exhaustive).length ?? 0;
    const sourceApplied = report.sourceBehaviour?.coverage.reduce((total, entry) => total + entry.applied, 0) ?? 0;
    const sourceSampled = report.sourceBehaviour?.coverage.filter((entry) => !entry.exhaustive).length ?? 0;
    const coverage = sampled === 0 ? 'exhaustive' : `${String(sampled)} domain(s) SAMPLED`;
    const sourceCoverage =
      report.sourceBehaviour === undefined
        ? ''
        : `; source ${String(sourceApplied)} input(s), ${sourceSampled === 0 ? 'exhaustive' : `${String(sourceSampled)} domain(s) SAMPLED`}`;
    process.stdout.write(`held ${name} (${String(applied)} input(s), ${coverage}${sourceCoverage})\n`);
    continue;
  }
  failed += 1;
  report_failure(name, report);
}

// The TypeScript-to-Lean direction is gated the same way, through the same public entry
// point. A hostile source is expected to be refused, and a run that stops refusing it is as
// much a failure as a good source that stops round-tripping.
const sources = [
  { path: 'examples/roundtrip/tier.ts', holds: true },
  { path: 'examples/roundtrip/hostile-recursive-union.ts', holds: false },
  { path: 'examples/roundtrip/hostile-mutable-class.ts', holds: false },
];
for (const entry of sources) {
  const report = await verifyTypeScriptToLeanRoundtrip([join(root, entry.path)], options);
  if (report.holds === entry.holds) {
    process.stdout.write(`${entry.holds ? 'held' : 'refused'} ${entry.path}\n`);
    continue;
  }
  failed += 1;
  if (entry.holds) {
    report_failure(entry.path, report);
  } else {
    process.stderr.write(`${entry.path}: expected a refusal, every check held\n`);
  }
}

function report_failure(name, report) {
  process.stderr.write(`failed ${name}\n`);
  for (const check of report.checks.filter((entry) => !entry.holds)) {
    process.stderr.write(`  ${check.name}: ${check.detail}\n`);
  }
  for (const counterexample of report.counterexamples.slice(0, 5)) {
    process.stderr.write(
      `  ${counterexample.check} @ ${counterexample.subject}\n` +
        `    expected ${counterexample.expected}\n    actual   ${counterexample.actual}\n`,
    );
  }
}

if (failed > 0) {
  process.stderr.write(`${String(failed)} of ${String(manifests.length + sources.length)} example(s) did not hold\n`);
  process.exitCode = 1;
}
