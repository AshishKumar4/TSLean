#!/usr/bin/env node
// Regenerate the Lean-to-TypeScript round-trip examples from their registry.
//
// Every example is one Lean module and the TypeScript the compiler emits for it. Nothing
// under `generated/` is written by hand, and `--check` fails when a committed tree differs
// from a clean regeneration.
//
//   node scripts/generate-roundtrip-examples.mjs [--check]

import { spawnSync } from 'node:child_process';
import process from 'node:process';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const registry = JSON.parse(readFileSync(join(root, 'examples/lean-to-typescript/roundtrip/registry.json'), 'utf8'));
const check = process.argv.includes('--check');

let failed = 0;
for (const entry of registry) {
  const call = [
    join(root, 'dist/cli.js'),
    'lean-to-ts',
    '--project-root',
    'lean',
    '--module',
    entry.module,
    '--source',
    entry.source,
    ...entry.declarations.flatMap((declaration) => ['--declaration', declaration]),
    '--out-dir',
    entry.outDir,
    '--manifest',
    `${entry.outDir}/tslean.manifest.json`,
    ...(check ? ['--check'] : []),
  ];
  const run = spawnSync(process.execPath, call, { cwd: root, encoding: 'utf8' });
  if (run.status === 0) {
    process.stdout.write(`${check ? 'checked' : 'generated'} ${entry.name}\n`);
    continue;
  }
  failed += 1;
  process.stderr.write(`${entry.name}: ${run.stderr.trim() || run.stdout.trim()}\n`);
}

if (failed > 0) {
  process.stderr.write(`${String(failed)} of ${String(registry.length)} example(s) failed\n`);
  process.exitCode = 1;
}
