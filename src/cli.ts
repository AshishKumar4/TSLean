#!/usr/bin/env node
// CLI entry point.
// Single file: tsx src/cli.ts input.ts [-o output.lean] [--verify]
// Project:     tsx src/cli.ts --project dir/ [-o outdir/] [--verify]

import * as fs from 'fs';
import * as path from 'path';
import { parseFile } from './parser/index.js';
import { rewriteModule } from './rewrite/index.js';
import { generateLean } from './codegen/index.js';
import { generateVerification } from './verification/index.js';
import { transpileProject, writeProjectOutputs } from './project/index.js';

// ─── Argument parsing ─────────────────────────────────────────────────────────

interface Args {
  mode: 'single' | 'project';
  input: string;
  output: string;
  verify: boolean;
  ns: string;
}

function parseArgs(argv: string[]): Args {
  const args = argv.slice(2);
  let mode: 'single' | 'project' = 'single';
  let input = '', output = '', verify = false, ns = 'TSLean.Generated';

  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    if (a === '--project') { mode = 'project'; input = args[++i] ?? ''; }
    else if (a === '-o' || a === '--output') { output = args[++i] ?? ''; }
    else if (a === '--verify')    { verify = true; }
    else if (a === '--namespace') { ns = args[++i] ?? ns; }
    else if (!a.startsWith('-') && !input) { input = a; }
  }

  if (!input) {
    process.stderr.write('Usage:\n  tsx src/cli.ts <file.ts> [-o output.lean] [--verify]\n  tsx src/cli.ts --project <dir/> [-o outdir/] [--verify]\n');
    process.exit(1);
  }

  if (!output) {
    output = mode === 'single'
      ? input.replace(/\.ts$/, '.lean')
      : input.replace(/\/$/, '') + '_lean';
  }

  return { mode, input, output, verify, ns };
}

// ─── Single file ──────────────────────────────────────────────────────────────

function single(opts: Args): void {
  const { input, output, verify } = opts;
  if (!fs.existsSync(input)) { process.stderr.write(`File not found: ${input}\n`); process.exit(1); }

  try {
    const src = fs.readFileSync(input, 'utf-8');
    const mod = parseFile({ fileName: path.resolve(input), sourceText: src });
    const rw  = rewriteModule(mod);
    let code  = generateLean(rw);

    if (verify) {
      const { leanCode, obligations } = generateVerification(rw);
      if (leanCode) code += '\n\n-- Verification obligations\n' + leanCode;
      if (obligations.length) process.stdout.write(`Generated ${obligations.length} proof obligation(s)\n`);
    }

    fs.mkdirSync(path.dirname(path.resolve(output)), { recursive: true });
    fs.writeFileSync(output, code, 'utf-8');
    process.stdout.write(`✓ ${input} → ${output}\n`);
  } catch (err) {
    process.stderr.write(`Error: ${(err as Error).message}\n`);
    if (process.env['DEBUG']) process.stderr.write((err as Error).stack + '\n');
    process.exit(1);
  }
}

// ─── Project mode ─────────────────────────────────────────────────────────────

function project(opts: Args): void {
  const { input, output, verify, ns } = opts;
  if (!fs.existsSync(input) || !fs.statSync(input).isDirectory()) {
    process.stderr.write(`Directory not found: ${input}\n`); process.exit(1);
  }

  const result = transpileProject({
    projectDir: path.resolve(input),
    outputDir:  path.resolve(output),
    verify, rootNS: ns,
  });

  for (const e of result.errors) process.stderr.write(`Error: ${e}\n`);
  writeProjectOutputs(result);
  for (const { tsFile, leanFile } of result.files)
    process.stdout.write(`✓ ${tsFile} → ${leanFile}\n`);
  process.stdout.write(`\nTranspiled ${result.files.length} file(s), ${result.errors.length} error(s)\n`);
}

// ─── Main ─────────────────────────────────────────────────────────────────────

const opts = parseArgs(process.argv);
if (opts.mode === 'single') single(opts);
else project(opts);
