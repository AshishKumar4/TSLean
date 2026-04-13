#!/usr/bin/env node
// TSLean CLI — TypeScript → Lean 4 transpiler.
//
// Usage:
//   tslean compile <file|dir> [--output <dir>] [--verify] [--watch] [--self-host] [--namespace <ns>]
//   tslean self-host             — run the self-hosting pipeline
//   tslean verify                — run fixpoint verification
//   tslean init [dir]            — scaffold a tslean project
//
// Legacy (still works):
//   tslean <file.ts> [-o output.lean] [--verify]
//   tslean --project <dir/> [-o outdir/] [--verify]

import * as fs from 'fs';
import * as path from 'path';
import { execSync } from 'child_process';
import { parseFile } from './parser/index.js';
import { rewriteModule } from './rewrite/index.js';
import { generateLean, generateLeanTracked } from './codegen/index.js';
import { generateLeanV2 } from './codegen/v2.js';
import { currentTracker } from './sorry-tracker.js';
import { generateVerification } from './verification/index.js';
import { transpileProject, writeProjectOutputs } from './project/index.js';

// ─── Colors (ANSI, respects NO_COLOR and --no-color) ─────────────────────────

let noColor = !!process.env['NO_COLOR'] || !process.stdout.isTTY;
const c = {
  bold:    (s: string) => noColor ? s : `\x1b[1m${s}\x1b[0m`,
  dim:     (s: string) => noColor ? s : `\x1b[2m${s}\x1b[0m`,
  red:     (s: string) => noColor ? s : `\x1b[31m${s}\x1b[0m`,
  green:   (s: string) => noColor ? s : `\x1b[32m${s}\x1b[0m`,
  yellow:  (s: string) => noColor ? s : `\x1b[33m${s}\x1b[0m`,
  cyan:    (s: string) => noColor ? s : `\x1b[36m${s}\x1b[0m`,
};

// ─── Version ─────────────────────────────────────────────────────────────────

function getVersion(): string {
  try {
    const pkg = JSON.parse(fs.readFileSync(path.join(__dirname, '..', 'package.json'), 'utf-8'));
    return pkg.version ?? '0.0.0';
  } catch {
    return '0.0.0';
  }
}

// ─── Help ────────────────────────────────────────────────────────────────────

const HELP = `
${c.bold('tslean')} — TypeScript → Lean 4 transpiler

${c.bold('USAGE')}
  tslean compile <file|dir>  [options]   Transpile TypeScript to Lean 4
  tslean self-host                       Run the self-hosting pipeline
  tslean verify                          Run fixpoint verification
  tslean init [dir]                      Scaffold a new tslean project

${c.bold('OPTIONS')}
  -o, --output <path>    Output file or directory
  -w, --watch            Watch for changes and recompile
  --verify               Generate proof obligations
  --self-host            Enable self-host transforms
  --base-name <name>     Module base name (self-host mode)
  --namespace <ns>       Root namespace (default: TSLean.Generated)
  --no-color             Disable colored output
  -v, --version          Show version
  -h, --help             Show this help
`.trimStart();

// ─── Argument parsing ────────────────────────────────────────────────────────

interface CompileOpts {
  input: string;
  output: string;
  verify: boolean;
  watch: boolean;
  ns: string;
  selfHost: boolean;
  baseName: string;
  isDir: boolean;
  genLakefile: boolean;
  tsconfigPath: string;
  strict: boolean;
}

type Command =
  | { cmd: 'compile'; opts: CompileOpts }
  | { cmd: 'self-host' }
  | { cmd: 'verify' }
  | { cmd: 'init'; dir: string }
  | { cmd: 'help' }
  | { cmd: 'version' };

function parseArgs(argv: string[]): Command {
  const args = argv.slice(2);

  if (args.length === 0 || args.includes('-h') || args.includes('--help')) {
    return { cmd: 'help' };
  }
  if (args.includes('-v') || args.includes('--version')) {
    return { cmd: 'version' };
  }

  const sub = args[0];

  if (sub === 'self-host') return { cmd: 'self-host' };
  if (sub === 'verify')    return { cmd: 'verify' };
  if (sub === 'init')      return { cmd: 'init', dir: args[1] ?? '.' };

  // "compile" subcommand or legacy mode (positional file / --project)
  const isCompile = sub === 'compile';
  const rest = isCompile ? args.slice(1) : args;

  let input = '', output = '', verify = false, watch = false, strict = false;
  let ns = 'TSLean.Generated', selfHost = false, baseName = '';
  let isDir = false, genLakefile = true, tsconfigPath = '';

  for (let i = 0; i < rest.length; i++) {
    const a = rest[i];
    if (a === '--project')       { isDir = true; tsconfigPath = rest[++i] ?? ''; input = tsconfigPath; }
    else if (a === '-o' || a === '--output') { output = rest[++i] ?? ''; }
    else if (a === '--verify')   { verify = true; }
    else if (a === '-w' || a === '--watch') { watch = true; }
    else if (a === '--namespace'){ ns = rest[++i] ?? ns; }
    else if (a === '--self-host'){ selfHost = true; }
    else if (a === '--base-name'){ baseName = rest[++i] ?? ''; }
    else if (a === '--no-color') { noColor = true; }
    else if (a === '--lakefile') { genLakefile = true; }
    else if (a === '--no-lakefile') { genLakefile = false; }
    else if (a === '--strict')   { strict = true; }
    else if (!a.startsWith('-') && !input) { input = a; }
  }

  if (!input) {
    error('No input file or directory specified.\n\n  Usage: tslean compile <file|dir>');
    process.exit(1);
  }

  // Detect directory input
  if (!isDir && fs.existsSync(input) && fs.statSync(input).isDirectory()) {
    isDir = true;
  }

  if (!output) {
    output = isDir
      ? input.replace(/\/$/, '') + '_lean'
      : input.replace(/\.ts$/, '.lean');
  }

  return { cmd: 'compile', opts: { input, output, verify, watch, ns, selfHost, baseName, isDir, genLakefile, tsconfigPath, strict } };
}

// ─── Output helpers ──────────────────────────────────────────────────────────

function error(msg: string): void {
  process.stderr.write(`${c.red('error')}: ${msg}\n`);
}

function success(msg: string): void {
  process.stdout.write(`${c.green('✓')} ${msg}\n`);
}

function info(msg: string): void {
  process.stdout.write(`${c.cyan('›')} ${msg}\n`);
}

// ─── Compile: single file ────────────────────────────────────────────────────

function compileSingle(opts: CompileOpts): boolean {
  const { input, output, verify, selfHost, baseName, strict } = opts;
  if (!fs.existsSync(input)) {
    error(`File not found: ${input}`);
    return false;
  }

  try {
    const src = fs.readFileSync(input, 'utf-8');
    const mod = parseFile({ fileName: path.resolve(input), sourceText: src });
    const rw  = rewriteModule(mod);
    const { code: rawCode, tracker } = selfHost
      ? { code: generateLeanV2(rw, { selfHost: true, baseName }), tracker: currentTracker() }
      : generateLeanTracked(rw);
    let code = rawCode;

    if (verify) {
      const { leanCode, obligations } = generateVerification(rw);
      if (leanCode) code += '\n\n-- Verification obligations\n' + leanCode;
      if (obligations.length) info(`Generated ${obligations.length} proof obligation(s)`);
    }

    // Summary report
    if (tracker.count > 0) {
      process.stdout.write(`${c.yellow('warn')}: ${tracker.count} sorry expression(s) in output\n`);
      if (strict) {
        error(`--strict: ${tracker.count} sorry(s) found — aborting. Use without --strict to emit anyway.`);
        return false;
      }
    }

    fs.mkdirSync(path.dirname(path.resolve(output)), { recursive: true });
    fs.writeFileSync(output, code, 'utf-8');
    success(`${input} → ${output}`);
    return true;
  } catch (err) {
    error((err as Error).message);
    if (process.env['DEBUG']) process.stderr.write((err as Error).stack + '\n');
    return false;
  }
}

// ─── Compile: project (directory) ────────────────────────────────────────────

function compileProject(opts: CompileOpts): boolean {
  const { input, output, verify, ns } = opts;
  const tsconfigPath = opts.tsconfigPath || '';
  const genLakefile = opts.genLakefile !== false;

  // --project tsconfig.json mode
  const projectDir = tsconfigPath && tsconfigPath.endsWith('.json')
    ? path.dirname(path.resolve(tsconfigPath))
    : path.resolve(input);

  if (!fs.existsSync(projectDir)) {
    error(`Directory not found: ${projectDir}`);
    return false;
  }

  const t0 = Date.now();
  const result = transpileProject({
    projectDir,
    outputDir: path.resolve(output),
    tsconfigPath: tsconfigPath && tsconfigPath.endsWith('.json') ? path.resolve(tsconfigPath) : undefined,
    verify,
    rootNS: ns,
    generateLakefile: genLakefile,
    onProgress: (step, cur, total) => {
      if (total > 0) info(`[${cur}/${total}] ${step}`);
      else info(step);
    },
  });

  for (const w of result.warnings) process.stdout.write(`${c.yellow('warn')}: ${w}\n`);
  for (const e of result.errors) error(e);
  writeProjectOutputs(result);
  for (const { tsFile, leanFile } of result.files) {
    success(`${path.relative(projectDir, tsFile)} → ${path.relative(process.cwd(), leanFile)}`);
  }

  const elapsed = ((Date.now() - t0) / 1000).toFixed(1);
  const nFiles = result.files.length;
  const nCycles = result.graph.cycles.length;
  const summary = `${nFiles} file(s) transpiled`;
  const cycleSummary = nCycles > 0 ? `, ${c.yellow(nCycles + ' cycle(s)')}` : '';
  const errSummary = result.errors.length ? `, ${c.red(result.errors.length + ' error(s)')}` : '';
  const lakeSummary = genLakefile && nFiles > 0 ? `, lakefile generated` : '';
  process.stdout.write(`\n${c.bold(summary)}${cycleSummary}${errSummary}${lakeSummary} ${c.dim(`(${elapsed}s)`)}\n`);

  return result.errors.length === 0;
}

// ─── Watch mode ──────────────────────────────────────────────────────────────

function watchMode(opts: CompileOpts): void {
  const target = path.resolve(opts.input);

  const run = () => {
    process.stdout.write(`\n${c.dim('─── recompiling ' + new Date().toLocaleTimeString() + ' ───')}\n`);
    if (opts.isDir) compileProject(opts);
    else compileSingle(opts);
  };

  // Initial compile
  if (opts.isDir) compileProject(opts);
  else compileSingle(opts);

  info(`Watching for changes... ${c.dim('(Ctrl+C to stop)')}`);

  const debounce = new Map<string, ReturnType<typeof setTimeout>>();
  const DEBOUNCE_MS = 200;

  if (opts.isDir) {
    fs.watch(target, { recursive: true }, (_event, filename) => {
      if (!filename || !filename.endsWith('.ts')) return;
      const key = filename;
      const existing = debounce.get(key);
      if (existing) clearTimeout(existing);
      debounce.set(key, setTimeout(() => { debounce.delete(key); run(); }, DEBOUNCE_MS));
    });
  } else {
    fs.watchFile(target, { interval: 500 }, () => {
      const key = target;
      const existing = debounce.get(key);
      if (existing) clearTimeout(existing);
      debounce.set(key, setTimeout(() => { debounce.delete(key); run(); }, DEBOUNCE_MS));
    });
  }
}

// ─── Self-host command ───────────────────────────────────────────────────────

function selfHost(): boolean {
  const scriptPath = path.join(__dirname, '..', 'scripts', 'self-host.sh');

  if (!fs.existsSync(scriptPath)) {
    error('Self-host script not found. Expected: scripts/self-host.sh');
    return false;
  }

  info('Running self-hosting pipeline...');
  try {
    execSync(`bash "${scriptPath}"`, { stdio: 'inherit', cwd: path.join(__dirname, '..') });
    return true;
  } catch {
    error('Self-hosting pipeline failed.');
    return false;
  }
}

// ─── Verify (fixpoint) command ───────────────────────────────────────────────

function fixpointVerify(): boolean {
  const scriptPath = path.join(__dirname, '..', 'scripts', 'fixpoint-verify.sh');

  if (!fs.existsSync(scriptPath)) {
    error('Fixpoint verify script not found. Expected: scripts/fixpoint-verify.sh');
    return false;
  }

  info('Running fixpoint verification...');
  try {
    execSync(`bash "${scriptPath}"`, { stdio: 'inherit', cwd: path.join(__dirname, '..') });
    return true;
  } catch {
    error('Fixpoint verification failed.');
    return false;
  }
}

// ─── Init command ────────────────────────────────────────────────────────────

function initProject(dir: string): boolean {
  const target = path.resolve(dir);

  if (fs.existsSync(path.join(target, 'tslean.json'))) {
    error(`Project already initialized in ${target}`);
    return false;
  }

  fs.mkdirSync(path.join(target, 'src'), { recursive: true });
  fs.mkdirSync(path.join(target, 'lean'), { recursive: true });

  // tslean.json project config
  fs.writeFileSync(path.join(target, 'tslean.json'), JSON.stringify({
    compilerOptions: {
      output: 'lean/Generated',
      namespace: 'TSLean.Generated',
      verify: false,
    },
    include: ['src/**/*.ts'],
    exclude: ['**/*.test.ts', '**/*.spec.ts'],
  }, null, 2) + '\n', 'utf-8');

  // Example source file
  fs.writeFileSync(path.join(target, 'src', 'example.ts'), [
    '// Example: transpile this with `tslean compile src/`',
    '',
    'export interface Point {',
    '  x: number;',
    '  y: number;',
    '}',
    '',
    'export function distance(a: Point, b: Point): number {',
    '  const dx = a.x - b.x;',
    '  const dy = a.y - b.y;',
    '  return Math.sqrt(dx * dx + dy * dy);',
    '}',
    '',
  ].join('\n'), 'utf-8');

  success(`Initialized tslean project in ${target}`);
  info('Created tslean.json, src/example.ts');
  info(`Run: ${c.bold('tslean compile src/ -o lean/Generated/')}`);
  return true;
}

// ─── Compile dispatcher ──────────────────────────────────────────────────────

function runCompile(opts: CompileOpts): void {
  if (opts.watch) {
    watchMode(opts);
  } else if (opts.isDir) {
    if (!compileProject(opts)) process.exit(1);
  } else {
    if (!compileSingle(opts)) process.exit(1);
  }
}

// ─── Main ────────────────────────────────────────────────────────────────────

function main(): void {
  const command = parseArgs(process.argv);
  const cmd = command.cmd;

  if (cmd === 'help') {
    process.stdout.write(HELP);
  } else if (cmd === 'version') {
    process.stdout.write(`tslean ${getVersion()}\n`);
  } else if (cmd === 'self-host') {
    if (!selfHost()) process.exit(1);
  } else if (cmd === 'verify') {
    if (!fixpointVerify()) process.exit(1);
  } else if (cmd === 'init') {
    if (!initProject(command.dir)) process.exit(1);
  } else if (cmd === 'compile') {
    runCompile(command.opts);
  }
}

main();
