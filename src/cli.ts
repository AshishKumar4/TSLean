#!/usr/bin/env node
// One explicit CLI for both compiler directions.
//
// Usage:
//   tslean ts-to-lean <file|dir> [options]
//   tslean lean-to-ts <compiler options>
//   tslean init [dir]

import * as fs from 'fs';
import * as path from 'path';
import { execFileSync } from 'child_process';
import { fileURLToPath, pathToFileURL } from 'url';
import { parseFile } from './parser/index.js';
import { rewriteModule } from './rewrite/index.js';
import { generateLeanTracked } from './codegen/index.js';
import { countLevel, degradationSites, describeDegradation, type DegradationMarker } from './codegen/degradation.js';
import { resetTimer } from './timing.js';
import { transpileProject, writeProjectOutputs } from './project/index.js';
import { runLeanToTypeScriptCli } from './lean-to-typescript/cli.js';
import {
  leanAccepts,
  PACKAGED_LEAN_PROJECT,
  type LeanAcceptance,
  type LeanModuleSource,
} from './lean-check.js';
import {
  verifyLeanToTypeScriptRoundtrip,
  verifyTypeScriptToLeanRoundtrip,
  type RoundtripOptions,
  type RoundtripReport,
} from './roundtrip/index.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

// ─── Colors (ANSI, respects NO_COLOR and --no-color) ─────────────────────────

let noColor = !!process.env['NO_COLOR'] || !process.stdout.isTTY;
const c = {
  bold: (s: string) => (noColor ? s : `\x1b[1m${s}\x1b[0m`),
  dim: (s: string) => (noColor ? s : `\x1b[2m${s}\x1b[0m`),
  red: (s: string) => (noColor ? s : `\x1b[31m${s}\x1b[0m`),
  green: (s: string) => (noColor ? s : `\x1b[32m${s}\x1b[0m`),
  yellow: (s: string) => (noColor ? s : `\x1b[33m${s}\x1b[0m`),
  cyan: (s: string) => (noColor ? s : `\x1b[36m${s}\x1b[0m`),
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
${c.bold('tslean')} — TypeScript and Lean compilers

${c.bold('USAGE')}
  tslean ts-to-lean <file|dir> [options]  Compile TypeScript to Lean 4
  tslean lean-to-ts [options]             Compile Lean 4 to TypeScript
  tslean roundtrip <target> [options]     Send a program round and report what held
  tslean init [dir]                        Create a TypeScript-to-Lean project

${c.bold('TS-TO-LEAN OPTIONS')}
  -o, --output <path>       Output file or directory
  --tsconfig <path>         Use an exact tsconfig.json
  -w, --watch               Watch for changes and recompile
  --lake                    Run Lake after each watch compilation
  --strict                  Accept only output Lean accepts, with no placeholder
  --lean-project <dir>      Lake project --strict elaborates against
  --namespace <name>        Root namespace (default: TSLean.Generated)
  --lakefile                Emit lakefile.toml (default for a directory)
  --no-lakefile             Do not emit lakefile.toml
  --timing                  Show compiler phase timing
  --no-color                Disable colored output

${c.bold('ROUNDTRIP OPTIONS')}
  --manifest <path>         Send a generated package Lean → TypeScript → Lean
  --source <file>           Send TypeScript → Lean → TypeScript; repeatable
  --lean-project <dir>      Lake project supplying the recovered Lean runtime
  --source-root <dir>       Original Lean project; defaults to the manifest source root
  --behaviour-limit <n>     Most inputs applied to one function (default 4096)
  --json                    Print the report as JSON

Use ${c.bold('tslean lean-to-ts --help')} for Lean-to-TypeScript options.
Global: -v, --version; -h, --help
`.trimStart();

// ─── Argument parsing ────────────────────────────────────────────────────────

interface CompileOpts {
  input: string;
  output: string;
  watch: boolean;
  lake: boolean;
  ns: string;
  isDir: boolean;
  genLakefile: boolean;
  tsconfigPath: string;
  strict: boolean;
  leanProject: string;
  timing: boolean;
}
interface RoundtripOpts {
  manifests: readonly string[];
  sources: readonly string[];
  leanProject: string;
  sourceRoot: string | undefined;
  behaviourLimit: number | undefined;
  json: boolean;
}

type Command =
  | { cmd: 'ts-to-lean'; opts: CompileOpts }
  | { cmd: 'lean-to-ts'; arguments: readonly string[] }
  | { cmd: 'roundtrip'; opts: RoundtripOpts }
  | { cmd: 'init'; dir: string }
  | { cmd: 'help' }
  | { cmd: 'version' };

function parseArgs(args: readonly string[]): Command {
  if (args.length === 0 || ((args[0] === '-h' || args[0] === '--help') && args.length === 1)) {
    return { cmd: 'help' };
  }
  if ((args[0] === '-v' || args[0] === '--version') && args.length === 1) {
    return { cmd: 'version' };
  }

  const [command, ...rest] = args;
  if (command === 'init') {
    if (rest.length > 1 || rest[0]?.startsWith('-')) {
      throw new TypeError('Usage: tslean init [dir]');
    }
    return { cmd: 'init', dir: rest[0] ?? '.' };
  }
  if (command === 'lean-to-ts') {
    return { cmd: 'lean-to-ts', arguments: rest };
  }
  if (command === 'roundtrip') {
    return rest.length === 1 && (rest[0] === '-h' || rest[0] === '--help')
      ? { cmd: 'help' }
      : { cmd: 'roundtrip', opts: parseRoundtripArgs(rest) };
  }
  if (command !== 'ts-to-lean') {
    throw new TypeError(`Unknown command ${command ?? ''}; expected ts-to-lean, lean-to-ts, roundtrip, or init`);
  }
  if (rest.length === 1 && (rest[0] === '-h' || rest[0] === '--help')) {
    return { cmd: 'help' };
  }

  let input = '';
  let output = '';
  let watch = false;
  let lake = false;
  let strict = false;
  let timing = false;
  let ns = 'TSLean.Generated';
  let genLakefile = true;
  let tsconfigPath = '';
  let leanProject = PACKAGED_LEAN_PROJECT;
  const seen = new Set<string>();

  for (let index = 0; index < rest.length; index += 1) {
    const option = rest[index]!;
    if (!option.startsWith('-')) {
      if (input !== '') throw new TypeError(`Unexpected positional argument ${option}`);
      input = option;
      continue;
    }
    if (option === '-o' || option === '--output') {
      uniqueOption(seen, 'output');
      output = optionValue(rest, ++index, option);
    } else if (option === '--tsconfig') {
      uniqueOption(seen, 'tsconfig');
      tsconfigPath = optionValue(rest, ++index, option);
    } else if (option === '--namespace') {
      uniqueOption(seen, 'namespace');
      ns = optionValue(rest, ++index, option);
    } else if (option === '-w' || option === '--watch') {
      uniqueOption(seen, 'watch');
      watch = true;
    } else if (option === '--lake') {
      uniqueOption(seen, 'lake');
      lake = true;
    } else if (option === '--strict') {
      uniqueOption(seen, 'strict');
      strict = true;
    } else if (option === '--lean-project') {
      uniqueOption(seen, 'lean-project');
      leanProject = optionValue(rest, ++index, option);
    } else if (option === '--timing') {
      uniqueOption(seen, 'timing');
      timing = true;
    } else if (option === '--no-color') {
      uniqueOption(seen, 'no-color');
      noColor = true;
    } else if (option === '--lakefile' || option === '--no-lakefile') {
      uniqueOption(seen, 'lakefile');
      genLakefile = option === '--lakefile';
    } else {
      throw new TypeError(`Unknown ts-to-lean option ${option}`);
    }
  }

  if (input === '') throw new TypeError('Usage: tslean ts-to-lean <file|dir> [options]');
  const isDir = fs.existsSync(input) && fs.statSync(input).isDirectory();
  if (tsconfigPath !== '' && !isDir) {
    throw new TypeError('--tsconfig requires a directory input');
  }
  if (lake && !watch) throw new TypeError('--lake requires --watch');
  if (output === '') {
    output = isDir ? `${input.replace(/\/$/u, '')}_lean` : input.replace(/\.tsx?$/u, '.lean');
  }
  return {
    cmd: 'ts-to-lean',
    opts: {
      input,
      output,
      watch,
      lake,
      ns,
      isDir,
      genLakefile,
      tsconfigPath,
      strict,
      leanProject,
      timing,
    },
  };
}
function parseRoundtripArgs(args: readonly string[]): RoundtripOpts {
  const manifests: string[] = [];
  const sources: string[] = [];
  let leanProject = PACKAGED_LEAN_PROJECT;
  let sourceRoot: string | undefined;
  let behaviourLimit: number | undefined;
  let json = false;
  const seen = new Set<string>();

  for (let index = 0; index < args.length; index += 1) {
    const option = args[index]!;
    if (option === '--manifest') {
      manifests.push(optionValue(args, ++index, option));
    } else if (option === '--source') {
      sources.push(optionValue(args, ++index, option));
    } else if (option === '--lean-project') {
      uniqueOption(seen, 'lean-project');
      leanProject = optionValue(args, ++index, option);
    } else if (option === '--source-root') {
      uniqueOption(seen, 'source-root');
      sourceRoot = optionValue(args, ++index, option);
    } else if (option === '--behaviour-limit') {
      uniqueOption(seen, 'behaviour-limit');
      const value = Number(optionValue(args, ++index, option));
      if (!Number.isSafeInteger(value) || value <= 0) {
        throw new TypeError('--behaviour-limit takes a positive safe integer');
      }
      behaviourLimit = value;
    } else if (option === '--json') {
      uniqueOption(seen, 'json');
      json = true;
    } else if (option === '--no-color') {
      uniqueOption(seen, 'no-color');
      noColor = true;
    } else {
      throw new TypeError(`Unknown roundtrip option ${option}`);
    }
  }

  if (manifests.length === 0 && sources.length === 0) {
    throw new TypeError('Usage: tslean roundtrip --manifest <path> | --source <file> [options]');
  }
  return { manifests, sources, leanProject, sourceRoot, behaviourLimit, json };
}

function uniqueOption(seen: Set<string>, option: string): void {
  if (seen.has(option)) throw new TypeError(`Option --${option} may be specified only once`);
  seen.add(option);
}

function optionValue(args: readonly string[], index: number, option: string): string {
  const value = args[index];
  if (value === undefined || value.startsWith('-')) {
    throw new TypeError(`${option} requires a value`);
  }
  return value;
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

/**
 * Report the placeholders the emitted Lean actually carries.
 *
 * Shared by single-file and project mode so `--strict` means the same thing in
 * both: the artifact, not the lowerer's bookkeeping, decides.
 *
 * @returns false when `--strict` rejects the output.
 */
function reportDegradation(markers: readonly DegradationMarker[], strict: boolean): boolean {
  if (markers.length === 0) return true;

  const counts = describeDegradation(markers);
  const severity = countLevel(markers, 'sorry') > 0 ? c.yellow('warn') : c.dim('info');
  process.stdout.write(`${severity}: ${counts} in output\n`);

  if (!strict) return true;
  error(`--strict: ${counts} in generated Lean — rejected. Re-run without --strict to accept degraded output.`);
  for (const site of degradationSites(markers)) process.stderr.write(`  ${c.dim(site)}\n`);
  return false;
}

/**
 * Whether `--strict` accepts this output.
 *
 * Strict acceptance means Lean accepts the emitted modules. A placeholder scan reads the
 * artifact, so it cannot see a lowering that is well-formed and ill-typed, and it cannot
 * see one that is well-typed and drops a call. Strict therefore elaborates the output
 * under the project's pinned toolchain as well. A checker that cannot run is a refusal:
 * an unrun check is not an acceptance.
 *
 * @returns false when `--strict` rejects the output.
 */
function acceptStrictly(
  modules: readonly LeanModuleSource[],
  markers: readonly DegradationMarker[],
  opts: CompileOpts,
): boolean {
  if (!reportDegradation(markers, opts.strict)) return false;
  if (!opts.strict) return true;
  try {
    return reportLeanAcceptance(leanAccepts(modules, { projectRoot: opts.leanProject }));
  } catch (failure) {
    const reason = failure instanceof Error ? failure.message : String(failure);
    error(`--strict: Lean could not be run, so acceptance is unknown — ${reason}`);
    return false;
  }
}

/** Report what Lean said, and answer whether it accepted. */
function reportLeanAcceptance(acceptance: LeanAcceptance): boolean {
  if (acceptance.accepted) {
    info(`Lean ${acceptance.toolchain} accepted the generated module(s)`);
    return true;
  }
  error(`--strict: Lean ${acceptance.toolchain} rejected the generated Lean.`);
  for (const diagnostic of acceptance.diagnostics.filter((entry) => entry.severity === 'error')) {
    process.stderr.write(
      `  ${c.dim(`${diagnostic.module}:${String(diagnostic.line)}:${String(diagnostic.column)}`)} ${diagnostic.message}\n`,
    );
  }
  return false;
}

// ─── Compile: single file ────────────────────────────────────────────────────

function compileSingle(opts: CompileOpts): boolean {
  const { input, output, timing } = opts;
  if (!fs.existsSync(input)) {
    error(`File not found: ${input}`);
    return false;
  }

  try {
    const timer = resetTimer();
    timer.start('parse');
    const source = fs.readFileSync(input, 'utf-8');
    const parsed = parseFile({ fileName: path.resolve(input), sourceText: source });

    timer.start('rewrite');
    const rewritten = rewriteModule(parsed);

    timer.start('codegen');
    const { code, degradations } = generateLeanTracked(rewritten);

    timer.start('lean');
    const modules = [{ module: rewritten.name, code, imports: [] }];
    if (!acceptStrictly(modules, degradations, opts)) return false;

    timer.start('write');
    fs.mkdirSync(path.dirname(path.resolve(output)), { recursive: true });
    fs.writeFileSync(output, code, 'utf-8');
    timer.end();

    success(`${input} → ${output}`);
    if (timing) process.stdout.write(`${timer.report()}\n`);
    return true;
  } catch (failure) {
    const message = failure instanceof Error ? failure.message : String(failure);
    error(message);
    if (process.env['DEBUG'] && failure instanceof Error && failure.stack) {
      process.stderr.write(`${failure.stack}\n`);
    }
    return false;
  }
}

// ─── Compile: project (directory) ────────────────────────────────────────────

function compileProject(opts: CompileOpts): boolean {
  const { input, output, ns } = opts;
  const projectDir = path.resolve(input);
  if (!fs.existsSync(projectDir)) {
    error(`Directory not found: ${projectDir}`);
    return false;
  }

  const t0 = Date.now();
  const result = transpileProject({
    projectDir,
    outputDir: path.resolve(output),
    tsconfigPath: opts.tsconfigPath === '' ? undefined : path.resolve(opts.tsconfigPath),
    rootNS: ns,
    generateLakefile: opts.genLakefile,
    onProgress: (step, current, total) => {
      if (total > 0) info(`[${current}/${total}] ${step}`);
      else info(step);
    },
  });

  for (const warning of result.warnings) process.stdout.write(`${c.yellow('warn')}: ${warning}\n`);
  for (const problem of result.errors) error(problem);
  const degradations = result.files.flatMap((file) =>
    file.degradations.map((marker) => ({
      ...marker,
      site: `${path.relative(projectDir, file.tsFile)}: ${marker.site}`,
    })),
  );
  const names = new Set(result.files.map((file) => file.module));
  const modules = result.files.map((file) => ({
    module: file.module,
    code: file.content,
    imports: result.graph.nodes.get(file.module)?.imports.filter((name) => names.has(name)) ?? [],
  }));
  const accepted = acceptStrictly(modules, degradations, opts);
  if (!accepted || result.errors.length > 0) return false;

  writeProjectOutputs(result);
  for (const { tsFile, leanFile } of result.files) {
    success(`${path.relative(projectDir, tsFile)} → ${path.relative(process.cwd(), leanFile)}`);
  }

  const elapsed = ((Date.now() - t0) / 1000).toFixed(1);
  const nFiles = result.files.length;
  const nCycles = result.graph.cycles.length;
  const summary = `${nFiles} file(s) transpiled`;
  const cycleSummary = nCycles > 0 ? `, ${c.yellow(nCycles + ' cycle(s)')}` : '';
  const lakeSummary = opts.genLakefile && nFiles > 0 ? ', lakefile generated' : '';
  process.stdout.write(`\n${c.bold(summary)}${cycleSummary}${lakeSummary} ${c.dim(`(${elapsed}s)`)}\n`);

  return true;
}

// ─── Watch mode ──────────────────────────────────────────────────────────────

function watchMode(opts: CompileOpts): void {
  const target = path.resolve(opts.input);
  const autoLake = opts.lake;
  let compileCount = 0;

  const clearScreen = () => process.stdout.write('\x1b[2J\x1b[H');

  const runLakeBuild = () => {
    if (!autoLake) return;
    info('Running lake build...');
    try {
      execFileSync('lake', ['build'], { cwd: path.join(process.cwd(), 'lean'), stdio: 'pipe', timeout: 120000 });
      success('lake build passed');
    } catch {
      error('lake build failed');
    }
  };

  const run = (changedFile?: string) => {
    compileCount++;
    const time = new Date().toLocaleTimeString();
    const fileInfo = changedFile ? ` ${c.cyan(changedFile)}` : '';
    clearScreen();
    process.stdout.write(`${c.dim(`─── #${compileCount} ${time}`)}${fileInfo} ${c.dim('───')}\n\n`);

    const t0 = Date.now();
    const ok = opts.isDir ? compileProject(opts) : compileSingle(opts);
    const elapsed = ((Date.now() - t0) / 1000).toFixed(1);

    if (ok) {
      process.stdout.write(`\n${c.green('✓')} Compiled in ${elapsed}s\n`);
      runLakeBuild();
    } else {
      process.stdout.write(`\n${c.red('✗')} Failed in ${elapsed}s\n`);
    }
    process.stdout.write(`\n${c.dim('Watching for changes... (Ctrl+C to stop)')}\n`);
  };

  // Initial compile
  run();

  const debounce = new Map<string, ReturnType<typeof setTimeout>>();
  const DEBOUNCE_MS = 250;

  const onFileChange = (filename: string) => {
    if (!filename.endsWith('.ts') && !filename.endsWith('.tsx')) return;
    const existing = debounce.get(filename);
    if (existing) clearTimeout(existing);
    debounce.set(
      filename,
      setTimeout(() => {
        debounce.delete(filename);
        run(filename);
      }, DEBOUNCE_MS),
    );
  };

  if (opts.isDir) {
    fs.watch(target, { recursive: true }, (_event, filename) => {
      if (filename) onFileChange(filename);
    });
  } else {
    fs.watchFile(target, { interval: 500 }, () => onFileChange(path.basename(target)));
  }
}

// ─── Init command ────────────────────────────────────────────────────────────

function initProject(dir: string): boolean {
  const target = path.resolve(dir);
  if (fs.existsSync(path.join(target, 'tsconfig.json'))) {
    error(`Project already initialized in ${target}`);
    return false;
  }

  fs.mkdirSync(path.join(target, 'src'), { recursive: true });
  fs.mkdirSync(path.join(target, 'lean'), { recursive: true });
  fs.writeFileSync(
    path.join(target, 'tsconfig.json'),
    JSON.stringify(
      {
        compilerOptions: {
          module: 'NodeNext',
          moduleResolution: 'NodeNext',
          strict: true,
          target: 'ES2022',
        },
        include: ['src/**/*.ts'],
        exclude: ['**/*.test.ts', '**/*.spec.ts'],
      },
      null,
      2,
    ) + '\n',
    'utf-8',
  );
  fs.writeFileSync(
    path.join(target, 'src', 'example.ts'),
    [
      '// Compile with: tslean ts-to-lean src --output lean/Generated',
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
    ].join('\n'),
    'utf-8',
  );

  success(`Initialized TSLean project in ${target}`);
  info('Created tsconfig.json and src/example.ts');
  info(`Run: ${c.bold('tslean ts-to-lean src --output lean/Generated')}`);
  return true;
}

// ─── Roundtrip ───────────────────────────────────────────────────────────────

/** Print one report, and answer whether it held. */
function reportRoundtrip(report: RoundtripReport, json: boolean): boolean {
  if (json) {
    process.stdout.write(`${JSON.stringify(report, null, 2)}\n`);
    return report.holds;
  }
  process.stdout.write(`\n${c.bold(report.direction)}  ${c.dim(report.subject)}\n`);
  for (const check of report.checks) {
    const mark = check.holds ? c.green('✓') : c.red('✗');
    process.stdout.write(`  ${mark} ${check.name} ${c.dim(`(${check.detail})`)}\n`);
  }
  for (const counterexample of report.counterexamples) {
    process.stderr.write(`  ${c.red('counterexample')} ${counterexample.check} @ ${counterexample.subject}\n`);
    process.stderr.write(`    expected ${counterexample.expected}\n`);
    process.stderr.write(`    actual   ${counterexample.actual}\n`);
  }
  return report.holds;
}

async function runRoundtrip(opts: RoundtripOpts): Promise<boolean> {
  const options: RoundtripOptions = {
    leanProjectRoot: opts.leanProject,
    ...(opts.sourceRoot === undefined ? {} : { sourceRoot: path.resolve(opts.sourceRoot) }),
    ...(opts.behaviourLimit === undefined ? {} : { behaviourLimit: opts.behaviourLimit }),
  };
  let held = true;
  for (const manifest of opts.manifests) {
    const report = await verifyLeanToTypeScriptRoundtrip(path.resolve(manifest), options);
    if (!reportRoundtrip(report, opts.json)) held = false;
  }
  if (opts.sources.length > 0) {
    const sources = opts.sources.map((source) => path.resolve(source));
    const report = await verifyTypeScriptToLeanRoundtrip(sources, options);
    if (!reportRoundtrip(report, opts.json)) held = false;
  }
  return held;
}

// ─── Compile dispatcher ──────────────────────────────────────────────────────

function runCompile(opts: CompileOpts): void {
  if (opts.watch) {
    watchMode(opts);
    return;
  }
  const accepted = opts.isDir ? compileProject(opts) : compileSingle(opts);
  if (!accepted) process.exitCode = 1;
}

export async function runTsleanCli(arguments_: readonly string[]): Promise<void> {
  const command = parseArgs(arguments_);
  if (command.cmd === 'help') {
    process.stdout.write(HELP);
  } else if (command.cmd === 'version') {
    process.stdout.write(`tslean ${getVersion()}\n`);
  } else if (command.cmd === 'init') {
    if (!initProject(command.dir)) process.exitCode = 1;
  } else if (command.cmd === 'ts-to-lean') {
    runCompile(command.opts);
  } else if (command.cmd === 'roundtrip') {
    if (!await runRoundtrip(command.opts)) process.exitCode = 1;
  } else {
    runLeanToTypeScriptCli(command.arguments);
  }
}

const entrypoint = process.argv[1];
if (entrypoint !== undefined && import.meta.url === pathToFileURL(fs.realpathSync(entrypoint)).href) {
  runTsleanCli(process.argv.slice(2)).catch((failure: unknown) => {
    error(failure instanceof Error ? failure.message : String(failure));
    process.exitCode = 1;
  });
}
