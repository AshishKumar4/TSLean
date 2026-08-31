/**
 * @module lean-check
 *
 * Elaborate generated Lean under the pinned toolchain and report what Lean said.
 *
 * A degradation scan reads the artifact the compiler produced. It cannot report a
 * miscompilation that emits well-formed but ill-typed Lean, because such an artifact
 * carries no placeholder at all. Only the Lean elaborator answers whether Lean accepts
 * the module, so every caller that claims acceptance runs this.
 *
 * The elaboration runs `lean` inside the runtime project, so the project's own
 * `lean-toolchain` pin selects the toolchain and the runtime library is the built one.
 * Generated modules live in a scratch root. That root overlays the project module path, so
 * the check writes nothing into the runtime project and still resolves a checked module in
 * preference to a stale build of the same name.
 */

import { spawnSync } from 'node:child_process';
import { delimiter, dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';

/** One generated Lean module and the modules of the same set it imports. */
export interface LeanModuleSource {
  /** Dotted Lean module name, for example `TSLean.Generated.Placement`. */
  readonly module: string;
  readonly code: string;
  /** Modules of this same set that must elaborate first. */
  readonly imports: readonly string[];
}

export interface LeanDiagnostic {
  readonly module: string;
  readonly severity: 'error' | 'warning';
  readonly line: number;
  readonly column: number;
  readonly message: string;
}

export interface LeanAcceptance {
  /** True when Lean reported no error for any module. */
  readonly accepted: boolean;
  /** Every diagnostic Lean reported, errors and warnings alike. */
  readonly diagnostics: readonly LeanDiagnostic[];
  /** The `lean-toolchain` pin the check ran under. */
  readonly toolchain: string;
}

export interface LeanCheckOptions {
  /** Lake project that supplies the toolchain pin and the runtime library. */
  readonly projectRoot?: string;
}

/** The Lake project shipped with this package. */
export const PACKAGED_LEAN_PROJECT = join(dirname(fileURLToPath(import.meta.url)), '..', 'lean');

/**
 * The toolchain a Lake project pins.
 *
 * @throws TypeError when the project has no `lean-toolchain`, because an unpinned project
 * cannot support a claim about which Lean accepted the module.
 */
export function pinnedLeanToolchain(projectRoot: string): string {
  const pin = join(projectRoot, 'lean-toolchain');
  if (!existsSync(pin)) {
    throw new TypeError(`${projectRoot} has no lean-toolchain, so no toolchain claim is possible`);
  }
  return readFileSync(pin, 'utf8').trim();
}

/**
 * Elaborate every module of the set and report Lean's diagnostics.
 *
 * Modules elaborate in dependency order and each one leaves an `.olean` behind, so a
 * module that imports another sees the same declarations Lean would see in a real build.
 *
 * @throws TypeError when Lake is unavailable. An unavailable checker is not an
 * acceptance: a caller that cannot run Lean has to say so rather than pass.
 */
export function leanAccepts(
  modules: readonly LeanModuleSource[],
  options: LeanCheckOptions = {},
): LeanAcceptance {
  const projectRoot = options.projectRoot ?? PACKAGED_LEAN_PROJECT;
  const root = mkdtempSync(join(tmpdir(), 'tslean-lean-check-'));
  try {
    return elaborateAll(modules, root, projectRoot);
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

/** What running a generated Lean program produced. */
export interface LeanRun extends LeanAcceptance {
  /** The program's standard output, empty when the modules were not accepted. */
  readonly output: string;
}

/**
 * Elaborate the modules, then run one more module that has a `main`, and return what it
 * printed. The driver is how the round trip observes what the Lean side computes.
 *
 * @throws TypeError when the driver itself fails to run after the modules were accepted,
 * because a driver that cannot run reports nothing about the modules.
 */
export function leanRun(
  modules: readonly LeanModuleSource[],
  driver: LeanModuleSource,
  options: LeanCheckOptions = {},
): LeanRun {
  const projectRoot = options.projectRoot ?? PACKAGED_LEAN_PROJECT;
  const root = mkdtempSync(join(tmpdir(), 'tslean-lean-run-'));
  try {
    const acceptance = elaborateAll(modules, root, projectRoot);
    if (!acceptance.accepted) return { ...acceptance, output: '' };
    const file = join(root, `${driver.module.split('.').join('/')}.lean`);
    mkdirSync(dirname(file), { recursive: true });
    writeFileSync(file, driver.code, 'utf8');
    const run = runLean(['--root=' + root, '--run', file], root, projectRoot);
    if (run.status !== 0) {
      throw new TypeError(`the Lean observation driver failed: ${run.stderr.trim() || run.stdout.trim()}`);
    }
    return { ...acceptance, output: run.stdout };
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

function elaborateAll(
  modules: readonly LeanModuleSource[],
  root: string,
  projectRoot: string,
): LeanAcceptance {
  overlayProjectModules(modules, root, projectRoot);
  const diagnostics: LeanDiagnostic[] = [];
  for (const source of elaborationOrder(modules)) {
    const file = join(root, `${source.module.split('.').join('/')}.lean`);
    mkdirSync(dirname(file), { recursive: true });
    writeFileSync(file, source.code, 'utf8');
    diagnostics.push(...elaborate(file, root, projectRoot, source.module));
  }
  return {
    accepted: !diagnostics.some((entry) => entry.severity === 'error'),
    diagnostics,
    toolchain: pinnedLeanToolchain(projectRoot),
  };
}

/**
 * Mirror the project's built modules into the scratch root, leaving the checked modules to
 * own their own paths.
 *
 * Lean resolves a module by turning its name into a path under the first module-path entry
 * that has the leading directory, not by looking for the file. A scratch root holding
 * `TSLean/Generated/Hello.lean` therefore claims the whole `TSLean` namespace and the
 * project's own `TSLean.Runtime.Basic` stops resolving. Linking the project's directories
 * into the scratch root restores them, and a directory a checked module needs is descended
 * into rather than linked, so the module under check always wins over a stale build of the
 * same name.
 */
function overlayProjectModules(
  modules: readonly LeanModuleSource[],
  root: string,
  projectRoot: string,
): void {
  const owned = new Set<string>();
  for (const source of modules) {
    const segments = source.module.split('.');
    for (let depth = 1; depth <= segments.length; depth++) owned.add(segments.slice(0, depth).join('/'));
  }

  const link = (from: string, relative: string): void => {
    for (const entry of readdirSync(from, { withFileTypes: true })) {
      const child = relative === '' ? entry.name : `${relative}/${entry.name}`;
      const target = join(root, child);
      if (existsSync(target)) {
        // A symlink is already a complete view of its source directory. Descending through
        // it could create a child in the runtime project's build tree when a later module
        // path contains a name the first one did not. Only the real directories the overlay
        // made for an owned module may receive more links.
        if (entry.isDirectory() && owned.has(child) && !lstatSync(target).isSymbolicLink()) {
          link(join(from, entry.name), child);
        }
        continue;
      }
      if (entry.isDirectory() && owned.has(child)) {
        mkdirSync(target, { recursive: true });
        link(join(from, entry.name), child);
        continue;
      }
      symlinkSync(join(from, entry.name), target);
    }
  };

  for (const entry of leanModulePath(projectRoot).split(delimiter)) {
    if (entry !== '' && existsSync(entry)) link(entry, '');
  }
}

/**
 * The modules of the set, each after the modules of the set it imports.
 *
 * @throws TypeError on an import cycle, which Lean rejects as well.
 */
function elaborationOrder(modules: readonly LeanModuleSource[]): readonly LeanModuleSource[] {
  const byName = new Map(modules.map((source) => [source.module, source]));
  const ordered: LeanModuleSource[] = [];
  const state = new Map<string, 'visiting' | 'done'>();
  const visit = (source: LeanModuleSource): void => {
    const mark = state.get(source.module);
    if (mark === 'done') return;
    if (mark === 'visiting') throw new TypeError(`import cycle through ${source.module}`);
    state.set(source.module, 'visiting');
    for (const name of source.imports) {
      const dependency = byName.get(name);
      if (dependency !== undefined) visit(dependency);
    }
    state.set(source.module, 'done');
    ordered.push(source);
  };
  for (const source of modules) visit(source);
  return ordered;
}

/** `path:line:column: severity: message`, with the indented detail lines folded in. */
const DIAGNOSTIC_HEADER = /^(?<path>.*?):(?<line>\d+):(?<column>\d+): (?<severity>error|warning): (?<message>.*)$/u;

/**
 * Run `lean` with the scratch root ahead of the runtime project on the module path.
 *
 * `lake env lean` cannot be used here: Lake maps every module under a library's root
 * namespace to that library's build directory, so a scratch module that shares the root
 * namespace would resolve to the project instead of to the scratch root. Asking Lake for
 * the environment once and then running `lean` directly keeps the search order the caller
 * asked for. `elan` still selects the toolchain the project pins, because `lean` runs with
 * the project as its working directory.
 *
 * @throws TypeError when Lake or Lean is unavailable. An unavailable checker is not an
 * acceptance: a caller that cannot run Lean has to say so rather than pass.
 */
function runLean(
  leanArguments: readonly string[],
  root: string,
  projectRoot: string,
): { readonly status: number | null; readonly stdout: string; readonly stderr: string } {
  const run = spawnSync('lean', leanArguments, {
    cwd: projectRoot,
    encoding: 'utf8',
    timeout: 300_000,
    env: { ...process.env, LEAN_PATH: `${root}${delimiter}${leanModulePath(projectRoot)}` },
  });
  if (run.error !== undefined) {
    throw new TypeError(`Lean acceptance needs Lean on PATH: ${run.error.message}`);
  }
  return { status: run.status, stdout: run.stdout, stderr: run.stderr };
}

/** The module path Lake builds for a project, asked once per project. */
const MODULE_PATHS = new Map<string, string>();

function leanModulePath(projectRoot: string): string {
  const cached = MODULE_PATHS.get(projectRoot);
  if (cached !== undefined) return cached;
  const run = spawnSync('lake', ['env', 'printenv', 'LEAN_PATH'], {
    cwd: projectRoot,
    encoding: 'utf8',
    timeout: 300_000,
  });
  if (run.error !== undefined) throw new TypeError(`Lean acceptance needs Lake on PATH: ${run.error.message}`);
  if (run.status !== 0) throw new TypeError(`${projectRoot} is not a Lake project: ${run.stderr.trim()}`);
  const path = run.stdout.trim();
  MODULE_PATHS.set(projectRoot, path);
  return path;
}

function elaborate(
  file: string,
  root: string,
  projectRoot: string,
  module: string,
): readonly LeanDiagnostic[] {
  const olean = `${file.slice(0, -'.lean'.length)}.olean`;
  const run = runLean([`--root=${root}`, '-o', olean, file], root, projectRoot);

  const lines = `${run.stdout}${run.stderr}`.split('\n');
  const diagnostics: LeanDiagnostic[] = [];
  for (let index = 0; index < lines.length; index++) {
    const header = DIAGNOSTIC_HEADER.exec(lines[index]);
    if (header?.groups === undefined) continue;
    // Lean breaks one diagnostic over several lines and does not indent all of them, so
    // the detail runs to the next header rather than to the next unindented line.
    const detail = [header.groups['message']];
    while (index + 1 < lines.length && !DIAGNOSTIC_HEADER.test(lines[index + 1])) {
      const next = lines[++index].trim();
      if (next !== '') detail.push(next);
    }
    diagnostics.push({
      module,
      severity: header.groups['severity'] === 'error' ? 'error' : 'warning',
      line: Number(header.groups['line']),
      column: Number(header.groups['column']),
      message: detail.join(' '),
    });
  }
  if (run.status !== 0 && !diagnostics.some((entry) => entry.severity === 'error')) {
    diagnostics.push({
      module,
      severity: 'error',
      line: 0,
      column: 0,
      message: `lean exited with status ${String(run.status)}${run.stderr.trim() === '' ? '' : `: ${run.stderr.trim()}`}`,
    });
  }
  return diagnostics;
}
