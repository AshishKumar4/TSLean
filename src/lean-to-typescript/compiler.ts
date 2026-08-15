import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { createRequire } from 'node:module';
import { tmpdir } from 'node:os';
import { basename, delimiter, dirname, extname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import ts from 'typescript';
import type { LeanToTypeScriptArtifact, LeanToTypeScriptInput, LeanToTypeScriptManifest } from './artifact.js';
import { emitTypeScript } from './emitter.js';
import { decodeLeanSemanticProgram } from './ir.js';
import { compareCodePoints } from './ordering.js';

export interface LeanToTypeScriptRequest {
  readonly projectRoot: string;
  readonly moduleName: string;
  readonly sourcePath: string;
  readonly declarations: readonly string[];
}

export interface LeanToTypeScriptCompilerInput {
  readonly identity: string;
  readonly path: string;
}

export interface LeanToTypeScriptCompilation {
  readonly artifact: LeanToTypeScriptArtifact;
  readonly inputs: readonly LeanToTypeScriptCompilerInput[];
}

export class UnsupportedLeanFragmentError extends TypeError {
  public readonly code = 'UNSUPPORTED_LEAN_FRAGMENT';

  public constructor(
    public readonly declaration: string,
    public readonly diagnostic: string,
  ) {
    super(`${declaration}: ${diagnostic}`);
    this.name = 'UnsupportedLeanFragmentError';
  }
}

interface InputFile {
  readonly kind: LeanToTypeScriptInput['kind'];
  readonly identity: string;
  readonly path: string;
}

interface InputSnapshot extends InputFile, LeanToTypeScriptInput {
  readonly contents: Buffer;
}

interface CompilationLayout {
  readonly packageRoot: string;
  readonly compilerLeanRoot: string;
  readonly compilerSourceSnapshots: readonly InputSnapshot[];
  readonly exporterBuildSourcePath: string;
  readonly typescriptPath: string;
  readonly targetSourcePath: string;
}

export function compileLeanToTypeScript(request: LeanToTypeScriptRequest): LeanToTypeScriptArtifact {
  return compileLeanToTypeScriptWithInputs(request).artifact;
}

export function compileLeanToTypeScriptWithInputs(request: LeanToTypeScriptRequest): LeanToTypeScriptCompilation {
  const normalized = normalizeRequest(request);
  const directory = mkdtempSync(join(tmpdir(), 'tslean-compilation-'));
  try {
    const layout = compilationLayout(normalized, join(directory, 'compiler'));
    return compileNormalized(normalized, layout, join(directory, 'export'));
  } finally {
    rmSync(directory, { force: true, recursive: true });
  }
}

function compileNormalized(
  normalized: LeanToTypeScriptRequest,
  layout: CompilationLayout,
  directory: string,
): LeanToTypeScriptCompilation {
  prepareLeanModules(normalized, layout);
  const moduleFiles = collectModuleFiles(normalized, layout);
  const targetModules = collectTargetModuleNames(normalized);
  assertTargetSource(moduleFiles, normalized.moduleName, layout.targetSourcePath);
  const snapshots = mergeSnapshots(
    layout.compilerSourceSnapshots,
    snapshotInputs(inputFiles(normalized, layout, moduleFiles)),
  );

  prepareLeanModules(normalized, layout);
  assertSameModuleClosure(moduleFiles, collectModuleFiles(normalized, layout));
  assertSameStrings(targetModules, collectTargetModuleNames(normalized), 'target Lean module closure changed');
  assertUnchanged(snapshots);

  mkdirSync(directory);
  const importRoot = join(directory, 'imports');
  const leanLibraryRoot = dirname(requiredInputPath(snapshots, 'module:Init'));
  stageLeanModules(importRoot, leanLibraryRoot, snapshots);
  const driverPath = join(directory, 'Export.lean');
  writeFileSync(driverPath, exportDriver(normalized, targetModules), 'utf8');
  const leanExecutable = requiredInputPath(snapshots, 'target-toolchain:lean-executable');
  const response = decodeExporterResponse(
    runLean(leanExecutable, normalized.projectRoot, [driverPath], 'semantic export', {
      LEAN_PATH: [importRoot, leanLibraryRoot].join(delimiter),
    }),
  );
  assertSameModuleClosure(moduleFiles, collectModuleFiles(normalized, layout));
  assertSameStrings(targetModules, collectTargetModuleNames(normalized), 'target Lean module closure changed');
  assertUnchanged(snapshots);
  if (!response.ok) throw unsupportedError(response.error, normalized.declarations[0]);

  const program = decodeLeanSemanticProgram(response.package);
  if (!sameStrings(program.roots, normalized.declarations)) {
    throw new TypeError('Lean semantic exporter returned different roots than requested');
  }
  const toolchain = toolchainIdentity(normalized.projectRoot);
  const compilerToolchain = toolchainIdentity(layout.compilerLeanRoot);
  if (!sameToolchain(toolchain, compilerToolchain)) {
    throw new TypeError('target and compiler Lean toolchains do not match exactly');
  }
  const inputs = snapshots.map(({ kind, identity, sha256: digest }) => ({
    kind,
    identity,
    sha256: digest,
  }));
  const artifact = emitTypeScript(program, {
    schemaVersion: 1,
    fragmentVersion: program.fragmentVersion,
    sourceModule: normalized.moduleName,
    declarations: normalized.declarations,
    semanticIrSha256: sha256(JSON.stringify(program)),
    inputClosureSha256: sha256(JSON.stringify(inputs)),
    inputs,
    typescriptVersion: ts.version,
    runtime: runtimeIdentity(),
    leanToolchain: toolchain,
  });
  assertTypeChecks(artifact.code, directory);
  assertSameModuleClosure(moduleFiles, collectModuleFiles(normalized, layout));
  assertSameStrings(targetModules, collectTargetModuleNames(normalized), 'target Lean module closure changed');
  assertUnchanged(snapshots);
  return {
    artifact,
    inputs: snapshots.map(({ identity, path }) => ({ identity, path })),
  };
}

function normalizeRequest(request: LeanToTypeScriptRequest): LeanToTypeScriptRequest {
  const modulePattern = /^[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*$/u;
  if (!modulePattern.test(request.moduleName)) {
    throw new TypeError(`invalid Lean module name: ${request.moduleName}`);
  }
  if (request.declarations.length === 0) throw new TypeError('at least one declaration is required');
  for (const declaration of request.declarations) {
    if (!isQualifiedLeanName(declaration)) {
      throw new TypeError(`invalid Lean declaration name: ${declaration}`);
    }
  }
  if (new Set(request.declarations).size !== request.declarations.length) {
    throw new TypeError('Lean declaration roots contain duplicates');
  }
  const projectRoot = realpathSync(request.projectRoot);
  const sourcePath = realpathSync(request.sourcePath);
  if (!statSync(sourcePath).isFile()) throw new TypeError('Lean source path must name a file');
  if (!isWithin(projectRoot, sourcePath)) throw new TypeError('Lean source path must be inside the target project');
  return {
    projectRoot,
    sourcePath,
    moduleName: request.moduleName,
    declarations: [...request.declarations].sort(compareCodePoints),
  };
}

function compilationLayout(request: LeanToTypeScriptRequest, compilerLeanRoot: string): CompilationLayout {
  const packageRoot = realpathSync(resolve(dirname(fileURLToPath(import.meta.url)), '..', '..'));
  const compilerSourceRoot = realpathSync(join(packageRoot, 'lean'));
  const compilerSourceSnapshots = snapshotInputs([
    ...compilerLeanSources(compilerSourceRoot),
    ...projectInputs(compilerSourceRoot, 'compiler-project'),
  ]);
  stageCompilerProject(compilerSourceRoot, compilerLeanRoot, compilerSourceSnapshots);
  return {
    packageRoot,
    compilerLeanRoot,
    compilerSourceSnapshots,
    exporterBuildSourcePath: realpathSync(join(compilerLeanRoot, 'TSLean', 'LeanToTypeScript', 'Export.lean')),
    typescriptPath: realpathSync(createRequire(import.meta.url).resolve('typescript')),
    targetSourcePath: request.sourcePath,
  };
}

function prepareLeanModules(request: LeanToTypeScriptRequest, layout: CompilationLayout): void {
  runLake(layout.compilerLeanRoot, ['-H', 'build', 'TSLean.LeanToTypeScript.Export'], 'exporter build');
  runLake(request.projectRoot, ['-H', 'build', request.moduleName], 'target build');
}

function collectModuleFiles(request: LeanToTypeScriptRequest, layout: CompilationLayout): readonly InputFile[] {
  const artifacts = [
    moduleArtifact(layout.compilerLeanRoot, 'TSLean.LeanToTypeScript.Export'),
    ...moduleDependencies(layout.compilerLeanRoot, layout.exporterBuildSourcePath),
    moduleArtifact(request.projectRoot, request.moduleName),
    ...moduleDependencies(request.projectRoot, request.sourcePath),
  ];
  const modules = new Map<string, string>();
  for (const artifact of artifacts.map((path) => realpathSync(path))) {
    const moduleName = moduleNameFromArtifact(artifact);
    const existing = modules.get(moduleName);
    if (existing !== undefined && existing !== artifact) {
      throw new TypeError(`Lean module ${moduleName} resolves to multiple artifacts`);
    }
    modules.set(moduleName, artifact);
  }
  const files: InputFile[] = [];
  for (const [moduleName, artifact] of [...modules].sort(([left], [right]) => compareCodePoints(left, right))) {
    files.push({ kind: 'lean-module', identity: `module:${moduleName}`, path: artifact });
    const source = sourceFromTrace(artifact);
    if (source !== undefined) files.push({ kind: 'lean-source', identity: `source:${moduleName}`, path: source });
  }
  return files;
}

function collectTargetModuleNames(request: LeanToTypeScriptRequest): readonly string[] {
  const targetBuildRoot = realpathSync(join(request.projectRoot, '.lake', 'build', 'lib', 'lean'));
  const names = [
    moduleArtifact(request.projectRoot, request.moduleName),
    ...moduleDependencies(request.projectRoot, request.sourcePath),
  ]
    .map((path) => realpathSync(path))
    .filter((path) => isWithin(targetBuildRoot, path))
    .map(moduleNameFromArtifact)
    .filter((name, index, names) => names.indexOf(name) === index)
    .sort(compareCodePoints);
  if (!names.includes(request.moduleName)) throw new TypeError('target module is outside its project build tree');
  return names;
}

function inputFiles(
  request: LeanToTypeScriptRequest,
  layout: CompilationLayout,
  moduleFiles: readonly InputFile[],
): readonly InputFile[] {
  const extension = extname(fileURLToPath(import.meta.url));
  const compilerDirectory = dirname(fileURLToPath(import.meta.url));
  const compilerFiles = compilerModuleFiles(compilerDirectory, extension);
  return [
    ...compilerFiles,
    { kind: 'compiler', identity: 'compiler:package', path: realpathSync(join(layout.packageRoot, 'package.json')) },
    { kind: 'compiler', identity: 'compiler:runtime', path: realpathSync(process.execPath) },
    {
      kind: 'compiler',
      identity: 'compiler-toolchain:lean-executable',
      path: toolchainExecutable(layout.compilerLeanRoot, 'lean'),
    },
    {
      kind: 'compiler',
      identity: 'compiler-toolchain:lake-executable',
      path: toolchainExecutable(layout.compilerLeanRoot, 'lake'),
    },
    {
      kind: 'compiler',
      identity: 'target-toolchain:lean-executable',
      path: toolchainExecutable(request.projectRoot, 'lean'),
    },
    {
      kind: 'compiler',
      identity: 'target-toolchain:lake-executable',
      path: toolchainExecutable(request.projectRoot, 'lake'),
    },
    ...projectInputs(request.projectRoot, 'target-project'),
    ...moduleFiles,
    { kind: 'typescript', identity: 'typescript:compiler', path: layout.typescriptPath },
    {
      kind: 'typescript',
      identity: 'typescript:package',
      path: realpathSync(join(dirname(layout.typescriptPath), '..', 'package.json')),
    },
    ...['lib.decorators.d.ts', 'lib.decorators.legacy.d.ts', 'lib.es5.d.ts'].map((name): InputFile => ({
      kind: 'typescript',
      identity: `typescript:library:${name}`,
      path: realpathSync(join(dirname(layout.typescriptPath), name)),
    })),
  ];
}

function compilerModuleFiles(directory: string, extension: string): readonly InputFile[] {
  return filesRecursively(directory, extension).map((path) => {
    const name = relative(directory, path).slice(0, -extension.length).split(sep).join('/');
    return { kind: 'compiler', identity: `compiler:${name}`, path };
  });
}

function compilerLeanSources(projectRoot: string): readonly InputFile[] {
  const sourceRoot = join(projectRoot, 'TSLean', 'LeanToTypeScript');
  const exporterPath = realpathSync(join(sourceRoot, 'Export.lean'));
  return filesRecursively(sourceRoot, '.lean').map((path) => ({
    kind: 'compiler',
    identity:
      path === exporterPath
        ? 'compiler:lean-exporter'
        : `compiler:lean-source:${relative(projectRoot, path).split(sep).join('/')}`,
    path,
  }));
}

function filesRecursively(directory: string, extension: string): readonly string[] {
  const files: string[] = [];
  const visit = (current: string): void => {
    for (const entry of readdirSync(current, { withFileTypes: true }).sort((left, right) =>
      compareCodePoints(left.name, right.name),
    )) {
      const path = join(current, entry.name);
      if (entry.isSymbolicLink()) throw new TypeError(`compiler source tree contains symlink: ${path}`);
      if (entry.isDirectory()) {
        visit(path);
      } else if (entry.isFile() && extname(entry.name) === extension) {
        files.push(realpathSync(path));
      }
    }
  };
  visit(directory);
  return files;
}

function stageCompilerProject(sourceRoot: string, destinationRoot: string, snapshots: readonly InputSnapshot[]): void {
  for (const snapshot of snapshots) {
    if (!isWithin(sourceRoot, snapshot.path)) throw new TypeError('compiler project input is outside the package');
    const destination = join(destinationRoot, relative(sourceRoot, snapshot.path));
    mkdirSync(dirname(destination), { recursive: true });
    writeFileSync(destination, snapshot.contents);
  }
}

function toolchainExecutable(projectRoot: string, executable: 'lake' | 'lean'): string {
  const path = runLake(projectRoot, ['env', 'which', executable], `${executable} executable`).trim();
  if (path.length === 0) throw new TypeError(`Lake environment has no ${executable} executable`);
  return realpathSync(path);
}

function projectInputs(projectRoot: string, identity: string): readonly InputFile[] {
  return ['lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain']
    .map((name) => join(projectRoot, name))
    .filter(existsSync)
    .map((path): InputFile => ({
      kind: 'lean-project',
      identity: `${identity}:${basename(path)}`,
      path: realpathSync(path),
    }));
}

function snapshotInputs(files: readonly InputFile[]): readonly InputSnapshot[] {
  const ordered = [...files].sort((left, right) => compareCodePoints(left.identity, right.identity));
  for (let index = 1; index < ordered.length; index += 1) {
    if (ordered[index - 1]?.identity === ordered[index]?.identity) {
      throw new TypeError(`duplicate compiler input identity ${ordered[index]?.identity}`);
    }
  }
  return ordered.map((file) => {
    const contents = readFileSync(file.path);
    return { ...file, contents, sha256: sha256(contents) };
  });
}

function mergeSnapshots(...groups: readonly (readonly InputSnapshot[])[]): readonly InputSnapshot[] {
  const snapshots = groups.flat().sort((left, right) => compareCodePoints(left.identity, right.identity));
  for (let index = 1; index < snapshots.length; index += 1) {
    if (snapshots[index - 1]?.identity === snapshots[index]?.identity) {
      throw new TypeError(`duplicate compiler input identity ${snapshots[index]?.identity}`);
    }
  }
  return snapshots;
}

function stageLeanModules(directory: string, leanLibraryRoot: string, snapshots: readonly InputSnapshot[]): void {
  for (const snapshot of snapshots) {
    if (snapshot.kind !== 'lean-module' || isWithin(leanLibraryRoot, snapshot.path)) continue;
    const moduleName = snapshot.identity.slice('module:'.length);
    const path = join(directory, `${moduleName.split('.').join(sep)}.olean`);
    mkdirSync(dirname(path), { recursive: true });
    writeFileSync(path, snapshot.contents);
  }
}

function requiredInputPath(snapshots: readonly InputSnapshot[], identity: string): string {
  const snapshot = snapshots.find((candidate) => candidate.identity === identity);
  if (snapshot === undefined) throw new TypeError(`compiler input ${identity} is missing`);
  return snapshot.path;
}

function assertUnchanged(snapshots: readonly InputSnapshot[]): void {
  for (const snapshot of snapshots) {
    if (!snapshot.contents.equals(readFileSync(snapshot.path))) {
      throw new TypeError(`compiler input changed during Lean to TypeScript compilation: ${snapshot.identity}`);
    }
  }
}

function assertSameModuleClosure(expected: readonly InputFile[], actual: readonly InputFile[]): void {
  const normalize = (files: readonly InputFile[]): readonly string[] =>
    files.map((file) => `${file.identity}\0${realpathSync(file.path)}`).sort(compareCodePoints);
  if (!sameStrings(normalize(expected), normalize(actual))) {
    throw new TypeError('Lean module closure changed during Lean to TypeScript compilation');
  }
}

function assertTargetSource(moduleFiles: readonly InputFile[], moduleName: string, sourcePath: string): void {
  const source = moduleFiles.find((file) => file.identity === `source:${moduleName}`);
  if (source === undefined) throw new TypeError(`Lean build trace has no source for module ${moduleName}`);
  if (realpathSync(source.path) !== sourcePath) {
    throw new TypeError(`Lean source path does not define module ${moduleName}`);
  }
}

function moduleArtifact(projectRoot: string, moduleName: string): string {
  const relativePath = `${moduleName.split('.').join(sep)}.olean`;
  const candidates = runLake(projectRoot, ['env', 'printenv', 'LEAN_PATH'], `${moduleName} search path`)
    .trim()
    .split(delimiter)
    .map((directory) => join(directory, relativePath))
    .filter(existsSync);
  const artifact = candidates[0];
  if (artifact === undefined) {
    throw new TypeError(`Lake returned no module artifact for ${moduleName}`);
  }
  return artifact;
}

function moduleDependencies(projectRoot: string, sourcePath: string): readonly string[] {
  return runLake(projectRoot, ['env', 'lean', '--deps', sourcePath], 'module dependencies')
    .split(/\r?\n/u)
    .filter((path) => path.endsWith('.olean'));
}

function moduleNameFromArtifact(path: string): string {
  const marker = `${sep}lib${sep}lean${sep}`;
  const markerIndex = path.lastIndexOf(marker);
  if (markerIndex < 0 || !path.endsWith('.olean')) {
    throw new TypeError(`cannot derive Lean module name from ${path}`);
  }
  return path
    .slice(markerIndex + marker.length, -'.olean'.length)
    .split(sep)
    .join('.');
}

function sourceFromTrace(artifact: string): string | undefined {
  const tracePath = artifact.replace(/\.olean$/u, '.trace');
  if (!existsSync(tracePath)) return undefined;
  const trace: unknown = JSON.parse(readFileSync(tracePath, 'utf8'));
  const sources = [
    ...new Set(
      allStrings(trace)
        .filter((value) => value.endsWith('.lean') && existsSync(value))
        .map((path) => realpathSync(path)),
    ),
  ];
  if (sources.length > 1) throw new TypeError(`Lean module trace names multiple source files: ${tracePath}`);
  return sources[0];
}

function allStrings(value: unknown): readonly string[] {
  if (typeof value === 'string') return [value];
  if (Array.isArray(value)) return value.flatMap(allStrings);
  if (isRecord(value)) return Object.values(value).flatMap(allStrings);
  return [];
}

function exportDriver(request: LeanToTypeScriptRequest, targetModules: readonly string[]): string {
  const roots = request.declarations.map((declaration) => JSON.stringify(declaration)).join(' ');
  const modules = JSON.stringify(targetModules.join('\n'));
  return [
    'import TSLean.LeanToTypeScript.Export',
    `import ${request.moduleName}`,
    '',
    `#tslean_export ${JSON.stringify(request.moduleName)} ${modules} ${roots}`,
    '',
  ].join('\n');
}

type ExporterResponse =
  { readonly ok: true; readonly package: unknown } | { readonly ok: false; readonly error: string };

function decodeExporterResponse(output: string): ExporterResponse {
  const lines = output
    .split(/\r?\n/u)
    .filter((candidate) => candidate.startsWith('{"error"') || candidate.startsWith('{"ok"'));
  if (lines.length !== 1) throw new TypeError('Lean semantic exporter must emit exactly one response');
  const line = lines[0];
  if (line === undefined) throw new TypeError('Lean semantic exporter emitted no response');
  const parsed: unknown = JSON.parse(line);
  if (!isRecord(parsed)) throw new TypeError('Lean semantic exporter response must be an object');
  const fields = Object.keys(parsed).sort(compareCodePoints);
  if (parsed['ok'] === true && sameStrings(fields, ['ok', 'package'])) {
    return { ok: true, package: parsed['package'] };
  }
  if (parsed['ok'] === false && typeof parsed['error'] === 'string' && sameStrings(fields, ['error', 'ok'])) {
    return { ok: false, error: parsed['error'] };
  }
  throw new TypeError('Lean semantic exporter response has an invalid shape');
}

function unsupportedError(message: string, fallbackDeclaration: string): UnsupportedLeanFragmentError {
  const separator = message.indexOf(': ');
  const candidate = separator < 0 ? '' : message.slice(0, separator);
  const declaration = isQualifiedLeanName(candidate) ? candidate : fallbackDeclaration;
  return new UnsupportedLeanFragmentError(declaration, separator < 0 ? message : message.slice(separator + 2));
}

function isQualifiedLeanName(value: string): boolean {
  const components = value.split('.');
  return components.length >= 2 && components.every((component) => component.length > 0);
}

function assertTypeChecks(code: string, directory: string): void {
  const path = join(directory, 'generated.ts');
  writeFileSync(path, code, 'utf8');
  const program = ts.createProgram([path], {
    module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext,
    noEmit: true,
    lib: ['lib.es5.d.ts'],
    strict: true,
    target: ts.ScriptTarget.ES2022,
  });
  const diagnostics = ts.getPreEmitDiagnostics(program);
  if (diagnostics.length > 0) {
    const rendered = diagnostics.map((diagnostic) => ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n'));
    throw new TypeError(`generated TypeScript failed type checking:\n${rendered.join('\n')}`);
  }
}

function toolchainIdentity(projectRoot: string): LeanToTypeScriptManifest['leanToolchain'] {
  const identity = readFileSync(join(projectRoot, 'lean-toolchain'), 'utf8').trim();
  if (identity.length === 0) throw new TypeError('lean-toolchain is empty');
  return {
    identity,
    leanVersion: runLake(projectRoot, ['env', 'lean', '--version'], 'Lean version').trim(),
    lakeVersion: runLake(projectRoot, ['--version'], 'Lake version').trim(),
  };
}

function sameToolchain(
  left: LeanToTypeScriptManifest['leanToolchain'],
  right: LeanToTypeScriptManifest['leanToolchain'],
): boolean {
  return (
    left.identity === right.identity && left.leanVersion === right.leanVersion && left.lakeVersion === right.lakeVersion
  );
}

function runLake(
  projectRoot: string,
  arguments_: readonly string[],
  label: string,
  environment: Readonly<Record<string, string>> = {},
): string {
  return runLean('lake', projectRoot, arguments_, label, environment);
}

function runLean(
  executable: string,
  projectRoot: string,
  arguments_: readonly string[],
  label: string,
  environment: Readonly<Record<string, string>> = {},
): string {
  const result = spawnSync(executable, arguments_, {
    cwd: projectRoot,
    encoding: 'utf8',
    env: { ...process.env, ...environment },
    maxBuffer: 64 * 1024 * 1024,
  });
  if (result.error !== undefined) throw new TypeError(`Lean ${label} could not start: ${result.error.message}`);
  if (result.status !== 0) {
    const output = [result.stdout.trimEnd(), result.stderr.trimEnd()].filter(Boolean).join('\n');
    throw new TypeError(`Lean ${label} failed${output ? `:\n${output}` : ''}`);
  }
  return result.stdout;
}

function runtimeIdentity(): string {
  const bunVersion = process.versions['bun'];
  return bunVersion === undefined ? `node:${process.version}` : `bun:${bunVersion}`;
}

function isWithin(root: string, path: string): boolean {
  const name = relative(root, path);
  return name.length > 0 && name !== '..' && !name.startsWith(`..${sep}`) && !isAbsolute(name);
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function sameStrings(left: readonly string[], right: readonly string[]): boolean {
  return left.length === right.length && left.every((value, index) => value === right[index]);
}

function assertSameStrings(expected: readonly string[], actual: readonly string[], message: string): void {
  if (!sameStrings(expected, actual)) throw new TypeError(message);
}

function sha256(value: string | Buffer): string {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}
