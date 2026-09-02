import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import {
  accessSync,
  chmodSync,
  constants,
  existsSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  realpathSync,
  rmSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, delimiter, dirname, extname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { assertRuntimeInputsUnchanged, runtimeInputSnapshots } from './runtime-provenance.js';
import * as ts from '../typescript-api/index.js';
import { emitted as printer } from '../typescript-api/emitted-syntax.js';
import { openProject, renderDiagnostics } from '../typescript-api/session.js';
import {
  LEAN_TO_TYPESCRIPT_INPUT_PLANES,
  type LeanToTypeScriptEnvironmentAttestation,
  type LeanToTypeScriptInput,
  type LeanToTypeScriptPackage,
} from './artifact.js';
import {
  assertRuntimeCertificateCoverage,
  assertRuntimeOpcodeCertificates,
  loadRuntimeCertificateRegistry,
} from './certificates.js';
import { emitTypeScriptPackage } from './emitter.js';
import { UnsupportedLeanFragmentError } from './fragment.js';
import { decodeLeanSemanticProgram, isLeanModuleName, LEAN_RUNTIME_OPCODES, referencedRuntimeOpcodes } from './ir.js';
import { compareCodePoints } from './ordering.js';
import { LEAN_TO_TYPESCRIPT_HOST_MODULE_PATH } from './package-layout.js';
import {
  assertLeanToTypeScriptPlatform,
  hostLeanToTypeScriptPlatform,
  type LeanToTypeScriptPlatform,
} from './platform.js';

export interface LeanToTypeScriptRequest {
  readonly projectRoot: string;
  readonly moduleName: string;
  readonly sourcePath: string;
  readonly declarations: readonly string[];
  /**
   * Where the generated package root will be written. Source maps resolve from their own location
   * back to the Lean sources, so callers that write elsewhere supply this directory. Library
   * callers that only inspect the package use the deterministic project-local default.
   */
  readonly outputDirectory?: string;
}

export interface LeanToTypeScriptCompilerInput {
  readonly identity: string;
  readonly path: string;
}

export interface LeanToTypeScriptCompilation {
  readonly package: LeanToTypeScriptPackage;
  readonly inputs: readonly LeanToTypeScriptCompilerInput[];
}

interface InputFile {
  readonly kind: LeanToTypeScriptInput['kind'];
  readonly identity: string;
  readonly path: string;
}

interface InputSnapshot extends InputFile, LeanToTypeScriptInput {
  readonly contents?: Buffer;
  readonly filesystemVersion?: FilesystemVersion;
}

interface FilesystemVersion {
  readonly device: bigint;
  readonly inode: bigint;
  readonly size: bigint;
  readonly modified: bigint;
  readonly changed: bigint;
}

interface CompilationLayout {
  readonly compilerLeanRoot: string;
  readonly compilerSourceSnapshots: readonly InputSnapshot[];
  readonly exporterBuildSourcePath: string;
  readonly targetProjectRoot: string;
  readonly targetProjectSnapshots: readonly InputSnapshot[];
  readonly targetSourcePath: string;
}

interface LeanToolchain {
  readonly identity: string;
  readonly leanVersion: string;
  readonly lakeVersion: string;
  readonly lake: InputSnapshot;
  readonly lean: InputSnapshot;
  readonly closure: readonly InputSnapshot[];
}

interface CachedToolchainInput {
  readonly filesystemVersion: FilesystemVersion;
  readonly sha256: string;
}

const toolchainInputCache = new Map<string, CachedToolchainInput>();

export function compileLeanToTypeScript(request: LeanToTypeScriptRequest): LeanToTypeScriptPackage {
  return compileLeanToTypeScriptWithInputs(request).package;
}

export function compileLeanToTypeScriptWithInputs(
  request: LeanToTypeScriptRequest,
  platform: LeanToTypeScriptPlatform = hostLeanToTypeScriptPlatform,
): LeanToTypeScriptCompilation {
  assertLeanToTypeScriptPlatform(platform);
  assertRuntimeInputsUnchanged();
  const normalized = normalizeRequest(request);
  const directory = mkdtempSync(join(tmpdir(), 'tslean-compilation-'));
  try {
    const layout = compilationLayout(normalized, join(directory, 'compiler'), join(directory, 'target'));
    const launcher = snapshotInputs([
      { kind: 'lean-toolchain', identity: 'toolchain-launcher:lake', path: findExecutableOnPath('lake') },
    ])[0];
    if (launcher === undefined) throw new TypeError('Lake launcher snapshot is missing');
    const compilerCandidate = resolveToolchain(layout.compilerLeanRoot, launcher, 'compiler-toolchain');
    const targetCandidate = resolveToolchain(layout.targetProjectRoot, launcher, 'target-toolchain');
    if (!sameToolchain(targetCandidate, compilerCandidate)) {
      throw new TypeError('target and compiler Lean toolchains do not match exactly');
    }
    const closure = snapshotToolchainInputs(toolchainClosure(compilerCandidate));
    const compilerToolchain = { ...compilerCandidate, closure };
    const targetToolchain = { ...targetCandidate, closure };
    return compileNormalized(
      normalized,
      layout,
      join(directory, 'export'),
      launcher,
      compilerToolchain,
      targetToolchain,
    );
  } finally {
    makeDirectoriesWritable(directory);
    rmSync(directory, { force: true, recursive: true });
  }
}

function compileNormalized(
  normalized: LeanToTypeScriptRequest,
  layout: CompilationLayout,
  directory: string,
  launcher: InputSnapshot,
  compilerToolchain: LeanToolchain,
  targetToolchain: LeanToolchain,
): LeanToTypeScriptCompilation {
  const targetRequest = stagedTargetRequest(normalized, layout);
  prepareLeanModules(targetRequest, layout, compilerToolchain, targetToolchain);
  assertRequestedSourceMatchesModule(targetRequest, targetToolchain);
  const moduleFiles = collectModuleFiles(targetRequest, layout, compilerToolchain, targetToolchain);
  const targetModules = collectTargetModuleNames(targetRequest, targetToolchain);
  assertTargetSource(moduleFiles, normalized.moduleName, layout.targetSourcePath);
  const snapshots = mergeSnapshots(
    runtimeInputSnapshots,
    layout.compilerSourceSnapshots,
    [
      launcher,
      compilerToolchain.lake,
      compilerToolchain.lean,
      targetToolchain.lake,
      targetToolchain.lean,
      ...compilerToolchain.closure,
    ],
    snapshotInputs(inputFiles(normalized, moduleFiles)),
  );

  prepareLeanModules(targetRequest, layout, compilerToolchain, targetToolchain);
  assertSameModuleClosure(moduleFiles, collectModuleFiles(targetRequest, layout, compilerToolchain, targetToolchain));
  assertSameStrings(
    targetModules,
    collectTargetModuleNames(targetRequest, targetToolchain),
    'target Lean module closure changed',
  );
  assertStagedProjectsUnchanged(layout);
  assertUnchanged(snapshots);

  mkdirSync(directory);
  const importRoot = join(directory, 'imports');
  const leanLibraryRoot = dirname(requiredInputPath(snapshots, 'module:Init'));
  stageLeanModules(importRoot, leanLibraryRoot, snapshots);
  const driverPath = join(directory, 'Export.lean');
  writeFileSync(driverPath, exportDriver(normalized, targetModules), 'utf8');
  const response = decodeExporterResponse(
    runCaptured(
      targetToolchain.lean,
      targetToolchain.closure,
      layout.targetProjectRoot,
      [driverPath],
      'semantic export',
      {
        LEAN_PATH: [importRoot, leanLibraryRoot].join(delimiter),
      },
    ),
  );
  assertSameModuleClosure(moduleFiles, collectModuleFiles(targetRequest, layout, compilerToolchain, targetToolchain));
  assertSameStrings(
    targetModules,
    collectTargetModuleNames(targetRequest, targetToolchain),
    'target Lean module closure changed',
  );
  assertStagedProjectsUnchanged(layout);
  assertUnchanged(snapshots);
  if (!response.ok) throw unsupportedError(response.error, normalized.declarations[0]);

  const program = decodeLeanSemanticProgram(response.package);
  if (!sameStrings(program.roots, normalized.declarations)) {
    throw new TypeError('Lean semantic exporter returned different roots than requested');
  }
  const inputs = snapshots.map(({ kind, identity, sha256: digest }) => ({ kind, identity, sha256: digest }));
  const semanticInputs = inputs.filter((input) => LEAN_TO_TYPESCRIPT_INPUT_PLANES[input.kind] === 'semantic');
  const environmentInputs = inputs.filter((input) => LEAN_TO_TYPESCRIPT_INPUT_PLANES[input.kind] === 'environment');
  const outputDirectory = normalized.outputDirectory;
  if (outputDirectory === undefined) throw new TypeError('normalized generated output directory is missing');
  // Before anything is built: the registry and the admitted opcode set cover each other exactly,
  // and every opcode this program spends carries a proved certificate.
  const { catalog } = loadRuntimeCertificateRegistry();
  assertRuntimeCertificateCoverage(Object.keys(LEAN_RUNTIME_OPCODES).sort(compareCodePoints), catalog);
  assertRuntimeOpcodeCertificates([...referencedRuntimeOpcodes(program)].sort(compareCodePoints), catalog);
  const emitted = emitTypeScriptPackage(program, {
    certificates: catalog,
    semantic: {
      fragmentVersion: program.fragmentVersion,
      entryModule: normalized.moduleName,
      declarations: normalized.declarations,
      leanToolchain: {
        identity: targetToolchain.identity,
        leanVersion: targetToolchain.leanVersion,
        lakeVersion: targetToolchain.lakeVersion,
      },
      inputs: semanticInputs,
      inputClosureSha256: sha256(JSON.stringify(semanticInputs)),
      semanticIrSha256: sha256(JSON.stringify(program)),
    },
    environment: hostEnvironmentAttestation(environmentInputs),
    sources: leanSourcePaths(normalized, moduleFiles, layout),
    leanProjectPath: relativeForwardSlashed(outputDirectory, normalized.projectRoot),
  });
  assertPackageTypeChecks(emitted, directory);
  assertSameModuleClosure(moduleFiles, collectModuleFiles(targetRequest, layout, compilerToolchain, targetToolchain));
  assertSameStrings(
    targetModules,
    collectTargetModuleNames(targetRequest, targetToolchain),
    'target Lean module closure changed',
  );
  assertStagedProjectsUnchanged(layout);
  assertUnchanged(snapshots);
  return {
    package: emitted,
    inputs: snapshots.map(({ identity, path }) => ({ identity, path })),
  };
}

function normalizeRequest(request: LeanToTypeScriptRequest): LeanToTypeScriptRequest {
  if (!isLeanModuleName(request.moduleName)) {
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
    outputDirectory: resolve(request.outputDirectory ?? join(projectRoot, '.tslean-generated')),
  };
}

/**
 * One directory relative to another, forward-slashed. The generated package records where its Lean
 * project sits, so a source map written anywhere still names a source a consumer can open.
 */
function relativeForwardSlashed(from: string, to: string): string {
  const path = relative(from, to).split(sep).join('/');
  if (path === '') throw new TypeError('generated package root and Lean project root are the same directory');
  return path;
}

function compilationLayout(
  request: LeanToTypeScriptRequest,
  compilerLeanRoot: string,
  targetProjectRoot: string,
): CompilationLayout {
  const packageRoot = realpathSync(resolve(dirname(fileURLToPath(import.meta.url)), '..', '..'));
  const compilerSourceRoot = realpathSync(join(packageRoot, 'lean'));
  const compilerSourceSnapshots = snapshotInputs([
    ...compilerLeanSources(compilerSourceRoot),
    ...projectInputs(compilerSourceRoot, 'compiler-project'),
  ]);
  const targetProjectSnapshots = snapshotInputs([
    ...projectInputs(request.projectRoot, 'target-project'),
    ...targetLeanSources(request.projectRoot),
  ]);
  stageCompilerProject(compilerSourceRoot, compilerLeanRoot, compilerSourceSnapshots);
  stageProject(request.projectRoot, targetProjectRoot, targetProjectSnapshots);
  return {
    compilerLeanRoot,
    compilerSourceSnapshots,
    exporterBuildSourcePath: realpathSync(join(compilerLeanRoot, 'TSLean', 'LeanToTypeScript', 'Export.lean')),
    targetProjectRoot,
    targetProjectSnapshots,
    targetSourcePath: request.sourcePath,
  };
}

function stagedTargetRequest(request: LeanToTypeScriptRequest, layout: CompilationLayout): LeanToTypeScriptRequest {
  return {
    ...request,
    projectRoot: layout.targetProjectRoot,
    sourcePath: join(layout.targetProjectRoot, relative(request.projectRoot, request.sourcePath)),
  };
}

function prepareLeanModules(
  request: LeanToTypeScriptRequest,
  layout: CompilationLayout,
  compilerToolchain: LeanToolchain,
  targetToolchain: LeanToolchain,
): void {
  runLake(
    compilerToolchain,
    layout.compilerLeanRoot,
    ['-H', 'build', 'TSLean.LeanToTypeScript.Export'],
    'exporter build',
  );
  runLake(targetToolchain, request.projectRoot, ['-H', 'build', request.moduleName], 'target build');
}

interface LeanProject {
  readonly toolchain: LeanToolchain;
  readonly projectRoot: string;
  readonly moduleName: string;
  readonly sourcePath: string;
}

function collectModuleFiles(
  request: LeanToTypeScriptRequest,
  layout: CompilationLayout,
  compilerToolchain: LeanToolchain,
  targetToolchain: LeanToolchain,
): readonly InputFile[] {
  const projects: readonly LeanProject[] = [
    {
      toolchain: compilerToolchain,
      projectRoot: layout.compilerLeanRoot,
      moduleName: 'TSLean.LeanToTypeScript.Export',
      sourcePath: layout.exporterBuildSourcePath,
    },
    {
      toolchain: targetToolchain,
      projectRoot: request.projectRoot,
      moduleName: request.moduleName,
      sourcePath: request.sourcePath,
    },
  ];
  const modules = new Map<string, { readonly artifact: string; readonly source: string | undefined }>();
  for (const project of projects) {
    const searchRoots = leanSearchRoots(project.toolchain, project.projectRoot);
    const sourceRoots = projectSourceRoots(project.toolchain, project.projectRoot);
    for (const path of transitiveModuleArtifacts(project)) {
      const artifact = realpathSync(path);
      const moduleName = moduleNameFromArtifact(searchRoots, artifact);
      const existing = modules.get(moduleName);
      if (existing !== undefined && existing.artifact !== artifact) {
        throw new TypeError(`Lean module ${moduleName} resolves to multiple artifacts`);
      }
      modules.set(moduleName, { artifact, source: moduleSource(sourceRoots, moduleName) });
    }
  }
  const files: InputFile[] = [];
  for (const [moduleName, module] of [...modules].sort(([left], [right]) => compareCodePoints(left, right))) {
    files.push({ kind: 'lean-module', identity: `module:${moduleName}`, path: module.artifact });
    if (module.source !== undefined) {
      files.push({
        kind: 'lean-source',
        identity: `source:${moduleName}`,
        path: originalTargetSourcePath(module.source, layout),
      });
    }
  }
  return files;
}

function collectTargetModuleNames(request: LeanToTypeScriptRequest, toolchain: LeanToolchain): readonly string[] {
  const project: LeanProject = {
    toolchain,
    projectRoot: request.projectRoot,
    moduleName: request.moduleName,
    sourcePath: request.sourcePath,
  };
  const searchRoots = leanSearchRoots(toolchain, request.projectRoot);
  const buildRoots = withinProject(request.projectRoot, searchRoots);
  const names = transitiveModuleArtifacts(project)
    .filter((path) => buildRoots.some((root) => isWithin(root, path)))
    .map((path) => moduleNameFromArtifact(searchRoots, path))
    .filter((name, index, names) => names.indexOf(name) === index)
    .sort(compareCodePoints);
  if (!names.includes(request.moduleName)) throw new TypeError('target module is outside its project build tree');
  return names;
}

/**
 * Every compiled Lean module the entry module reaches, transitively. `lean --deps` names one hop,
 * so the walk follows each project-built dependency through its own source. A dependency Lake
 * resolved outside the project's own build directories is the toolchain boundary: it is recorded
 * and not expanded, because Lake's source path for the project cannot name its source.
 */
function transitiveModuleArtifacts(project: LeanProject): readonly string[] {
  const { toolchain, projectRoot } = project;
  const searchRoots = leanSearchRoots(toolchain, projectRoot);
  const sourceRoots = projectSourceRoots(toolchain, projectRoot);
  const artifacts = new Set<string>([realpathSync(moduleArtifact(toolchain, projectRoot, project.moduleName))]);
  const pending = [realpathSync(project.sourcePath)];
  const visited = new Set<string>();
  while (pending.length > 0) {
    const source = pending.pop();
    if (source === undefined || visited.has(source)) continue;
    visited.add(source);
    for (const dependency of moduleDependencies(toolchain, projectRoot, source)) {
      const artifact = realpathSync(dependency);
      if (artifacts.has(artifact)) continue;
      artifacts.add(artifact);
      const dependencySource = moduleSource(sourceRoots, moduleNameFromArtifact(searchRoots, artifact));
      if (dependencySource !== undefined) pending.push(dependencySource);
    }
  }
  return [...artifacts].sort(compareCodePoints);
}

function inputFiles(request: LeanToTypeScriptRequest, moduleFiles: readonly InputFile[]): readonly InputFile[] {
  return [...projectInputs(request.projectRoot, 'target-project'), ...moduleFiles];
}

function compilerLeanSources(projectRoot: string): readonly InputFile[] {
  const sourceRoot = join(projectRoot, 'TSLean', 'LeanToTypeScript');
  const exporterPath = realpathSync(join(sourceRoot, 'Export.lean'));
  return filesRecursively(sourceRoot, '.lean').map((path) => ({
    kind: 'compiler-source',
    identity:
      path === exporterPath
        ? 'compiler:lean-exporter'
        : `compiler:lean-source:${relative(projectRoot, path).split(sep).join('/')}`,
    path,
  }));
}

/**
 * Every Lean source in the target project, staged so Lake can rebuild it in isolation.
 * `lakefile.lean` is deliberately excluded: it is Lake configuration rather than a module of the
 * project, `projectInputs` already captures it, and staging the same path under two identities
 * would both double-count it in the recorded input closure and write it twice into a tree whose
 * files are made read-only as they land.
 */
function targetLeanSources(projectRoot: string): readonly InputFile[] {
  const files: InputFile[] = [];
  const visit = (directory: string): void => {
    for (const entry of readdirSync(directory, { withFileTypes: true }).sort((left, right) =>
      compareCodePoints(left.name, right.name),
    )) {
      if (entry.name === '.git' || entry.name === '.lake') continue;
      if (directory === projectRoot && entry.name === 'lakefile.lean') continue;
      const path = join(directory, entry.name);
      if (entry.isSymbolicLink()) throw new TypeError(`target project source tree contains symlink: ${path}`);
      if (entry.isDirectory()) {
        visit(path);
      } else if (entry.isFile() && extname(entry.name) === '.lean') {
        files.push({
          kind: 'lean-source',
          identity: `target-stage-source:${relative(projectRoot, path).split(sep).join('/')}`,
          path: realpathSync(path),
        });
      }
    }
  };
  visit(projectRoot);
  return files;
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
  stageProject(sourceRoot, destinationRoot, snapshots);
}

function stageProject(sourceRoot: string, destinationRoot: string, snapshots: readonly InputSnapshot[]): void {
  for (const snapshot of snapshots) {
    if (!isWithin(sourceRoot, snapshot.path)) throw new TypeError('staged project input is outside its project root');
    const destination = join(destinationRoot, relative(sourceRoot, snapshot.path));
    mkdirSync(dirname(destination), { recursive: true });
    writeFileSync(destination, requiredSnapshotContents(snapshot));
    chmodSync(destination, 0o444);
  }
  mkdirSync(join(destinationRoot, '.lake'), { recursive: true });
  makeSourceDirectoriesReadOnly(destinationRoot);
}

function originalTargetSourcePath(sourcePath: string, layout: CompilationLayout): string {
  if (!isWithin(layout.targetProjectRoot, sourcePath)) return sourcePath;
  const candidate = resolve(
    commonProjectRoot(layout.targetProjectSnapshots, layout.targetSourcePath),
    relative(layout.targetProjectRoot, sourcePath),
  );
  return existsSync(candidate) ? realpathSync(candidate) : sourcePath;
}

function commonProjectRoot(snapshots: readonly InputSnapshot[], targetSourcePath: string): string {
  const projectInput = snapshots.find((snapshot) => snapshot.identity.startsWith('target-project:'));
  if (projectInput !== undefined) return dirname(projectInput.path);
  let candidate = dirname(targetSourcePath);
  while (dirname(candidate) !== candidate) {
    if (existsSync(join(candidate, 'lean-toolchain'))) return candidate;
    candidate = dirname(candidate);
  }
  throw new TypeError('target project root cannot be recovered from staged inputs');
}

function resolveToolchain(projectRoot: string, launcher: InputSnapshot, prefix: string): LeanToolchain {
  const lakePath = executableReportedByLake(launcher, projectRoot, 'lake');
  const lake = snapshotInputs([{ kind: 'lean-toolchain', identity: `${prefix}:lake-executable`, path: lakePath }])[0];
  if (lake === undefined) throw new TypeError(`${prefix} Lake executable snapshot is missing`);
  const leanPath = executableReportedByLake(lake, projectRoot, 'lean');
  const lean = snapshotInputs([{ kind: 'lean-toolchain', identity: `${prefix}:lean-executable`, path: leanPath }])[0];
  if (lean === undefined) throw new TypeError(`${prefix} Lean executable snapshot is missing`);
  const identity = readFileSync(join(projectRoot, 'lean-toolchain'), 'utf8').trim();
  if (identity.length === 0) throw new TypeError('lean-toolchain is empty');
  return {
    identity,
    leanVersion: runCaptured(lean, [], projectRoot, ['--version'], 'Lean version').trim(),
    lakeVersion: runCaptured(lake, [], projectRoot, ['--version'], 'Lake version').trim(),
    lake,
    lean,
    closure: [],
  };
}

function executableReportedByLake(
  lakeExecutable: InputSnapshot,
  projectRoot: string,
  executable: 'lake' | 'lean',
): string {
  const path = runCaptured(lakeExecutable, [], projectRoot, ['env', 'which', executable], `${executable} executable`, {
    PATH: executablePath(lakeExecutable.path),
  }).trim();
  if (path.length === 0) throw new TypeError(`Lake environment has no ${executable} executable`);
  return realpathSync(path);
}

function toolchainClosure(toolchain: LeanToolchain): readonly InputFile[] {
  const paths = [...new Set([...linkedLibraries(toolchain.lake), ...linkedLibraries(toolchain.lean)])].sort(
    compareCodePoints,
  );
  return paths.map((path, index) => ({
    kind: 'lean-toolchain',
    identity: `toolchain-runtime:${index.toString().padStart(2, '0')}:${basename(path)}`,
    path,
  }));
}

function linkedLibraries(executable: InputSnapshot): readonly string[] {
  assertUnchanged([executable]);
  const result = spawnSync(executable.path, [], {
    encoding: 'utf8',
    env: { ...sanitizedProcessEnvironment(), LD_TRACE_LOADED_OBJECTS: '1' },
    maxBuffer: 4 * 1024 * 1024,
  });
  assertUnchanged([executable]);
  if (result.error !== undefined) {
    throw new TypeError(`toolchain runtime closure could not be inspected: ${result.error.message}`);
  }
  if (result.status !== 0) {
    throw new TypeError(`toolchain runtime closure inspection failed: ${result.stderr.trim()}`);
  }
  const libraries: string[] = [];
  for (const line of result.stdout.split(/\r?\n/u)) {
    const normalized = line.trim();
    if (normalized.length === 0 || normalized.startsWith('linux-vdso')) continue;
    if (normalized.includes('=> not found')) {
      throw new TypeError(`toolchain runtime dependency is unavailable: ${normalized}`);
    }
    const resolved = normalized.includes('=>')
      ? normalized
          .slice(normalized.indexOf('=>') + 2)
          .trim()
          .split(/\s+/u)[0]
      : normalized.split(/\s+/u)[0];
    if (resolved !== undefined && isAbsolute(resolved)) libraries.push(realpathSync(resolved));
  }
  if (libraries.length === 0) throw new TypeError('toolchain runtime closure inspection returned no files');
  return libraries;
}

function findExecutableOnPath(name: string): string {
  const path = process.env['PATH'];
  if (path === undefined) throw new TypeError('PATH is unavailable while locating the Lake launcher');
  for (const component of path.split(delimiter)) {
    const candidate = resolve(component.length === 0 ? process.cwd() : component, name);
    try {
      accessSync(candidate, constants.X_OK);
      if (statSync(candidate).isFile()) return realpathSync(candidate);
    } catch (error: unknown) {
      if (!hasFilesystemError(error, 'ENOENT', 'ENOTDIR', 'EACCES')) throw error;
    }
  }
  throw new TypeError('Lake launcher is not available on PATH');
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
  const ordered = orderedUniqueInputs(files);
  return ordered.map((file) => {
    const before = filesystemVersion(file.path);
    const contents = readFileSync(file.path);
    const after = filesystemVersion(file.path);
    if (!sameFilesystemVersion(before, after)) {
      throw new TypeError(`compiler input changed while it was captured: ${file.identity}`);
    }
    return { ...file, contents, filesystemVersion: after, sha256: sha256(contents) };
  });
}

function snapshotToolchainInputs(files: readonly InputFile[]): readonly InputSnapshot[] {
  return orderedUniqueInputs(files).map((file) => {
    const current = filesystemVersion(file.path);
    const cached = toolchainInputCache.get(file.path);
    if (cached !== undefined && sameFilesystemVersion(cached.filesystemVersion, current)) {
      return { ...file, ...cached };
    }
    const contents = readFileSync(file.path);
    const after = filesystemVersion(file.path);
    if (!sameFilesystemVersion(current, after)) {
      throw new TypeError(`toolchain input changed while it was captured: ${file.identity}`);
    }
    const captured = { filesystemVersion: after, sha256: sha256(contents) };
    toolchainInputCache.set(file.path, captured);
    return { ...file, ...captured };
  });
}

function orderedUniqueInputs(files: readonly InputFile[]): readonly InputFile[] {
  const ordered = [...files].sort((left, right) => compareCodePoints(left.identity, right.identity));
  for (let index = 1; index < ordered.length; index += 1) {
    if (ordered[index - 1]?.identity === ordered[index]?.identity) {
      throw new TypeError(`duplicate compiler input identity ${ordered[index]?.identity}`);
    }
  }
  return ordered;
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
    writeFileSync(path, requiredSnapshotContents(snapshot));
  }
}

function requiredInputPath(snapshots: readonly InputSnapshot[], identity: string): string {
  const snapshot = snapshots.find((candidate) => candidate.identity === identity);
  if (snapshot === undefined) throw new TypeError(`compiler input ${identity} is missing`);
  return snapshot.path;
}

function assertUnchanged(snapshots: readonly InputSnapshot[]): void {
  for (const snapshot of snapshots) {
    const changed =
      snapshot.filesystemVersion === undefined
        ? !requiredSnapshotContents(snapshot).equals(readFileSync(snapshot.path))
        : !sameFilesystemVersion(snapshot.filesystemVersion, filesystemVersion(snapshot.path));
    if (changed) {
      throw new TypeError(`compiler input changed during Lean to TypeScript compilation: ${snapshot.identity}`);
    }
  }
}

function requiredSnapshotContents(snapshot: InputSnapshot): Buffer {
  if (snapshot.contents === undefined) {
    throw new TypeError(`compiler input bytes are unavailable: ${snapshot.identity}`);
  }
  return snapshot.contents;
}

function filesystemVersion(path: string): FilesystemVersion {
  const metadata = statSync(path, { bigint: true });
  if (!metadata.isFile()) throw new TypeError(`compiler input is not a regular file: ${path}`);
  return {
    device: metadata.dev,
    inode: metadata.ino,
    size: metadata.size,
    modified: metadata.mtimeNs,
    changed: metadata.ctimeNs,
  };
}

function sameFilesystemVersion(left: FilesystemVersion, right: FilesystemVersion): boolean {
  return (
    left.device === right.device &&
    left.inode === right.inode &&
    left.size === right.size &&
    left.modified === right.modified &&
    left.changed === right.changed
  );
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

/**
 * A path list Lake reports for a project, as absolute directories. Lake 5.0.0-128a1e6 (Lean 4.16)
 * reports the project's own directories relative to the package — `././.lake/build/lib`,
 * `./././.` — while later Lake versions report them absolutely, and the compiled-module directory
 * moved one level deeper into `lib/lean`. Resolving against the project root normalises both, so
 * nothing downstream has to know which layout produced a path.
 */
function leanPathRoots(
  toolchain: LeanToolchain,
  projectRoot: string,
  variable: string,
  label: string,
): readonly string[] {
  return runLake(toolchain, projectRoot, ['env', 'printenv', variable], label)
    .trim()
    .split(delimiter)
    .filter((entry) => entry.length > 0)
    .map((entry) => resolve(projectRoot, entry))
    .map((directory) => (existsSync(directory) ? realpathSync(directory) : directory));
}

/** Where Lake looks for compiled modules. */
function leanSearchRoots(toolchain: LeanToolchain, projectRoot: string): readonly string[] {
  return leanPathRoots(toolchain, projectRoot, 'LEAN_PATH', 'Lean search path');
}

/**
 * Where Lake looks for the project's own module sources, honouring each library's `srcDir`. The
 * toolchain's own source directories are excluded, so a module the project did not build has no
 * source and terminates the walk instead of dragging core Lean sources into the input closure.
 */
function projectSourceRoots(toolchain: LeanToolchain, projectRoot: string): readonly string[] {
  return withinProject(projectRoot, leanPathRoots(toolchain, projectRoot, 'LEAN_SRC_PATH', 'Lean source path'));
}

function withinProject(projectRoot: string, directories: readonly string[]): readonly string[] {
  const root = realpathSync(projectRoot);
  return directories.filter((directory) => directory === root || isWithin(root, directory));
}

function moduleArtifact(toolchain: LeanToolchain, projectRoot: string, moduleName: string): string {
  const relativePath = `${moduleName.split('.').join(sep)}.olean`;
  const artifact = leanSearchRoots(toolchain, projectRoot)
    .map((directory) => join(directory, relativePath))
    .find(existsSync);
  if (artifact === undefined) {
    throw new TypeError(`Lake returned no module artifact for ${moduleName}`);
  }
  return artifact;
}

/**
 * `sourcePath` is a provenance identity, not a hint. Resolve the requested Lake module through
 * the configured source roots before traversing dependencies, so a path for another module is
 * rejected without accidentally treating its imports as the target program.
 */
function assertRequestedSourceMatchesModule(request: LeanToTypeScriptRequest, toolchain: LeanToolchain): void {
  const source = moduleSource(projectSourceRoots(toolchain, request.projectRoot), request.moduleName);
  if (source === undefined || source !== realpathSync(request.sourcePath)) {
    throw new TypeError(`Lean source path does not define module ${request.moduleName}`);
  }
}

/** The source Lake would compile for a module, or `undefined` when the project does not own it. */
function moduleSource(sourceRoots: readonly string[], moduleName: string): string | undefined {
  const relativePath = `${moduleName.split('.').join(sep)}.lean`;
  const source = sourceRoots.map((directory) => join(directory, relativePath)).find(existsSync);
  return source === undefined ? undefined : realpathSync(source);
}

function moduleDependencies(toolchain: LeanToolchain, projectRoot: string, sourcePath: string): readonly string[] {
  return runLake(toolchain, projectRoot, ['env', 'lean', '--deps', sourcePath], 'module dependencies')
    .split(/\r?\n/u)
    .filter((path) => path.endsWith('.olean'))
    .map((path) => resolve(projectRoot, path));
}

function moduleNameFromArtifact(searchRoots: readonly string[], path: string): string {
  if (!path.endsWith('.olean')) throw new TypeError(`cannot derive Lean module name from ${path}`);
  const root = searchRoots.find((candidate) => isWithin(candidate, path));
  if (root === undefined) {
    throw new TypeError(`Lean module artifact is outside every Lake search root: ${path}`);
  }
  return relative(root, path).slice(0, -'.olean'.length).split(sep).join('.');
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

/**
 * The exporter's one response line, selected by shape rather than by leading text. Lean's `Json`
 * renderer walks an object's keys in ascending order at 4.29 and descending order at 4.16, so
 * `{"ok":true,"package":…}` and `{"package":…,"ok":true}` are the same response and neither
 * spelling may be privileged. The recorded semantic IR digest is unaffected: it is taken over the
 * decoded program this compiler rebuilds, not over the bytes Lean printed.
 */
function decodeExporterResponse(output: string): ExporterResponse {
  const candidates = output
    .split(/\r?\n/u)
    .map((line) => parsedJsonObject(line))
    .filter((value): value is Record<string, unknown> => value !== undefined && 'ok' in value);
  if (candidates.length !== 1) throw new TypeError('Lean semantic exporter must emit exactly one response');
  const parsed = candidates[0];
  if (parsed === undefined) throw new TypeError('Lean semantic exporter emitted no response');
  const fields = Object.keys(parsed).sort(compareCodePoints);
  if (parsed['ok'] === true && sameStrings(fields, ['ok', 'package'])) {
    return { ok: true, package: parsed['package'] };
  }
  if (parsed['ok'] === false && typeof parsed['error'] === 'string' && sameStrings(fields, ['error', 'ok'])) {
    return { ok: false, error: parsed['error'] };
  }
  throw new TypeError('Lean semantic exporter response has an invalid shape');
}

function parsedJsonObject(line: string): Record<string, unknown> | undefined {
  if (!line.startsWith('{')) return undefined;
  let parsed: unknown;
  try {
    parsed = JSON.parse(line);
  } catch {
    return undefined;
  }
  return isRecord(parsed) ? parsed : undefined;
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

/**
 * The whole emitted tree is type-checked as one program, in the layout a consumer receives, so a
 * cross-module import that does not resolve is a compilation failure rather than a later surprise.
 * `noUnusedLocals` is on: an import the module does not need would mean the reference analysis
 * over-approximated, and that is a compiler defect, not a style question.
 *
 * The modules are written immediately before they are read, and an earlier compilation in this
 * process may have written the same paths: opening a project carries a change notice for every
 * path the session has already read, so the check grades the bytes just written rather than the
 * ones an earlier call left behind. The project is released afterwards because nothing outside
 * this check reads the generated tree.
 */
function assertPackageTypeChecks(emitted: LeanToTypeScriptPackage, directory: string): void {
  const root = join(directory, 'package');
  const paths = emitted.modules.map((module) => {
    const path = join(root, module.path);
    mkdirSync(dirname(path), { recursive: true });
    writeFileSync(path, module.code, 'utf8');
    return path;
  });
  // A package that declares a host boundary imports the substrate's module through a path the
  // package itself reserves, so the tree the consumer links always carries one more file than the
  // tree this compiler writes. The stub linked here is generated from the manifest's own hosts rows,
  // so the type check exercises the same names the artifact declares and the substrate owes.
  const hosts = emitted.manifest.semantic.hosts;
  if (hosts.length > 0) {
    const hostPath = join(root, LEAN_TO_TYPESCRIPT_HOST_MODULE_PATH);
    writeFileSync(
      hostPath,
      [
        '// Generated host-module stub: the substrate provides the real implementation.',
        ...hosts.map((host) => `export declare const ${host.binding}: (...arguments_: readonly unknown[]) => unknown;`),
        '',
      ].join('\n'),
      'utf8',
    );
    paths.push(hostPath);
  }
  const project = openProject({
    files: paths,
    settings: {
      module: 'nodenext',
      moduleResolution: 'nodenext',
      noEmit: true,
      noUnusedLocals: true,
      lib: ['es2022'],
      strict: true,
      target: 'es2022',
    },
  });
  try {
    const diagnostics = project.diagnostics();
    if (diagnostics.length > 0) {
      throw new TypeError(`generated TypeScript failed type checking:\n${renderDiagnostics(diagnostics)}`);
    }
  } finally {
    project.close();
  }
}

/**
 * Each target Lean module's source path, relative to the target project root. The compiler
 * already resolved every module's source through Lake's build traces, so provenance reuses that
 * resolution instead of guessing a source layout from the module name.
 */
function leanSourcePaths(
  request: LeanToTypeScriptRequest,
  moduleFiles: readonly InputFile[],
  layout: CompilationLayout,
): ReadonlyMap<string, string> {
  const sources = new Map<string, string>();
  for (const file of moduleFiles) {
    if (file.kind !== 'lean-source') continue;
    const moduleName = file.identity.slice('source:'.length);
    if (!isWithin(request.projectRoot, file.path) && !isWithin(layout.targetProjectRoot, file.path)) continue;
    const root = isWithin(request.projectRoot, file.path) ? request.projectRoot : layout.targetProjectRoot;
    sources.set(moduleName, relative(root, file.path).split(sep).join('/'));
  }
  return sources;
}

/**
 * The machine this compilation ran on. Two TypeScript versions are recorded because two compilers
 * did the work: the printer built and wrote the emitted syntax, so it is the version the generated
 * bytes came out of, and the reader type-checked that tree, so it is the version whose acceptance
 * the package claims.
 */
function hostEnvironmentAttestation(inputs: readonly LeanToTypeScriptInput[]): LeanToTypeScriptEnvironmentAttestation {
  const bunVersion = process.versions['bun'];
  return {
    runtime: bunVersion === undefined ? `node:${process.version}` : `bun:${bunVersion}`,
    typescriptVersion: ts.version,
    printerVersion: printer.version,
    platform: `${process.platform}-${process.arch}`,
    inputs,
    inputClosureSha256: sha256(JSON.stringify(inputs)),
    runtimeConformance: [],
  };
}

function sameToolchain(left: LeanToolchain, right: LeanToolchain): boolean {
  return (
    left.identity === right.identity &&
    left.leanVersion === right.leanVersion &&
    left.lakeVersion === right.lakeVersion &&
    left.lean.path === right.lean.path &&
    left.lake.path === right.lake.path &&
    left.lean.sha256 === right.lean.sha256 &&
    left.lake.sha256 === right.lake.sha256
  );
}

function runLake(
  toolchain: LeanToolchain,
  projectRoot: string,
  arguments_: readonly string[],
  label: string,
  environment: Readonly<Record<string, string>> = {},
): string {
  return runCaptured(toolchain.lake, [toolchain.lean, ...toolchain.closure], projectRoot, arguments_, label, {
    ...environment,
    PATH: executablePath(toolchain.lake.path, environment['PATH']),
  });
}

function runCaptured(
  executable: InputSnapshot,
  closure: readonly InputSnapshot[],
  projectRoot: string,
  arguments_: readonly string[],
  label: string,
  environment: Readonly<Record<string, string>> = {},
): string {
  const captured = [executable, ...closure];
  assertUnchanged(captured);
  try {
    return runLean(executable.path, projectRoot, arguments_, label, environment);
  } finally {
    assertUnchanged(captured);
  }
}

function executablePath(executable: string, inheritedPath = process.env['PATH']): string {
  return [dirname(executable), inheritedPath].filter((value): value is string => value !== undefined).join(delimiter);
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
    env: { ...sanitizedProcessEnvironment(), ...environment },
    maxBuffer: 64 * 1024 * 1024,
  });
  if (result.error !== undefined) throw new TypeError(`Lean ${label} could not start: ${result.error.message}`);
  if (result.status !== 0) {
    const output = [result.stdout.trimEnd(), result.stderr.trimEnd()].filter(Boolean).join('\n');
    throw new TypeError(`Lean ${label} failed${output ? `:\n${output}` : ''}`);
  }
  return result.stdout;
}

function sanitizedProcessEnvironment(): NodeJS.ProcessEnv {
  const environment = { ...process.env };
  for (const name of Object.keys(environment)) {
    if (
      name.startsWith('LD_') ||
      name.startsWith('DYLD_') ||
      name === 'ELAN_TOOLCHAIN' ||
      name === 'LEAN_PATH' ||
      name === 'LEAN_SRC_PATH' ||
      name === 'LEAN_SYSROOT'
    ) {
      delete environment[name];
    }
  }
  return environment;
}

function assertStagedProjectsUnchanged(layout: CompilationLayout): void {
  assertUnchanged(layout.compilerSourceSnapshots);
  assertUnchanged(layout.targetProjectSnapshots);
  for (const snapshot of [...layout.compilerSourceSnapshots, ...layout.targetProjectSnapshots]) {
    const sourceRoot = snapshot.identity.startsWith('compiler')
      ? commonCompilerProjectRoot(layout.compilerSourceSnapshots)
      : commonProjectRoot(layout.targetProjectSnapshots, layout.targetSourcePath);
    const destinationRoot = snapshot.identity.startsWith('compiler')
      ? layout.compilerLeanRoot
      : layout.targetProjectRoot;
    const stagedPath = join(destinationRoot, relative(sourceRoot, snapshot.path));
    if (!requiredSnapshotContents(snapshot).equals(readFileSync(stagedPath))) {
      throw new TypeError(`staged compiler input changed during Lean to TypeScript compilation: ${snapshot.identity}`);
    }
  }
}

function commonCompilerProjectRoot(snapshots: readonly InputSnapshot[]): string {
  const projectInput = snapshots.find((snapshot) => snapshot.identity.startsWith('compiler-project:'));
  if (projectInput === undefined) throw new TypeError('compiler project root cannot be recovered from staged inputs');
  return dirname(projectInput.path);
}

function makeSourceDirectoriesReadOnly(root: string): void {
  const visit = (directory: string): void => {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      if (entry.name === '.lake') continue;
      if (entry.isDirectory()) visit(join(directory, entry.name));
    }
    chmodSync(directory, 0o555);
  };
  visit(root);
}

function makeDirectoriesWritable(root: string): void {
  if (!existsSync(root)) return;
  const metadata = lstatSync(root);
  if (!metadata.isDirectory() || metadata.isSymbolicLink()) return;
  chmodSync(root, metadata.mode | 0o700);
  for (const entry of readdirSync(root)) makeDirectoriesWritable(join(root, entry));
}

function hasFilesystemError(error: unknown, ...codes: readonly string[]): boolean {
  return error instanceof Error && 'code' in error && typeof error.code === 'string' && codes.includes(error.code);
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
