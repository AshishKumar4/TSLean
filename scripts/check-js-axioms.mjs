import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import {
  existsSync,
  lstatSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, isAbsolute, join, resolve, sep } from 'node:path';
import { argv, env, stdout } from 'node:process';
import { fileURLToPath } from 'node:url';
import { STATIC_LEAN_IMPORTS } from '../src/codegen/lower.js';
import { buildLeanFile } from '../src/codegen/v2.js';
import { DO_LEAN_IMPORTS, WORKERS_LEAN_IMPORTS } from '../src/do-model/ambient.js';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { refinementProofRegistry } from './refinement-proof-registry.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const leanDirectory = join(root, 'lean');
const compiledLibraryDirectory = join(leanDirectory, '.lake/build/lib/lean');
const fixtureDirectory = join(root, 'tests/fixtures');
const allowedAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const usage = 'Usage: check-js-axioms.mjs --evidence <input.json> | --self-test';

/**
 * Modules whose source is deliberately outside the default `lake build` target.
 *
 * `TSLean.Veil` is an aggregate of `TSLean.Veil.*` that nothing imports — `TSLean.lean` names the
 * children directly — so Lake never compiles the barrel itself. Every entry is re-checked below:
 * it must name a source module that really has no artifact, so the list cannot outlive its reason.
 */
const unbuiltSourceAllowlist = new Set(['TSLean.Veil']);

/**
 * What the emitted trusted base is measured by, and pinned to the evidence input under
 * `counts.emittedTrustedBase`: the library modules generated code can import, the modules an
 * environment importing them loads, and the declarations audited across those modules.
 *
 * Pinned because printing a number proves nothing: the closure is derived, so a compiler change that
 * stops reaching a module shrinks it silently, and the audit of a module nothing reaches passes for
 * the wrong reason. The key is optional in the input, and every count present is compared exactly,
 * the way `counts.auditedTheorems` is.
 */
const EMITTED_TRUSTED_BASE_KEYS = ['imports', 'modules', 'declarations'];

function fail(message) {
  throw new Error(`JS trust gate failed: ${message}`);
}

function parseArgs(args) {
  if (args.length === 1 && args[0] === '--self-test') return { selfTest: true };
  if (args.length === 2 && args[0] === '--evidence' && !args[1].startsWith('--')) {
    return { evidence: args[1], selfTest: false };
  }
  fail(usage);
}

function object(value, label) {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) fail(`${label} must be an object`);
  return value;
}

function exactKeys(value, expected, label) {
  const actual = Object.keys(object(value, label)).sort();
  const wanted = [...expected].sort();
  if (JSON.stringify(actual) !== JSON.stringify(wanted)) {
    fail(`${label} must contain exactly: ${wanted.join(', ')}`);
  }
}

function nonNegativeInteger(value, label) {
  if (!Number.isSafeInteger(value) || value < 0) fail(`${label} must be a non-negative integer`);
}

function countObject(value, label) {
  for (const [key, entry] of Object.entries(object(value, label))) {
    if (entry !== null && typeof entry === 'object' && !Array.isArray(entry)) countObject(entry, `${label}.${key}`);
    else nonNegativeInteger(entry, `${label}.${key}`);
  }
}

function repositoryFile(path) {
  if (typeof path !== 'string' || path.length === 0 || isAbsolute(path)) {
    fail('--evidence must be a repository-relative path');
  }
  const resolved = resolve(root, path);
  if (!resolved.startsWith(`${root}${sep}`)) fail('--evidence escapes the repository');
  let canonical;
  try {
    canonical = realpathSync(resolved);
  } catch (error) {
    fail(`cannot read --evidence: ${error instanceof Error ? error.message : String(error)}`);
  }
  if (!canonical.startsWith(`${root}${sep}`)) fail('--evidence resolves outside the repository');
  if (!lstatSync(canonical).isFile()) fail('--evidence must name a file');
  return canonical;
}

function readExpectedAuditCount(path) {
  const file = repositoryFile(path);
  let input;
  try {
    input = JSON.parse(readFileSync(file, 'utf8'));
  } catch (error) {
    fail(`invalid evidence JSON: ${error instanceof Error ? error.message : String(error)}`);
  }
  const expectedKeys = [
    'schemaVersion',
    'outputPath',
    'baseRevision',
    'counts',
    'knownTodos',
    'validation',
    'hashGroups',
  ];
  if (input.formalDebt !== undefined) expectedKeys.push('formalDebt');
  if (input.executableAssumptions !== undefined) expectedKeys.push('executableAssumptions');
  if (input.refinementProofs !== undefined) expectedKeys.push('refinementProofs');
  exactKeys(input, expectedKeys, 'evidence input');
  if (input.schemaVersion !== 1) fail('unsupported evidence input schema');
  for (const key of ['outputPath', 'baseRevision']) {
    if (typeof input[key] !== 'string' || input[key].length === 0) fail(`evidence input ${key} must be non-empty`);
  }
  if (!Array.isArray(input.knownTodos)) fail('evidence input knownTodos must be an array');
  object(input.validation, 'evidence input validation');
  object(input.hashGroups, 'evidence input hashGroups');
  if (input.formalDebt !== undefined) object(input.formalDebt, 'evidence input formalDebt');
  if (input.executableAssumptions !== undefined) {
    object(input.executableAssumptions, 'evidence input executableAssumptions');
  }
  let refinementProofs;
  if (input.refinementProofs !== undefined) {
    refinementProofs = object(input.refinementProofs, 'evidence input refinementProofs');
    exactKeys(refinementProofs, ['audited', 'required', 'registryHash'], 'evidence input refinementProofs');
    for (const key of ['audited', 'required']) {
      nonNegativeInteger(refinementProofs[key], `refinementProofs.${key}`);
      if (refinementProofs[key] === 0) fail(`refinementProofs.${key} must be positive`);
    }
    if (refinementProofs.required > refinementProofs.audited) {
      fail('refinementProofs.required must not exceed refinementProofs.audited');
    }
    if (
      typeof refinementProofs.registryHash !== 'string' ||
      !/^sha256:[0-9a-f]{64}$/.test(refinementProofs.registryHash)
    ) {
      fail('refinementProofs.registryHash must be a lowercase SHA-256 digest');
    }
  }
  const counts = object(input.counts, 'counts');
  const countKeys = ['tests', 'lean', 'corpus', 'auditedTheorems', 'lint', 'build'];
  if (counts.differentialScenarios !== undefined) countKeys.push('differentialScenarios');
  if (counts.differential !== undefined) countKeys.push('differential');
  if (counts.emittedTrustedBase !== undefined) countKeys.push('emittedTrustedBase');
  exactKeys(counts, countKeys, 'counts');
  exactKeys(counts.tests, ['files', 'passed', 'failed', 'todo'], 'counts.tests');
  for (const key of ['files', 'passed', 'failed', 'todo']) nonNegativeInteger(counts.tests[key], `counts.tests.${key}`);
  exactKeys(counts.lean, ['jobs', 'status'], 'counts.lean');
  nonNegativeInteger(counts.lean.jobs, 'counts.lean.jobs');
  if (counts.lean.status !== 'passed') fail('counts.lean.status must be passed');
  exactKeys(counts.corpus, ['entries', 'red'], 'counts.corpus');
  nonNegativeInteger(counts.corpus.entries, 'counts.corpus.entries');
  nonNegativeInteger(counts.corpus.red, 'counts.corpus.red');
  if (counts.corpus.red > counts.corpus.entries) fail('counts.corpus.red must not exceed counts.corpus.entries');
  nonNegativeInteger(counts.auditedTheorems, 'counts.auditedTheorems');
  if (counts.auditedTheorems === 0) fail('counts.auditedTheorems must be positive');
  if (counts.differentialScenarios !== undefined) {
    nonNegativeInteger(counts.differentialScenarios, 'counts.differentialScenarios');
  }
  if (counts.differential !== undefined) countObject(counts.differential, 'counts.differential');
  if (counts.lint !== 'passed') fail('counts.lint must be passed');
  if (counts.build !== 'passed') fail('counts.build must be passed');
  let emittedTrustedBase;
  if (counts.emittedTrustedBase !== undefined) {
    emittedTrustedBase = object(counts.emittedTrustedBase, 'counts.emittedTrustedBase');
    exactKeys(emittedTrustedBase, EMITTED_TRUSTED_BASE_KEYS, 'counts.emittedTrustedBase');
    for (const key of EMITTED_TRUSTED_BASE_KEYS) {
      nonNegativeInteger(emittedTrustedBase[key], `counts.emittedTrustedBase.${key}`);
      if (emittedTrustedBase[key] === 0) fail(`counts.emittedTrustedBase.${key} must be positive`);
    }
    // Every emitted import is a loaded module, so the environment cannot hold fewer.
    if (emittedTrustedBase.modules < emittedTrustedBase.imports) {
      fail('counts.emittedTrustedBase.modules must not be below counts.emittedTrustedBase.imports');
    }
  }
  return { js: counts.auditedTheorems, refinement: refinementProofs, emittedTrustedBase };
}

function refinementRegistryHash() {
  const source = readFileSync(join(root, 'scripts/refinement-proof-registry.mjs'));
  return `sha256:${createHash('sha256').update(source).digest('hex')}`;
}

export function parseEnvironmentAudit(output) {
  const records = new Map();
  for (const line of output.split('\n').filter((value) => value.trim().length > 0)) {
    const match = line.match(/^JS_AUDIT\t([^\t]+)\t(.*)$/);
    if (!match) fail(`unparsed Lean audit record: ${line}`);
    if (records.has(match[1])) fail(`duplicate Lean audit record: ${match[1]}`);
    records.set(
      match[1],
      match[2]
        .split(',')
        .map((axiom) => axiom.trim())
        .filter(Boolean),
    );
  }
  if (records.size === 0) fail('Lean audit emitted no proof records');
  return records;
}

function enforceAllowlist(records) {
  for (const [name, axioms] of records) {
    for (const axiom of axioms) {
      if (!allowedAxioms.has(axiom)) fail(`${name} depends on disallowed axiom ${axiom}`);
    }
  }
}

function stripLeanComments(source) {
  let result = '';
  let blockDepth = 0;
  for (let index = 0; index < source.length; index += 1) {
    if (blockDepth > 0 && source.startsWith('/-', index)) {
      blockDepth += 1;
      index += 1;
    } else if (blockDepth > 0 && source.startsWith('-/', index)) {
      blockDepth -= 1;
      index += 1;
    } else if (blockDepth > 0) {
      if (source[index] === '\n') result += '\n';
    } else if (source.startsWith('/-', index)) {
      blockDepth = 1;
      index += 1;
    } else if (source.startsWith('--', index)) {
      while (index < source.length && source[index] !== '\n') index += 1;
      result += '\n';
    } else {
      result += source[index];
    }
  }
  if (blockDepth !== 0) fail('unterminated Lean block comment');
  return result;
}

function moduleRole(name) {
  const stem = name.endsWith('.lean') ? name.slice(0, -'.lean'.length) : name;
  const segments = stem.split('.');
  if (segments.includes('Oracle')) return 'oracle';
  if (segments.includes('Tests')) return 'support';
  const leaf = segments.at(-1);
  return /(?:Tests|Audit|Meta)$/.test(leaf) ? 'support' : 'semantic';
}

function inNamespace(name, namespace) {
  return name === namespace || name.startsWith(`${namespace}.`);
}

function sourceImports(source) {
  return [...stripLeanComments(source).matchAll(/^\s*import\s+([^\s]+)/gm)].map((match) => match[1]);
}

/**
 * Every line of an audited module that names a construct able to introduce an axiom the allowlist
 * does not carry.
 *
 * `native_decide` is on the list because it discharges a goal by trusting the compiler's evaluation
 * of it, which the elaborator records as a `Lean.ofReduceBool` application — an axiom, and one the
 * proof audit never saw while it filtered private names.
 *
 * Every violation is returned rather than thrown so one run names every offending file.
 */
function forbiddenTokenViolations(file, source) {
  const forbidden = /\b(sorry|admit|axiom|opaque|partial|unsafe|noncomputable|native_decide)\b/;
  return stripLeanComments(source)
    .split('\n')
    .filter((line) => forbidden.test(line))
    .map((line) => `${file} contains forbidden declaration token: ${line.trim()}`);
}

/**
 * Every import an audited JS module may not have.
 *
 * Returned rather than thrown, like the token violations, so one run reports both classes at once
 * instead of stopping at whichever it happened to check first.
 */
function semanticImportViolations(file, source) {
  const violations = [];
  for (const imported of sourceImports(source)) {
    if (imported.startsWith('TSLean.JS.') && moduleRole(imported) !== 'semantic') {
      violations.push(`${file} imports non-semantic JS module ${imported}`);
    }
    if (!imported.startsWith('TSLean.JS.') && !imported.startsWith('Init') && !imported.startsWith('Std')) {
      violations.push(`${file} imports non-isolated module ${imported}`);
    }
  }
  return violations;
}

function productionBarrelViolations(source) {
  return semanticImportViolations('JS.lean', source);
}

/** Every import an audited refinement module may not have; see {@link semanticImportViolations}. */
function refinementImportViolations(file, source, semantic = true) {
  const violations = [];
  for (const imported of sourceImports(source)) {
    if (inNamespace(imported, 'TSLean.Runtime')) {
      violations.push(`${file} imports legacy runtime module ${imported}`);
    }
    if (semantic && inNamespace(imported, 'TSLean.Refinement') && moduleRole(imported) !== 'semantic') {
      violations.push(`${file} imports non-semantic refinement module ${imported}`);
    }
    if (semantic && inNamespace(imported, 'TSLean.JS') && moduleRole(imported) !== 'semantic') {
      violations.push(`${file} imports non-semantic JS module ${imported}`);
    }
    if (
      !inNamespace(imported, 'TSLean.Refinement') &&
      !inNamespace(imported, 'TSLean.JS') &&
      !inNamespace(imported, 'Init') &&
      !inNamespace(imported, 'Std')
    ) {
      violations.push(`${file} imports non-isolated module ${imported}`);
    }
  }
  return violations;
}

function filesRecursively(directory, extension, symlinkFailure) {
  const files = [];
  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    const path = join(directory, entry.name);
    if (entry.isSymbolicLink()) fail(`${symlinkFailure}: ${path}`);
    else if (entry.isDirectory()) files.push(...filesRecursively(path, extension, symlinkFailure));
    else if (entry.isFile() && entry.name.endsWith(extension)) files.push(path);
  }
  return files;
}

export function leanFilesRecursively(directory) {
  return filesRecursively(directory, '.lean', 'refinement source tree contains symlink');
}

/** The module an audited tree compiled a file as, from the file's path relative to that tree. */
function sourceModuleName(namespace, relative) {
  return `${namespace}.${relative.slice(0, -'.lean'.length).split(sep).join('.')}`;
}

export function checkSources() {
  const violations = [];
  const jsDirectory = join(root, 'lean/TSLean/JS');
  // Recursive, and filtered per file: a module under `JS/<subdir>/` is as importable by a semantic
  // module as one beside it, so reading only the top level left every nested module — the `Oracle`
  // tree today, anything a subdirectory holds tomorrow — with no token scrutiny at all.
  for (const file of leanFilesRecursively(jsDirectory)) {
    const relative = file.slice(jsDirectory.length + 1);
    const module = sourceModuleName('TSLean.JS', relative);
    if (moduleRole(module) !== 'semantic') continue;
    const source = readFileSync(file, 'utf8');
    violations.push(...forbiddenTokenViolations(relative, source));
    violations.push(...semanticImportViolations(relative, source));
  }
  const jsBarrel = readFileSync(join(root, 'lean/TSLean/JS.lean'), 'utf8');
  violations.push(...forbiddenTokenViolations('JS.lean', jsBarrel));
  violations.push(...productionBarrelViolations(jsBarrel));
  const refinementDirectory = join(root, 'lean/TSLean/Refinement');
  for (const file of leanFilesRecursively(refinementDirectory)) {
    const relative = file.slice(refinementDirectory.length + 1);
    const module = sourceModuleName('TSLean.Refinement', relative);
    const source = readFileSync(file, 'utf8');
    violations.push(...forbiddenTokenViolations(relative, source));
    violations.push(...refinementImportViolations(relative, source, moduleRole(module) === 'semantic'));
  }
  const refinementBarrel = readFileSync(join(root, 'lean/TSLean/Refinement.lean'), 'utf8');
  violations.push(...forbiddenTokenViolations('Refinement.lean', refinementBarrel));
  violations.push(...refinementImportViolations('Refinement.lean', refinementBarrel));
  if (violations.length > 0) {
    fail(`audited sources carry ${violations.length} violation(s):\n  ${violations.sort().join('\n  ')}`);
  }
  const heap = readFileSync(join(jsDirectory, 'Heap.lean'), 'utf8');
  const orderedProps = readFileSync(join(jsDirectory, 'OrderedProps.lean'), 'utf8');
  if (!/structure OrderedProps where\s+private mk ::/.test(orderedProps)) fail('OrderedProps constructor is public');
  if (!/structure Heap where\s+private mk ::/.test(heap)) fail('Heap constructor is public');
  if (!/structure ObjectRecord where\s+private mk ::/.test(heap)) fail('ObjectRecord constructor is public');
  if (!/private def insertRep\b/.test(orderedProps) || !/private def deleteRep\b/.test(orderedProps)) {
    fail('OrderedProps mutation is public');
  }
  if (/\bdef (setProperties|setExtensible)\b/.test(heap)) fail('raw heap mutation is public');
}

function readRefinementRegistry(registry = refinementProofRegistry) {
  exactKeys(registry, ['schemaVersion', 'requiredDeclarations'], 'refinement proof registry');
  if (registry.schemaVersion !== 1) fail('unsupported refinement proof registry schema');
  if (!Array.isArray(registry.requiredDeclarations) || registry.requiredDeclarations.length === 0) {
    fail('refinement proof registry requiredDeclarations must be nonempty');
  }
  const sorted = [...registry.requiredDeclarations].sort();
  if (JSON.stringify(registry.requiredDeclarations) !== JSON.stringify(sorted)) {
    fail('refinement proof registry requiredDeclarations must be sorted');
  }
  const required = new Set();
  for (const declaration of registry.requiredDeclarations) {
    if (typeof declaration !== 'string' || !inNamespace(declaration, 'TSLean.Refinement')) {
      fail('refinement proof registry contains an invalid declaration name');
    }
    if (required.has(declaration)) fail(`duplicate refinement proof registry declaration: ${declaration}`);
    required.add(declaration);
  }
  return required;
}

function enforceRefinementRegistry(records, registry = refinementProofRegistry) {
  const required = readRefinementRegistry(registry);
  for (const declaration of required) {
    if (!records.has(declaration)) fail(`required refinement proof declaration is missing: ${declaration}`);
  }
  return required.size;
}

function moduleSourceFile(name) {
  return join(leanDirectory, `${name.split('.').join(sep)}.lean`);
}

export function ensureLeanBuildCurrent(lakeExecutable = 'lake', targets = []) {
  const result = spawnSync(lakeExecutable, ['build', ...targets, '--quiet', '--no-ansi'], {
    cwd: leanDirectory,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (result.error) fail(`cannot run lake build: ${result.error.message}`);
  if (result.status !== 0) {
    const detail = [result.stderr, result.stdout]
      .map((output) => output.trim())
      .filter(Boolean)
      .join('\n');
    fail(`lake build exited with status ${result.status}: ${detail}`);
  }
}

function compiledModuleName(artifact) {
  return artifact
    .slice(compiledLibraryDirectory.length + 1, -'.olean'.length)
    .split(sep)
    .join('.');
}

function compiledArtifactFile(name) {
  return join(compiledLibraryDirectory, `${name.split('.').join(sep)}.olean`);
}

/** Every module of the `TSLean` Lean library, taken from the source tree Lake compiles. */
function libraryModules() {
  const sources = [
    join(leanDirectory, 'TSLean.lean'),
    ...filesRecursively(join(leanDirectory, 'TSLean'), '.lean', 'Lean source tree contains symlink'),
  ];
  return new Set(
    sources.map((file) =>
      file
        .slice(leanDirectory.length + 1, -'.lean'.length)
        .split(sep)
        .join('.'),
    ),
  );
}

/**
 * Require the compiled library and its source tree to name the same modules.
 *
 * Both directions matter and neither implies the other. An artifact with no source is a proof that
 * survived the deletion of what proved it; a source with no artifact is a module that no build ever
 * elaborated, which is how thousands of lines of unverified Lean can sit in the tree looking
 * verified. Only `unbuiltSourceAllowlist` may be missing an artifact, and only while it stays
 * missing.
 */
function checkCompiledArtifacts() {
  const directory = join(compiledLibraryDirectory, 'TSLean');
  const orphans = filesRecursively(directory, '.olean', 'Lean build tree contains symlink')
    .filter((artifact) => !existsSync(moduleSourceFile(compiledModuleName(artifact))))
    .map((artifact) => artifact.slice(root.length + 1))
    .sort();
  if (orphans.length > 0) fail(`orphaned Lean build artifacts have no source module: ${orphans.join(', ')}`);
  const modules = libraryModules();
  const unbuilt = [...modules]
    .filter((name) => !unbuiltSourceAllowlist.has(name) && !existsSync(compiledArtifactFile(name)))
    .sort();
  if (unbuilt.length > 0) fail(`Lean source modules have no compiled artifact: ${unbuilt.join(', ')}`);
  for (const name of [...unbuiltSourceAllowlist].sort()) {
    if (!modules.has(name)) fail(`unbuilt-source allowlist names a module with no source: ${name}`);
    if (existsSync(compiledArtifactFile(name))) fail(`unbuilt-source allowlist names a compiled module: ${name}`);
  }
}

function withTemporaryLeanFile(source, use) {
  const directory = mkdtempSync(join(tmpdir(), 'tslean-audit-'));
  try {
    const file = join(directory, 'Audit.lean');
    writeFileSync(file, source);
    return use(file);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

function auditedModules(imports) {
  const result = withTemporaryLeanFile(
    [
      'import Lean',
      ...imports.map((name) => `import ${name}`),
      'open Lean in',
      'run_cmd do',
      '  let environment ← Lean.getEnv',
      '  for name in environment.header.moduleNames do',
      '    logInfo m!"JS_MODULE\\t{name}"',
      '',
    ].join('\n'),
    runLean,
  );
  if (result.stderr.trim().length > 0) fail(`unexpected Lean module probe stderr: ${result.stderr.trim()}`);
  const modules = new Set();
  for (const line of result.stdout.split('\n').filter((value) => value.trim().length > 0)) {
    const match = line.match(/^JS_MODULE\t(\S+)$/);
    if (!match) fail(`unparsed Lean module record: ${line}`);
    modules.add(match[1]);
  }
  if (modules.size === 0) fail('Lean module probe emitted no records');
  return modules;
}

function checkAuditedEnvironment(imports) {
  const modules = auditedModules(imports);
  const unsourced = [...modules]
    .filter((name) => inNamespace(name, 'TSLean') && !existsSync(moduleSourceFile(name)))
    .sort();
  if (unsourced.length > 0) fail(`audited Lean environment loaded modules with no source: ${unsourced.join(', ')}`);
  return modules.size;
}

/** The Lean modules the compiler puts at the top of the file it emits for `file`. */
function emittedImports(file) {
  const emitted = buildLeanFile(rewriteModule(parseFile({ fileName: file })));
  return emitted.decls.flatMap((declaration) => (declaration.tag === 'Import' ? [declaration.module] : []));
}

/**
 * The library modules generated code can import, taken from the compiler rather than listed here.
 *
 * Two sources, because an emitted import has two origins and neither one covers the other.
 *
 * The compiler's own: `STATIC_LEAN_IMPORTS` is every module `LowerCtx.resolveImports` can request
 * (and the lowerer's scan is typed by it, so adding a target without declaring it does not compile),
 * `DO_LEAN_IMPORTS` is what the parser injects into a Durable Object file, and
 * `WORKERS_LEAN_IMPORTS` is the declared set for Workers bindings. Declared, so a module is audited
 * whether or not a fixture happens to reach it — the defect this closed was that no fixture used a
 * `KV.`/`R2.`/`D1.` expression, so five Workers modules sat in the emitted trusted base of every
 * Workers artifact while the gate never looked at them.
 *
 * The program's own: whatever the source imported, mapped to a Lean module by the parser. That
 * cannot be declared, so it is measured, by lowering every fixture and reading the imports off the
 * emitted file. `TSLean.Generated.*` names the compiler's output for a *sibling* source file, not a
 * library module, so it is only audited when the repository does commit that module; everything else
 * an emitted file imports has to exist in `lean/`, or the compiler emits Lean that cannot elaborate.
 */
export function emittedImportClosure(directory = fixtureDirectory) {
  const audited = new Set();
  const unsourced = new Set();
  const consider = (module, origin) => {
    if (existsSync(moduleSourceFile(module))) audited.add(module);
    else if (!inNamespace(module, 'TSLean.Generated')) unsourced.add(`${module} (${origin})`);
  };
  for (const module of [...STATIC_LEAN_IMPORTS, ...DO_LEAN_IMPORTS, ...WORKERS_LEAN_IMPORTS]) {
    consider(module, 'declared');
  }
  for (const file of filesRecursively(directory, '.ts', 'fixture source tree contains symlink')) {
    for (const module of emittedImports(file)) consider(module, file.slice(directory.length + 1));
  }
  if (unsourced.size > 0) {
    fail(`emitted imports name Lean modules with no source: ${[...unsourced].sort().join(', ')}`);
  }
  if (audited.size === 0) fail('no emitted library imports were derived from the fixture corpus');
  return [...audited].sort();
}

/**
 * Audit every declaration of every loaded module under `modulePrefix`, allowlist included.
 *
 * `#audit_proofs` reports public proposition-valued declarations of a *namespace*, which leaves two
 * ways to hold a `sorry`: be private, or not be a `Prop` — `instance : Inhabited Server := ⟨sorry⟩`
 * is neither private nor visible to it. `#audit_constants` selects by compiled module and filters
 * nothing, so both are reported.
 *
 * `leanPath` is added to the module search path, which is how a test can put a module with a
 * fabricated axiom dependency into the audited environment without touching the repository.
 */
export function checkModuleConstants(imports, modulePrefix, leanPath) {
  const result = withTemporaryLeanFile(
    [
      'import TSLean.JS.AxiomAuditMeta',
      ...imports.map((name) => `import ${name}`),
      `#audit_constants ${modulePrefix}`,
      '',
    ].join('\n'),
    (file) => runLean(file, leanPath),
  );
  if (result.stderr.trim().length > 0) fail(`unexpected Lean constant audit stderr: ${result.stderr.trim()}`);
  const records = parseEnvironmentAudit(result.stdout);
  enforceAllowlist(records);
  return records;
}

function runLean(file, leanPath) {
  const result = spawnSync('lake', ['env', 'lean', file], {
    cwd: leanDirectory,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
    env: leanPath === undefined ? env : { ...env, LEAN_PATH: leanPath },
  });
  if (result.status !== 0) fail(`Lean audit exited with status ${result.status}: ${result.stderr.trim()}`);
  return result;
}

function runLeanAudit(file, allowDiagnostics = false) {
  const result = runLean(file);
  const output = allowDiagnostics
    ? result.stdout
        .split('\n')
        .filter((line) => line.startsWith('JS_AUDIT\t'))
        .join('\n')
    : result.stdout;
  return { records: parseEnvironmentAudit(output), stderr: result.stderr };
}

function refinementAuditImports() {
  const refinementDirectory = join(root, 'lean/TSLean/Refinement');
  const discovered = leanFilesRecursively(refinementDirectory)
    .map((file) => file.slice(refinementDirectory.length + 1))
    .filter((relative) => relative !== 'AxiomAudit.lean')
    .map((relative) => sourceModuleName('TSLean.Refinement', relative));
  return [
    'TSLean.JS.AxiomAuditMeta',
    'TSLean.Refinement',
    ...discovered.filter((name) => moduleRole(name) === 'semantic').sort(),
    ...discovered.filter((name) => moduleRole(name) !== 'semantic').sort(),
  ];
}

function runRefinementAudit(imports) {
  return withTemporaryLeanFile(
    `${imports.map((name) => `import ${name}`).join('\n')}\n#audit_proofs TSLean.Refinement\n`,
    runLeanAudit,
  );
}

function selfTest() {
  const { records } = runLeanAudit('../tests/lean-fixtures/axiom-audit-synthetic.lean', true);
  const required = ['TSLean.AuditSynthetic.omittedLemma', 'TSLean.AuditSynthetic.multilineTheorem'];
  for (const name of required) {
    if (!records.has(name)) fail(`synthetic elaborated proof was omitted: ${name}`);
  }
  if (![...records.keys()].some((name) => name.startsWith('TSLean.AuditSynthetic.instNonemptyUnit'))) {
    fail('synthetic proposition-valued instance was omitted');
  }
  const expectDisallowed = (name, axiom) => {
    try {
      enforceAllowlist(new Map([[name, records.get(name) ?? []]]));
    } catch (error) {
      if (error instanceof Error && error.message.includes(`disallowed axiom ${axiom}`)) return;
      throw error;
    }
    fail(`synthetic ${axiom} dependency was accepted`);
  };
  expectDisallowed('TSLean.AuditSynthetic.sorryTheorem', 'sorryAx');
  expectDisallowed('TSLean.AuditSynthetic.customAxiom', 'TSLean.AuditSynthetic.customAxiom');
  const recursiveRefinementFiles = leanFilesRecursively(join(root, 'lean/TSLean/Refinement'));
  if (!recursiveRefinementFiles.some((file) => file.endsWith(join('Tests', 'Core.lean')))) {
    fail('recursive refinement source discovery omitted nested test module');
  }
  const expectSourceFailure = (label, check, expected) => {
    try {
      check();
    } catch (error) {
      if (error instanceof Error && error.message.includes(expected)) return;
      throw error;
    }
    fail(`synthetic ${label} was accepted`);
  };
  const requiredProofs = refinementProofRegistry.requiredDeclarations;
  const completeProofRecords = new Map(requiredProofs.map((name) => [name, []]));
  enforceRefinementRegistry(completeProofRecords);
  const deletedProofRecords = new Map(completeProofRecords);
  deletedProofRecords.delete(requiredProofs[0]);
  expectSourceFailure(
    'refinement registry deletion',
    () => enforceRefinementRegistry(deletedProofRecords),
    `required refinement proof declaration is missing: ${requiredProofs[0]}`,
  );
  const substitutedProofRecords = new Map(deletedProofRecords);
  substitutedProofRecords.set('TSLean.Refinement.SubstitutedTheorem', []);
  expectSourceFailure(
    'refinement registry substitution',
    () => enforceRefinementRegistry(substitutedProofRecords),
    `required refinement proof declaration is missing: ${requiredProofs[0]}`,
  );
  // The import checks report rather than throw, so a rejection is a violation in the returned list
  // and an acceptance is an empty one. Both directions are asserted: a check that silently stopped
  // reporting would otherwise look exactly like a tree with nothing wrong in it.
  const expectViolation = (label, violations, expected) => {
    if (!violations.some((violation) => violation.includes(expected))) fail(`synthetic ${label} was accepted`);
  };
  const expectNoViolation = (label, violations) => {
    if (violations.length > 0) fail(`legitimate ${label} was rejected: ${violations.join(', ')}`);
  };
  expectViolation(
    'production test import',
    productionBarrelViolations('import TSLean.JS.ExecutionTests\n'),
    'imports non-semantic JS module TSLean.JS.ExecutionTests',
  );
  expectViolation(
    'refinement prefix bypass',
    refinementImportViolations('Core.lean', 'import TSLean.RefinementBackdoor.Core\n'),
    'imports non-isolated module TSLean.RefinementBackdoor.Core',
  );
  expectViolation(
    'JS prefix bypass',
    refinementImportViolations('Core.lean', 'import TSLean.JSBackdoor.Value\n'),
    'imports non-isolated module TSLean.JSBackdoor.Value',
  );
  expectViolation(
    'indented production test import',
    productionBarrelViolations('  import TSLean.JS.ExecutionTests\n'),
    'imports non-semantic JS module TSLean.JS.ExecutionTests',
  );
  expectViolation(
    'production audit-meta import',
    productionBarrelViolations('import TSLean.JS.AxiomAuditMeta\n'),
    'imports non-semantic JS module TSLean.JS.AxiomAuditMeta',
  );
  expectViolation(
    'semantic test import',
    semanticImportViolations('Value.lean', 'import TSLean.JS.FutureTests\n'),
    'imports non-semantic JS module TSLean.JS.FutureTests',
  );
  expectViolation(
    'production oracle import',
    productionBarrelViolations('import TSLean.JS.Oracle.Primitive\n'),
    'imports non-semantic JS module TSLean.JS.Oracle.Primitive',
  );
  expectViolation(
    'semantic oracle import',
    semanticImportViolations('Value.lean', 'import TSLean.JS.Oracle.Protocol\n'),
    'imports non-semantic JS module TSLean.JS.Oracle.Protocol',
  );
  expectNoViolation('indented production import', productionBarrelViolations('  import TSLean.JS.Value\n'));
  expectViolation(
    'refinement legacy runtime import',
    refinementImportViolations('Core.lean', 'import TSLean.Runtime.Basic\n'),
    'imports legacy runtime module TSLean.Runtime.Basic',
  );
  expectViolation(
    'refinement test import',
    refinementImportViolations('Refinement.lean', 'import TSLean.Refinement.Tests.Core\n'),
    'imports non-semantic refinement module TSLean.Refinement.Tests.Core',
  );
  expectViolation(
    'nested refinement test import',
    refinementImportViolations('Refinement.lean', 'import TSLean.Refinement.Nested.Tests.Core\n'),
    'imports non-semantic refinement module TSLean.Refinement.Nested.Tests.Core',
  );
  expectNoViolation(
    'refinement production import',
    refinementImportViolations('Refinement.lean', 'import TSLean.Refinement.Core\n'),
  );
  expectNoViolation(
    'support test import',
    refinementImportViolations('Support.lean', 'import TSLean.Refinement.Tests.Core\n', false),
  );
  expectNoViolation(
    'commented barrel import',
    productionBarrelViolations(`
    -- import TSLean.JS.ExecutionTests
    /- import TSLean.JS.AxiomAuditMeta -/
    import TSLean.JS.Value
  `),
  );
  try {
    parseEnvironmentAudit('not a record');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('unparsed Lean audit record')) throw error;
    stdout.write('synthetic environment audit passed\n');
    return;
  }
  fail('synthetic unparsed record was accepted');
}

function main() {
  const args = parseArgs(argv.slice(2));
  ensureLeanBuildCurrent('lake', args.selfTest ? ['TSLean.JS.AxiomAuditMeta'] : []);
  checkCompiledArtifacts();
  if (args.selfTest) return selfTest();
  const expected = readExpectedAuditCount(args.evidence);
  checkSources();
  const closure = emittedImportClosure();
  const measured = {
    imports: closure.length,
    modules: checkAuditedEnvironment(closure),
    declarations: checkModuleConstants(closure, 'TSLean').size,
  };
  stdout.write(
    `Emitted trusted base passed: ${measured.imports} emitted library imports, ` +
      `${measured.modules} loaded modules, ${measured.declarations} audited declarations\n`,
  );
  if (expected.emittedTrustedBase !== undefined) {
    for (const key of EMITTED_TRUSTED_BASE_KEYS) {
      if (measured[key] !== expected.emittedTrustedBase[key]) {
        fail(`expected ${expected.emittedTrustedBase[key]} emitted trusted base ${key}, found ${measured[key]}`);
      }
    }
  }
  checkAuditedEnvironment(['TSLean.JS.AxiomAudit']);
  const { records, stderr } = runLeanAudit('TSLean/JS/AxiomAudit.lean');
  if (stderr.trim().length > 0) fail(`unexpected Lean audit stderr: ${stderr.trim()}`);
  enforceAllowlist(records);
  stdout.write(`JS trust checks passed: ${records.size} elaborated proof declarations\n`);
  if (records.size !== expected.js) {
    fail(`expected ${expected.js} audited proof declarations, found ${records.size}`);
  }
  stdout.write(`JS trust gate passed: ${records.size} proof declarations\n`);
  const refinementImports = refinementAuditImports();
  checkAuditedEnvironment(refinementImports);
  const refinementAudit = runRefinementAudit(refinementImports);
  if (refinementAudit.stderr.trim().length > 0) {
    fail(`unexpected refinement audit stderr: ${refinementAudit.stderr.trim()}`);
  }
  enforceAllowlist(refinementAudit.records);
  const requiredRefinementProofs = enforceRefinementRegistry(refinementAudit.records);
  if (expected.refinement !== undefined) {
    if (refinementAudit.records.size !== expected.refinement.audited) {
      fail(
        `expected ${expected.refinement.audited} audited refinement proof declarations, ` +
          `found ${refinementAudit.records.size}`,
      );
    }
    if (requiredRefinementProofs !== expected.refinement.required) {
      fail(
        `expected ${expected.refinement.required} required refinement proof declarations, ` +
          `found ${requiredRefinementProofs}`,
      );
    }
    const registryHash = refinementRegistryHash();
    if (registryHash !== expected.refinement.registryHash) {
      fail(`expected refinement registry ${expected.refinement.registryHash}, found ${registryHash}`);
    }
  }
  stdout.write(
    `Refinement trust gate passed: ${refinementAudit.records.size} audited proof declarations; ` +
      `${requiredRefinementProofs} required production theorems\n`,
  );
}

if (import.meta.main) main();
