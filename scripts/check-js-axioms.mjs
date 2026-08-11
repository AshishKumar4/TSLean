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
import { argv, stdout } from 'node:process';
import { fileURLToPath } from 'node:url';
import { refinementProofRegistry } from './refinement-proof-registry.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const leanDirectory = join(root, 'lean');
const compiledLibraryDirectory = join(leanDirectory, '.lake/build/lib/lean');
const allowedAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const usage = 'Usage: check-js-axioms.mjs --evidence <input.json> | --self-test';

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
    'branch',
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
  for (const key of ['outputPath', 'baseRevision', 'branch']) {
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
  return { js: counts.auditedTheorems, refinement: refinementProofs };
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

function validateSemanticSource(file, source) {
  const forbidden = /\b(sorry|admit|axiom|opaque|partial|unsafe|noncomputable)\b/;
  const stripped = stripLeanComments(source);
  const violation = stripped.split('\n').find((line) => forbidden.test(line));
  if (violation) fail(`${file} contains forbidden declaration token: ${violation.trim()}`);
  for (const imported of sourceImports(source)) {
    if (imported.startsWith('TSLean.JS.') && moduleRole(imported) !== 'semantic') {
      fail(`${file} imports non-semantic JS module ${imported}`);
    }
    if (!imported.startsWith('TSLean.JS.') && !imported.startsWith('Init') && !imported.startsWith('Std')) {
      fail(`${file} imports non-isolated module ${imported}`);
    }
  }
}

function validateProductionBarrel(source) {
  validateSemanticSource('JS.lean', source);
}

function validateRefinementSource(file, source, semantic = true) {
  const forbidden = /\b(sorry|admit|axiom|opaque|partial|unsafe|noncomputable)\b/;
  const stripped = stripLeanComments(source);
  const violation = stripped.split('\n').find((line) => forbidden.test(line));
  if (violation) fail(`${file} contains forbidden declaration token: ${violation.trim()}`);
  for (const imported of sourceImports(source)) {
    if (inNamespace(imported, 'TSLean.Runtime')) {
      fail(`${file} imports legacy runtime module ${imported}`);
    }
    if (semantic && inNamespace(imported, 'TSLean.Refinement') && moduleRole(imported) !== 'semantic') {
      fail(`${file} imports non-semantic refinement module ${imported}`);
    }
    if (semantic && inNamespace(imported, 'TSLean.JS') && moduleRole(imported) !== 'semantic') {
      fail(`${file} imports non-semantic JS module ${imported}`);
    }
    if (
      !inNamespace(imported, 'TSLean.Refinement') &&
      !inNamespace(imported, 'TSLean.JS') &&
      !inNamespace(imported, 'Init') &&
      !inNamespace(imported, 'Std')
    ) {
      fail(`${file} imports non-isolated module ${imported}`);
    }
  }
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

function checkSources() {
  const jsDirectory = join(root, 'lean/TSLean/JS');
  const files = readdirSync(jsDirectory).filter((name) => name.endsWith('.lean') && moduleRole(name) === 'semantic');
  for (const name of files) validateSemanticSource(name, readFileSync(join(jsDirectory, name), 'utf8'));
  validateProductionBarrel(readFileSync(join(root, 'lean/TSLean/JS.lean'), 'utf8'));
  const refinementDirectory = join(root, 'lean/TSLean/Refinement');
  for (const file of leanFilesRecursively(refinementDirectory)) {
    const relative = file.slice(refinementDirectory.length + 1);
    const module = `TSLean.Refinement.${relative.slice(0, -'.lean'.length).split(sep).join('.')}`;
    validateRefinementSource(relative, readFileSync(file, 'utf8'), moduleRole(module) === 'semantic');
  }
  validateRefinementSource('Refinement.lean', readFileSync(join(root, 'lean/TSLean/Refinement.lean'), 'utf8'));
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

export function ensureLeanBuildCurrent(lakeExecutable = 'lake') {
  const result = spawnSync(lakeExecutable, ['build', '--quiet', '--no-ansi'], {
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

function checkCompiledArtifacts() {
  const directory = join(compiledLibraryDirectory, 'TSLean');
  const orphans = filesRecursively(directory, '.olean', 'Lean build tree contains symlink')
    .filter((artifact) => !existsSync(moduleSourceFile(compiledModuleName(artifact))))
    .map((artifact) => artifact.slice(root.length + 1))
    .sort();
  if (orphans.length > 0) fail(`orphaned Lean build artifacts have no source module: ${orphans.join(', ')}`);
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
  const unsourced = [...auditedModules(imports)]
    .filter((name) => inNamespace(name, 'TSLean') && !existsSync(moduleSourceFile(name)))
    .sort();
  if (unsourced.length > 0) fail(`audited Lean environment loaded modules with no source: ${unsourced.join(', ')}`);
}

function runLean(file) {
  const result = spawnSync('lake', ['env', 'lean', file], {
    cwd: leanDirectory,
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
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
    .map((relative) => `TSLean.Refinement.${relative.slice(0, -'.lean'.length).split(sep).join('.')}`);
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
  expectSourceFailure(
    'production test import',
    () => validateProductionBarrel('import TSLean.JS.ExecutionTests\n'),
    'imports non-semantic JS module TSLean.JS.ExecutionTests',
  );
  expectSourceFailure(
    'refinement prefix bypass',
    () => validateRefinementSource('Core.lean', 'import TSLean.RefinementBackdoor.Core\n'),
    'imports non-isolated module TSLean.RefinementBackdoor.Core',
  );
  expectSourceFailure(
    'JS prefix bypass',
    () => validateRefinementSource('Core.lean', 'import TSLean.JSBackdoor.Value\n'),
    'imports non-isolated module TSLean.JSBackdoor.Value',
  );
  expectSourceFailure(
    'indented production test import',
    () => validateProductionBarrel('  import TSLean.JS.ExecutionTests\n'),
    'imports non-semantic JS module TSLean.JS.ExecutionTests',
  );
  expectSourceFailure(
    'production audit-meta import',
    () => validateProductionBarrel('import TSLean.JS.AxiomAuditMeta\n'),
    'imports non-semantic JS module TSLean.JS.AxiomAuditMeta',
  );
  expectSourceFailure(
    'semantic test import',
    () => validateSemanticSource('Value.lean', 'import TSLean.JS.FutureTests\n'),
    'imports non-semantic JS module TSLean.JS.FutureTests',
  );
  expectSourceFailure(
    'production oracle import',
    () => validateProductionBarrel('import TSLean.JS.Oracle.Primitive\n'),
    'imports non-semantic JS module TSLean.JS.Oracle.Primitive',
  );
  expectSourceFailure(
    'semantic oracle import',
    () => validateSemanticSource('Value.lean', 'import TSLean.JS.Oracle.Protocol\n'),
    'imports non-semantic JS module TSLean.JS.Oracle.Protocol',
  );
  validateProductionBarrel('  import TSLean.JS.Value\n');
  expectSourceFailure(
    'refinement legacy runtime import',
    () => validateRefinementSource('Core.lean', 'import TSLean.Runtime.Basic\n'),
    'imports legacy runtime module TSLean.Runtime.Basic',
  );
  expectSourceFailure(
    'refinement test import',
    () => validateRefinementSource('Refinement.lean', 'import TSLean.Refinement.Tests.Core\n'),
    'imports non-semantic refinement module TSLean.Refinement.Tests.Core',
  );
  expectSourceFailure(
    'nested refinement test import',
    () => validateRefinementSource('Refinement.lean', 'import TSLean.Refinement.Nested.Tests.Core\n'),
    'imports non-semantic refinement module TSLean.Refinement.Nested.Tests.Core',
  );
  validateRefinementSource('Refinement.lean', 'import TSLean.Refinement.Core\n');
  validateRefinementSource('Support.lean', 'import TSLean.Refinement.Tests.Core\n', false);
  validateProductionBarrel(`
    -- import TSLean.JS.ExecutionTests
    /- import TSLean.JS.AxiomAuditMeta -/
    import TSLean.JS.Value
  `);
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
  ensureLeanBuildCurrent();
  checkCompiledArtifacts();
  if (args.selfTest) return selfTest();
  const expected = readExpectedAuditCount(args.evidence);
  checkSources();
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
