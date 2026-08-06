import { spawnSync } from 'node:child_process';
import { lstatSync, readFileSync, readdirSync, realpathSync } from 'node:fs';
import { dirname, isAbsolute, join, resolve, sep } from 'node:path';
import { argv, stdout } from 'node:process';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
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
  exactKeys(
    input,
    ['schemaVersion', 'outputPath', 'baseRevision', 'branch', 'counts', 'knownTodos', 'validation', 'hashGroups'],
    'evidence input',
  );
  if (input.schemaVersion !== 1) fail('unsupported evidence input schema');
  for (const key of ['outputPath', 'baseRevision', 'branch']) {
    if (typeof input[key] !== 'string' || input[key].length === 0) fail(`evidence input ${key} must be non-empty`);
  }
  if (!Array.isArray(input.knownTodos)) fail('evidence input knownTodos must be an array');
  object(input.validation, 'evidence input validation');
  object(input.hashGroups, 'evidence input hashGroups');
  const counts = object(input.counts, 'counts');
  exactKeys(counts, ['tests', 'lean', 'corpus', 'auditedTheorems', 'lint', 'build'], 'counts');
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
  if (counts.lint !== 'passed') fail('counts.lint must be passed');
  if (counts.build !== 'passed') fail('counts.build must be passed');
  return counts.auditedTheorems;
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
  const leaf = stem.split('.').at(-1);
  return /(?:Tests|Audit|Meta)$/.test(leaf) ? 'support' : 'semantic';
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

function checkSources() {
  const jsDirectory = join(root, 'lean/TSLean/JS');
  const files = readdirSync(jsDirectory).filter((name) => name.endsWith('.lean') && moduleRole(name) === 'semantic');
  for (const name of files) validateSemanticSource(name, readFileSync(join(jsDirectory, name), 'utf8'));
  validateProductionBarrel(readFileSync(join(root, 'lean/TSLean/JS.lean'), 'utf8'));
  const heap = readFileSync(join(jsDirectory, 'Heap.lean'), 'utf8');
  if (!/structure OrderedProps where\s+private mk ::/.test(heap)) fail('OrderedProps constructor is public');
  if (!/structure Heap where\s+private mk ::/.test(heap)) fail('Heap constructor is public');
  if (!/structure ObjectRecord where\s+private mk ::/.test(heap)) fail('ObjectRecord constructor is public');
  if (!/private def insert\b/.test(heap) || !/private def delete\b/.test(heap)) {
    fail('OrderedProps mutation is public');
  }
  if (/\bdef (setProperties|setExtensible)\b/.test(heap)) fail('raw heap mutation is public');
}

function runLeanAudit(file, allowDiagnostics = false) {
  const result = spawnSync('lake', ['env', 'lean', file], {
    cwd: join(root, 'lean'),
    encoding: 'utf8',
    stdio: ['ignore', 'pipe', 'pipe'],
  });
  if (result.status !== 0) fail(`Lean audit exited with status ${result.status}: ${result.stderr.trim()}`);
  const output = allowDiagnostics
    ? result.stdout
        .split('\n')
        .filter((line) => line.startsWith('JS_AUDIT\t'))
        .join('\n')
    : result.stdout;
  return { records: parseEnvironmentAudit(output), stderr: result.stderr };
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
  const expectSourceFailure = (label, check, expected) => {
    try {
      check();
    } catch (error) {
      if (error instanceof Error && error.message.includes(expected)) return;
      throw error;
    }
    fail(`synthetic ${label} was accepted`);
  };
  expectSourceFailure(
    'production test import',
    () => validateProductionBarrel('import TSLean.JS.ExecutionTests\n'),
    'imports non-semantic JS module TSLean.JS.ExecutionTests',
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
  validateProductionBarrel('  import TSLean.JS.Value\n');
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
  if (args.selfTest) return selfTest();
  const expectedCount = readExpectedAuditCount(args.evidence);
  checkSources();
  const { records, stderr } = runLeanAudit('TSLean/JS/AxiomAudit.lean');
  if (stderr.trim().length > 0) fail(`unexpected Lean audit stderr: ${stderr.trim()}`);
  enforceAllowlist(records);
  stdout.write(`JS trust checks passed: ${records.size} elaborated proof declarations\n`);
  if (records.size !== expectedCount) {
    fail(`expected ${expectedCount} audited proof declarations, found ${records.size}`);
  }
  stdout.write(`JS trust gate passed: ${records.size} proof declarations\n`);
}

if (import.meta.main) main();
