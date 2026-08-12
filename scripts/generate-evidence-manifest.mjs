import { Buffer } from 'node:buffer';
import { createHash } from 'node:crypto';
import { execFileSync, spawnSync } from 'node:child_process';
import { lstatSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve, sep } from 'node:path';
import { argv } from 'node:process';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const usage = 'Usage: generate-evidence-manifest.mjs --input <json> [--check]';

function fail(message) {
  throw new Error(`Cannot generate evidence manifest: ${message}`);
}

function parseArgs(args) {
  let input;
  let check = false;
  for (let index = 0; index < args.length; index += 1) {
    const argument = args[index];
    if (argument === '--input' && input === undefined) {
      input = args[index + 1];
      if (input === undefined || input.startsWith('--')) fail(usage);
      index += 1;
    } else if (argument === '--check' && !check) {
      check = true;
    } else {
      fail(`${usage}; unexpected argument ${argument}`);
    }
  }
  if (input === undefined) fail(usage);
  return { check, input };
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

function repositoryPath(path, label) {
  if (typeof path !== 'string' || path.length === 0 || isAbsolute(path)) fail(`${label} must be a relative path`);
  const resolved = resolve(root, path);
  if (resolved !== root && !resolved.startsWith(`${root}${sep}`)) fail(`${label} escapes the repository`);
  return resolved;
}

function command(executable, args, cwd = root, encoding = 'utf8') {
  try {
    return execFileSync(executable, args, {
      cwd,
      encoding,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
  } catch (error) {
    const stderr =
      error !== null && typeof error === 'object' && 'stderr' in error && Buffer.isBuffer(error.stderr)
        ? error.stderr.toString('utf8').trim()
        : '';
    const detail = stderr || (error instanceof Error ? error.message : String(error));
    fail(`${executable} ${args.join(' ')} failed: ${detail}`);
  }
}

function textCommand(executable, args, cwd = root) {
  return command(executable, args, cwd).trim();
}

function filesUnder(path) {
  const stat = lstatSync(path);
  if (stat.isFile()) return [path];
  if (!stat.isDirectory()) fail(`unsupported filesystem entry ${relative(root, path)}`);
  return readdirSync(path, { withFileTypes: true }).flatMap((entry) => {
    const child = join(path, entry.name);
    if (entry.isDirectory()) return filesUnder(child);
    if (entry.isFile()) return [child];
    fail(`unsupported filesystem entry ${relative(root, child)}`);
  });
}

function compare(left, right) {
  return left < right ? -1 : left > right ? 1 : 0;
}

function currentFiles(paths) {
  return [...new Set(paths.flatMap((path) => filesUnder(repositoryPath(path, 'hash path'))))].sort(compare);
}

function revisionFiles(paths, revision) {
  const names = textCommand('git', ['ls-tree', '-r', '--name-only', revision, '--', ...paths])
    .split('\n')
    .filter(Boolean);
  if (names.length === 0) fail(`no files found at revision ${revision} under ${paths.join(', ')}`);
  return [...new Set(names)].sort(compare);
}

function revisionContents(files, revision) {
  if (files.length === 0) return [];
  const result = spawnSync('git', ['cat-file', '--batch'], {
    cwd: root,
    input: `${files.map((file) => `${revision}:${file}`).join('\n')}\n`,
    encoding: null,
    maxBuffer: 1024 * 1024 * 100,
  });
  if (result.status !== 0 || result.stdout === null) {
    fail(`git cat-file --batch failed: ${result.stderr?.toString('utf8').trim() || `exit ${result.status}`}`);
  }

  const contents = [];
  let offset = 0;
  for (const file of files) {
    const headerEnd = result.stdout.indexOf(10, offset);
    if (headerEnd === -1) fail(`git cat-file returned no header for ${file}`);
    const header = result.stdout.subarray(offset, headerEnd).toString('utf8').split(' ');
    const size = Number(header[2]);
    if (header[1] !== 'blob' || !Number.isSafeInteger(size) || size < 0) fail(`${file} is not a Git blob`);
    const contentStart = headerEnd + 1;
    const contentEnd = contentStart + size;
    if (result.stdout[contentEnd] !== 10) fail(`git cat-file returned incomplete content for ${file}`);
    contents.push(result.stdout.subarray(contentStart, contentEnd));
    offset = contentEnd + 1;
  }
  return contents;
}

function hashGroup(group, name) {
  const allowed = group.revision === undefined ? ['paths'] : ['paths', 'revision'];
  exactKeys(group, allowed, `hashGroups.${name}`);
  if (!Array.isArray(group.paths) || group.paths.length === 0) fail(`hashGroups.${name}.paths must be non-empty`);
  for (const path of group.paths) repositoryPath(path, `hashGroups.${name}.paths`);
  if (group.revision !== undefined && (typeof group.revision !== 'string' || group.revision.length === 0)) {
    fail(`hashGroups.${name}.revision must be a non-empty string`);
  }

  const hash = createHash('sha256');
  const files = group.revision === undefined ? currentFiles(group.paths) : revisionFiles(group.paths, group.revision);
  if (files.length === 0) fail(`no files found for hash group ${name}`);
  const contents =
    group.revision === undefined ? files.map((file) => readFileSync(file)) : revisionContents(files, group.revision);
  for (const [index, file] of files.entries()) {
    const repositoryName = group.revision === undefined ? relative(root, file) : file;
    hash.update(repositoryName);
    hash.update('\0');
    hash.update(contents[index]);
    hash.update('\0');
  }
  return `sha256:${hash.digest('hex')}`;
}

// Directories whose every Lean module must be hashed by some group, so that a new production
// module cannot ship outside the freshness evidence.
const coveredDirectories = ['lean/TSLean/JS', 'lean/TSLean/Refinement'];

/**
 * A snapshot is either live or frozen, never half of each.
 *
 * Freezing is a manual step, and `phase1-differential` was frozen with its hash groups pinned but
 * its validation left reading the working tree. That snapshot was not immutable: it reproduced only
 * while the live test-file count happened to match, and broke the moment the suite grew. Validation
 * counts and hashes have to describe the same tree, so pinning one without the other is rejected
 * here rather than discovered later by an unrelated change.
 */
function assertFreezingIsCoherent(input, groups) {
  const pinned = Object.entries(groups).filter(([, group]) => group.revision !== undefined);
  if (pinned.length === 0) return;
  if (pinned.length !== Object.entries(groups).length) {
    const live = Object.entries(groups)
      .filter(([, group]) => group.revision === undefined)
      .map(([name]) => name);
    fail(`hashGroups mix frozen and live entries; live: ${live.join(', ')}`);
  }
  const validation = input.validation;
  if (validation === undefined) return;
  const reads = ['testFiles', 'todos', 'corpus'].filter((key) => validation[key] !== undefined);
  const unfrozen = reads.filter((key) => validation[key].revision === undefined);
  if (validation.revision !== undefined) return;
  const metrics = Array.isArray(validation.jsonMetrics) ? validation.jsonMetrics.length : 0;
  if (unfrozen.length === 0 && metrics === 0) return;
  const detail = [...unfrozen.map((key) => `validation.${key}`), ...(metrics > 0 ? ['validation.jsonMetrics'] : [])];
  fail(`hashGroups are frozen but ${detail.join(', ')} still read the working tree; set validation.revision`);
}

function assertModuleCoverage(groups) {
  // Only groups that hash the working tree can be checked against it. Every historical input pins
  // all of its groups to a frozen revision and describes a tree this checkout is not at, so those
  // inputs are skipped: their coverage was whatever the pinned revision contained.
  const live = Object.values(groups).filter((group) => group.revision === undefined);
  if (live.length === 0) return;
  const covered = new Set(live.flatMap((group) => currentFiles(group.paths)).map((file) => relative(root, file)));
  const uncovered = coveredDirectories
    .flatMap((directory) => filesUnder(repositoryPath(directory, 'covered directory')))
    .map((file) => relative(root, file))
    .filter((file) => file.endsWith('.lean') && !covered.has(file))
    .sort(compare);
  if (uncovered.length > 0) {
    fail(`no hash group covers ${uncovered.join(', ')}; add each to a hashGroups entry`);
  }
}

function countAt(counts, path) {
  if (typeof path !== 'string' || path.length === 0) fail('validation count paths must be non-empty strings');
  let value = counts;
  for (const part of path.split('.')) {
    value = object(value, `counts.${path}`)[part];
  }
  if (!Number.isSafeInteger(value) || value < 0) fail(`counts.${path} must be a non-negative integer`);
  return value;
}

function valueAt(value, path, label) {
  if (typeof path !== 'string' || path.length === 0) fail(`${label} must be a non-empty string`);
  let result = value;
  for (const part of path.split('.')) result = object(result, label)[part];
  return result;
}

function validateCounts(value, label = 'counts') {
  const record = object(value, label);
  if (Object.keys(record).length === 0) fail(`${label} must not be empty`);
  for (const [key, entry] of Object.entries(record)) {
    if (entry !== null && typeof entry === 'object' && !Array.isArray(entry)) validateCounts(entry, `${label}.${key}`);
    else if (typeof entry === 'number' && (!Number.isSafeInteger(entry) || entry < 0)) {
      fail(`${label}.${key} must be a non-negative integer`);
    } else if (typeof entry !== 'number' && typeof entry !== 'string') {
      fail(`${label}.${key} must be a string, integer, or count object`);
    }
  }
}

function validateFormalDebt(value) {
  const debt = object(value, 'formalDebt');
  exactKeys(debt, ['counts', 'obligations'], 'formalDebt');
  const counts = object(debt.counts, 'formalDebt.counts');
  const areas = Object.keys(counts).filter((area) => area !== 'total');
  if (areas.length === 0 || !Object.hasOwn(counts, 'total')) {
    fail('formalDebt.counts must contain total and at least one area');
  }
  for (const [area, count] of Object.entries(counts)) {
    if (!Number.isSafeInteger(count) || count < 0) fail(`formalDebt.counts.${area} must be a non-negative integer`);
  }
  if (!Array.isArray(debt.obligations) || debt.obligations.length !== counts.total) {
    fail('formalDebt.obligations must match formalDebt.counts.total');
  }
  const actual = Object.fromEntries(areas.map((area) => [area, 0]));
  const ids = new Set();
  for (const [index, obligation] of debt.obligations.entries()) {
    exactKeys(obligation, ['id', 'area', 'statement'], `formalDebt.obligations[${index}]`);
    for (const key of ['id', 'area', 'statement']) {
      if (typeof obligation[key] !== 'string' || obligation[key].length === 0) {
        fail(`formalDebt.obligations[${index}].${key} must be non-empty`);
      }
    }
    if (!Object.hasOwn(actual, obligation.area)) fail(`unknown formal debt area ${obligation.area}`);
    if (ids.has(obligation.id)) fail(`duplicate formal debt id ${obligation.id}`);
    ids.add(obligation.id);
    actual[obligation.area] += 1;
  }
  for (const area of areas) {
    if (actual[area] !== counts[area]) fail(`formalDebt.counts.${area} does not match its obligations`);
  }
  if (areas.reduce((sum, area) => sum + counts[area], 0) !== counts.total) {
    fail('formalDebt area counts do not sum to total');
  }
}

function validateExecutableAssumptions(value) {
  const ledger = object(value, 'executableAssumptions');
  exactKeys(ledger, ['statement', 'assumptions'], 'executableAssumptions');
  if (typeof ledger.statement !== 'string' || ledger.statement.length === 0) {
    fail('executableAssumptions.statement must be non-empty');
  }
  if (!Array.isArray(ledger.assumptions) || ledger.assumptions.length === 0) {
    fail('executableAssumptions.assumptions must be a non-empty array');
  }
  const ids = new Set();
  for (const [index, assumption] of ledger.assumptions.entries()) {
    exactKeys(assumption, ['id', 'primitives', 'statement'], `executableAssumptions.assumptions[${index}]`);
    if (typeof assumption.id !== 'string' || assumption.id.length === 0) {
      fail(`executableAssumptions.assumptions[${index}].id must be non-empty`);
    }
    if (ids.has(assumption.id)) fail(`duplicate executable assumption id ${assumption.id}`);
    ids.add(assumption.id);
    const primitives = object(assumption.primitives, `executableAssumptions.assumptions[${index}].primitives`);
    if (
      Object.keys(primitives).length === 0 ||
      Object.values(primitives).some((primitive) => typeof primitive !== 'string' || primitive.length === 0)
    ) {
      fail(`executableAssumptions.assumptions[${index}].primitives must contain named non-empty strings`);
    }
    if (typeof assumption.statement !== 'string' || assumption.statement.length === 0) {
      fail(`executableAssumptions.assumptions[${index}].statement must be non-empty`);
    }
  }
}

function validateRefinementProofs(value) {
  const proofs = object(value, 'refinementProofs');
  exactKeys(proofs, ['audited', 'required', 'registryHash'], 'refinementProofs');
  for (const key of ['audited', 'required']) {
    if (!Number.isSafeInteger(proofs[key]) || proofs[key] <= 0) {
      fail(`refinementProofs.${key} must be a positive integer`);
    }
  }
  if (proofs.required > proofs.audited) {
    fail('refinementProofs.required must not exceed refinementProofs.audited');
  }
  if (typeof proofs.registryHash !== 'string' || !/^sha256:[0-9a-f]{64}$/.test(proofs.registryHash)) {
    fail('refinementProofs.registryHash must be a lowercase SHA-256 digest');
  }
}

function selectedFiles(config, label) {
  const directory = repositoryPath(config.directory, `${label}.directory`);
  if (typeof config.suffix !== 'string' || config.suffix.length === 0) fail(`${label}.suffix must be non-empty`);
  if (config.revision !== undefined && (typeof config.revision !== 'string' || config.revision.length === 0)) {
    fail(`${label}.revision must be a non-empty string`);
  }
  if (config.revision !== undefined) {
    const names = revisionFiles([config.directory], config.revision).filter((path) => path.endsWith(config.suffix));
    const contents = revisionContents(names, config.revision);
    return names.map((name, index) => ({ contents: contents[index].toString('utf8'), name }));
  }
  return filesUnder(directory)
    .filter((path) => path.endsWith(config.suffix))
    .sort(compare)
    .map((path) => ({ contents: readFileSync(path, 'utf8'), name: relative(root, path) }));
}

function validationText(path, revision, label) {
  repositoryPath(path, label);
  if (revision === undefined) return readFileSync(join(root, path), 'utf8');
  if (typeof revision !== 'string' || revision.length === 0) fail(`${label} revision must be a non-empty string`);
  return revisionContents([path], revision)[0].toString('utf8');
}

function validateEvidence(input) {
  const validation = object(input.validation, 'validation');
  const validationRevision = validation.revision;
  exactKeys(
    validation,
    validation.jsonMetrics === undefined
      ? ['testFiles', 'todos', 'corpus', 'lineCounts', ...(validationRevision === undefined ? [] : ['revision'])]
      : [
          'testFiles',
          'todos',
          'corpus',
          'lineCounts',
          'jsonMetrics',
          ...(validationRevision === undefined ? [] : ['revision']),
        ],
    'validation',
  );
  if (validationRevision !== undefined && (typeof validationRevision !== 'string' || validationRevision.length === 0)) {
    fail('validation.revision must be a non-empty string');
  }

  exactKeys(
    validation.testFiles,
    validation.testFiles.revision === undefined
      ? ['directory', 'suffix', 'countPath']
      : ['directory', 'suffix', 'countPath', 'revision'],
    'validation.testFiles',
  );
  const tests = selectedFiles(
    validationRevision === undefined ? validation.testFiles : { ...validation.testFiles, revision: validationRevision },
    'validation.testFiles',
  );
  const expectedTestFiles = countAt(input.counts, validation.testFiles.countPath);
  if (tests.length !== expectedTestFiles) fail(`expected ${expectedTestFiles} test files, found ${tests.length}`);

  exactKeys(
    validation.todos,
    validation.todos.revision === undefined
      ? ['directory', 'suffix', 'countPath']
      : ['directory', 'suffix', 'countPath', 'revision'],
    'validation.todos',
  );
  const todoFiles = selectedFiles(
    validationRevision === undefined ? validation.todos : { ...validation.todos, revision: validationRevision },
    'validation.todos',
  );
  const todoPattern = /\b(?:it|test)\.todo\s*\(\s*(?:'([^']+)'|"([^"]+)")/g;
  const todos = todoFiles
    .flatMap((file) =>
      [...file.contents.matchAll(todoPattern)].map((match) => {
        const id = (match[1] ?? match[2]).match(/^\[([^\]]+)\]/)?.[1];
        if (id === undefined) fail(`todo in ${file.name} must begin with an [id]`);
        return { id, location: file.name };
      }),
    )
    .sort((left, right) => compare(`${left.id}:${left.location}`, `${right.id}:${right.location}`));
  const expectedTodos = input.knownTodos
    .map((todo, index) => {
      exactKeys(todo, ['id', 'location'], `knownTodos[${index}]`);
      if (typeof todo.id !== 'string' || typeof todo.location !== 'string') fail(`knownTodos[${index}] is invalid`);
      return todo;
    })
    .sort((left, right) => compare(`${left.id}:${left.location}`, `${right.id}:${right.location}`));
  if (JSON.stringify(todos) !== JSON.stringify(expectedTodos)) fail('known todos differ from validated input');
  const expectedTodoCount = countAt(input.counts, validation.todos.countPath);
  if (todos.length !== expectedTodoCount) fail(`expected ${expectedTodoCount} todos, found ${todos.length}`);

  exactKeys(
    validation.corpus,
    validation.corpus.revision === undefined
      ? ['path', 'entriesPath', 'redPath']
      : ['path', 'entriesPath', 'redPath', 'revision'],
    'validation.corpus',
  );
  const corpus = JSON.parse(
    validationText(validation.corpus.path, validation.corpus.revision ?? validationRevision, 'validation.corpus.path'),
  );
  if (!Array.isArray(corpus.groups)) fail('corpus groups are unavailable');
  const entries = corpus.groups.flatMap((group) => {
    if (!Array.isArray(group.entries)) fail('a corpus group has no entries array');
    return group.entries;
  });
  const red = entries.filter((entry) => entry.status === 'red').length;
  const expectedEntries = countAt(input.counts, validation.corpus.entriesPath);
  const expectedRed = countAt(input.counts, validation.corpus.redPath);
  if (entries.length !== expectedEntries || red !== expectedRed) {
    fail(`corpus counts differ from validated input (${entries.length} entries, ${red} red)`);
  }

  if (!Array.isArray(validation.lineCounts)) fail('validation.lineCounts must be an array');
  for (const [index, lineCount] of validation.lineCounts.entries()) {
    exactKeys(
      lineCount,
      lineCount.revision === undefined ? ['path', 'prefix', 'countPath'] : ['path', 'prefix', 'countPath', 'revision'],
      `validation.lineCounts[${index}]`,
    );
    if (typeof lineCount.prefix !== 'string' || lineCount.prefix.length === 0) {
      fail(`validation.lineCounts[${index}].prefix must be non-empty`);
    }
    const lines = validationText(
      lineCount.path,
      lineCount.revision ?? validationRevision,
      `validation.lineCounts[${index}].path`,
    ).split('\n');
    const actual = lines.filter((line) => line.startsWith(lineCount.prefix)).length;
    const expected = countAt(input.counts, lineCount.countPath);
    if (actual !== expected) fail(`expected ${expected} matching lines in ${lineCount.path}, found ${actual}`);
  }

  if (validation.jsonMetrics !== undefined) {
    if (!Array.isArray(validation.jsonMetrics)) fail('validation.jsonMetrics must be an array');
    for (const [index, metric] of validation.jsonMetrics.entries()) {
      const label = `validation.jsonMetrics[${index}]`;
      const expectedKeys =
        metric.where === undefined
          ? ['path', 'jsonPath', 'countPath', 'measure']
          : ['path', 'jsonPath', 'countPath', 'measure', 'where'];
      exactKeys(metric, expectedKeys, label);
      if (!['value', 'length', 'count'].includes(metric.measure)) fail(`${label}.measure is invalid`);
      if (metric.where !== undefined) {
        exactKeys(metric.where, ['path', 'equals'], `${label}.where`);
        if (metric.measure !== 'count') fail(`${label}.where requires count measurement`);
      }
      const document = JSON.parse(validationText(metric.path, validationRevision, `${label}.path`));
      const selected = valueAt(document, metric.jsonPath, `${label}.jsonPath`);
      let actual;
      if (metric.measure === 'value') actual = selected;
      else {
        if (!Array.isArray(selected)) fail(`${label}.jsonPath must select an array`);
        actual =
          metric.measure === 'length'
            ? selected.length
            : selected.filter(
                (entry) => valueAt(entry, metric.where.path, `${label}.where.path`) === metric.where.equals,
              ).length;
      }
      const expected = countAt(input.counts, metric.countPath);
      if (actual !== expected) fail(`${label} expected ${expected}, found ${String(actual)}`);
    }
  }

  return expectedTodos;
}

const { check, input: inputArgument } = parseArgs(argv.slice(2));
const inputPath = repositoryPath(inputArgument, '--input');
const input = JSON.parse(readFileSync(inputPath, 'utf8'));
const revisionKey = input.baseRevision === undefined ? 'upstreamRevision' : 'baseRevision';
const expectedKeys = [
  'schemaVersion',
  'outputPath',
  revisionKey,
  'branch',
  'counts',
  'knownTodos',
  'validation',
  'hashGroups',
];
if (input.formalDebt !== undefined) expectedKeys.push('formalDebt');
if (input.executableAssumptions !== undefined) expectedKeys.push('executableAssumptions');
if (input.refinementProofs !== undefined) expectedKeys.push('refinementProofs');
exactKeys(input, expectedKeys, 'input');
if (input.schemaVersion !== 1) fail('unsupported evidence input schema');
if (typeof input[revisionKey] !== 'string' || input[revisionKey].length === 0) fail(`${revisionKey} must be non-empty`);
if (typeof input.branch !== 'string' || input.branch.length === 0) fail('branch must be non-empty');
if (!Array.isArray(input.knownTodos)) fail('knownTodos must be an array');
validateCounts(input.counts);
if (input.formalDebt !== undefined) validateFormalDebt(input.formalDebt);
if (input.executableAssumptions !== undefined) validateExecutableAssumptions(input.executableAssumptions);
if (input.refinementProofs !== undefined) validateRefinementProofs(input.refinementProofs);

const branch = textCommand('git', ['branch', '--show-current']);
if (branch !== input.branch) fail(`expected branch ${input.branch}, found ${branch || '<detached HEAD>'}`);
const groups = object(input.hashGroups, 'hashGroups');
if (Object.keys(groups).length === 0) fail('hashGroups must not be empty');
// Before any count is read, so a half-frozen snapshot reports why rather than surfacing as a
// confusing mismatch against whatever the working tree happens to contain.
assertFreezingIsCoherent(input, groups);
const knownTodos = validateEvidence(input);
assertModuleCoverage(groups);

const localBin = (name) => join(root, 'node_modules/.bin', name);
const hashes = Object.fromEntries(Object.entries(groups).map(([name, group]) => [name, hashGroup(group, name)]));
const manifest = {
  schemaVersion: 1,
  [revisionKey]: input[revisionKey],
  branch,
  toolchain: {
    bun: textCommand('bun', ['--version']),
    node: textCommand('node', ['--version']),
    typescript: textCommand(localBin('tsc'), ['--version']).replace(/^Version /, ''),
    vitest: textCommand(localBin('vitest'), ['--version']),
    prettier: textCommand(localBin('prettier'), ['--version']),
    eslint: textCommand(localBin('eslint'), ['--version']),
    lean: textCommand('lean', ['--version'], join(root, 'lean')),
    lake: textCommand('lake', ['--version'], join(root, 'lean')),
  },
  counts: input.counts,
  ...(input.refinementProofs === undefined ? {} : { refinementProofs: input.refinementProofs }),
  ...(input.executableAssumptions === undefined ? {} : { executableAssumptions: input.executableAssumptions }),
  ...(input.formalDebt === undefined ? {} : { formalDebt: input.formalDebt }),
  knownTodos,
  hashes,
};
const canonical = `${JSON.stringify(manifest, null, 2)}\n`;
const outputPath = repositoryPath(input.outputPath, 'outputPath');

if (check) {
  const checkedIn = readFileSync(outputPath, 'utf8');
  if (checkedIn !== canonical) {
    const checkedInLines = checkedIn.split('\n');
    const canonicalLines = canonical.split('\n');
    const line = canonicalLines.findIndex((value, index) => value !== checkedInLines[index]);
    fail(
      `${input.outputPath} is stale at line ${line + 1}\n` +
        `- ${checkedInLines[line] ?? '<missing>'}\n` +
        `+ ${canonicalLines[line] ?? '<missing>'}\n` +
        `Run \`bun scripts/generate-evidence-manifest.mjs --input ${inputArgument}\` to update it.`,
    );
  }
} else {
  writeFileSync(outputPath, canonical);
}
