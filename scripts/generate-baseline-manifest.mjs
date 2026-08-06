import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { lstatSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { dirname, join, relative, resolve } from 'node:path';
import { argv } from 'node:process';
import { fileURLToPath } from 'node:url';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const inputPath = join(root, 'evidence/baseline-input.json');
const outputPath = join(root, 'evidence/baseline-manifest.json');
const input = JSON.parse(readFileSync(inputPath, 'utf8'));
const check = argv.slice(2).includes('--check');

if (argv.length !== (check ? 3 : 2)) {
  throw new Error('Usage: generate-baseline-manifest.mjs [--check]');
}

function fail(message) {
  throw new Error(`Cannot generate baseline manifest: ${message}`);
}

function command(executable, args, cwd = root) {
  try {
    return execFileSync(executable, args, { cwd, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }).trim();
  } catch (error) {
    const detail = error instanceof Error ? error.message : String(error);
    fail(`${executable} ${args.join(' ')} failed: ${detail}`);
  }
}

function filesUnder(directory) {
  const files = [];
  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    const path = join(directory, entry.name);
    if (entry.isDirectory()) files.push(...filesUnder(path));
    else if (entry.isFile()) files.push(path);
    else fail(`unsupported filesystem entry ${relative(root, path)}`);
  }
  return files;
}

function hashDirectories(directories) {
  const hash = createHash('sha256');
  const files = directories.flatMap((directory) => filesUnder(join(root, directory))).sort();
  if (files.length === 0) fail(`no files found under ${directories.join(', ')}`);
  for (const path of files) {
    if (!lstatSync(path).isFile()) fail(`${relative(root, path)} is not a regular file`);
    hash.update(relative(root, path));
    hash.update('\0');
    hash.update(readFileSync(path));
    hash.update('\0');
  }
  return `sha256:${hash.digest('hex')}`;
}

function testFiles(directory) {
  return filesUnder(directory)
    .filter((path) => path.endsWith('.test.ts'))
    .sort();
}

if (input.schemaVersion !== 1) fail('unsupported evidence input schema');

const branch = command('git', ['branch', '--show-current']);
if (branch !== input.branch) fail(`expected branch ${input.branch}, found ${branch}`);

const corpus = JSON.parse(readFileSync(join(root, 'spec/corpus/counterexamples.json'), 'utf8'));
if (!Array.isArray(corpus.groups)) fail('corpus groups are unavailable');
const corpusEntries = corpus.groups.flatMap((group) => group.entries);
const redCorpusEntries = corpusEntries.filter((entry) => entry.status === 'red').length;
if (corpusEntries.length !== input.current.corpus.entries || redCorpusEntries !== input.current.corpus.red) {
  fail(`corpus counts differ from validated input (${corpusEntries.length} entries, ${redCorpusEntries} red)`);
}

const tests = testFiles(join(root, 'tests'));
if (tests.length !== input.current.tests.files)
  fail(`expected ${input.current.tests.files} test files, found ${tests.length}`);
const todoPattern = /\b(?:it|test)\.todo\s*\(\s*(?:'([^']+)'|"([^"]+)")/g;
const todos = tests
  .flatMap((path) =>
    [...readFileSync(path, 'utf8').matchAll(todoPattern)].map((match) => ({
      id: (match[1] ?? match[2]).match(/^\[([^\]]+)\]/)?.[1],
      location: relative(root, path),
    })),
  )
  .sort((left, right) => `${left.id}:${left.location}`.localeCompare(`${right.id}:${right.location}`));
const expectedTodos = [...input.knownTodos].sort((left, right) =>
  `${left.id}:${left.location}`.localeCompare(`${right.id}:${right.location}`),
);
if (JSON.stringify(todos) !== JSON.stringify(expectedTodos)) fail('known todos differ from validated input');
if (todos.length !== input.current.tests.todo)
  fail(`expected ${input.current.tests.todo} todos, found ${todos.length}`);

const localBin = (name) => join(root, 'node_modules/.bin', name);
const manifest = {
  schemaVersion: 1,
  upstreamRevision: input.upstreamRevision,
  branch,
  toolchain: {
    bun: command('bun', ['--version']),
    node: command('node', ['--version']),
    typescript: command(localBin('tsc'), ['--version']).replace(/^Version /, ''),
    vitest: command(localBin('vitest'), ['--version']),
    prettier: command(localBin('prettier'), ['--version']),
    eslint: command(localBin('eslint'), ['--version']),
    lean: command('lean', ['--version'], join(root, 'lean')),
    lake: command('lake', ['--version'], join(root, 'lean')),
  },
  counts: {
    original: input.original,
    phase0Repaired: input.phase0Repaired,
    current: input.current,
  },
  knownTodos: expectedTodos,
  hashes: {
    source: hashDirectories(['src']),
    runtime: hashDirectories(['lean/TSLean']),
    corpus: hashDirectories(['spec/corpus']),
  },
};

const canonical = `${JSON.stringify(manifest, null, 2)}\n`;

if (check) {
  const checkedIn = readFileSync(outputPath, 'utf8');
  if (checkedIn !== canonical) {
    const checkedInLines = checkedIn.split('\n');
    const canonicalLines = canonical.split('\n');
    const line = canonicalLines.findIndex((value, index) => value !== checkedInLines[index]);
    fail(
      `checked-in manifest is stale at line ${line + 1}\n` +
        `- ${checkedInLines[line] ?? '<missing>'}\n` +
        `+ ${canonicalLines[line] ?? '<missing>'}\n` +
        'Run `bun run evidence:generate` to update it.',
    );
  }
} else {
  writeFileSync(outputPath, canonical);
}
