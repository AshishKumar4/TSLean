import { existsSync, readFileSync, readdirSync } from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { describe, expect, it } from 'vitest';
import { isJsonObject, type JsonValue, validateJsonSchema } from './helpers/json-schema.js';

type Outcome = { kind: string; value: string };
type Provenance = { sourceRevision: string; transcript: string; sourceRefs: string[] };
type Entry = {
  id: string;
  title: string;
  source: string;
  partial: boolean;
  partialExplanation?: string;
  expected: Outcome;
  priorLean: Outcome;
  severity: string;
  provenance: Provenance[];
  status: string;
};
type Corpus = {
  schemaVersion: number;
  groups: Array<{ group: string; entries: Entry[] }>;
};
type Todo = { id: string; location: string };

const repositoryRoot = dirname(dirname(fileURLToPath(import.meta.url)));
const corpusPath = join(repositoryRoot, 'spec/corpus/counterexamples.json');
const schemaPath = join(repositoryRoot, 'spec/corpus/schema.json');
const corpusSource = readFileSync(corpusPath, 'utf8');
const corpus: Corpus = JSON.parse(corpusSource);
const corpusDocument: JsonValue = JSON.parse(corpusSource);
const schema: JsonValue = JSON.parse(readFileSync(schemaPath, 'utf8'));

function collectTestFiles(directory: string): string[] {
  const files: string[] = [];
  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    const path = join(directory, entry.name);
    if (entry.isDirectory()) files.push(...collectTestFiles(path));
    else if (entry.name.endsWith('.test.ts')) files.push(path);
  }
  return files;
}

function collectTodos(): { todos: Todo[]; errors: string[] } {
  const todos: Todo[] = [];
  const errors: string[] = [];
  const invocationPattern = /\b(?:it|test)\.todo\s*\(/g;
  const staticTitlePattern = /\b(?:it|test)\.todo\s*\(\s*(?:'((?:\\.|[^'\\\r\n])*)'|"((?:\\.|[^"\\\r\n])*)")/g;
  const idPattern = /^\[([a-z0-9]+(?:-[a-z0-9]+)*)\]\s+\S/;

  for (const file of collectTestFiles(join(repositoryRoot, 'tests')).sort()) {
    const source = readFileSync(file, 'utf8');
    const invocationCount = [...source.matchAll(invocationPattern)].length;
    const matches = [...source.matchAll(staticTitlePattern)];
    const location = relative(repositoryRoot, file);
    if (matches.length !== invocationCount) errors.push(`${location}: todo titles must be static strings`);
    for (const match of matches) {
      const title = match[1] ?? match[2];
      const idMatch = title.match(idPattern);
      if (idMatch === null) errors.push(`${location}: todo title lacks a [corpus-id]: ${title}`);
      else todos.push({ id: idMatch[1], location });
    }
  }
  return { todos, errors };
}

function duplicates(values: string[]): string[] {
  const seen = new Set<string>();
  const duplicateValues = new Set<string>();
  for (const value of values) {
    if (seen.has(value)) duplicateValues.add(value);
    seen.add(value);
  }
  return [...duplicateValues].sort();
}

const entries = corpus.groups.flatMap((group) => group.entries);

describe('semantic counterexample corpus', () => {
  it('uses a strict draft 2020-12 schema', () => {
    expect(isJsonObject(schema) && schema.$schema).toBe('https://json-schema.org/draft/2020-12/schema');
  });

  it('validates against the complete checked-in JSON Schema', () => {
    const errors: string[] = [];
    validateJsonSchema(corpusDocument, schema, schema, 'corpus', errors);
    expect(errors).toEqual([]);
  });

  it('has unique corpus IDs and nonempty complete sources', () => {
    expect(duplicates(entries.map((entry) => entry.id))).toEqual([]);
    expect(entries.filter((entry) => !entry.partial && entry.source.length === 0).map((entry) => entry.id)).toEqual([]);
  });

  it('validates source references in their declared revision context', () => {
    const errors: string[] = [];
    for (const entry of entries) {
      for (const provenance of entry.provenance) {
        for (const sourceRef of provenance.sourceRefs) {
          const match = sourceRef.match(/^(.+?)(?::(\d+)(?:-(\d+)|\+)?)?$/);
          const referencedPath = match?.[1];
          const absolutePath = referencedPath === undefined ? repositoryRoot : resolve(repositoryRoot, referencedPath);
          const repositoryPath = relative(repositoryRoot, absolutePath);
          if (
            referencedPath === undefined ||
            repositoryPath.startsWith('..') ||
            isAbsolute(repositoryPath) ||
            !existsSync(absolutePath)
          ) {
            errors.push(`${entry.id}: ${sourceRef}`);
            continue;
          }

          if (provenance.sourceRevision === 'current' && match?.[2] !== undefined) {
            const firstLine = Number(match[2]);
            const lastLine = match[3] === undefined ? firstLine : Number(match[3]);
            const source = readFileSync(absolutePath, 'utf8');
            const lineCount = source.length === 0 ? 0 : source.split(/\r?\n/).length - (source.endsWith('\n') ? 1 : 0);
            if (firstLine < 1 || firstLine > lastLine || lastLine > lineCount) {
              errors.push(`${entry.id}: ${sourceRef}`);
            }
          }
        }

        if (
          provenance.sourceRevision !== 'current' &&
          (provenance.sourceRevision.trim().length === 0 || provenance.transcript.trim().length === 0)
        ) {
          errors.push(`${entry.id}: historical provenance lacks a revision or transcript locator`);
        }
      }
    }
    expect(errors).toEqual([]);
  });

  it('keeps Vitest todos synchronized with corpus obligations', () => {
    const { todos, errors } = collectTodos();
    const corpusIds = new Set(entries.map((entry) => entry.id));
    const baselineIds = entries
      .filter((entry) => entry.provenance.some(({ transcript }) => transcript.startsWith('baseline-suite-')))
      .map((entry) => entry.id);

    errors.push(...duplicates(todos.map((todo) => todo.id)).map((id) => `duplicate todo ID: ${id}`));
    errors.push(
      ...todos.filter((todo) => !corpusIds.has(todo.id)).map((todo) => `${todo.location}: orphan todo ${todo.id}`),
    );
    const todoIds = new Set(todos.map((todo) => todo.id));
    errors.push(...baselineIds.filter((id) => !todoIds.has(id)).map((id) => `baseline corpus entry lacks todo: ${id}`));

    expect(errors).toEqual([]);
  });
});
