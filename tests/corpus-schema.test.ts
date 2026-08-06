import { existsSync, readFileSync, readdirSync } from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { describe, expect, it } from 'vitest';

type JsonValue = null | boolean | number | string | JsonValue[] | { [key: string]: JsonValue };
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

const supportedSchemaKeywords = new Set([
  '$defs',
  '$id',
  '$ref',
  '$schema',
  'additionalProperties',
  'allOf',
  'const',
  'else',
  'enum',
  'if',
  'items',
  'maxItems',
  'minItems',
  'minLength',
  'not',
  'pattern',
  'properties',
  'required',
  'then',
  'title',
  'type',
]);

function isObject(value: JsonValue | undefined): value is { [key: string]: JsonValue } {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function sameJson(left: JsonValue, right: JsonValue): boolean {
  return JSON.stringify(left) === JSON.stringify(right);
}

function resolveReference(rootSchema: JsonValue, reference: string): JsonValue | undefined {
  if (!reference.startsWith('#/')) return undefined;
  let current: JsonValue | undefined = rootSchema;
  for (const segment of reference.slice(2).split('/')) {
    if (!isObject(current)) return undefined;
    current = current[segment.replaceAll('~1', '/').replaceAll('~0', '~')];
  }
  return current;
}

function validateJsonSchema(
  value: JsonValue,
  currentSchema: JsonValue,
  rootSchema: JsonValue,
  path: string,
  errors: string[],
): void {
  if (!isObject(currentSchema)) {
    errors.push(`${path}: schema node must be an object`);
    return;
  }

  for (const keyword of Object.keys(currentSchema)) {
    if (!supportedSchemaKeywords.has(keyword)) errors.push(`${path}: unsupported schema keyword ${keyword}`);
  }

  const reference = currentSchema.$ref;
  if (typeof reference === 'string') {
    const referencedSchema = resolveReference(rootSchema, reference);
    if (referencedSchema === undefined) errors.push(`${path}: unresolved schema reference ${reference}`);
    else validateJsonSchema(value, referencedSchema, rootSchema, path, errors);
  }

  const allOf = currentSchema.allOf;
  if (Array.isArray(allOf)) {
    for (const subSchema of allOf) validateJsonSchema(value, subSchema, rootSchema, path, errors);
  }

  const condition = currentSchema.if;
  if (condition !== undefined) {
    const conditionErrors: string[] = [];
    validateJsonSchema(value, condition, rootSchema, path, conditionErrors);
    const branch = conditionErrors.length === 0 ? currentSchema.then : currentSchema.else;
    if (branch !== undefined) validateJsonSchema(value, branch, rootSchema, path, errors);
  }

  const negatedSchema = currentSchema.not;
  if (negatedSchema !== undefined) {
    const negatedErrors: string[] = [];
    validateJsonSchema(value, negatedSchema, rootSchema, path, negatedErrors);
    if (negatedErrors.length === 0) errors.push(`${path}: must not match negated schema`);
  }

  const expectedType = currentSchema.type;
  if (typeof expectedType === 'string') {
    const matchesType =
      expectedType === 'object'
        ? isObject(value)
        : expectedType === 'array'
          ? Array.isArray(value)
          : expectedType === 'string'
            ? typeof value === 'string'
            : expectedType === 'number'
              ? typeof value === 'number'
              : expectedType === 'boolean'
                ? typeof value === 'boolean'
                : expectedType === 'null'
                  ? value === null
                  : false;
    if (!matchesType) {
      errors.push(`${path}: expected ${expectedType}`);
      return;
    }
  }

  if (currentSchema.const !== undefined && !sameJson(value, currentSchema.const)) {
    errors.push(`${path}: does not equal const value`);
  }
  const enumValues = currentSchema.enum;
  if (Array.isArray(enumValues) && !enumValues.some((candidate) => sameJson(value, candidate))) {
    errors.push(`${path}: is not an allowed enum value`);
  }

  if (typeof value === 'string') {
    const minLength = currentSchema.minLength;
    if (typeof minLength === 'number' && value.length < minLength) errors.push(`${path}: is too short`);
    const pattern = currentSchema.pattern;
    if (typeof pattern === 'string' && !new RegExp(pattern, 'u').test(value)) {
      errors.push(`${path}: does not match ${pattern}`);
    }
  }

  if (Array.isArray(value)) {
    const minItems = currentSchema.minItems;
    const maxItems = currentSchema.maxItems;
    if (typeof minItems === 'number' && value.length < minItems) errors.push(`${path}: has too few items`);
    if (typeof maxItems === 'number' && value.length > maxItems) errors.push(`${path}: has too many items`);
    if (currentSchema.items !== undefined) {
      for (const [index, item] of value.entries()) {
        validateJsonSchema(item, currentSchema.items, rootSchema, `${path}[${index}]`, errors);
      }
    }
  }

  if (isObject(value)) {
    const required = currentSchema.required;
    if (Array.isArray(required)) {
      for (const field of required) {
        if (typeof field === 'string' && !Object.hasOwn(value, field)) errors.push(`${path}: missing ${field}`);
      }
    }

    const properties = currentSchema.properties;
    if (isObject(properties)) {
      for (const [field, fieldValue] of Object.entries(value)) {
        const fieldSchema = properties[field];
        if (fieldSchema !== undefined) {
          validateJsonSchema(fieldValue, fieldSchema, rootSchema, `${path}.${field}`, errors);
        } else if (currentSchema.additionalProperties === false) {
          errors.push(`${path}.${field}: additional property is not allowed`);
        }
      }
    }
  }
}

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
    expect(isObject(schema) && schema.$schema).toBe('https://json-schema.org/draft/2020-12/schema');
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
