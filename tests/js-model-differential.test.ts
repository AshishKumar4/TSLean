import { createHash } from 'node:crypto';
import { execFileSync, spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { beforeAll, describe, expect, it } from 'vitest';
import {
  buildDifferentialSuite,
  compareCodeUnits,
  loadCombinedDifferential,
  renderDifferentialManifest,
  renderLeanRegistry,
  validateFixture,
  verifyDifferentialArtifacts,
} from '../scripts/differential-manifest-lib.mjs';
import { Canonicalizer } from './differential/canonical.js';
import { observationMismatch } from './differential/compare.js';
import { LeanOracle } from './differential/lean-oracle.js';
import { materializeFixtures } from './differential/fixture.js';
import { runNodeVector } from './differential/node-runner.js';
import type { DifferentialManifest, Fixture, GraphFixture, Observation, OracleRequest } from './differential/types.js';
import { isJsonObject, type JsonValue, validateJsonSchema } from './helpers/json-schema.js';

const root = resolve(import.meta.dirname, '..');
const leanRoot = resolve(root, 'lean');
const suiteSource = readFileSync(resolve(root, 'spec/differential/primitive.json'), 'utf8');
const abstractSuiteSource = readFileSync(resolve(root, 'spec/differential/abstract-operations.json'), 'utf8');
const coverageSource = readFileSync(resolve(root, 'spec/differential/corpus-coverage.json'), 'utf8');
const generated = loadCombinedDifferential(root);
const suite = generated.suite;
const manifestSource = readFileSync(resolve(root, 'spec/differential/manifest.json'), 'utf8');
const checkedManifest: DifferentialManifest = JSON.parse(manifestSource);
const manifest: DifferentialManifest = generated.manifest;
const registrySource = readFileSync(resolve(leanRoot, 'TSLean/JS/Oracle/Registry.lean'), 'utf8');
const exactCorpusOperations = new Map<string, string>([
  ['identity-strict-coercive-equality', 'value-strict'],
  ['identity-array-reference-equality', 'value-strict'],
  ['identity-null-undefined', 'value-strict'],
  ['operators-short-circuit-assignment', 'short-circuit-assignment'],
  ['truthiness-empty-array', 'truthiness-empty-array'],
  ['truthiness-nullable-empty-string', 'logical-or'],
  ['operators-effectful-compound-condition', 'while-call-once'],
  ['operators-number-string-addition', 'value-add'],
  ['completion-try-finally-return', 'finally-return'],
  ['completion-try-finally-order', 'finally-order'],
  ['completion-forof-live-array', 'iterate-live'],
  ['mutation-object-spread-order', 'spread-overwrite'],
  ['globals-typeof-stub', 'typeof-string-check'],
]);
const registry = new Map(suite.registry.map((operation) => [operation.id, operation]));

function sha256(value: string): string {
  return createHash('sha256').update(value).digest('hex');
}

function request(vector: DifferentialManifest['vectors'][number]): OracleRequest {
  return { id: vector.id, operation: vector.operation, fixtures: vector.fixtures };
}

function units(value: string): number[] {
  return Array.from({ length: value.length }, (_, index) => value.charCodeAt(index));
}

function textFromCodeUnits(value: number[]): string {
  return String.fromCharCode(...value);
}


function fakeOracle(source: string): () => ChildProcessWithoutNullStreams {
  return () => spawn(process.execPath, ['-e', source], { stdio: ['pipe', 'pipe', 'pipe'] });
}

const fakeResponseSource = `
let input = '';
process.stdin.setEncoding('utf8');
process.stdin.on('data', chunk => {
  input += chunk;
  for (;;) {
    const newline = input.indexOf('\\n');
    if (newline < 0) break;
    const line = input.slice(0, newline);
    input = input.slice(newline + 1);
    const request = JSON.parse(line);
    process.stdout.write(JSON.stringify({
      id: request.id,
      status: 'ok',
      observation: { completion: { type: 'normal', value: { type: 'undefined' } }, trace: [] }
    }) + '\\n');
  }
});
`;

beforeAll(() => {
  execFileSync('lake', ['build', 'js-model-oracle'], { cwd: leanRoot, stdio: 'pipe' });
}, 120_000);

describe('generic model differential infrastructure', () => {
  it('validates the strict source schema and generated manifest invariants', () => {
    const schema: JsonValue = JSON.parse(readFileSync(resolve(root, 'spec/differential/schema.json'), 'utf8'));
    const document: JsonValue = JSON.parse(suiteSource);
    const abstractDocument: JsonValue = JSON.parse(abstractSuiteSource);
    const errors: string[] = [];
    validateJsonSchema(document, schema, schema, 'primitive', errors);
    validateJsonSchema(abstractDocument, schema, schema, 'abstract-operations', errors);
    expect(isJsonObject(schema) && schema.$schema).toBe('https://json-schema.org/draft/2020-12/schema');
    const definitions = isJsonObject(schema) ? schema.$defs : undefined;
    if (!isJsonObject(definitions) || definitions.observation === undefined) {
      throw new Error('differential schema lacks the observation definition');
    }
    const canonicalSamples: JsonValue[] = [
      { completion: { type: 'normal', value: { type: 'undefined' } }, trace: [] },
      { completion: { type: 'normal', value: { type: 'string', units: [0, 0xd800, 0xffff] } }, trace: [] },
      {
        completion: {
          type: 'throw',
          value: {
            type: 'error', identity: 'ref-0',
            name: { type: 'string', units: units('TypeError') }, message: { type: 'string', units: [] },
          },
        },
        trace: [],
      },
      {
        completion: { type: 'normal', value: { type: 'object', identity: 'ref-0' } },
        trace: [],
        roots: [{ type: 'object', identity: 'ref-0' }],
        objects: [{
          identity: 'ref-0', kind: 'object', prototype: { type: 'null' }, extensible: true,
          properties: [{
            key: { type: 'string', units: units('self') },
            descriptor: {
              kind: 'data', value: { type: 'object', identity: 'ref-0' },
              writable: true, enumerable: true, configurable: true,
            },
          }],
        }],
      },
    ];
    canonicalSamples.forEach((sample, index) => {
      validateJsonSchema(sample, definitions.observation, schema, `observation[${index}]`, errors);
    });
    expect(errors).toEqual([]);
    expect(suiteSource.includes('"expected"')).toBe(false);
    expect(manifestSource.includes('"expected"')).toBe(false);
    expect(checkedManifest).toEqual(manifest);
    expect(renderDifferentialManifest(manifest)).toBe(manifestSource);
    expect(renderLeanRegistry(suite)).toBe(registrySource);
    expect(manifest.sourceHashes.primitive).toBe(sha256(suiteSource));
    expect(manifest.sourceHashes['abstract-operations']).toBe(sha256(abstractSuiteSource));
    expect(manifest.corpusCoverageHash).toBe(sha256(coverageSource));
    expect(manifest.legacyInventoryHash).toBe(sha256(
      readFileSync(resolve(root, 'spec/differential/legacy-abstract-inventory.json'), 'utf8'),
    ));
    expect(manifest.corpusClassifications).toEqual({
      'model-covered': 13,
      'compiler-only': 43,
      'model-pending': 26,
      'proof-integrity': 11,
      scale: 9,
    });
    expect(manifest.operationRegistry).toEqual(suite.registry.map(({ id }) => id));
    expect(manifest.operationDefinitions).toEqual(suite.registry);
    expect([...new Set(manifest.vectors.map(({ operation }) => operation))].sort(compareCodeUnits)).toEqual(manifest.operationRegistry);
    expect(suite.registry.some(({ source }) => /\b(?:process|require|fetch|setTimeout|setInterval)\b/.test(source))).toBe(false);
    expect(manifest.scenarioCount).toBe(16);
    expect(manifest.fixedCount).toBe(734);
    expect(manifest.generatedCount).toBe(6_530);
    expect(manifest.vectorCount).toBe(7_264);
    expect(manifest.comparisonCount).toBe(7_264);
    expect(manifest.totalCount).toBe(7_264);
    expect(manifest.uniqueOperationInputCount).toBe(6_088);
    expect(manifest.parityDuplicateCount).toBe(1_176);
    expect(manifest.duplicatePolicy).toBe('preserved-for-v1-parity');
    expect(manifest.counts).toEqual({
      'abstract-coercion-operators': 30,
      'abstract-instanceof': 10,
      'abstract-ordinary-conversion': 8,
      'abstract-realm-copy': 31,
      'abstract-wrapper-matrix': 18,
      'canonical-graphs': 11,
      'canonical-script-formats': 6,
      'canonical-symbols': 3,
      'canonical-utf16': 1,
      'canonical-wrapper-prototypes': 5,
      'curated-operators': 23,
      'conversion-equality': 504,
      'corpus-model-probes': 14,
      format: 278,
      parse: 322,
      'seeded-operators': 6_000,
    });
    expect(manifest.vectors.map(({ id }) => id)).toEqual(manifest.vectors.map(({ id }) => id).sort(compareCodeUnits));
    expect(new Set(manifest.vectors.map(({ id }) => id)).size).toBe(manifest.totalCount);
    for (const vector of manifest.vectors) {
      expect(vector.inputHash).toBe(sha256(JSON.stringify({ operation: vector.operation, fixtures: vector.fixtures })));
      expect(vector.tags).toEqual([...new Set(vector.tags)].sort(compareCodeUnits));
      if (vector.replay !== undefined) expect(vector.replay.index).toBeGreaterThanOrEqual(0);
    }
    expect(manifest.vectors.filter(({ tags }) => tags.includes('bigint-arithmetic-regression'))).toHaveLength(5);
  });

  it('classifies every corpus entry once with bidirectional model scenario links', () => {
    const coverageSchema: JsonValue = JSON.parse(
      readFileSync(resolve(root, 'spec/differential/corpus-coverage.schema.json'), 'utf8'),
    );
    const coverageDocument: JsonValue = JSON.parse(coverageSource);
    const errors: string[] = [];
    validateJsonSchema(coverageDocument, coverageSchema, coverageSchema, 'coverage', errors);
    expect(errors).toEqual([]);

    const coverage = JSON.parse(coverageSource);
    const corpus = JSON.parse(readFileSync(resolve(root, 'spec/corpus/counterexamples.json'), 'utf8'));
    const corpusEntries = corpus.groups.flatMap((group: { entries: Array<{ id: string; status: string }> }) => group.entries);
    const corpusIds = corpusEntries.map(({ id }: { id: string }) => id).sort(compareCodeUnits);
    const coverageIds = coverage.entries.map(({ id }: { id: string }) => id).sort(compareCodeUnits);
    expect(coverageIds).toEqual(corpusIds);
    expect(new Set(coverageIds).size).toBe(102);
    expect(corpusEntries.every(({ status }: { status: string }) => status === 'red')).toBe(true);

    const suites = [JSON.parse(suiteSource), JSON.parse(abstractSuiteSource)];
    const scenarios = new Map<string, { corpusIds: string[]; vectors: Map<string, string[]> }>(suites.flatMap((suite) =>
      suite.scenarios.map((scenario: {
        id: string; corpusIds?: string[]; vectors: Array<{ id: string; corpusIds: string[] }>;
      }): [string, { corpusIds: string[]; vectors: Map<string, string[]> }] => [scenario.id, {
        corpusIds: scenario.corpusIds ?? [],
        vectors: new Map(scenario.vectors.map((vector): [string, string[]] => [vector.id, vector.corpusIds])),
      }])));
    const forward = new Map<string, string[]>();
    for (const entry of coverage.entries) {
      if (entry.classification !== 'model-covered') continue;
      for (const scenarioId of entry.scenarioIds) {
        expect(scenarios.has(scenarioId)).toBe(true);
        expect(scenarios.get(scenarioId)?.vectors.get(entry.id)).toContain(entry.id);
        const suite = suites.find((candidate) => candidate.scenarios.some((scenario: { id: string }) => scenario.id === scenarioId));
        const scenario = suite?.scenarios.find((candidate: { id: string }) => candidate.id === scenarioId);
        const vector = scenario?.vectors.find((candidate: { id: string }) => candidate.id === entry.id);
        expect(vector?.operation).toBe(exactCorpusOperations.get(entry.id));
        const ids = forward.get(scenarioId) ?? [];
        ids.push(entry.id);
        forward.set(scenarioId, ids);
      }
    }
    for (const [scenarioId, scenario] of scenarios) {
      expect([...new Set([...scenario.vectors.values()].flat())].sort(compareCodeUnits))
        .toEqual([...scenario.corpusIds].sort(compareCodeUnits));
      expect((forward.get(scenarioId) ?? []).sort(compareCodeUnits))
        .toEqual([...scenario.corpusIds].sort(compareCodeUnits));
    }
    for (const entry of coverage.entries) {
      for (const test of entry.tests ?? []) expect(existsSync(resolve(root, test))).toBe(true);
    }
    expect([...exactCorpusOperations.keys()].sort(compareCodeUnits)).toEqual(
      coverage.entries.filter((entry: { classification: string }) => entry.classification === 'model-covered')
        .map((entry: { id: string }) => entry.id).sort(compareCodeUnits),
    );
  });

  it('detects tampered manifest and operation registry artifacts', () => {
    const tamperedManifest = structuredClone(checkedManifest);
    tamperedManifest.vectors[0].inputHash = '0'.repeat(64);
    expect(() => verifyDifferentialArtifacts(root, renderDifferentialManifest(tamperedManifest), registrySource))
      .toThrow('differential manifest is stale');
    expect(() => verifyDifferentialArtifacts(root, manifestSource, `${registrySource}\n`))
      .toThrow('Lean operation registry is stale');
    const wrongDomain = JSON.parse(suiteSource);
    wrongDomain.registry.find((operation: { id: string }) => operation.id === 'parse').domain = 'graph';
    expect(() => buildDifferentialSuite(JSON.stringify(wrongDomain))).toThrow('incorrect fixture domain');
    for (const [field, value, message] of [
      ['domain', 'bogus', '.domain is invalid'], ['arity', 0, '.arity is invalid'],
      ['source', '', '.source is invalid'], ['id', 'Bad ID', '.id is invalid'],
    ]) {
      const malformed = JSON.parse(suiteSource);
      malformed.registry[0][field] = value;
      expect(() => buildDifferentialSuite(JSON.stringify(malformed))).toThrow(message);
    }
    const extraRegistryField = JSON.parse(suiteSource);
    extraRegistryField.registry[0].extra = true;
    expect(() => buildDifferentialSuite(JSON.stringify(extraRegistryField))).toThrow('must contain exactly');
  });

  it('anchors the 97-entry legacy abstract inventory to be709a4', () => {
    const output = execFileSync('bun', ['scripts/check-differential-inventory.mjs'], {
      cwd: root, encoding: 'utf8',
    });
    expect(output.trim()).toBe('Legacy abstract inventory is current: 97 entries');
  });

  it('rejects duplicate scenario IDs before expansion can overwrite counts', () => {
    const duplicated = JSON.parse(suiteSource);
    const duplicate = structuredClone(duplicated.scenarios[0]);
    duplicate.expectedCount = 1;
    duplicated.scenarios.push(duplicate);
    expect(() => buildDifferentialSuite(JSON.stringify(duplicated))).toThrow('scenario IDs must be unique');
  });

  it('renders identical artifacts under varied locale environments', () => {
    const childSource = `
      import { createHash } from 'node:crypto';
      import { readFileSync } from 'node:fs';
      import { loadCombinedDifferential, renderDifferentialManifest } from './scripts/differential-manifest-lib.mjs';
      const output = renderDifferentialManifest(loadCombinedDifferential(process.cwd()).manifest);
      process.stdout.write(createHash('sha256').update(output).digest('hex'));
    `;
    const hashes = ['C', 'en_US.UTF-8', 'tr_TR.UTF-8'].map((locale) =>
      execFileSync(process.execPath, ['--input-type=module', '-e', childSource], {
        cwd: root,
        encoding: 'utf8',
        env: { ...process.env, LANG: locale, LC_ALL: locale },
      }),
    );
    expect(new Set(hashes).size).toBe(1);
  });

  it('rejects invalid fixture encodings before materialization', () => {
    const valid = [
      { kind: 'number', bits: '0' },
      { kind: 'number', bits: '18446744073709551615' },
      { kind: 'bigint', decimal: '0' },
      { kind: 'bigint', decimal: '1' },
      { kind: 'bigint', decimal: '-1' },
    ];
    valid.forEach(validateFixture);
    const invalid: Fixture[] = [
      { kind: 'number', bits: '' },
      { kind: 'number', bits: '00' },
      { kind: 'number', bits: '-1' },
      { kind: 'number', bits: '18446744073709551616' },
      { kind: 'bigint', decimal: '-0' },
      { kind: 'bigint', decimal: '+1' },
      { kind: 'bigint', decimal: '01' },
      { kind: 'bigint', decimal: '-01' },
    ];
    invalid.forEach((fixture) => {
      expect(() => validateFixture(fixture)).toThrow();
      expect(() => materializeFixtures([fixture], new Canonicalizer())).toThrow();
    });

    const tampered = JSON.parse(suiteSource);
    tampered.scenarios.find((scenario: { id: string }) => scenario.id === 'format').vectors[0].fixtures[0].bits =
      '18446744073709551616';
    const rangeSchema: JsonValue = JSON.parse(readFileSync(resolve(root, 'spec/differential/schema.json'), 'utf8'));
    const lexicalDocument: JsonValue = JSON.parse(JSON.stringify(tampered));
    const lexicalErrors: string[] = [];
    validateJsonSchema(lexicalDocument, rangeSchema, rangeSchema, 'primitive', lexicalErrors);
    expect(lexicalErrors).toEqual([]);
    expect(() => buildDifferentialSuite(JSON.stringify(tampered))).toThrow('number bits exceed UInt64');
    tampered.scenarios.find((scenario: { id: string }) => scenario.id === 'format').vectors[0].fixtures[0].bits = '0';
    tampered.scenarios.find((scenario: { id: string }) => scenario.id === 'curated-operators').vectors[0].operation = 'format';
    expect(() => buildDifferentialSuite(JSON.stringify(tampered))).toThrow('outside scenario');

    const graphSuite = JSON.parse(abstractSuiteSource);
    expect(() => buildDifferentialSuite(JSON.stringify(graphSuite))).not.toThrow();
    const accessorGraph = structuredClone(graphSuite);
    accessorGraph.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle')
      .nodes.find((node: { id: string }) => node.id === 'root')
      .properties.find((property: { descriptor: { kind: string } }) => property.descriptor.kind === 'accessor')
      .descriptor.get = 'root';
    expect(() => buildDifferentialSuite(JSON.stringify(accessorGraph))).toThrow('is not a function');
    const prototypeGraph = structuredClone(graphSuite);
    const cycle = prototypeGraph.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle');
    cycle.nodes.find((node: { id: string }) => node.id === 'root').prototype = 'array';
    expect(() => buildDifferentialSuite(JSON.stringify(prototypeGraph))).toThrow('prototype cycle');
    const danglingGraph = structuredClone(graphSuite);
    danglingGraph.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle')
      .nodes.find((node: { id: string }) => node.id === 'root').properties[0].descriptor.value =
        { kind: 'ref', id: 'missing' };
    expect(() => buildDifferentialSuite(JSON.stringify(danglingGraph))).toThrow('unknown node missing');

    const malformed: Array<[string, (suite: typeof graphSuite) => void]> = [
      ['unknown prototype', (value) => {
        value.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle').nodes[0].prototype = '@bogus';
      }],
      ['duplicate property key', (value) => {
        const node = value.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle').nodes[0];
        node.properties.push(structuredClone(node.properties[0]));
      }],
      ['invalid index', (value) => {
        value.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle')
          .nodes.find((node: { id: string }) => node.id === 'array').elements[0].index = 4_294_967_295;
      }],
      ['unknown receiver', (value) => {
        value.graphs.find((graph: { id: string }) => graph.id === 'pair')
          .nodes.find((node: { id: string }) => node.id === 'left-method').script.cases.push({
            receiver: 'missing', events: [], completion: { type: 'return', value: { kind: 'undefined' } },
          });
      }],
      ['argument is out of bounds', (value) => {
        value.graphs.find((graph: { id: string }) => graph.id === 'pair')
          .nodes.find((node: { id: string }) => node.id === 'left-method').script.events[0].argument = 1;
      }],
      ['references unknown node', (value) => {
        value.graphs.find((graph: { id: string }) => graph.id === 'pair').bindings.push({
          name: 'dangling', mutable: true, value: { kind: 'ref', id: 'missing' },
        });
      }],
    ];
    for (const [message, mutate] of malformed) {
      const value = structuredClone(graphSuite);
      mutate(value);
      expect(() => buildDifferentialSuite(JSON.stringify(value))).toThrow(message);
    }
    for (const format of ['object', 'array', 'function', 'symbol', 'error']) {
      const value = structuredClone(graphSuite);
      value.graphs.find((graph: { id: string }) => graph.id === 'pair')
        .nodes.find((node: { id: string }) => node.id === 'left-method').script.events[0].format = format;
      expect(() => buildDifferentialSuite(JSON.stringify(value))).toThrow('unsupported argument format');
    }
    for (const identity of ['', 'shared-key']) {
      const value = structuredClone(graphSuite);
      value.scenarios.find((scenario: { id: string }) => scenario.id === 'canonical-symbols')
        .vectors.find((vector: { id: string }) => vector.id === 'registered-key-for')
        .fixtures[0].arguments[0].identity = identity;
      expect(() => buildDifferentialSuite(JSON.stringify(value))).toThrow(
        identity === '' ? 'invalid symbol metadata' : 'registered symbol key is not namespaced',
      );
    }
    const nodeBound = structuredClone(graphSuite);
    const nodeTemplate = nodeBound.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle').nodes[0];
    nodeBound.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle').nodes =
      new Array(1_025).fill(nodeTemplate);
    expect(() => buildDifferentialSuite(JSON.stringify(nodeBound))).toThrow('exceeds graph bounds');
    const propertyBound = structuredClone(graphSuite);
    const propertyNode = propertyBound.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle').nodes[0];
    propertyNode.properties = new Array(4_097).fill(propertyNode.properties[0]);
    expect(() => buildDifferentialSuite(JSON.stringify(propertyBound))).toThrow('exceeds node bounds');
    const elementBound = structuredClone(graphSuite);
    const elementNode = elementBound.graphs.find((graph: { id: string }) => graph.id === 'canonical-cycle')
      .nodes.find((node: { kind: string }) => node.kind === 'array');
    elementNode.elements = new Array(65_537).fill(elementNode.elements[0]);
    expect(() => buildDifferentialSuite(JSON.stringify(elementBound))).toThrow('exceeds node bounds');
    expect(() => validateFixture({ kind: 'graph', nodes: [], arguments: [] })).toThrow('must contain exactly');

    const maximumString = { kind: 'string' as const, units: new Array<number>(65_536).fill(0xd800) };
    expect(() => validateFixture(maximumString)).not.toThrow();
    expect(materializeFixtures([maximumString], new Canonicalizer())[0]).toHaveLength(65_536);
    expect(() => validateFixture({ kind: 'string', units: [...maximumString.units, 0] }))
      .toThrow('UInt16 code units');
  });

  it('canonicalizes every primitive edge and both completion forms structurally', () => {
    const canonical = new Canonicalizer();
    const shared = Symbol.for('tslean-test-shared');
    const unique = Symbol('unique');
    const values = [
      [undefined, { type: 'undefined' }],
      [null, { type: 'null' }],
      [false, { type: 'boolean', value: false }],
      [-0, { type: 'number', bits: '9223372036854775808' }],
      [Number.NaN, { type: 'number', bits: '9221120237041090560' }],
      ['\ud800x\udfff', { type: 'string', units: units('\ud800x\udfff') }],
      [-12345678901234567890n, { type: 'bigint', decimal: '-12345678901234567890' }],
      [shared, { type: 'symbol', kind: 'registered', identity: 'tslean-test-shared' }],
      [Symbol.iterator, { type: 'symbol', kind: 'well-known', identity: 'iterator' }],
      [unique, { type: 'symbol', kind: 'unique', identity: 'symbol-0' }],
    ];
    for (const [value, expected] of values) expect(canonical.datum(value)).toEqual(expected);
    expect(canonical.datum(unique)).toEqual(canonical.datum(unique));
    expect(canonical.normal(undefined)).toEqual({
      completion: { type: 'normal', value: { type: 'undefined' } }, trace: [],
    });
    expect(canonical.thrown(new TypeError())).toEqual({
      completion: {
        type: 'throw',
        value: {
          type: 'error', identity: 'ref-0',
          name: { type: 'string', units: units('TypeError') }, message: { type: 'string', units: [] },
        },
      },
      trace: [],
    });
  });

  it('canonicalizes hostile errors without invoking getters', () => {
    let effects = 0;
    const error = Object.create(TypeError.prototype);
    Object.defineProperty(error, 'name', { get() { effects += 1; return 'Hostile'; } });
    Object.defineProperty(error, Symbol.toStringTag, { get() { effects += 1; return 'Hostile'; } });
    Object.defineProperty(error, 'message', { value: 'secret', enumerable: false });
    const observation = new Canonicalizer().thrown(error);
    expect(effects).toBe(0);
    expect(observation.completion.value).toEqual({
      type: 'error', identity: 'ref-0',
      name: { type: 'string', units: units('TypeError') }, message: { type: 'string', units: [] },
    });
  });

  it('canonicalizes selected cyclic graphs without invoking accessors', () => {
    const vector = manifest.vectors.find(({ id }) => id === 'canonical-graphs-cycle-alias-descriptors');
    if (vector === undefined) throw new Error('canonical graph vector is missing');
    const observation = runNodeVector(vector, registry, new Canonicalizer());
    expect(observation.trace).toEqual([]);
    expect(observation.roots?.map((root) => root.type === 'object' || root.type === 'error' ? root.identity : '')).toEqual([
      'ref-0', 'ref-0', 'ref-1', 'ref-2', 'ref-3',
    ]);
    expect(observation.objects?.map(({ kind }) => kind)).toEqual(['object', 'array', 'function', 'error']);
    const root = observation.objects?.[0];
    expect(root?.properties.map(({ key }) => key.type === 'string' ? textFromCodeUnits(key.units)
      : key.type === 'symbol' ? key.identity : '')).toEqual([
      '2', 'alpha', 'self', 'lazy', 'local-key', 'tslean-differential:registered-key', 'iterator',
    ]);
    expect(root?.properties.find(({ key }) => key.type === 'string' && textFromCodeUnits(key.units) === 'lazy')?.descriptor.kind)
      .toBe('accessor');
  });

  it('shares encounter identity across completion, roots, cycles, and intrinsic prototypes', () => {
    const identityVector = manifest.vectors.find(({ id }) => id === 'canonical-graphs-return-root-repeated-cycle');
    const intrinsicVector = manifest.vectors.find(({ id }) => id === 'canonical-graphs-intrinsic-prototypes');
    const realmIntrinsicVector = manifest.vectors.find(({ id }) => id === 'canonical-graphs-intrinsic-prototypes-realm');
    if (identityVector === undefined || intrinsicVector === undefined || realmIntrinsicVector === undefined) {
      throw new Error('canonical identity vectors are missing');
    }
    const identity = runNodeVector(identityVector, registry, new Canonicalizer());
    expect(identity.completion.value).toEqual({ type: 'object', identity: 'ref-0' });
    expect(identity.roots).toEqual([{ type: 'object', identity: 'ref-0' }, { type: 'object', identity: 'ref-0' }]);
    expect(identity.objects?.[0].properties.find(({ key }) =>
      key.type === 'string' && textFromCodeUnits(key.units) === 'self')?.descriptor).toMatchObject({
      kind: 'data', value: { type: 'object', identity: 'ref-0' },
    });

    const intrinsics = runNodeVector(intrinsicVector, registry, new Canonicalizer());
    expect(intrinsics.roots).toEqual([
      { type: 'object', identity: 'ref-0' }, { type: 'object', identity: 'ref-1' },
      { type: 'object', identity: 'ref-2' },
    ]);
    expect(intrinsics.objects?.slice(0, 3).map(({ prototype }) => prototype)).toEqual([
      { type: 'object', identity: 'ref-3' }, { type: 'object', identity: 'ref-4' },
      { type: 'object', identity: 'ref-5' },
    ]);
    expect(intrinsics.objects?.slice(3).map(({ kind }) => kind)).toEqual(['object', 'function', 'array']);
    expect(runNodeVector(realmIntrinsicVector, registry, new Canonicalizer()))
      .toEqual(intrinsics);
  });

  it('uses real registered and local symbol semantics', () => {
    const run = (id: string) => {
      const vector = manifest.vectors.find((candidate) => candidate.id === id);
      if (vector === undefined) throw new Error(`missing symbol vector ${id}`);
      return runNodeVector(vector, registry, new Canonicalizer()).completion.value;
    };
    expect(run('canonical-symbols-registered-key-for')).toEqual({
      type: 'string', units: units('tslean-differential:shared-key'),
    });
    expect(run('canonical-symbols-registered-same-key')).toEqual({ type: 'boolean', value: true });
    expect(run('canonical-symbols-local-distinct')).toEqual({ type: 'boolean', value: false });
  });

  it('enforces registered symbol keys at the Lean protocol boundary', async () => {
    const vector = manifest.vectors.find(({ id }) => id === 'canonical-symbols-registered-key-for');
    if (vector === undefined || vector.fixtures[0].kind !== 'graph') throw new Error('registered symbol vector is missing');
    const empty = structuredClone(vector.fixtures[0]);
    const shared = structuredClone(vector.fixtures[0]);
    const emptySymbol = empty.arguments[0];
    const sharedSymbol = shared.arguments[0];
    if (emptySymbol.kind !== 'symbol' || sharedSymbol.kind !== 'symbol') throw new Error('registered symbol fixture changed');
    emptySymbol.identity = '';
    sharedSymbol.identity = 'shared-key';
    const oracle = new LeanOracle(root);
    const responses = await oracle.exchangeLines([
      JSON.stringify({ id: 'valid-registered', operation: vector.operation, fixtures: vector.fixtures }),
      JSON.stringify({ id: 'empty-registered', operation: vector.operation, fixtures: [empty] }),
      JSON.stringify({ id: 'unnamespaced-registered', operation: vector.operation, fixtures: [shared] }),
    ]);
    expect(responses[0]).toMatchObject({
      status: 'ok', observation: { completion: { value: { type: 'string', units: units('tslean-differential:shared-key') } } },
    });
    expect(responses.slice(1).every((response) =>
      response.status === 'protocol-error' && response.error.code === 'invalid-fixture')).toBe(true);
    await oracle.close();
  });

  it('preserves error, object, and primitive throw identity', () => {
    const run = (id: string) => {
      const vector = manifest.vectors.find((candidate) => candidate.id === id);
      if (vector === undefined) throw new Error(`missing throw vector ${id}`);
      return runNodeVector(vector, registry, new Canonicalizer());
    };
    const error = run('canonical-graphs-throw-error-root');
    expect(error.completion.value).toEqual({
      type: 'error', identity: 'ref-0',
      name: { type: 'string', units: units('Error') }, message: { type: 'string', units: units('selected') },
    });
    expect(error.roots?.[0]).toEqual(error.completion.value);
    expect(error.objects?.[0]).toMatchObject({ identity: 'ref-0', kind: 'error' });
    const object = run('canonical-graphs-throw-object-root');
    expect(object.completion.value).toEqual({ type: 'object', identity: 'ref-0' });
    expect(object.roots?.[0]).toEqual(object.completion.value);
    expect(run('canonical-graphs-throw-string').completion.value).toEqual({
      type: 'string', units: units('arbitrary'),
    });
  });

  it('preserves UTF-16 units in graph keys, errors, events, and prefixes', () => {
    const vector = manifest.vectors.find(({ id }) => id === 'canonical-utf16-surrogate-fields');
    if (vector === undefined) throw new Error('UTF-16 graph vector is missing');
    const observation = runNodeVector(vector, registry, new Canonicalizer());
    expect(observation.trace.map(({ detail }) => detail.type === 'string' ? detail.units : [])).toEqual([
      [0xd800], [0xdfff, 0xd800],
    ]);
    expect(observation.objects?.[0].properties.map(({ key }) => key.type === 'string' ? key.units : [])).toEqual([
      [0xd800], [0xdfff],
    ]);
    expect(observation.roots?.[1]).toMatchObject({
      type: 'error', name: { units: units('Error') }, message: { units: [0xd800, 0xdfff] },
    });
  });

  it('formats only declared primitive script argument categories', () => {
    const expected = new Map<string, number[]>([
      ['string', [0xd800]], ['number', units('1')], ['boolean', units('true')],
      ['bigint', units('-2')], ['null', units('null')], ['undefined', units('undefined')],
    ]);
    for (const [format, units_] of expected) {
      const vector = manifest.vectors.find(({ id }) => id === `canonical-script-formats-${format}`);
      if (vector === undefined) throw new Error(`missing script format vector ${format}`);
      const observation = runNodeVector(vector, registry, new Canonicalizer());
      expect(observation.trace[0]?.detail).toEqual({ type: 'string', units: units_ });
    }
  });

  it('uses the effectful condition callback Boolean result', () => {
    const run = (id: string) => {
      const vector = manifest.vectors.find((candidate) => candidate.id === id);
      if (vector === undefined) throw new Error(`missing effectful condition vector ${id}`);
      return runNodeVector(vector, registry, new Canonicalizer());
    };
    const truthy = run('corpus-model-probes-operators-effectful-compound-condition');
    const falsy = run('corpus-model-probes-operators-effectful-compound-condition-false');
    expect(truthy.completion.value).toEqual({ type: 'number', bits: '4607182418800017408' });
    expect(falsy.completion.value).toEqual({ type: 'number', bits: '0' });
    expect(truthy.trace).toEqual(falsy.trace);
  });

  it('returns one correlated response for malformed, unknown, and multiple NDJSON requests', async () => {
    const oracle = new LeanOracle(root);
    const validVector = manifest.vectors.find(({ operation }) => operation === 'parse');
    if (validVector === undefined) throw new Error('manifest has no parse vector');
    const valid = request(validVector);
    const responses = await oracle.exchangeLines([
      '{',
      JSON.stringify({ id: 'unknown', operation: 'not-registered', fixtures: [] }),
      JSON.stringify({ ...valid, extra: true }),
      JSON.stringify(valid),
      JSON.stringify({ ...valid, id: 'second' }),
    ]);
    expect(responses).toHaveLength(5);
    expect(responses.map(({ id }) => id)).toEqual([null, 'unknown', valid.id, valid.id, 'second']);
    expect(responses.slice(0, 3).map((response) => response.status === 'protocol-error' ? response.error.code : '')).toEqual([
      'malformed-json', 'unknown-operation', 'invalid-request',
    ]);
    expect(responses.slice(3).every(({ status }) => status === 'ok')).toBe(true);
    await oracle.close();
  });

  it('rejects noncanonical fixture encodings at the Lean protocol boundary', async () => {
    const oracle = new LeanOracle(root);
    const requests = [
      { id: 'number-leading-zero', operation: 'format', fixtures: [{ kind: 'number', bits: '00' }] },
      { id: 'number-overflow', operation: 'format', fixtures: [{ kind: 'number', bits: '18446744073709551616' }] },
      { id: 'bigint-negative-zero', operation: 'number', fixtures: [{ kind: 'bigint', decimal: '-0' }] },
      { id: 'bigint-leading-zero', operation: 'number', fixtures: [{ kind: 'bigint', decimal: '01' }] },
    ];
    const responses = await oracle.exchangeLines(requests.map((value) => JSON.stringify(value)));
    expect(responses.every((response) => response.status === 'protocol-error' && response.error.code === 'invalid-fixture')).toBe(true);
    await oracle.close();
  });

  it('enforces the shared UTF-16 boundary at the Lean protocol', async () => {
    const oracle = new LeanOracle(root);
    const boundary = new Array<number>(65_536).fill(0xd800);
    const responses = await oracle.exchangeLines([
      JSON.stringify({ id: 'utf16-boundary', operation: 'parse', fixtures: [{ kind: 'string', units: boundary }] }),
      JSON.stringify({ id: 'utf16-overflow', operation: 'parse', fixtures: [{ kind: 'string', units: [...boundary, 0] }] }),
    ]);
    expect(responses[0].status).toBe('ok');
    expect(responses[1].status === 'protocol-error' && responses[1].error.code === 'invalid-fixture').toBe(true);
    await oracle.close();
  });

  it('enforces the aggregate dense-array budget before materialization', async () => {
    const vector = manifest.vectors.find(({ id }) => id === 'canonical-graphs-cycle-alias-descriptors');
    if (vector === undefined || vector.fixtures[0].kind !== 'graph') throw new Error('canonical graph fixture is missing');
    const boundary = structuredClone(vector.fixtures[0]);
    const array = boundary.nodes.find(({ kind }) => kind === 'array');
    if (array === undefined) throw new Error('canonical array node is missing');
    array.elements.push({ index: 65_535, value: { kind: 'undefined' } });
    boundary.observe = [];
    const plusOne = structuredClone(boundary);
    const extraArray = structuredClone(array);
    extraArray.id = 'array-extra';
    extraArray.properties = [];
    extraArray.elements = [{ index: 0, value: { kind: 'undefined' } }];
    plusOne.nodes.push(extraArray);
    const attack = structuredClone(boundary);
    attack.nodes = Array.from({ length: 1_024 }, (_, index) => ({
      ...structuredClone(array), id: `attack-${index}`,
      prototype: '@array', properties: [], elements: [{ index: 65_535, value: { kind: 'undefined' } }],
    }));
    const indexOverflow = structuredClone(boundary);
    const overflowArray = indexOverflow.nodes.find(({ kind }) => kind === 'array');
    if (overflowArray === undefined) throw new Error('overflow array node is missing');
    overflowArray.elements[overflowArray.elements.length - 1].index = 4_294_967_294;

    const sourceBoundary = JSON.parse(abstractSuiteSource);
    const sourceGraph = sourceBoundary.graphs.find(({ id }: { id: string }) => id === 'canonical-cycle');
    const sourceArray = sourceGraph.nodes.find(({ kind }: { kind: string }) => kind === 'array');
    sourceArray.elements.push({ index: 65_535, value: { kind: 'undefined' } });
    expect(() => buildDifferentialSuite(JSON.stringify(sourceBoundary))).not.toThrow();
    const sourcePlusOne = structuredClone(sourceBoundary);
    const sourceExtra = structuredClone(sourceArray);
    sourceExtra.id = 'array-extra';
    sourceExtra.properties = [];
    sourceExtra.elements = [{ index: 0, value: { kind: 'undefined' } }];
    sourcePlusOne.graphs.find(({ id }: { id: string }) => id === 'canonical-cycle').nodes.push(sourceExtra);
    expect(() => buildDifferentialSuite(JSON.stringify(sourcePlusOne))).toThrow('dense-array materialization budget');
    const sourceAttack = structuredClone(sourceBoundary);
    sourceAttack.graphs.find(({ id }: { id: string }) => id === 'canonical-cycle').nodes =
      Array.from({ length: 1_024 }, (_, index) => ({
        ...structuredClone(sourceArray), id: `attack-${index}`,
        prototype: '@array', properties: [], elements: [{ index: 65_535, value: { kind: 'undefined' } }],
      }));
    expect(() => buildDifferentialSuite(JSON.stringify(sourceAttack))).toThrow('dense-array materialization budget');

    const oracle = new LeanOracle(root);
    const responses = await oracle.exchangeLines([
      JSON.stringify({ id: 'array-index-boundary', operation: vector.operation, fixtures: [boundary] }),
      JSON.stringify({ id: 'array-budget-plus-one', operation: vector.operation, fixtures: [plusOne] }),
      JSON.stringify({ id: 'array-budget-attack', operation: vector.operation, fixtures: [attack] }),
      JSON.stringify({ id: 'array-index-overflow', operation: vector.operation, fixtures: [indexOverflow] }),
    ]);
    expect(responses[0].status).toBe('ok');
    expect(responses.slice(1).every((response) =>
      response.status === 'protocol-error' && response.error.code === 'invalid-fixture')).toBe(true);
    for (const response of responses.slice(1, 3)) {
      expect(response.status === 'protocol-error' && response.error.message).toContain('dense-array materialization budget');
    }
    await oracle.close();
  });

  it('rejects registry-valid operations with the wrong fixture domain', async () => {
    const graphVector = manifest.vectors.find(({ id }) => id === 'canonical-graphs-cycle-alias-descriptors');
    if (graphVector === undefined) throw new Error('canonical graph vector is missing');
    const oracle = new LeanOracle(root);
    const responses = await oracle.exchangeLines([
      JSON.stringify({ id: 'primitive-with-graph', operation: 'parse', fixtures: graphVector.fixtures }),
      JSON.stringify({ id: 'graph-with-primitive', operation: 'value-strict', fixtures: [{ kind: 'undefined' }] }),
    ]);
    expect(responses.every((response) => response.status === 'protocol-error' && response.error.code === 'invalid-domain'))
      .toBe(true);
    await oracle.close();
  });

  it('rejects malformed expanded graphs at the Lean boundary', async () => {
    const vector = manifest.vectors.find(({ id }) => id === 'abstract-coercion-operators-add-pair');
    if (vector === undefined || vector.fixtures[0].kind !== 'graph') throw new Error('graph fixture is missing');
    const malformed: Array<[string, (fixture: GraphFixture) => void]> = [
      ['missing-case-receiver', (fixture) => {
        if (fixture.kind !== 'graph') return;
        fixture.nodes.find(({ kind }) => kind === 'function')?.script.cases.push({
          receiver: 'missing', events: [], completion: { type: 'return', value: { kind: 'undefined' } },
        });
      }],
      ['unknown-prototype', (fixture) => { if (fixture.kind === 'graph') fixture.nodes[0].prototype = '@bogus'; }],
      ['duplicate-node', (fixture) => { if (fixture.kind === 'graph') fixture.nodes.push(structuredClone(fixture.nodes[0])); }],
      ['duplicate-property', (fixture) => {
        if (fixture.kind === 'graph') fixture.nodes[0].properties.push(structuredClone(fixture.nodes[0].properties[0]));
      }],
      ['invalid-index', (fixture) => {
        if (fixture.kind !== 'graph') return;
        const array = fixture.nodes.find(({ kind }) => kind === 'array');
        if (array !== undefined) array.elements.push({ index: 65_536, value: { kind: 'undefined' } });
        else fixture.nodes[0].kind = 'array', fixture.nodes[0].elements.push({ index: 65_536, value: { kind: 'undefined' } });
      }],
      ['argument-bound', (fixture) => {
        if (fixture.kind !== 'graph') return;
        const event = fixture.nodes.find(({ kind }) => kind === 'function')?.script.events.find(({ kind }) => kind === 'argument');
        if (event?.kind === 'argument') event.argument = 99;
      }],
      ['unsupported-format', (fixture) => {
        if (fixture.kind !== 'graph') return;
        const event = fixture.nodes.find(({ kind }) => kind === 'function')?.script.events.find(({ kind }) => kind === 'argument');
        if (event?.kind === 'argument') Object.assign(event, { format: 'object' });
      }],
      ['dangling-binding', (fixture) => {
        if (fixture.kind === 'graph') fixture.bindings.push({
          name: 'dangling', mutable: true, value: { kind: 'ref', id: 'missing' },
        });
      }],
      ['extra-field', (fixture) => { Object.assign(fixture, { extra: true }); }],
    ];
    const oracle = new LeanOracle(root);
    const requests = malformed.map(([id, mutate]) => {
      const fixture = structuredClone(vector.fixtures[0]);
      if (fixture.kind !== 'graph') throw new Error('graph fixture changed domain');
      mutate(fixture);
      return JSON.stringify({ id, operation: vector.operation, fixtures: [fixture] });
    });
    const rangeVector = manifest.vectors.find(({ id }) => id === 'abstract-coercion-operators-throw-range-error');
    if (rangeVector === undefined || rangeVector.fixtures[0].kind !== 'graph') throw new Error('range fixture is missing');
    const invalidError = structuredClone(rangeVector.fixtures[0]);
    const errorCompletion = invalidError.nodes.find(({ kind }) => kind === 'function')?.script.completion.value;
    if (errorCompletion?.kind === 'error') errorCompletion.name = [0xd800];
    const invalidSymbol = structuredClone(vector.fixtures[0]);
    if (invalidSymbol.kind === 'graph') {
      const symbolKey = invalidSymbol.nodes.flatMap(({ properties }) => properties)
        .map(({ key }) => key).find(({ kind }) => kind === 'symbol');
      if (symbolKey?.kind === 'symbol') Object.assign(symbolKey, { symbolKind: 'bogus' });
    }
    const responses = await oracle.exchangeLines([...requests,
      JSON.stringify({ id: 'incomplete-graph', operation: vector.operation, fixtures: [{ kind: 'graph' }] }),
      JSON.stringify({ id: 'invalid-error-name', operation: rangeVector.operation, fixtures: [invalidError] }),
      JSON.stringify({ id: 'invalid-symbol-kind', operation: vector.operation, fixtures: [invalidSymbol] }),
    ]);
    expect(responses.every((response) => response.status === 'protocol-error' && response.error.code === 'invalid-fixture'))
      .toBe(true);
    await oracle.close();
  });

  it('is deterministic across persistent, restarted, and fresh oracle processes', async () => {
    const requests = manifest.vectors.slice(0, 32).map(request);
    const persistent = new LeanOracle(root);
    const first = await persistent.requestBatch(requests);
    const second = await persistent.requestBatch(requests);
    await persistent.restart();
    const restarted = await persistent.requestBatch(requests);
    await persistent.close();
    const fresh = new LeanOracle(root);
    const freshResult = await fresh.requestBatch(requests);
    await fresh.close();
    expect(second).toEqual(first);
    expect(restarted).toEqual(first);
    expect(freshResult).toEqual(first);
  });

  it('rejects missing executables and request timeouts', async () => {
    const missing = new LeanOracle(root, { executable: resolve(root, 'missing-js-model-oracle'), requestTimeoutMs: 50 });
    await expect(missing.exchangeLines(['{}'])).rejects.toThrow('oracle process error');

    const hanging = new LeanOracle(root, {
      spawnChild: fakeOracle('setInterval(() => {}, 1000);'),
      requestTimeoutMs: 20,
    });
    await expect(hanging.exchangeLines(['{}'])).rejects.toThrow('oracle batch timed out after 20ms');

    const exited = new LeanOracle(root, {
      spawnChild: fakeOracle(`process.stdin.once('data', () => process.exit(0));`),
      requestTimeoutMs: 1_000,
    });
    await expect(exited.exchangeLines(['{}'])).rejects.toThrow(/stdout closed unexpectedly|exited unexpectedly/);
  });

  it('treats malformed and excess stdout as fatal and restarts fresh', async () => {
    let starts = 0;
    const oracle = new LeanOracle(root, {
      spawnChild: () => {
        starts += 1;
        return fakeOracle(starts === 1 ? `process.stdin.once('data', () => process.stdout.write('not-json\\n'));` : fakeResponseSource)();
      },
      requestTimeoutMs: 1_000,
    });
    await expect(oracle.exchangeLines(['{}'])).rejects.toThrow('invalid JSON');
    await expect(oracle.requestBatch([{ id: 'fresh', operation: 'parse', fixtures: [] }])).resolves.toHaveLength(1);
    expect(starts).toBe(2);
    await oracle.close();

    const validLine = JSON.stringify({
      id: 'one', status: 'ok',
      observation: { completion: { type: 'normal', value: { type: 'undefined' } }, trace: [] },
    });
    const excess = new LeanOracle(root, {
      spawnChild: fakeOracle(`process.stdin.once('data', () => process.stdout.write(${JSON.stringify(`${validLine}\n{}\n`)}));`),
      requestTimeoutMs: 1_000,
    });
    await expect(excess.requestBatch([{ id: 'one', operation: 'parse', fixtures: [] }]))
      .rejects.toThrow(/unsolicited|invalid response/);

    const wrongId = new LeanOracle(root, {
      spawnChild: fakeOracle(`process.stdin.once('data', () => process.stdout.write(${JSON.stringify(
        `${validLine.replace('"one"', '"wrong"')}\n`,
      )}));`),
      requestTimeoutMs: 1_000,
    });
    await expect(wrongId.requestBatch([{ id: 'one', operation: 'parse', fixtures: [] }]))
      .rejects.toThrow('response correlation failed');
  });

  it('bounds close time and stderr while rejecting newline injection before spawn', async () => {
    let starts = 0;
    const injection = new LeanOracle(root, { spawnChild: () => { starts += 1; return fakeOracle(fakeResponseSource)(); } });
    await expect(injection.exchangeLines(['{}\n{}'])).rejects.toThrow('must not contain CR or LF');
    await expect(injection.exchangeLines(['{}\r{}'])).rejects.toThrow('must not contain CR or LF');
    expect(starts).toBe(0);

    const closeTimeout = new LeanOracle(root, {
      spawnChild: fakeOracle(`${fakeResponseSource}\nsetInterval(() => {}, 1000);`),
      closeTimeoutMs: 20,
      requestTimeoutMs: 1_000,
    });
    await closeTimeout.requestBatch([{ id: 'close', operation: 'parse', fixtures: [] }]);
    await expect(closeTimeout.close()).rejects.toThrow('oracle close timed out after 20ms');

    const stderr = new LeanOracle(root, {
      spawnChild: fakeOracle(`process.stderr.write('x'.repeat(1000));\n${fakeResponseSource}`),
      stderrLimit: 32,
      requestTimeoutMs: 1_000,
    });
    await stderr.requestBatch([{ id: 'stderr', operation: 'parse', fixtures: [] }]);
    await expect(stderr.close()).rejects.toThrow('oracle stderr truncated');
  });

  it('detects a synthetic observation mismatch', () => {
    const observation: Observation = {
      completion: { type: 'normal', value: { type: 'boolean', value: true } }, trace: [],
    };
    const changed: Observation = {
      completion: { type: 'normal', value: { type: 'boolean', value: false } }, trace: [],
    };
    expect(observationMismatch('synthetic', observation, observation)).toBeUndefined();
    expect(observationMismatch('synthetic', observation, changed)).toContain('synthetic');
  });

  it('matches Node and Lean for all 7,264 model vectors', async () => {
    const oracle = new LeanOracle(root);
    const responses = await oracle.requestBatch(manifest.vectors.map(request));
    await oracle.close();
    const mismatches: string[] = [];
    responses.forEach((response, index) => {
      const vector = manifest.vectors[index];
      if (response.status !== 'ok') {
        mismatches.push(`${vector.id}: protocol error ${response.error.code}: ${response.error.message}`);
        return;
      }
      const node = runNodeVector(vector, registry, new Canonicalizer());
      const mismatch = observationMismatch(vector.id, node, response.observation);
      if (mismatch !== undefined) mismatches.push(mismatch);
    });
    expect(responses).toHaveLength(7_264);
    expect(mismatches).toEqual([]);
  }, 120_000);

});
