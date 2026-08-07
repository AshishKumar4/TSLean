export type DifferentialSuite = {
  registry: Array<{ id: string; domain: 'primitive' | 'graph'; arity: 1 | 2; source: string }>;
  scenarios: Array<{ id: string; operations: string[]; expectedCount: number }>;
};

export type DifferentialSummary = {
  schemaVersion: 2;
  suite: string;
  sourceHash: string;
  operationRegistry: Array<{ id: string; domain: 'primitive' | 'graph'; arity: 1 | 2; sourceHash: string }>;
  scenarioCount: number;
  fixedCount: number;
  generatedCount: number;
  vectorCount: number;
  comparisonCount: number;
  totalCount: number;
  uniqueOperationInputCount: number;
  parityDuplicateCount: number;
  duplicatePolicy: 'preserved-for-v1-parity';
  scenarioCounts: Record<string, number>;
  operationCounts: Record<string, number>;
  regressionTagCounts: Record<string, number>;
  scenarios: Array<{ id: string; vectorCount: number; vectorHash: string }>;
  generators: Array<{ scenario: string; algorithm: string; version: number; seed: string; count: number }>;
  vectorStreamHash: string;
};

export type DifferentialSuiteArtifacts = {
  suite: DifferentialSuite;
  vectors: DifferentialVector[];
  manifest: DifferentialSummary;
};

export type DifferentialArtifacts = {
  suite: { registry: DifferentialSuite['registry'] };
  vectors: DifferentialVector[];
  manifest: DifferentialSummary & {
    schemaHash: string;
    sourceHashes: Record<string, string>;
    corpusCoverageHash: string;
    legacyInventoryHash: string;
    legacyInventoryCount: number;
    classificationCounts: Record<string, number>;
    bounds: { aggregateDenseArrayCells: number };
  };
  artifacts: Array<[string, DifferentialSuiteArtifacts]>;
};

export type DifferentialVector = {
  id: string;
  scenario: string;
  operation: string;
  source: string;
  fixtures: Array<
    | { kind: 'undefined' }
    | { kind: 'null' }
    | { kind: 'boolean'; value: boolean }
    | { kind: 'number'; bits: string }
    | { kind: 'string'; units: number[] }
    | { kind: 'bigint'; decimal: string }
    | { kind: 'symbol'; identity: string }
    | GraphFixture
  >;
  tags: string[];
  corpusIds: string[];
  replay?: { algorithm: string; seed: string; index: number };
  inputHash: string;
};

export type GraphValue =
  | { kind: 'undefined' }
  | { kind: 'null' }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'number'; bits: string }
  | { kind: 'string'; units: number[] }
  | { kind: 'bigint'; decimal: string }
  | { kind: 'symbol'; symbolKind: 'local' | 'registered' | 'well-known'; identity: string }
  | { kind: 'error'; name: number[]; message: number[] }
  | { kind: 'ref'; id: string };

export type GraphScript = {
  events: Array<
    | { kind: 'fixed'; units: number[] }
    | {
        kind: 'argument'; prefixUnits: number[]; argument: number;
        format: 'string' | 'number' | 'boolean' | 'bigint' | 'null' | 'undefined';
      }
  >;
  completion: { type: 'return' | 'throw'; value: GraphValue };
  cases: Array<{ receiver: string; events: GraphScript['events']; completion: GraphScript['completion'] }>;
};

export type GraphFixture = {
  kind: 'graph';
  graphId: string;
  realm: boolean;
  nodes: Array<{
    id: string;
    kind: 'object' | 'function' | 'array' | 'error';
    prototype: string;
    properties: Array<{
      key: { kind: 'string'; units: number[] } | { kind: 'symbol'; symbolKind: 'local' | 'registered' | 'well-known'; identity: string };
      descriptor:
        | { kind: 'data'; value: GraphValue; writable: boolean; enumerable: boolean; configurable: boolean }
        | { kind: 'accessor'; get: string; set: string; enumerable: boolean; configurable: boolean };
    }>;
    elements: Array<{ index: number; value: GraphValue }>;
    script: GraphScript;
  }>;
  bindings: Array<{ name: string; mutable: boolean; value: GraphValue }>;
  arguments: GraphValue[];
  observe: GraphValue[];
};

export function validateFixture(fixture: object): void;
export function compareCodeUnits(left: string, right: string): number;
export function buildDifferentialSuite(source: string): DifferentialSuiteArtifacts;
export function loadDifferentialSuite(root: string, suiteName?: string): DifferentialSuiteArtifacts;
export function loadCombinedDifferential(root: string, suiteNames?: string[]): DifferentialArtifacts;
export function renderLeanRegistry(suite: DifferentialSuite): string;
export function renderDifferentialManifest(manifest: object): string;
export function verifyDifferentialArtifacts(root: string, manifestSource: string, registrySource: string): DifferentialArtifacts;
