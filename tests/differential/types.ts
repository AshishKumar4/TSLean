export type Fixture =
  | { kind: 'undefined' }
  | { kind: 'null' }
  | { kind: 'boolean'; value: boolean }
  | { kind: 'number'; bits: string }
  | { kind: 'string'; units: number[] }
  | { kind: 'bigint'; decimal: string }
  | { kind: 'symbol'; identity: string }
  | GraphFixture;

export type ModelValue =
  | Exclude<Fixture, GraphFixture | { kind: 'symbol'; identity: string }>
  | { kind: 'symbol'; symbolKind: 'local' | 'registered' | 'well-known'; identity: string }
  | { kind: 'error'; name: number[]; message: number[] }
  | { kind: 'ref'; id: string };

export type GraphFixture = {
  kind: 'graph';
  graphId: string;
  realm: boolean;
  nodes: GraphNode[];
  bindings: Array<{ name: string; mutable: boolean; value: ModelValue }>;
  arguments: ModelValue[];
  observe: ModelValue[];
};

export type GraphNode = {
  id: string;
  kind: 'object' | 'function' | 'array' | 'error';
  prototype: string;
  properties: Array<{
    key:
      | { kind: 'string'; units: number[] }
      | { kind: 'symbol'; symbolKind: 'local' | 'registered' | 'well-known'; identity: string };
    descriptor:
      | { kind: 'data'; value: ModelValue; writable: boolean; enumerable: boolean; configurable: boolean }
      | { kind: 'accessor'; get: string; set: string; enumerable: boolean; configurable: boolean };
  }>;
  elements: Array<{ index: number; value: ModelValue }>;
  script: GraphScript;
};

export type GraphScript = {
  events: Array<
    | { kind: 'fixed'; units: number[] }
    | {
        kind: 'argument'; prefixUnits: number[]; argument: number;
        format: 'string' | 'number' | 'boolean' | 'bigint' | 'null' | 'undefined';
      }
  >;
  completion: { type: 'return' | 'throw'; value: ModelValue };
  cases: Array<{
    receiver: string;
    events: GraphScript['events'];
    completion: GraphScript['completion'];
  }>;
};

export type Replay = { algorithm: string; seed: string; index: number };

export type DifferentialVector = {
  id: string;
  scenario: string;
  operation: string;
  source: string;
  fixtures: Fixture[];
  tags: string[];
  corpusIds: string[];
  replay?: Replay;
  inputHash: string;
};

export type CanonicalDatum =
  | { type: 'undefined' }
  | { type: 'null' }
  | { type: 'boolean'; value: boolean }
  | { type: 'number'; bits: string }
  | { type: 'string'; units: number[] }
  | { type: 'bigint'; decimal: string }
  | { type: 'symbol'; kind: 'registered' | 'well-known' | 'unique'; identity: string }
  | {
      type: 'error';
      identity: string;
      name: { type: 'string'; units: number[] };
      message: { type: 'string'; units: number[] };
    }
  | { type: 'object'; identity: string };

export type Observation = {
  completion:
    | { type: 'normal'; value: CanonicalDatum }
    | { type: 'throw'; value: CanonicalDatum };
  trace: Array<{ event: string; detail: CanonicalDatum }>;
  roots?: CanonicalDatum[];
  objects?: Array<{
    identity: string;
    kind: 'object' | 'function' | 'array' | 'error';
    prototype: CanonicalDatum;
    extensible: boolean;
    properties: Array<{
      key: CanonicalDatum;
      descriptor:
        | { kind: 'data'; value: CanonicalDatum; writable: boolean; enumerable: boolean; configurable: boolean }
        | { kind: 'accessor'; get: CanonicalDatum; set: CanonicalDatum; enumerable: boolean; configurable: boolean };
    }>;
  }>;
};

export type OracleRequest = {
  id: string;
  operation: string;
  fixtures: Fixture[];
};

export type OracleResponse =
  | { id: string | null; status: 'ok'; observation: Observation }
  | { id: string | null; status: 'protocol-error'; error: { code: string; message: string } };

export type DifferentialManifest = {
  schemaVersion: 2;
  suite: string;
  schemaHash: string;
  sourceHash: string;
  sourceHashes: Record<string, string>;
  corpusCoverageHash: string;
  legacyInventoryHash: string;
  legacyInventoryCount: number;
  classificationCounts: Record<string, number>;
  operationRegistry: Array<{ id: string; domain: 'primitive' | 'graph'; arity: 1 | 2; sourceHash: string }>;
  bounds: { aggregateDenseArrayCells: number };
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
