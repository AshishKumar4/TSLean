import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const operations = ['add', 'sub', 'mul', 'div', 'rem', 'lt', 'le', 'gt', 'ge'];
const operatorStrings = ['', '0', '-1', '1.5', '0x10', '9007199254740993', 'not-a-number', '\ud800'];
const maximumUInt64 = 18446744073709551615n;
const canonicalUnsignedDecimal = /^(?:0|[1-9][0-9]*)$/;
const canonicalBigIntDecimal = /^(?:0|-?[1-9][0-9]*)$/;
const maximumStringCodeUnits = 65_536;
const maximumArrayIndex = 65_535;
const maximumGraphNodes = 1_024;
const maximumNodeProperties = 4_096;
const maximumNodeElements = 65_536;
const maximumBindings = 1_024;
const maximumScriptEvents = 1_024;
const maximumScriptCases = 1_024;
const maximumGraphRoots = 1_024;
const maximumDenseArrayCells = 65_536;
const intrinsicNames = new Set(['@null', '@object', '@function', '@array']);
const wellKnownSymbolNames = new Set([
  'asyncDispose',
  'asyncIterator',
  'dispose',
  'hasInstance',
  'isConcatSpreadable',
  'iterator',
  'match',
  'matchAll',
  'replace',
  'search',
  'species',
  'split',
  'toPrimitive',
  'toStringTag',
  'unscopables',
]);
const errorNameUnits = new Set([
  '69,114,114,111,114',
  '84,121,112,101,69,114,114,111,114',
  '82,97,110,103,101,69,114,114,111,114',
  '82,101,102,101,114,101,110,99,101,69,114,114,111,114',
  '83,121,110,116,97,120,69,114,114,111,114',
]);

function exactKeys(value, expected, label) {
  const actual = Object.keys(value).sort(compareCodeUnits);
  const wanted = [...expected].sort(compareCodeUnits);
  if (JSON.stringify(actual) !== JSON.stringify(wanted)) {
    throw new Error(`${label} must contain exactly: ${wanted.join(', ')}`);
  }
}

function validateCodeUnits(units, label) {
  if (
    !Array.isArray(units) ||
    units.length > maximumStringCodeUnits ||
    units.some((unit) => !Number.isInteger(unit) || unit < 0 || unit > 65_535)
  ) {
    throw new Error(`${label} must contain at most ${maximumStringCodeUnits} UTF-16 code units`);
  }
}

function validateModelValue(value, refs, label) {
  if (value === null || typeof value !== 'object' || Array.isArray(value))
    throw new Error(`${label} must be an object`);
  if (value.kind === 'undefined' || value.kind === 'null') {
    exactKeys(value, ['kind'], label);
    return;
  }
  if (value.kind === 'boolean') {
    exactKeys(value, ['kind', 'value'], label);
    if (typeof value.value !== 'boolean') throw new Error(`${label}.value must be boolean`);
    return;
  }
  if (value.kind === 'number') {
    exactKeys(value, ['kind', 'bits'], label);
    validateFixture(value);
    return;
  }
  if (value.kind === 'string') {
    exactKeys(value, ['kind', 'units'], label);
    validateCodeUnits(value.units, `${label}.units`);
    return;
  }
  if (value.kind === 'bigint') {
    exactKeys(value, ['kind', 'decimal'], label);
    validateFixture(value);
    return;
  }
  if (value.kind === 'symbol') {
    exactKeys(value, ['kind', 'symbolKind', 'identity'], label);
    if (
      !['local', 'registered', 'well-known'].includes(value.symbolKind) ||
      typeof value.identity !== 'string' ||
      value.identity.length === 0
    ) {
      throw new Error(`${label} has invalid symbol metadata`);
    }
    if (value.symbolKind === 'well-known' && !wellKnownSymbolNames.has(value.identity)) {
      throw new Error(`${label} names an unknown well-known symbol`);
    }
    if (value.symbolKind === 'registered' && !value.identity.startsWith('tslean-differential:')) {
      throw new Error(`${label} registered symbol key is not namespaced`);
    }
    return;
  }
  if (value.kind === 'error') {
    exactKeys(value, ['kind', 'name', 'message'], label);
    validateCodeUnits(value.name, `${label}.name`);
    validateCodeUnits(value.message, `${label}.message`);
    if (!errorNameUnits.has(value.name.join(','))) throw new Error(`${label} has invalid error metadata`);
    return;
  }
  if (value.kind === 'ref') {
    exactKeys(value, ['kind', 'id'], label);
    if (!refs.has(value.id)) throw new Error(`${label} references unknown node ${value.id}`);
    return;
  }
  throw new Error(`${label} has unknown value kind ${String(value.kind)}`);
}

function propertyKeyIdentity(key, label) {
  if (key.kind === 'string') {
    exactKeys(key, ['kind', 'units'], label);
    validateCodeUnits(key.units, `${label}.units`);
    return `string:${key.units.join(',')}`;
  }
  validateModelValue(key, new Set(), label);
  return `symbol:${key.symbolKind}:${key.identity}`;
}

function validateScript(script, refs, node, label) {
  exactKeys(script, ['events', 'completion', 'cases'], label);
  if (!Array.isArray(script.events) || !Array.isArray(script.cases)) throw new Error(`${label} arrays are required`);
  if (script.events.length > maximumScriptEvents || script.cases.length > maximumScriptCases) {
    throw new Error(`${label} exceeds script bounds`);
  }
  const validateEvents = (events, eventLabel) =>
    events.forEach((event, index) => {
      const current = `${eventLabel}[${index}]`;
      if (event.kind === 'fixed') {
        exactKeys(event, ['kind', 'units'], current);
        validateCodeUnits(event.units, `${current}.units`);
      } else if (event.kind === 'argument') {
        exactKeys(event, ['kind', 'prefixUnits', 'argument', 'format'], current);
        validateCodeUnits(event.prefixUnits, `${current}.prefixUnits`);
        if (!['string', 'number', 'boolean', 'bigint', 'null', 'undefined'].includes(event.format)) {
          throw new Error(`${current} has unsupported argument format`);
        }
        if (!Number.isInteger(event.argument) || event.argument < 0 || event.argument >= node.scriptArity)
          throw new Error(`${current} argument is out of bounds`);
      } else throw new Error(`${current} has unknown event kind`);
    });
  const validateCompletion = (completion, completionLabel) => {
    exactKeys(completion, ['type', 'value'], completionLabel);
    if (completion.type !== 'return' && completion.type !== 'throw')
      throw new Error(`${completionLabel}.type is invalid`);
    validateModelValue(completion.value, refs, `${completionLabel}.value`);
  };
  validateEvents(script.events, `${label}.events`);
  validateCompletion(script.completion, `${label}.completion`);
  script.cases.forEach((candidate, index) => {
    const current = `${label}.cases[${index}]`;
    exactKeys(candidate, ['receiver', 'events', 'completion'], current);
    if (!refs.has(candidate.receiver)) throw new Error(`${current} references unknown receiver ${candidate.receiver}`);
    validateEvents(candidate.events, `${current}.events`);
    validateCompletion(candidate.completion, `${current}.completion`);
  });
}

function validateGraphDefinition(graph) {
  exactKeys(graph, ['id', 'realm', 'nodes', 'bindings'], `graph ${graph.id ?? '<unknown>'}`);
  if (
    typeof graph.id !== 'string' ||
    typeof graph.realm !== 'boolean' ||
    !Array.isArray(graph.nodes) ||
    !Array.isArray(graph.bindings)
  )
    throw new Error('invalid graph definition');
  if (graph.nodes.length > maximumGraphNodes || graph.bindings.length > maximumBindings) {
    throw new Error(`${graph.id} exceeds graph bounds`);
  }
  const nodeIds = graph.nodes.map(({ id }) => id);
  if (nodeIds.some((id) => typeof id !== 'string') || new Set(nodeIds).size !== nodeIds.length) {
    throw new Error(`${graph.id} graph node IDs must be unique`);
  }
  const refs = new Set(nodeIds);
  const nodeKinds = new Map(graph.nodes.map(({ id, kind }) => [id, kind]));
  let denseArrayCells = 0;
  for (const node of graph.nodes) {
    const label = `${graph.id}.${node.id}`;
    exactKeys(node, ['id', 'kind', 'prototype', 'properties', 'elements', 'script', 'scriptArity'], label);
    if (
      !['object', 'function', 'array', 'error'].includes(node.kind) ||
      typeof node.prototype !== 'string' ||
      !Array.isArray(node.properties) ||
      !Array.isArray(node.elements) ||
      !Number.isInteger(node.scriptArity) ||
      node.scriptArity < 0
    ) {
      throw new Error(`${label} is invalid`);
    }
    if (node.properties.length > maximumNodeProperties || node.elements.length > maximumNodeElements) {
      throw new Error(`${label} exceeds node bounds`);
    }
    if (!intrinsicNames.has(node.prototype) && !refs.has(node.prototype)) {
      throw new Error(`${label} has unknown prototype ${node.prototype}`);
    }
    const propertyKeys = new Set();
    for (const [index, property] of node.properties.entries()) {
      const propertyLabel = `${label}.properties[${index}]`;
      exactKeys(property, ['key', 'descriptor'], propertyLabel);
      const key = propertyKeyIdentity(property.key, `${propertyLabel}.key`);
      if (propertyKeys.has(key)) throw new Error(`${label} has duplicate property key ${key}`);
      propertyKeys.add(key);
      const descriptor = property.descriptor;
      if (descriptor.kind === 'data') {
        exactKeys(
          descriptor,
          ['kind', 'value', 'writable', 'enumerable', 'configurable'],
          `${propertyLabel}.descriptor`,
        );
        validateModelValue(descriptor.value, refs, `${propertyLabel}.descriptor.value`);
        for (const field of ['writable', 'enumerable', 'configurable']) {
          if (typeof descriptor[field] !== 'boolean') throw new Error(`${propertyLabel}.${field} must be boolean`);
        }
      } else if (descriptor.kind === 'accessor') {
        exactKeys(descriptor, ['kind', 'get', 'set', 'enumerable', 'configurable'], `${propertyLabel}.descriptor`);
        for (const accessor of [descriptor.get, descriptor.set]) {
          if (accessor !== '' && nodeKinds.get(accessor) !== 'function') {
            throw new Error(`${label} accessor ${accessor} is not a function`);
          }
        }
      } else throw new Error(`${propertyLabel} has unknown descriptor kind`);
    }
    const indices = new Set();
    let maximumIndex = -1;
    node.elements.forEach((element, index) => {
      const current = `${label}.elements[${index}]`;
      exactKeys(element, ['index', 'value'], current);
      if (
        node.kind !== 'array' ||
        !Number.isInteger(element.index) ||
        element.index < 0 ||
        element.index > maximumArrayIndex ||
        indices.has(element.index)
      )
        throw new Error(`${current} has invalid index`);
      indices.add(element.index);
      maximumIndex = Math.max(maximumIndex, element.index);
      validateModelValue(element.value, refs, `${current}.value`);
    });
    if (node.kind === 'array') {
      const cells = maximumIndex + 1;
      if (cells > maximumDenseArrayCells - denseArrayCells) {
        throw new Error(`${graph.id} exceeds dense-array materialization budget`);
      }
      denseArrayCells += cells;
    }
    validateScript(node.script, refs, node, `${label}.script`);
  }
  const bindingNames = new Set();
  graph.bindings.forEach((binding, index) => {
    const label = `${graph.id}.bindings[${index}]`;
    exactKeys(binding, ['name', 'mutable', 'value'], label);
    if (typeof binding.name !== 'string' || bindingNames.has(binding.name) || typeof binding.mutable !== 'boolean') {
      throw new Error(`${label} is invalid`);
    }
    bindingNames.add(binding.name);
    validateModelValue(binding.value, refs, `${label}.value`);
  });
  for (const node of graph.nodes) {
    const seen = new Set([node.id]);
    let prototype = node.prototype;
    while (!prototype.startsWith('@')) {
      if (seen.has(prototype)) throw new Error(`${graph.id} contains a prototype cycle`);
      seen.add(prototype);
      prototype = graph.nodes.find(({ id }) => id === prototype)?.prototype ?? '@null';
    }
  }
}

export function compareCodeUnits(left, right) {
  if (left === right) return 0;
  return left < right ? -1 : 1;
}

function hash(value) {
  return createHash('sha256').update(value).digest('hex');
}

function stringFixture(value) {
  return {
    kind: 'string',
    units: Array.from({ length: value.length }, (_, index) => value.charCodeAt(index)),
  };
}

function normalizeModelValue(value) {
  if (value.kind === 'string' || value.kind === 'error') {
    validateModelValue(value, new Set(), 'graph value');
    return value;
  }
  if (value.kind === 'ref') return value;
  if (value.kind === 'symbol') {
    return value;
  }
  validateFixture(value);
  return value;
}

function referencedIds(graph) {
  const ids = [];
  const visit = (value) => {
    if (value.kind === 'ref') ids.push(value.id);
  };
  for (const node of graph.nodes) {
    if (node.prototype !== '' && !node.prototype.startsWith('@')) ids.push(node.prototype);
    for (const property of node.properties) {
      if (property.descriptor.kind === 'data') visit(property.descriptor.value);
      else {
        if (property.descriptor.get !== '') ids.push(property.descriptor.get);
        if (property.descriptor.set !== '') ids.push(property.descriptor.set);
      }
    }
    node.elements.forEach((element) => visit(element.value));
    [node.script, ...node.script.cases].forEach((script) => visit(script.completion.value));
  }
  return ids;
}

function expandGraphFixture(fixture, graphs) {
  exactKeys(fixture, ['kind', 'graph', 'arguments', 'observe'], `graph fixture ${fixture.graph ?? '<unknown>'}`);
  if (
    !Array.isArray(fixture.arguments) ||
    !Array.isArray(fixture.observe) ||
    fixture.arguments.length > maximumGraphRoots ||
    fixture.observe.length > maximumGraphRoots
  ) {
    throw new Error(`graph fixture ${fixture.graph ?? '<unknown>'} exceeds root bounds`);
  }
  const graph = graphs.get(fixture.graph);
  if (graph === undefined) throw new Error(`unknown fixture graph ${fixture.graph}`);
  validateGraphDefinition(graph);
  const nodeIds = graph.nodes.map(({ id }) => id);
  if (new Set(nodeIds).size !== nodeIds.length) throw new Error(`${graph.id} graph node IDs must be unique`);
  const nodeIdSet = new Set(nodeIds);
  const nodeKinds = new Map(graph.nodes.map(({ id, kind }) => [id, kind]));
  for (const id of referencedIds(graph)) {
    if (!nodeIdSet.has(id)) throw new Error(`${graph.id} references unknown node ${id}`);
  }
  for (const [index, value] of [...fixture.arguments, ...fixture.observe].entries()) {
    validateModelValue(value, nodeIdSet, `${graph.id}.fixtureValues[${index}]`);
    if (value.kind === 'ref' && !nodeIdSet.has(value.id))
      throw new Error(`${graph.id} references unknown root ${value.id}`);
  }
  for (const binding of graph.bindings ?? []) {
    if (binding.value.kind === 'ref' && !nodeIdSet.has(binding.value.id)) {
      throw new Error(`${graph.id} binding references unknown node ${binding.value.id}`);
    }
  }
  for (const node of graph.nodes) {
    const indices = node.elements.map(({ index }) => index);
    if (new Set(indices).size !== indices.length) throw new Error(`${graph.id}.${node.id} has duplicate array indices`);
    for (const property of node.properties) {
      if (property.descriptor.kind !== 'accessor') continue;
      for (const accessor of [property.descriptor.get, property.descriptor.set]) {
        if (accessor !== '' && nodeKinds.get(accessor) !== 'function') {
          throw new Error(`${graph.id}.${node.id} accessor ${accessor} is not a function`);
        }
      }
    }
  }
  for (const node of graph.nodes) {
    const seen = new Set([node.id]);
    let prototype = node.prototype;
    while (prototype !== '' && !prototype.startsWith('@')) {
      if (seen.has(prototype)) throw new Error(`${graph.id} contains a prototype cycle`);
      seen.add(prototype);
      prototype = graph.nodes.find(({ id }) => id === prototype)?.prototype ?? '';
    }
  }
  const normalizeScript = (script) => ({
    ...script,
    completion: { ...script.completion, value: normalizeModelValue(script.completion.value) },
  });
  const expanded = {
    kind: 'graph',
    graphId: graph.id,
    realm: graph.realm,
    nodes: graph.nodes.map((node) => ({
      ...node,
      properties: node.properties.map((property) => ({
        ...property,
        key: property.key,
        descriptor:
          property.descriptor.kind === 'data'
            ? { ...property.descriptor, value: normalizeModelValue(property.descriptor.value) }
            : property.descriptor,
      })),
      elements: node.elements.map((element) => ({ ...element, value: normalizeModelValue(element.value) })),
      script: { ...normalizeScript(node.script), cases: node.script.cases.map(normalizeScript) },
    })),
    bindings: (graph.bindings ?? []).map((binding) => ({ ...binding, value: normalizeModelValue(binding.value) })),
    arguments: fixture.arguments.map(normalizeModelValue),
    observe: fixture.observe.map(normalizeModelValue),
  };
  exactKeys(
    expanded,
    ['kind', 'graphId', 'realm', 'nodes', 'bindings', 'arguments', 'observe'],
    `expanded graph ${graph.id}`,
  );
  validateGraphDefinition({
    id: expanded.graphId,
    realm: expanded.realm,
    nodes: expanded.nodes,
    bindings: expanded.bindings,
  });
  expanded.arguments.forEach((value, index) => validateModelValue(value, nodeIdSet, `${graph.id}.arguments[${index}]`));
  expanded.observe.forEach((value, index) => validateModelValue(value, nodeIdSet, `${graph.id}.observe[${index}]`));
  return expanded;
}

function normalizeFixture(fixture, graphs) {
  if (fixture.kind === 'graph') return expandGraphFixture(fixture, graphs);
  const normalized =
    fixture.kind === 'string' && Object.hasOwn(fixture, 'value') ? stringFixture(fixture.value) : fixture;
  if (normalized.kind === 'symbol') {
    const registered = { ...normalized, identity: `tslean-differential:${normalized.identity}` };
    validateFixture(registered);
    return registered;
  }
  validateFixture(normalized);
  return normalized;
}

export function validateFixture(fixture) {
  if (fixture === null || typeof fixture !== 'object' || Array.isArray(fixture))
    throw new Error('fixture must be an object');
  if (fixture.kind === 'undefined' || fixture.kind === 'null') {
    exactKeys(fixture, ['kind'], 'fixture');
    return;
  }
  if (fixture.kind === 'boolean' && typeof fixture.value === 'boolean') {
    exactKeys(fixture, ['kind', 'value'], 'fixture');
    return;
  }
  if (fixture.kind === 'number') {
    exactKeys(fixture, ['kind', 'bits'], 'fixture');
    if (typeof fixture.bits !== 'string' || !canonicalUnsignedDecimal.test(fixture.bits)) {
      throw new Error('number bits must use canonical unsigned decimal');
    }
    if (BigInt(fixture.bits) > maximumUInt64) throw new Error('number bits exceed UInt64');
    return;
  }
  if (fixture.kind === 'string') {
    exactKeys(fixture, ['kind', 'units'], 'fixture');
    if (
      !Array.isArray(fixture.units) ||
      fixture.units.length > maximumStringCodeUnits ||
      fixture.units.some((unit) => !Number.isInteger(unit) || unit < 0 || unit > 65535)
    ) {
      throw new Error('string fixture must contain UInt16 code units');
    }
    return;
  }
  if (fixture.kind === 'bigint') {
    exactKeys(fixture, ['kind', 'decimal'], 'fixture');
    if (typeof fixture.decimal !== 'string' || !canonicalBigIntDecimal.test(fixture.decimal)) {
      throw new Error('BigInt must use canonical decimal');
    }
    return;
  }
  if (fixture.kind === 'symbol' && typeof fixture.identity === 'string' && fixture.identity.length > 0) {
    exactKeys(fixture, ['kind', 'identity'], 'fixture');
    return;
  }
  if (fixture.kind === 'graph') {
    exactKeys(
      fixture,
      ['kind', 'graphId', 'realm', 'nodes', 'bindings', 'arguments', 'observe'],
      'expanded graph fixture',
    );
    const refs = new Set(fixture.nodes.map(({ id }) => id));
    validateGraphDefinition({
      id: fixture.graphId,
      realm: fixture.realm,
      nodes: fixture.nodes,
      bindings: fixture.bindings,
    });
    fixture.arguments.forEach((value, index) =>
      validateModelValue(value, refs, `${fixture.graphId}.arguments[${index}]`),
    );
    fixture.observe.forEach((value, index) => validateModelValue(value, refs, `${fixture.graphId}.observe[${index}]`));
    return;
  }
  throw new Error(`invalid fixture kind: ${String(fixture.kind)}`);
}

function vector(id, scenario, operation, fixtures, graphs, tags = [], replay, source, corpusIds = []) {
  const normalized = fixtures.map((fixture) => normalizeFixture(fixture, graphs));
  const input = { operation, fixtures: normalized };
  return {
    id,
    scenario,
    operation,
    ...(source === undefined ? {} : { source }),
    fixtures: normalized,
    tags: [...new Set(tags)].sort(compareCodeUnits),
    corpusIds: [...new Set(corpusIds)].sort(compareCodeUnits),
    ...(replay === undefined ? {} : { replay }),
    inputHash: hash(JSON.stringify(input)),
  };
}

function generatedId(scenario, algorithm, index) {
  return `${scenario}-${algorithm.replace(/-v[0-9]+$/, '')}-${String(index).padStart(4, '0')}`;
}

function xorshift64(state) {
  state ^= state << 13n;
  state ^= state >> 7n;
  state ^= state << 17n;
  return BigInt.asUintN(64, state);
}

function expandGenerator(scenario, generator, graphs) {
  const result = [];
  const replay = (index) => ({ algorithm: generator.algorithm, seed: generator.seed, index });
  if (generator.algorithm === 'trim-code-units-v1') {
    const whitespace = [
      0x0009, 0x000a, 0x000b, 0x000c, 0x000d, 0x0020, 0x00a0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005,
      0x2006, 0x2007, 0x2008, 0x2009, 0x200a, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff,
    ];
    for (const unit of whitespace) {
      for (const value of [String.fromCharCode(unit), `${String.fromCharCode(unit)}1${String.fromCharCode(unit)}`]) {
        const index = result.length;
        result.push(
          vector(
            generatedId(scenario.id, generator.algorithm, index),
            scenario.id,
            'parse',
            [{ kind: 'string', value }],
            graphs,
            [],
            replay(index),
          ),
        );
      }
    }
  } else if (generator.algorithm === 'decimal-cases-v1') {
    let state = Number(generator.seed) | 0;
    for (let index = 0; index < generator.count; index += 1) {
      state = (Math.imul(state ^ (state >>> 15), 1 | state) + index) | 0;
      const sign = state & 1 ? '-' : '';
      const integer = String(Math.abs(state % 1_000_000));
      const fraction = String(Math.abs(Math.imul(state, 2654435761) % 1_000_000)).padStart(6, '0');
      const exponent = (state % 700) - 350;
      result.push(
        vector(
          generatedId(scenario.id, generator.algorithm, index),
          scenario.id,
          'parse',
          [{ kind: 'string', value: `${sign}${integer}.${fraction}e${exponent}` }],
          graphs,
          [],
          replay(index),
        ),
      );
    }
  } else if (generator.algorithm === 'finite-binary64-v1') {
    let state = BigInt(generator.seed);
    for (let index = 0; index < generator.count; index += 1) {
      state ^= state << 13n;
      state ^= state >> 7n;
      state ^= state << 17n;
      const candidate = BigInt.asUintN(64, state);
      if ((candidate & 0x7ff0000000000000n) !== 0x7ff0000000000000n) {
        result.push(
          vector(
            generatedId(scenario.id, generator.algorithm, index),
            scenario.id,
            'format',
            [{ kind: 'number', bits: String(candidate) }],
            graphs,
            [],
            replay(index),
          ),
        );
      }
    }
  } else if (generator.algorithm === 'primitive-operators-v1') {
    let state = BigInt(generator.seed);
    const next = () => {
      state = xorshift64(state);
      return state;
    };
    const sample = () => {
      const tag = Number(next() % 8n);
      if (tag === 0) return { kind: 'undefined' };
      if (tag === 1) return { kind: 'null' };
      if (tag === 2) return { kind: 'boolean', value: Boolean(next() & 1n) };
      if (tag === 3) return { kind: 'number', bits: String(next()) };
      if (tag === 4 || tag === 5) {
        const magnitude = (next() << 128n) | (next() << 64n) | next();
        const value = next() & 1n ? magnitude : -magnitude;
        return { kind: 'bigint', decimal: String(value) };
      }
      if (tag === 6) return { kind: 'string', value: operatorStrings[Number(next() % BigInt(operatorStrings.length))] };
      return { kind: 'symbol', identity: `fuzz-${next() % 8n}` };
    };
    for (let index = 0; index < generator.count; index += 1) {
      const operation = operations[Number(next() % BigInt(operations.length))];
      result.push(
        vector(
          generatedId(scenario.id, generator.algorithm, index),
          scenario.id,
          operation,
          [sample(), sample()],
          graphs,
          [],
          replay(index),
        ),
      );
    }
  } else {
    throw new Error(`unknown differential generator: ${generator.algorithm}`);
  }
  if (result.length !== generator.count) {
    throw new Error(`${generator.algorithm} declared ${generator.count} vectors but generated ${result.length}`);
  }
  return result;
}

function expandScenario(scenario, graphs) {
  const result = [];
  if (scenario.id === 'conversion-equality') {
    for (const operation of ['number', 'string', 'key']) {
      scenario.fixtures.forEach((fixture, index) => {
        result.push(
          vector(
            `${scenario.id}-${operation}-${String(index).padStart(2, '0')}`,
            scenario.id,
            operation,
            [fixture],
            graphs,
          ),
        );
      });
    }
    scenario.fixtures.forEach((left, leftIndex) => {
      scenario.fixtures.forEach((right, rightIndex) => {
        result.push(
          vector(
            `${scenario.id}-loose-${String(leftIndex).padStart(2, '0')}-${String(rightIndex).padStart(2, '0')}`,
            scenario.id,
            'loose',
            [left, right],
            graphs,
          ),
        );
      });
    });
  } else {
    for (const entry of scenario.vectors) {
      result.push(
        vector(
          `${scenario.id}-${entry.id}`,
          scenario.id,
          entry.operation,
          entry.fixtures,
          graphs,
          entry.tags,
          undefined,
          entry.source,
          entry.corpusIds,
        ),
      );
    }
  }
  for (const generator of scenario.generators) result.push(...expandGenerator(scenario, generator, graphs));
  if (result.length !== scenario.expectedCount) {
    throw new Error(`${scenario.id} declared ${scenario.expectedCount} vectors but expanded ${result.length}`);
  }
  return result;
}

export function buildDifferentialSuite(source) {
  const suite = JSON.parse(source);
  if (!Array.isArray(suite.registry)) throw new Error('operation registry must be an array');
  for (const [index, operation] of suite.registry.entries()) {
    const label = `registry[${index}]`;
    exactKeys(operation, ['id', 'domain', 'arity', 'source'], label);
    if (typeof operation.id !== 'string' || !/^[a-z][a-z0-9]*(?:-[a-z0-9]+)*$/.test(operation.id)) {
      throw new Error(`${label}.id is invalid`);
    }
    if (operation.domain !== 'primitive' && operation.domain !== 'graph') {
      throw new Error(`${label}.domain is invalid`);
    }
    if (operation.arity !== 1 && operation.arity !== 2) throw new Error(`${label}.arity is invalid`);
    if (typeof operation.source !== 'string' || operation.source.length === 0 || /[\r\n]/.test(operation.source)) {
      throw new Error(`${label}.source is invalid`);
    }
  }
  const graphIds = (suite.graphs ?? []).map(({ id }) => id);
  if (new Set(graphIds).size !== graphIds.length) throw new Error('graph IDs must be unique');
  const graphs = new Map((suite.graphs ?? []).map((graph) => [graph.id, graph]));
  const scenarioIds = suite.scenarios.map(({ id }) => id);
  if (new Set(scenarioIds).size !== scenarioIds.length) throw new Error('scenario IDs must be unique');
  const orderedScenarios = [...suite.scenarios].sort((left, right) => compareCodeUnits(left.id, right.id));
  const registryIds = suite.registry.map(({ id }) => id);
  if (new Set(registryIds).size !== registryIds.length) throw new Error('operation registry IDs must be unique');
  if (JSON.stringify(registryIds) !== JSON.stringify([...registryIds].sort(compareCodeUnits))) {
    throw new Error('operation registry must be sorted by ID');
  }
  const registry = new Set(registryIds);
  const arities = new Map(suite.registry.map(({ id, arity }) => [id, arity]));
  const domains = new Map(suite.registry.map(({ id, domain }) => [id, domain]));
  const operationSources = new Map(suite.registry.map(({ id, source }) => [id, source]));
  const vectors = orderedScenarios
    .flatMap((scenario) => expandScenario(scenario, graphs))
    .sort((left, right) => compareCodeUnits(left.id, right.id));
  const ids = vectors.map(({ id }) => id);
  if (new Set(ids).size !== ids.length) throw new Error('expanded vector IDs must be unique');
  const scenarios = new Map(orderedScenarios.map((scenario) => [scenario.id, new Set(scenario.operations)]));
  for (const entry of vectors) {
    if (!registry.has(entry.operation)) throw new Error(`${entry.id} uses unknown operation ${entry.operation}`);
    const operationSource = operationSources.get(entry.operation);
    if (entry.source !== undefined && entry.source !== operationSource) {
      throw new Error(`${entry.id} source differs from registered operation ${entry.operation}`);
    }
    entry.source = operationSource;
    if (!scenarios.get(entry.scenario)?.has(entry.operation)) {
      throw new Error(`${entry.id} uses operation ${entry.operation} outside scenario ${entry.scenario}`);
    }
    if (entry.fixtures.length !== arities.get(entry.operation))
      throw new Error(`${entry.id} has incorrect fixture arity`);
    const isGraph = entry.fixtures.length === 1 && entry.fixtures[0].kind === 'graph';
    if ((domains.get(entry.operation) === 'graph') !== isGraph) {
      throw new Error(`${entry.id} has incorrect fixture domain`);
    }
    entry.fixtures.forEach(validateFixture);
  }
  const uniqueOperationInputCount = new Set(
    vectors.map(({ operation, fixtures }) => JSON.stringify({ operation, fixtures })),
  ).size;
  return {
    suite,
    manifest: {
      schemaVersion: 1,
      suite: suite.suite,
      sourceHash: hash(source),
      operationRegistry: registryIds,
      counts: Object.fromEntries(orderedScenarios.map((scenario) => [scenario.id, scenario.expectedCount])),
      totalCount: vectors.length,
      uniqueOperationInputCount,
      parityDuplicateCount: vectors.length - uniqueOperationInputCount,
      duplicatePolicy: 'preserved-for-v1-parity',
      vectors,
    },
  };
}

export function loadDifferentialSuite(root, suiteName = 'primitive') {
  return buildDifferentialSuite(readFileSync(resolve(root, `spec/differential/${suiteName}.json`), 'utf8'));
}

export function loadCombinedDifferential(root, suiteNames = ['primitive', 'abstract-operations']) {
  const artifacts = suiteNames.map((name) => [name, loadDifferentialSuite(root, name)]);
  const definitions = new Map();
  for (const [, artifact] of artifacts) {
    for (const operation of artifact.suite.registry) {
      const current = definitions.get(operation.id);
      if (current !== undefined && JSON.stringify(current) !== JSON.stringify(operation)) {
        throw new Error(`operation ${operation.id} has conflicting definitions`);
      }
      definitions.set(operation.id, operation);
    }
  }
  const registry = [...definitions.values()].sort((left, right) => compareCodeUnits(left.id, right.id));
  const vectors = artifacts
    .flatMap(([, artifact]) => artifact.manifest.vectors)
    .sort((left, right) => compareCodeUnits(left.id, right.id));
  const ids = vectors.map(({ id }) => id);
  if (new Set(ids).size !== ids.length) throw new Error('combined vector IDs must be unique');
  const counts = Object.fromEntries(
    artifacts
      .flatMap(([, artifact]) => Object.entries(artifact.manifest.counts))
      .sort(([left], [right]) => compareCodeUnits(left, right)),
  );
  const sourceHashes = Object.fromEntries(artifacts.map(([name, artifact]) => [name, artifact.manifest.sourceHash]));
  const generatedCount = vectors.filter(({ replay }) => replay !== undefined).length;
  const uniqueOperationInputCount = new Set(
    vectors.map(({ operation, fixtures }) => JSON.stringify({ operation, fixtures })),
  ).size;
  const coverageSource = readFileSync(resolve(root, 'spec/differential/corpus-coverage.json'), 'utf8');
  const inventorySource = readFileSync(resolve(root, 'spec/differential/legacy-abstract-inventory.json'), 'utf8');
  const coverage = JSON.parse(coverageSource);
  const corpusClassifications = Object.fromEntries(
    ['model-covered', 'compiler-only', 'model-pending', 'proof-integrity', 'scale'].map((classification) => [
      classification,
      coverage.entries.filter((entry) => entry.classification === classification).length,
    ]),
  );
  return {
    suite: { registry },
    manifest: {
      schemaVersion: 1,
      suite: 'combined',
      sourceHash: hash(JSON.stringify(sourceHashes)),
      sourceHashes,
      corpusCoverageHash: hash(coverageSource),
      legacyInventoryHash: hash(inventorySource),
      corpusClassifications,
      operationRegistry: registry.map(({ id }) => id),
      operationDefinitions: registry,
      counts,
      bounds: {
        aggregateDenseArrayCells: maximumDenseArrayCells,
      },
      scenarioCount: Object.keys(counts).length,
      fixedCount: vectors.length - generatedCount,
      generatedCount,
      vectorCount: vectors.length,
      comparisonCount: vectors.length,
      totalCount: vectors.length,
      uniqueOperationInputCount,
      parityDuplicateCount: vectors.length - uniqueOperationInputCount,
      duplicatePolicy: 'preserved-for-v1-parity',
      vectors,
    },
    artifacts,
  };
}

export function renderLeanRegistry(suite) {
  const bySpec = (domain, arity) =>
    suite.registry
      .filter((operation) => operation.domain === domain && operation.arity === arity)
      .map(({ id }) => `"${id}"`)
      .join(', ');
  return `namespace TSLean.JS.Oracle

inductive OracleDomain where
  | primitive
  | graph
  deriving DecidableEq

structure OperationSpec where
  arity : Nat
  domain : OracleDomain

def operationRegistry : List String :=
  [${suite.registry.map(({ id }) => `"${id}"`).join(', ')}]

def operationSpec? (operation : String) : Option OperationSpec :=
  if [${bySpec('primitive', 1)}].contains operation then some ⟨1, .primitive⟩
  else if [${bySpec('primitive', 2)}].contains operation then some ⟨2, .primitive⟩
  else if [${bySpec('graph', 1)}].contains operation then some ⟨1, .graph⟩
  else if [${bySpec('graph', 2)}].contains operation then some ⟨2, .graph⟩
  else none

def operationArity? (operation : String) : Option Nat := (operationSpec? operation).map (·.arity)
def operationDomain? (operation : String) : Option OracleDomain := (operationSpec? operation).map (·.domain)

end TSLean.JS.Oracle
`;
}

export function renderDifferentialManifest(manifest) {
  return `${JSON.stringify(manifest, null, 2)}\n`;
}

export function verifyDifferentialArtifacts(root, manifestSource, registrySource) {
  const generated = loadCombinedDifferential(root);
  if (manifestSource !== renderDifferentialManifest(generated.manifest))
    throw new Error('differential manifest is stale');
  if (registrySource !== renderLeanRegistry(generated.suite)) throw new Error('Lean operation registry is stale');
  return generated;
}
