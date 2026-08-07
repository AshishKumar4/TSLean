import vm from 'node:vm';
import { validateFixture } from '../../scripts/differential-manifest-lib.mjs';
import type { Canonicalizer } from './canonical.js';
import type { GraphFixture } from './types.js';

export type MaterializedGraph = {
  arguments: Parameters<typeof structuredClone>[0][];
  observe: Parameters<typeof structuredClone>[0][];
  environment: Record<string, Parameters<typeof structuredClone>[0]>;
  trace: string[];
  selections: Map<object, PropertyKey[]>;
  kinds: Map<object, 'object' | 'function' | 'array' | 'error'>;
  errorPrototypes: Map<object, string>;
  fixtureErrors: Map<object, { name: string; message: string }>;
};

const materializerSource = `(() => {
  const descriptor = globalThis.__graphDescriptor;
  const nodes = new Map();
  const symbols = new Map();
  const trace = [];
  const selections = new Map();
  const kinds = new Map();
  const errorPrototypes = new Map([
    [Error.prototype, 'Error'], [TypeError.prototype, 'TypeError'], [RangeError.prototype, 'RangeError'],
    [ReferenceError.prototype, 'ReferenceError'], [SyntaxError.prototype, 'SyntaxError'],
  ]);
  const fixtureErrors = new Map();
  const registerSymbol = globalThis.__registerGraphSymbol;
  const textFromUnits = units => {
    let result = '';
    for (let index = 0; index < units.length; index += 1024) {
      result += String.fromCharCode(...units.slice(index, index + 1024));
    }
    return result;
  };
  const objectPrototype = Object.prototype;
  const functionPrototype = Function.prototype;
  const arrayPrototype = Array.prototype;
  selections.set(objectPrototype, []);
  selections.set(functionPrototype, []);
  selections.set(arrayPrototype, []);
  selections.set(Boolean.prototype, []);
  selections.set(Number.prototype, []);
  selections.set(String.prototype, []);
  selections.set(BigInt.prototype, []);
  selections.set(Symbol.prototype, []);
  kinds.set(objectPrototype, 'object');
  kinds.set(functionPrototype, 'function');
  kinds.set(arrayPrototype, 'array');
  kinds.set(Boolean.prototype, 'object');
  kinds.set(Number.prototype, 'object');
  kinds.set(String.prototype, 'object');
  kinds.set(BigInt.prototype, 'object');
  kinds.set(Symbol.prototype, 'object');
  for (const prototype of errorPrototypes.keys()) {
    selections.set(prototype, []);
    kinds.set(prototype, 'object');
  }
  const symbol = value => {
    const key = value.symbolKind + ':' + value.identity;
    if (symbols.has(key)) return symbols.get(key);
    let result;
    if (value.symbolKind === 'well-known') {
      result = Object.getOwnPropertyDescriptor(Symbol, value.identity)?.value;
      if (typeof result !== 'symbol') throw new Error('unknown well-known symbol: ' + value.identity);
    } else if (value.symbolKind === 'registered') {
      result = Symbol.for(value.identity);
      registerSymbol(result, value.identity, value.symbolKind);
    } else {
      result = Symbol();
      registerSymbol(result, value.identity, value.symbolKind);
    }
    symbols.set(key, result);
    return result;
  };
  const value = encoded => {
    switch (encoded.kind) {
      case 'undefined': return undefined;
      case 'null': return null;
      case 'boolean': return encoded.value;
      case 'number': {
        const buffer = new ArrayBuffer(8);
        const view = new DataView(buffer);
        view.setBigUint64(0, BigInt(encoded.bits), false);
        return view.getFloat64(0, false);
      }
      case 'string': {
        return textFromUnits(encoded.units);
      }
      case 'bigint': return BigInt(encoded.decimal);
      case 'symbol': return symbol(encoded);
      case 'error': {
        const name = textFromUnits(encoded.name);
        const message = textFromUnits(encoded.message);
        const result = new globalThis[name](message);
        fixtureErrors.set(result, { name, message });
        return result;
      }
      case 'ref': return nodes.get(encoded.id);
      default: throw new Error('unknown graph value kind: ' + encoded.kind);
    }
  };
  const emit = (events, args) => {
    for (const event of events) {
      if (event.kind === 'fixed') {
        trace.push(textFromUnits(event.units));
        continue;
      }
      const argument = args[event.argument];
      const valid = event.format === 'null' ? argument === null
        : event.format === 'undefined' ? argument === undefined
        : typeof argument === event.format;
      if (!valid) throw new TypeError('script argument does not match declared format');
      trace.push(textFromUnits(event.prefixUnits) + String(argument));
    }
  };
  const execute = (script, receiver, args) => {
    const selected = script.cases.find(candidate => nodes.get(candidate.receiver) === receiver) ?? script;
    emit(selected.events, args);
    const result = value(selected.completion.value);
    if (selected.completion.type === 'throw') throw result;
    return result;
  };
  for (const node of descriptor.nodes) {
    let result;
    if (node.kind === 'function') result = function (...args) { return execute(node.script, this, args); };
    else if (node.kind === 'array') result = [];
    else if (node.kind === 'error') result = new Error();
    else result = {};
    nodes.set(node.id, result);
    kinds.set(result, node.kind);
  }
  const intrinsicPrototype = name => {
    if (name === '@null') return null;
    if (name === '@object') return objectPrototype;
    if (name === '@function') return functionPrototype;
    if (name === '@array') return arrayPrototype;
    return nodes.get(name);
  };
  const propertyKey = key => key.kind === 'string' ? textFromUnits(key.units) : symbol(key);
  for (const node of descriptor.nodes) {
    const target = nodes.get(node.id);
    Object.setPrototypeOf(target, intrinsicPrototype(node.prototype));
    for (const element of node.elements) target[element.index] = value(element.value);
    const selectedKeys = node.elements.map(element => String(element.index));
    if (node.kind === 'array') selectedKeys.push('length');
    for (const property of node.properties) {
      const key = propertyKey(property.key);
      const encoded = property.descriptor;
      const descriptorValue = encoded.kind === 'data'
        ? { value: value(encoded.value), writable: encoded.writable, enumerable: encoded.enumerable, configurable: encoded.configurable }
        : {
            get: encoded.get === '' ? undefined : nodes.get(encoded.get),
            set: encoded.set === '' ? undefined : nodes.get(encoded.set),
            enumerable: encoded.enumerable,
            configurable: encoded.configurable,
          };
      const existing = Object.getOwnPropertyDescriptor(target, key);
      if (existing?.configurable === false && encoded.kind === 'data') {
        Object.defineProperty(target, key, { ...existing, value: descriptorValue.value });
      } else {
        Object.defineProperty(target, key, descriptorValue);
      }
      selectedKeys.push(key);
    }
    selections.set(target, Reflect.ownKeys(target).filter(key => selectedKeys.includes(key)));
  }
  const environment = Object.create(null);
  for (const binding of descriptor.bindings) environment[binding.name] = value(binding.value);
  return {
    arguments: descriptor.arguments.map(value),
    observe: descriptor.observe.map(value),
    environment,
    trace,
    selections,
    kinds,
    errorPrototypes,
    fixtureErrors,
  };
})()`;

export function materializeGraphFixture(
  context: vm.Context,
  fixture: GraphFixture,
  canonicalizer: Canonicalizer,
): MaterializedGraph {
  validateFixture(fixture);
  context.__graphDescriptor = fixture;
  context.__registerGraphSymbol = (symbol: symbol, identity: string, kind: 'local' | 'registered') => {
    canonicalizer.registerSymbol(symbol, identity, kind === 'registered' ? 'registered' : 'unique');
  };
  try {
    return vm.runInContext(materializerSource, context, { timeout: 50 });
  } finally {
    delete context.__graphDescriptor;
    delete context.__registerGraphSymbol;
  }
}
