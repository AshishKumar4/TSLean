import type { CanonicalDatum, Observation } from './types.js';

const canonicalNaN = 0x7ff8000000000000n;
const wellKnownSymbols = new Map<symbol, string>();
for (const name of Object.getOwnPropertyNames(Symbol)) {
  const value = Object.getOwnPropertyDescriptor(Symbol, name)?.value;
  if (typeof value === 'symbol') wellKnownSymbols.set(value, name);
}
const hostErrorPrototypes = new Map<object, string>([
  [Error.prototype, 'Error'], [TypeError.prototype, 'TypeError'], [RangeError.prototype, 'RangeError'],
  [ReferenceError.prototype, 'ReferenceError'], [SyntaxError.prototype, 'SyntaxError'],
]);

function stringDatum(value: string): { type: 'string'; units: number[] } {
  const units: number[] = [];
  for (let index = 0; index < value.length; index += 1) units.push(value.charCodeAt(index));
  return { type: 'string', units };
}

function numberBits(value: number): string {
  if (Number.isNaN(value)) return String(canonicalNaN);
  const buffer = new ArrayBuffer(8);
  const view = new DataView(buffer);
  view.setFloat64(0, value, false);
  return String(view.getBigUint64(0, false));
}

function ownDataString(value: object, key: string): string | undefined {
  const descriptor = Object.getOwnPropertyDescriptor(value, key);
  return descriptor !== undefined && 'value' in descriptor && typeof descriptor.value === 'string'
    ? descriptor.value : undefined;
}

function isReference(value: Parameters<typeof structuredClone>[0]): value is object {
  return (typeof value === 'object' && value !== null) || typeof value === 'function';
}

export class Canonicalizer {
  readonly #registeredSymbols = new Map<symbol, { identity: string; kind: 'registered' | 'unique' }>();
  readonly #uniqueSymbols = new Map<symbol, string>();
  readonly #objects = new WeakMap<object, string>();
  #nextSymbolId = 0;
  #nextObjectId = 0;

  registerSymbol(symbol: symbol, identity: string, kind: 'registered' | 'unique' = 'registered'): void {
    this.#registeredSymbols.set(symbol, { identity, kind });
  }

  #reference(value: object): string {
    let identity = this.#objects.get(value);
    if (identity === undefined) {
      identity = `ref-${this.#nextObjectId}`;
      this.#nextObjectId += 1;
      this.#objects.set(value, identity);
    }
    return identity;
  }

  #primitive(value: Parameters<typeof structuredClone>[0]): CanonicalDatum | undefined {
    if (value === undefined) return { type: 'undefined' };
    if (value === null) return { type: 'null' };
    if (typeof value === 'boolean') return { type: 'boolean', value };
    if (typeof value === 'number') return { type: 'number', bits: numberBits(value) };
    if (typeof value === 'string') return stringDatum(value);
    if (typeof value === 'bigint') return { type: 'bigint', decimal: String(value) };
    if (typeof value !== 'symbol') return undefined;
    const wellKnown = wellKnownSymbols.get(value);
    if (wellKnown !== undefined) return { type: 'symbol', kind: 'well-known', identity: wellKnown };
    const registered = this.#registeredSymbols.get(value);
    if (registered !== undefined) return { type: 'symbol', kind: registered.kind, identity: registered.identity };
    const globalIdentity = Symbol.keyFor(value);
    if (globalIdentity !== undefined) return { type: 'symbol', kind: 'registered', identity: globalIdentity };
    let identity = this.#uniqueSymbols.get(value);
    if (identity === undefined) {
      identity = `symbol-${this.#nextSymbolId}`;
      this.#nextSymbolId += 1;
      this.#uniqueSymbols.set(value, identity);
    }
    return { type: 'symbol', kind: 'unique', identity };
  }

  datum(value: Parameters<typeof structuredClone>[0]): CanonicalDatum {
    const primitive = this.#primitive(value);
    if (primitive !== undefined) return primitive;
    if (!isReference(value)) throw new Error('unsupported canonical value');
    return { type: 'object', identity: this.#reference(value) };
  }

  normal(value: Parameters<typeof structuredClone>[0]): Observation {
    return this.observation({ type: 'normal', value }, [], [], new Map(), new Map(), hostErrorPrototypes);
  }

  thrown(value: Parameters<typeof structuredClone>[0]): Observation {
    return this.observation({ type: 'throw', value }, [], [], new Map(), new Map(), hostErrorPrototypes);
  }

  observation(
    completion: { type: 'normal' | 'throw'; value: Parameters<typeof structuredClone>[0] },
    trace: string[],
    roots: Parameters<typeof structuredClone>[0][],
    selections: Map<object, PropertyKey[]>,
    kinds: Map<object, 'object' | 'function' | 'array' | 'error'>,
    errorPrototypes: Map<object, string>,
    fixtureErrors: Map<object, { name: string; message: string }> = new Map(),
  ): Observation {
    const queue: object[] = [];
    const queued = new Set<object>();
    const objects: NonNullable<Observation['objects']> = [];
    const errorName = (value: object): string | undefined => errorPrototypes.get(Object.getPrototypeOf(value));
    const encounter = (value: Parameters<typeof structuredClone>[0]): CanonicalDatum => {
      const primitive = this.#primitive(value);
      if (primitive !== undefined) return primitive;
      if (!isReference(value)) throw new Error('unsupported canonical value');
      const identity = this.#reference(value);
      const intrinsicName = errorName(value);
      const fixtureError = fixtureErrors.get(value);
      const followedError = kinds.get(value) === 'error';
      if (fixtureError === undefined && (intrinsicName === undefined || followedError) && !queued.has(value)) {
        queued.add(value);
        queue.push(value);
      }
      if (followedError || fixtureError !== undefined || intrinsicName !== undefined) {
        return {
          type: 'error',
          identity,
          name: stringDatum(fixtureError?.name ?? ownDataString(value, 'name') ?? intrinsicName ?? 'Error'),
          message: stringDatum(fixtureError?.message ?? (followedError ? ownDataString(value, 'message') ?? '' : '')),
        };
      }
      return { type: 'object', identity };
    };

    const completionDatum = encounter(completion.value);
    const canonicalTrace = Array.from(trace, (detail) => ({ event: 'emit', detail: encounter(detail) }));
    const canonicalRoots = Array.from(roots, encounter);
    for (let index = 0; index < queue.length; index += 1) {
      const object = queue[index];
      const intrinsicError = errorName(object);
      const kind = kinds.get(object) ?? (intrinsicError !== undefined ? 'error'
        : typeof object === 'function' ? 'function' : Array.isArray(object) ? 'array' : 'object');
      const selected = selections.get(object);
      const keys = selected ?? (kind === 'error' ? [] : Reflect.ownKeys(object));
      const properties: NonNullable<Observation['objects']>[number]['properties'] = [];
      for (const key of keys) {
        if (key === 'stack') continue;
        const descriptor = Object.getOwnPropertyDescriptor(object, key);
        if (descriptor === undefined) continue;
        const canonicalKey = typeof key === 'symbol' ? encounter(key) : stringDatum(String(key));
        if ('value' in descriptor) {
          properties.push({
            key: canonicalKey,
            descriptor: {
              kind: 'data', value: encounter(descriptor.value),
              writable: descriptor.writable ?? false,
              enumerable: descriptor.enumerable ?? false,
              configurable: descriptor.configurable ?? false,
            },
          });
        } else {
          properties.push({
            key: canonicalKey,
            descriptor: {
              kind: 'accessor', get: encounter(descriptor.get), set: encounter(descriptor.set),
              enumerable: descriptor.enumerable ?? false,
              configurable: descriptor.configurable ?? false,
            },
          });
        }
      }
      objects.push({
        identity: this.#reference(object), kind,
        prototype: encounter(Object.getPrototypeOf(object)),
        extensible: Object.isExtensible(object), properties,
      });
    }
    return {
      completion: { type: completion.type, value: completionDatum },
      trace: canonicalTrace,
      ...(roots.length === 0 ? {} : { roots: canonicalRoots }),
      ...(objects.length === 0 ? {} : { objects }),
    };
  }
}
