import { execFileSync } from 'node:child_process';
import { resolve } from 'node:path';
import { beforeAll, describe, expect, it } from 'vitest';

const root = resolve(import.meta.dirname, '..');
const leanRoot = resolve(root, 'lean');
const oracle = resolve(leanRoot, '.lake/build/bin/js-primitive-oracle');
const canonicalNaN = 0x7ff8000000000000n;

function numberBits(value: number): bigint {
  if (Number.isNaN(value)) return canonicalNaN;
  const buffer = new ArrayBuffer(8);
  new DataView(buffer).setFloat64(0, value, false);
  return new DataView(buffer).getBigUint64(0, false);
}

function numberResult(value: number): string {
  return `number:${numberBits(value)}`;
}

function encodeString(value: string): string {
  if (value.length === 0) return '_';
  return Array.from({ length: value.length }, (_, index) => value.charCodeAt(index)).join(',');
}

function stringResult(value: string): string {
  return `string:${encodeString(value)}`;
}

function decodeString(value: string): string {
  if (value === '_') return '';
  return String.fromCharCode(...value.split(',').map(Number));
}

type PrimitiveCase = {
  encoded: string;
  value: undefined | null | boolean | number | string | bigint | symbol;
};

function primitive(encoded: string, value: PrimitiveCase['value']): PrimitiveCase {
  return { encoded, value };
}

function decodePrimitive(encoded: string): PrimitiveCase['value'] {
  const separator = encoded.indexOf(':');
  const tag = separator < 0 ? encoded : encoded.slice(0, separator);
  const payload = separator < 0 ? '' : encoded.slice(separator + 1);
  if (tag === 'u') return undefined;
  if (tag === 'n') return null;
  if (tag === 'f') return false;
  if (tag === 't') return true;
  if (tag === 'd') {
    const buffer = new ArrayBuffer(8);
    new DataView(buffer).setBigUint64(0, BigInt(payload), false);
    return new DataView(buffer).getFloat64(0, false);
  }
  if (tag === 's') return decodeString(payload);
  if (tag === 'i') return BigInt(payload);
  if (tag === 'y') return Symbol.for(`oracle-${payload}`);
  throw new Error(`invalid primitive descriptor: ${encoded}`);
}

function runOracle(queries: string[]): string[] {
  return execFileSync(oracle, queries, { cwd: leanRoot, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 })
    .trimEnd()
    .split('\n');
}

function expectOracle(queries: string[], expected: string[]): void {
  expect(runOracle(queries)).toEqual(expected);
}

function expectOracleChunked(queries: string[], expected: string[], chunkSize = 400): void {
  const actual: string[] = [];
  for (let index = 0; index < queries.length; index += chunkSize) {
    actual.push(...runOracle(queries.slice(index, index + chunkSize)));
  }
  expect(actual).toEqual(expected);
}

type RuntimeOperation = 'add' | 'sub' | 'mul' | 'div' | 'rem' | 'lt' | 'le' | 'gt' | 'ge';

function runtimeOperator(
  operation: RuntimeOperation,
  left: PrimitiveCase['value'],
  right: PrimitiveCase['value'],
): string {
  try {
    let result: PrimitiveCase['value'];
    switch (operation) {
      // These intentionally exercise JavaScript's runtime operators across incompatible unions.
      // @ts-expect-error Runtime differential boundary.
      case 'add': result = left + right; break;
      // @ts-expect-error Runtime differential boundary.
      case 'sub': result = left - right; break;
      // @ts-expect-error Runtime differential boundary.
      case 'mul': result = left * right; break;
      // @ts-expect-error Runtime differential boundary.
      case 'div': result = left / right; break;
      // @ts-expect-error Runtime differential boundary.
      case 'rem': result = left % right; break;
      // @ts-expect-error Runtime differential boundary.
      case 'lt': result = left < right; break;
      // @ts-expect-error Runtime differential boundary.
      case 'le': result = left <= right; break;
      // @ts-expect-error Runtime differential boundary.
      case 'gt': result = left > right; break;
      // @ts-expect-error Runtime differential boundary.
      case 'ge': result = left >= right; break;
    }
    if (typeof result === 'number') return numberResult(result);
    if (typeof result === 'bigint') return `bigint:${result}`;
    if (typeof result === 'string') return stringResult(result);
    if (typeof result === 'boolean') return `boolean:${result}`;
    return `unexpected:${String(result)}`;
  } catch (error) {
    return `error:${error instanceof Error ? error.name : 'Thrown'}`;
  }
}

beforeAll(() => {
  execFileSync('lake', ['build', 'js-primitive-oracle'], { cwd: leanRoot, stdio: 'pipe' });
});

describe('isolated ECMAScript primitive semantics', () => {
  it('differentially parses StringNumericValue including every trim code unit', () => {
    const whitespace = [
      0x0009, 0x000a, 0x000b, 0x000c, 0x000d, 0x0020, 0x00a0, 0x1680, 0x2000, 0x2001,
      0x2002, 0x2003, 0x2004, 0x2005, 0x2006, 0x2007, 0x2008, 0x2009, 0x200a, 0x2028,
      0x2029, 0x202f, 0x205f, 0x3000, 0xfeff,
    ];
    const malformed = [
      '+', '-', '.', '+.', '1e', '1e+', '1e-', '.e1', '1x', '1 2', 'Infinityx',
      'NaN', 'nan', '+0x1', '-0x1', '0x', '0o8', '0b2', '0x1p2', '1_0', '\ud800', '1\udfff',
    ];
    const valid = [
      '', ' ', '0', '-0', '+0', '1', '-1', '.5', '1.', '1.25', '1e3', '1E-3', '+Infinity',
      '-Infinity', '0x10', '0Xffffffffffffffff', '0o777', '0b101010', '1e309', '-1e309',
      '1e-324', '5e-324', '2.2250738585072014e-308', '1.7976931348623157e308',
      '9007199254740991', '9007199254740992', '9007199254740993',
      '2.2250738585072011e-308', '2.2250738585072012e-308', '1.00000000000000011102230246251565404236316680908203125',
    ];
    const strings = [
      ...valid,
      ...malformed,
      ...whitespace.flatMap((unit) => [String.fromCharCode(unit), `${String.fromCharCode(unit)}1${String.fromCharCode(unit)}`]),
    ];
    let state = 0x6d2b79f5;
    for (let index = 0; index < 220; index += 1) {
      state = (Math.imul(state ^ (state >>> 15), 1 | state) + index) | 0;
      const sign = state & 1 ? '-' : '';
      const integer = String(Math.abs(state % 1_000_000));
      const fraction = String(Math.abs(Math.imul(state, 2654435761) % 1_000_000)).padStart(6, '0');
      const exponent = (state % 700) - 350;
      strings.push(`${sign}${integer}.${fraction}e${exponent}`);
    }
    expectOracle(
      strings.map((value) => `parse/${encodeString(value)}`),
      strings.map((value) => numberResult(Number(value))),
    );
  });

  it('differentially formats finite and exceptional binary64 values', () => {
    const bits = [
      0n, 0x8000000000000000n, 0x7ff0000000000000n, 0xfff0000000000000n,
      canonicalNaN, 0x7ff0000000000001n, 0xfff8000000000042n,
      1n, 0x000fffffffffffffn, 0x0010000000000000n, 0x7fefffffffffffffn,
      numberBits(1e-7), numberBits(1e-6), numberBits(1e20), numberBits(1e21),
      numberBits(9007199254740991), numberBits(9007199254740992), numberBits(0.1),
    ];
    let state = 0x123456789abcdef0n;
    for (let index = 0; index < 260; index += 1) {
      state ^= state << 13n;
      state ^= state >> 7n;
      state ^= state << 17n;
      const candidate = BigInt.asUintN(64, state);
      const exponent = candidate & 0x7ff0000000000000n;
      if (exponent !== 0x7ff0000000000000n) bits.push(candidate);
    }
    const values = bits.map((value) => {
      const buffer = new ArrayBuffer(8);
      new DataView(buffer).setBigUint64(0, value, false);
      return new DataView(buffer).getFloat64(0, false);
    });
    expectOracle(
      bits.map((value) => `format/${value}`),
      values.map((value) => stringResult(String(value))),
    );
  });

  it('differentially checks coercion and the finite primitive loose-equality matrix', () => {
    const sharedSymbol = Symbol('shared');
    const values = [
      primitive('u', undefined), primitive('n', null), primitive('f', false), primitive('t', true),
      primitive(`d:${numberBits(0)}`, 0), primitive(`d:${numberBits(-0)}`, -0),
      primitive(`d:${numberBits(1)}`, 1), primitive(`d:${numberBits(1.5)}`, 1.5),
      primitive(`d:${numberBits(Number.NaN)}`, Number.NaN),
      primitive('s:_', ''), primitive(`s:${encodeString('0')}`, '0'),
      primitive(`s:${encodeString('1')}`, '1'), primitive(`s:${encodeString('0x10')}`, '0x10'),
      primitive(`s:${encodeString('\ud800')}`, '\ud800'), primitive('i:0', 0n), primitive('i:1', 1n),
      primitive('i:9007199254740992', 9007199254740992n),
      primitive('i:9007199254740993', 9007199254740993n), primitive('y:1', sharedSymbol),
      primitive('y:1', sharedSymbol),
      primitive('y:2', Symbol('other')),
    ];
    const numberQueries = values.map(({ encoded }) => `number/${encoded}`);
    const numberExpected = values.map(({ value }) => {
      if (typeof value === 'bigint' || typeof value === 'symbol') return 'error:TypeError';
      return numberResult(Number(value));
    });
    const stringQueries = values.map(({ encoded }) => `string/${encoded}`);
    const stringExpected = values.map(({ value }) =>
      typeof value === 'symbol' ? 'error:TypeError' : stringResult(String(value)),
    );
    const keyQueries = values.map(({ encoded }) => `key/${encoded}`);
    const keyExpected = values.map(({ encoded, value }) =>
      typeof value === 'symbol' ? `symbol:${encoded.slice(2)}` : stringResult(String(value)),
    );
    const looseQueries: string[] = [];
    const looseExpected: string[] = [];
    for (const left of values) {
      for (const right of values) {
        looseQueries.push(`loose/${left.encoded}/${right.encoded}`);
        // eslint-disable-next-line eqeqeq
        looseExpected.push(`boolean:${left.value == right.value}`);
      }
    }
    expectOracle(
      [...numberQueries, ...stringQueries, ...keyQueries, ...looseQueries],
      [...numberExpected, ...stringExpected, ...keyExpected, ...looseExpected],
    );
  });

  it('differentially checks runtime primitive operators and error categories', () => {
    const cases: Array<[RuntimeOperation, PrimitiveCase, PrimitiveCase]> = [
      ['add', primitive('s:120', 'x'), primitive(`d:${numberBits(1)}`, 1)],
      ['add', primitive('t', true), primitive('n', null)],
      ['add', primitive('s:_', ''), primitive('i:42', 42n)],
      ['add', primitive('i:1', 1n), primitive('i:2', 2n)],
      ['sub', primitive(`s:${encodeString('5')}`, '5'), primitive('t', true)],
      ['sub', primitive('i:-5', -5n), primitive('i:2', 2n)],
      ['mul', primitive(`d:${numberBits(-0)}`, -0), primitive(`d:${numberBits(3)}`, 3)],
      ['mul', primitive('i:-5', -5n), primitive('i:2', 2n)],
      ['div', primitive(`d:${numberBits(1)}`, 1), primitive(`d:${numberBits(0)}`, 0)],
      ['div', primitive('i:-5', -5n), primitive('i:2', 2n)],
      ['div', primitive('i:1', 1n), primitive('i:0', 0n)],
      ['rem', primitive(`d:${numberBits(-5)}`, -5), primitive(`d:${numberBits(2)}`, 2)],
      ['rem', primitive('i:-5', -5n), primitive('i:2', 2n)],
      ['lt', primitive(`s:${encodeString('a')}`, 'a'), primitive(`s:${encodeString('b')}`, 'b')],
      ['lt', primitive(`s:${encodeString('2')}`, '2'), primitive(`d:${numberBits(10)}`, 10)],
      ['lt', primitive(`d:${numberBits(9007199254740992)}`, 9007199254740992),
        primitive('i:9007199254740993', 9007199254740993n)],
      ['lt', primitive(`s:${encodeString('1.5')}`, '1.5'), primitive('i:2', 2n)],
      ['le', primitive('i:9007199254740992', 9007199254740992n),
        primitive(`d:${numberBits(9007199254740992)}`, 9007199254740992)],
      ['gt', primitive(`d:${numberBits(1.5)}`, 1.5), primitive('i:1', 1n)],
      ['ge', primitive('i:-9007199254740993', -9007199254740993n),
        primitive(`d:${numberBits(-9007199254740992)}`, -9007199254740992)],
      ['add', primitive('i:1', 1n), primitive(`d:${numberBits(1)}`, 1)],
      ['add', primitive('y:1', Symbol('x')), primitive('s:120', 'x')],
      ['add', primitive('y:1', Symbol('x')), primitive(`d:${numberBits(1)}`, 1)],
    ];
    const expected = cases.map(([operation, left, right]) =>
      runtimeOperator(operation, decodePrimitive(left.encoded), decodePrimitive(right.encoded)),
    );
    expectOracle(cases.map(([operation, left, right]) => `${operation}/${left.encoded}/${right.encoded}`), expected);
  });

  it('catches the previous BigInt arithmetic defect adversarially', () => {
    const cases: Array<[RuntimeOperation, PrimitiveCase, PrimitiveCase]> = [
      ['add', primitive('i:1', 1n), primitive('i:2', 2n)],
      ['div', primitive('i:-5', -5n), primitive('i:2', 2n)],
      ['rem', primitive('i:-5', -5n), primitive('i:2', 2n)],
      ['div', primitive('i:1', 1n), primitive('i:0', 0n)],
      ['add', primitive('i:1', 1n), primitive(`d:${numberBits(1)}`, 1)],
    ];
    const expected = cases.map(([operation, left, right]) =>
      runtimeOperator(operation, decodePrimitive(left.encoded), decodePrimitive(right.encoded)),
    );
    expect(expected).toEqual(['bigint:3', 'bigint:-2', 'bigint:-1', 'error:RangeError', 'error:TypeError']);
    expectOracle(cases.map(([operation, left, right]) => `${operation}/${left.encoded}/${right.encoded}`), expected);
  });

  it('differentially fuzzes thousands of runtime operator applications', () => {
    const operations: RuntimeOperation[] = ['add', 'sub', 'mul', 'div', 'rem', 'lt', 'le', 'gt', 'ge'];
    const strings = ['', '0', '-1', '1.5', '0x10', '9007199254740993', 'not-a-number', '\ud800'];
    let state = 0x9e3779b97f4a7c15n;
    const next = (): bigint => {
      state ^= state << 13n;
      state ^= state >> 7n;
      state ^= state << 17n;
      state = BigInt.asUintN(64, state);
      return state;
    };
    const sample = (): PrimitiveCase => {
      const tag = Number(next() % 8n);
      if (tag === 0) return primitive('u', undefined);
      if (tag === 1) return primitive('n', null);
      if (tag === 2) {
        const value = Boolean(next() & 1n);
        return primitive(value ? 't' : 'f', value);
      }
      if (tag === 3) {
        const bits = next();
        const buffer = new ArrayBuffer(8);
        new DataView(buffer).setBigUint64(0, bits, false);
        return primitive(`d:${bits}`, new DataView(buffer).getFloat64(0, false));
      }
      if (tag === 4 || tag === 5) {
        const magnitude = (next() << 128n) | (next() << 64n) | next();
        const value = next() & 1n ? magnitude : -magnitude;
        return primitive(`i:${value}`, value);
      }
      if (tag === 6) {
        const value = strings[Number(next() % BigInt(strings.length))];
        return primitive(`s:${encodeString(value)}`, value);
      }
      const id = Number(next() % 8n);
      return primitive(`y:${id}`, Symbol.for(`fuzz-${id}`));
    };
    const queries: string[] = [];
    const expected: string[] = [];
    for (let index = 0; index < 6000; index += 1) {
      const operation = operations[Number(next() % BigInt(operations.length))];
      const left = sample();
      const right = sample();
      queries.push(`${operation}/${left.encoded}/${right.encoded}`);
      expected.push(runtimeOperator(operation, decodePrimitive(left.encoded), decodePrimitive(right.encoded)));
    }
    expectOracleChunked(queries, expected);
  });
});
