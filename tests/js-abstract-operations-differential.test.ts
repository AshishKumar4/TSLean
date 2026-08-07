import { execFileSync } from 'node:child_process';
import { resolve } from 'node:path';
import { beforeAll, describe, expect, it } from 'vitest';

const root = resolve(import.meta.dirname, '..');
const leanRoot = resolve(root, 'lean');
const oracle = resolve(leanRoot, '.lake/build/bin/js-abstract-operations-oracle');
const canonicalNaN = 0x7ff8000000000000n;

type JSValue = undefined | null | boolean | number | string | bigint | symbol | object;

function numberBits(value: number): bigint {
  if (Number.isNaN(value)) return canonicalNaN;
  const buffer = new ArrayBuffer(8);
  new DataView(buffer).setFloat64(0, value, false);
  return new DataView(buffer).getBigUint64(0, false);
}

function encode(value: JSValue): string {
  if (typeof value === 'number') return `number:${numberBits(value)}`;
  if (typeof value === 'symbol') return 'symbol';
  if (typeof value === 'object' && value !== null) return 'object';
  return `${typeof value}:${value}`;
}

function capture(action: () => JSValue, trace: string[]): string {
  try {
    return `${encode(action())}|${trace.join(',')}`;
  } catch (error) {
    let result: string;
    if (error instanceof Error) result = `error:${error.name}`;
    else if (typeof error === 'string') result = `throw:string:${error}`;
    else if (typeof error === 'bigint') result = `throw:bigint:${error}`;
    else if (typeof error === 'number') result = `throw:number:${numberBits(error)}`;
    else if (typeof error === 'boolean') result = `throw:boolean:${error}`;
    else if (typeof error === 'symbol') result = 'throw:symbol';
    else if (error === undefined) result = 'throw:undefined';
    else if (error === null) result = 'throw:null';
    else result = 'throw:object';
    return `${result}|${trace.join(',')}`;
  }
}

function add(left: JSValue, right: JSValue): JSValue {
  // @ts-expect-error Deliberate runtime operator differential over the complete value union.
  return left + right;
}

function loose(left: JSValue, right: JSValue): boolean {
  // @ts-expect-error Deliberate runtime loose-equality differential.
  return left == right;
}

function less(left: JSValue, right: JSValue): boolean {
  // @ts-expect-error Deliberate runtime relational differential.
  return left < right;
}

function greater(left: JSValue, right: JSValue): boolean {
  // @ts-expect-error Deliberate runtime relational differential.
  return left > right;
}

function lessEqual(left: JSValue, right: JSValue): boolean {
  // @ts-expect-error Deliberate runtime relational differential.
  return left <= right;
}

function greaterEqual(left: JSValue, right: JSValue): boolean {
  // @ts-expect-error Deliberate runtime relational differential.
  return left >= right;
}

function instanceOf(left: object, right: JSValue): boolean {
  // @ts-expect-error Deliberate runtime instanceof differential without a static RHS restriction.
  return left instanceof right;
}

function primitiveAndOperatorScenarios(): string[] {
  const trace: string[] = [];
  const make = (name: string, result: JSValue) => ({
    [Symbol.toPrimitive](hint: string) {
      trace.push(`${name}:${hint}`);
      return result;
    },
  });
  const run = (action: () => JSValue) => {
    trace.length = 0;
    return capture(action, trace);
  };
  const left = make('left', '5');
  const right = make('right', '7');
  const sameSymbol = Symbol('same');
  const symbolObject = make('left', sameSymbol);
  const objectResult = make('left', {});
  const throwingRight = {
    [Symbol.toPrimitive]() {
      trace.push('right');
      throw 88n;
    },
  };
  const throwingLeft = {
    [Symbol.toPrimitive]() {
      trace.push('left');
      return '5';
    },
  };
  const stringThrow = {
    [Symbol.toPrimitive]() {
      trace.push('string-throw');
      throw 'user-thrown';
    },
  };
  const rangeThrow = {
    [Symbol.toPrimitive]() {
      trace.push('range-throw');
      throw new RangeError('range');
    },
  };
  return [
    run(() => add(left, '')),
    run(() => Number(left)),
    run(() => String(left)),
    run(() => loose(left, '5')),
    run(() => loose(left, 5)),
    run(() => loose(left, 5n)),
    run(() => loose(left, true)),
    run(() => loose(left, false)),
    run(() => loose(left, null)),
    run(() => loose(left, undefined)),
    run(() => loose(left, sameSymbol)),
    run(() => loose(left, left)),
    run(() => loose(left, right)),
    run(() => loose(symbolObject, sameSymbol)),
    run(() => loose(symbolObject, Symbol('other'))),
    run(() => add(left, right)),
    run(() => less(left, right)),
    run(() => greater(right, left)),
    run(() => lessEqual(left, right)),
    run(() => greaterEqual(right, left)),
    run(() => less(right, left)),
    run(() => greater(left, right)),
    run(() => lessEqual(right, left)),
    run(() => greaterEqual(left, right)),
    run(() => add(objectResult, '')),
    run(() => add(throwingRight, '')),
    run(() => add(throwingLeft, throwingRight)),
    run(() => less(throwingLeft, throwingRight)),
    run(() => add(stringThrow, '')),
    run(() => add(rangeThrow, '')),
  ];
}

function getAndOrdinaryScenarios(): string[] {
  const run = (action: (trace: string[]) => JSValue) => {
    const trace: string[] = [];
    return capture(() => action(trace), trace);
  };
  const withMethod = (method: undefined | null | bigint, trace: string[]) => ({
    [Symbol.toPrimitive]: method,
    valueOf() {
      trace.push('valueOf');
      return 'value';
    },
  });
  const ordinary = (trace: string[]) => ({
    __proto__: {
      valueOf() {
        trace.push('valueOf');
        return this;
      },
      toString() {
        trace.push('toString');
        return 'ordinary';
      },
    },
  });
  return [
    run((trace) => add(withMethod(undefined, trace), '')),
    run((trace) => add(withMethod(null, trace), '')),
    run((trace) => add(withMethod(1n, trace), '')),
    run((trace) => Number(ordinary(trace))),
    run((trace) => String(ordinary(trace))),
    run((trace) => {
      const value = Object.create({ toString: () => 'unused' });
      Object.defineProperty(value, 'valueOf', {
        get() {
          trace.push('get');
          return () => {
            trace.push('call');
            return 'getter';
          };
        },
      });
      return add(value, '');
    }),
    run((trace) => {
      const value = {};
      Object.defineProperty(value, 'valueOf', {
        get() {
          trace.push('get');
          throw 17n;
        },
      });
      return add(value, '');
    }),
    run((trace) => {
      const value = {
        valueOf() {
          trace.push('valueOf');
          return {};
        },
        toString() {
          trace.push('toString');
          return {};
        },
      };
      return add(value, '');
    }),
  ];
}

function hasInstanceScenarios(): string[] {
  const run = (action: (trace: string[]) => JSValue) => {
    const trace: string[] = [];
    return capture(() => action(trace), trace);
  };
  const custom = (trace: string[], result: JSValue, methodThrows = false) => {
    const constructor = function () {};
    Object.defineProperty(constructor, Symbol.hasInstance, {
      configurable: true,
      get() {
        trace.push('get');
        return function () {
          trace.push('call');
          if (methodThrows) throw 73n;
          return result;
        };
      },
    });
    return constructor;
  };
  return [
    run((trace) => instanceOf({}, custom(trace, {}))),
    run((trace) => instanceOf({}, custom(trace, false))),
    run((trace) => {
      const constructor = function () {};
      Object.defineProperty(constructor, Symbol.hasInstance, {
        get() {
          trace.push('get');
          throw 72n;
        },
      });
      return instanceOf({}, constructor);
    }),
    run((trace) => instanceOf({}, custom(trace, false, true))),
    run(() => {
      const constructor = function () {};
      Object.defineProperty(constructor, Symbol.hasInstance, { value: 1 });
      return instanceOf({}, constructor);
    }),
    run(() => {
      const constructor = function () {};
      return instanceOf(Object.create(constructor.prototype), constructor);
    }),
    run(() => instanceOf({}, function () {})),
    run(() => instanceOf({}, {})),
    run(() => {
      const constructor = function () {};
      constructor.prototype = 1;
      return instanceOf({}, constructor);
    }),
    run(() => instanceOf({}, 1n)),
  ];
}

function realmAndCopyScenarios(): string[] {
  const run = (action: () => JSValue) => capture(action, []);
  const booleanWrapper = Object(true);
  const numberWrapper = Object(1);
  const stringWrapper = Object('box');
  const bigintWrapper = Object(9n);
  const symbol = Symbol();
  const symbolWrapper = Object(symbol);
  return [
    run(() => Number(booleanWrapper)),
    run(() => add(numberWrapper, 0)),
    run(() => String(numberWrapper)),
    run(() => add(stringWrapper, '')),
    run(() => String(stringWrapper)),
    run(() => add(bigintWrapper, 0n)),
    run(() => String(bigintWrapper)),
    run(() => symbolWrapper.valueOf()),
    run(() => symbolWrapper.toString()),
    run(() => loose(numberWrapper, 1)),
    run(() => Object.getPrototypeOf(booleanWrapper) === Boolean.prototype),
    run(() => Object.getPrototypeOf(numberWrapper) === Number.prototype),
    run(() => Object.getPrototypeOf(stringWrapper) === String.prototype),
    run(() => Object.getPrototypeOf(bigintWrapper) === BigInt.prototype),
    run(() => Object.getPrototypeOf(symbolWrapper) === Symbol.prototype),
    run(() => Object.getPrototypeOf(Object.assign(true)) === Boolean.prototype),
    run(() => {
      const result = Object.assign({}, 'ab');
      return `${result[0]}${result[1]}`;
    }),
    run(() => {
      const result = { ...'xy' };
      return `${result[0]}${result[1]}`;
    }),
    run(() => Reflect.ownKeys({ ...null, ...undefined, ...symbol }).length),
    run(() => Boolean.prototype.valueOf()),
    run(() => Boolean.prototype.toString()),
    run(() => Number.prototype.valueOf()),
    run(() => Number.prototype.toString()),
    run(() => String.prototype.valueOf()),
    run(() => String.prototype.toString()),
    run(() => BigInt.prototype.valueOf()),
    run(() => BigInt.prototype.toString()),
    run(() => Symbol.prototype.valueOf()),
    run(() => Symbol.prototype.toString()),
    run(() => {
      const original = Object.getPrototypeOf(Boolean.prototype);
      try {
        Object.setPrototypeOf(Boolean.prototype, null);
        return Object.getPrototypeOf(Object(true)) === Boolean.prototype;
      } finally {
        Object.setPrototypeOf(Boolean.prototype, original);
      }
    }),
    run(() => {
      const wrapper = Object(true);
      Object.setPrototypeOf(wrapper, null);
      return Object.getPrototypeOf(wrapper) === null;
    }),
  ];
}

function realmFuzzScenarios(): string[] {
  const symbol = Symbol('fuzz');
  const samples: JSValue[] = [false, 0, '0', 0n, true, 1, '1', 1n, symbol];
  return samples.flatMap((value, index) => {
    const wrapper = Object(value);
    return [
      capture(() => loose(wrapper, value), []),
      capture(() => loose(wrapper, samples[(index + 1) % samples.length]), []),
    ];
  });
}

beforeAll(() => {
  execFileSync('lake', ['build', 'js-abstract-operations-oracle'], { cwd: leanRoot, stdio: 'pipe' });
});

describe('Value-level ECMAScript abstract operations', () => {
  it('matches Node for the complete deterministic result and trace scenario set', () => {
    const expected = [
      ...primitiveAndOperatorScenarios(),
      ...getAndOrdinaryScenarios(),
      ...hasInstanceScenarios(),
      ...realmAndCopyScenarios(),
      ...realmFuzzScenarios(),
    ];
    const actual = execFileSync(oracle, [], { cwd: leanRoot, encoding: 'utf8' }).trimEnd().split('\n');
    expect(actual).toHaveLength(97);
    expect(actual).toEqual(expected);
  });

  it('is deterministic across repeated oracle executions', () => {
    const first = execFileSync(oracle, [], { cwd: leanRoot, encoding: 'utf8' });
    const second = execFileSync(oracle, [], { cwd: leanRoot, encoding: 'utf8' });
    expect(second).toBe(first);
  });
});
