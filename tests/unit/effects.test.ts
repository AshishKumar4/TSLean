// Unit tests for effect inference and the effect algebra.

import { describe, it, expect } from 'vitest';
import * as ts from 'typescript';
import {
  Pure, IO, Async,
  stateEffect, exceptEffect, combineEffects,
  isPure, hasAsync, hasState, hasExcept, hasIO,
  TyString, TyFloat, TyNat, TyUnit,
  Effect,
} from '../../src/ir/types.js';
import { inferNodeEffect, monadString, joinEffects, effectSubsumes, doMonadType } from '../../src/effects/index.js';

// ─── Helper ───────────────────────────────────────────────────────────────────

function inferFrom(src: string): Effect {
  const opts: ts.CompilerOptions = { strict: true, target: ts.ScriptTarget.ES2022, skipLibCheck: true };
  const host = ts.createCompilerHost(opts);
  const prog = ts.createProgram({
    rootNames: ['t.ts'], options: opts,
    host: {
      ...host,
      getSourceFile: (n, v) => n === 't.ts' ? ts.createSourceFile(n, src, v, true) : host.getSourceFile(n, v),
      fileExists: f => f === 't.ts' || host.fileExists(f),
      readFile: f => f === 't.ts' ? src : host.readFile(f),
    },
  });
  const checker = prog.getTypeChecker();
  const sf = prog.getSourceFile('t.ts')!;
  return inferNodeEffect(sf.statements[0], checker);
}

// ─── Pure functions ───────────────────────────────────────────────────────────

describe('inferNodeEffect: pure functions', () => {
  it('arithmetic → Pure',           () => expect(isPure(inferFrom('function add(a: number, b: number) { return a + b; }'))).toBe(true));
  it('string concat → Pure',        () => expect(isPure(inferFrom('function hi(n: string) { return "Hello " + n; }'))).toBe(true));
  it('early return conditional → Pure', () => expect(isPure(inferFrom('function abs(n: number) { if (n < 0) return -n; return n; }'))).toBe(true));
  it('recursive → Pure',            () => expect(isPure(inferFrom('function fact(n: number): number { if (n <= 1) return 1; return n * fact(n-1); }'))).toBe(true));
  it('empty body → Pure',           () => expect(isPure(inferFrom('function noop(): void {}'))).toBe(true));
  it('boolean expr → Pure',         () => expect(isPure(inferFrom('function pos(n: number): boolean { return n > 0; }'))).toBe(true));
  it('object literal → Pure',       () => expect(isPure(inferFrom('function mk(x: number) { return { x, y: 0 }; }'))).toBe(true));
});

// ─── Throw → Except ───────────────────────────────────────────────────────────

describe('inferNodeEffect: throw → Except', () => {
  it('unconditional throw → non-Pure', () =>
    expect(isPure(inferFrom('function fail(): never { throw new Error("oops"); }'))).toBe(false));
  it('conditional throw → non-Pure', () =>
    expect(isPure(inferFrom('function div(a: number, b: number) { if (b === 0) throw new Error(); return a / b; }'))).toBe(false));
  it('try-catch outer stays manageable', () =>
    expect(inferFrom('function safe() { try { return 1; } catch { return 0; } }')).toBeDefined());
});

// ─── Async/await → Async ──────────────────────────────────────────────────────

describe('inferNodeEffect: async/await → Async', () => {
  it('await → Async', () =>
    expect(hasAsync(inferFrom('async function f(u: string): Promise<string> { const r = await Promise.resolve(u); return r; }'))).toBe(true));
  it('non-async → no Async', () =>
    expect(hasAsync(inferFrom('function id(x: string): string { return x; }'))).toBe(false));
  it('async without await → may be Pure (body has no await)',
    () => expect(inferFrom('async function f(): Promise<number> { return 1; }')).toBeDefined());
});

// ─── Mutations → State ────────────────────────────────────────────────────────

describe('inferNodeEffect: mutations → State', () => {
  it('assignment to property → non-Pure', () =>
    expect(isPure(inferFrom('function bump(obj: { n: number }): void { obj.n = obj.n + 1; }'))).toBe(false));
  it('++ operator → non-Pure', () =>
    expect(isPure(inferFrom('function inc(a: number[]): void { a[0]++; }'))).toBe(false));
  it('pure function stays Pure', () =>
    expect(isPure(inferFrom('function double(n: number): number { return n * 2; }'))).toBe(true));
  it('+= operator → non-Pure', () =>
    expect(isPure(inferFrom('function grow(x: { v: number }): void { x.v += 1; }'))).toBe(false));
});

// ─── IO effects ──────────────────────────────────────────────────────────────

describe('inferNodeEffect: IO', () => {
  it('console.log → IO (non-Pure)', () =>
    expect(isPure(inferFrom('function log(m: string): void { console.log(m); }'))).toBe(false));
  it('Date.now() → IO (non-Pure)', () =>
    expect(isPure(inferFrom('function now(): number { return Date.now(); }'))).toBe(false));
  it('Math.floor → Pure', () =>
    expect(isPure(inferFrom('function fl(x: number): number { return Math.floor(x); }'))).toBe(true));
  it('Math.max → Pure', () =>
    expect(isPure(inferFrom('function m(a: number, b: number): number { return Math.max(a,b); }'))).toBe(true));
});

// ─── monadString ─────────────────────────────────────────────────────────────

describe('monadString', () => {
  it('Pure → Id',           () => expect(monadString(Pure)).toBe('Id'));
  it('IO → IO',             () => expect(monadString(IO)).toBe('IO'));
  it('Async → IO',          () => expect(monadString(Async)).toBe('IO'));
  it('State String → StateT String IO', () => {
    const s = monadString(stateEffect(TyString));
    expect(s).toBe('StateT String IO');
  });
  it('Except String → ExceptT String IO', () => {
    const s = monadString(exceptEffect(TyString));
    expect(s).toBe('ExceptT String IO');
  });
  it('State+Except → StateT S (ExceptT E IO)', () => {
    const s = monadString(combineEffects([stateEffect(TyString), exceptEffect(TyFloat)]));
    expect(s).toBe('StateT String (ExceptT Float IO)');
  });
  it('State+Async → StateT Nat IO', () => {
    const s = monadString(combineEffects([stateEffect(TyNat), Async]));
    expect(s).toContain('StateT');
    expect(s).toContain('IO');
    expect(s).not.toContain('(IO)');
  });
  it('no (IO) wrapping in any case', () => {
    const cases = [
      stateEffect(TyString),
      exceptEffect(TyFloat),
      combineEffects([stateEffect(TyString), exceptEffect(TyFloat)]),
      combineEffects([stateEffect(TyNat), Async]),
    ];
    for (const e of cases) {
      expect(monadString(e)).not.toContain('(IO)');
    }
  });
  it('doMonadType → DOMonad X', () => {
    expect(doMonadType('CounterState')).toContain('DOMonad');
    expect(doMonadType('CounterState')).toContain('CounterState');
  });
});

// ─── Effect algebra ───────────────────────────────────────────────────────────

describe('combineEffects: algebra', () => {
  it('[] → Pure',              () => expect(combineEffects([])).toEqual(Pure));
  it('[Pure] → Pure',          () => expect(combineEffects([Pure])).toEqual(Pure));
  it('[IO] → IO',              () => expect(combineEffects([IO])).toEqual(IO));
  it('[Pure, IO] → IO',        () => expect(combineEffects([Pure, IO])).toEqual(IO));
  it('[IO, Pure] → IO',        () => expect(combineEffects([IO, Pure])).toEqual(IO));
  it('[IO, IO] → IO (dedup)',  () => expect(combineEffects([IO, IO])).toEqual(IO));
  it('[Async, Async] → Async', () => expect(combineEffects([Async, Async])).toEqual(Async));
  it('[IO, Async] → Combined', () => expect(combineEffects([IO, Async]).tag).toBe('Combined'));
  it('Pure is identity (left)',  () => {
    const e = stateEffect(TyString);
    expect(combineEffects([Pure, e])).toEqual(e);
  });
  it('Pure is identity (right)', () => {
    const e = stateEffect(TyString);
    expect(combineEffects([e, Pure])).toEqual(e);
  });
  it('nested Combined flattened', () => {
    const inner = combineEffects([IO, Async]);
    const outer = combineEffects([inner, stateEffect(TyNat)]);
    expect(outer.tag).toBe('Combined');
    if (outer.tag === 'Combined') {
      expect(outer.effects.every(e => e.tag !== 'Combined')).toBe(true);
    }
  });
});

describe('joinEffects', () => {
  it('Pure ⊔ IO = IO',    () => expect(joinEffects(Pure, IO)).toEqual(IO));
  it('IO ⊔ Pure = IO',    () => expect(joinEffects(IO, Pure)).toEqual(IO));
  it('Pure ⊔ Pure = Pure', () => expect(joinEffects(Pure, Pure)).toEqual(Pure));
  it('IO ⊔ IO = IO',      () => expect(joinEffects(IO, IO)).toEqual(IO));
  it('IO ⊔ Async = Combined', () => expect(joinEffects(IO, Async).tag).toBe('Combined'));
});

describe('effectSubsumes', () => {
  it('anything subsumes Pure', () => {
    expect(effectSubsumes(IO, Pure)).toBe(true);
    expect(effectSubsumes(Async, Pure)).toBe(true);
    expect(effectSubsumes(Pure, Pure)).toBe(true);
  });
  it('Pure does NOT subsume IO', () => expect(effectSubsumes(Pure, IO)).toBe(false));
  it('IO subsumes IO',           () => expect(effectSubsumes(IO, IO)).toBe(true));
  it('Combined subsumes members', () => {
    const e = combineEffects([IO, Async]);
    expect(effectSubsumes(e, IO)).toBe(true);
    expect(effectSubsumes(e, Async)).toBe(true);
  });
});

describe('effect predicates', () => {
  it('isPure(Pure)',          () => expect(isPure(Pure)).toBe(true));
  it('!isPure(IO)',           () => expect(isPure(IO)).toBe(false));
  it('hasAsync(Async)',       () => expect(hasAsync(Async)).toBe(true));
  it('!hasAsync(IO)',         () => expect(hasAsync(IO)).toBe(false));
  it('hasAsync in Combined',  () => expect(hasAsync(combineEffects([IO, Async]))).toBe(true));
  it('hasState(stateEffect)', () => expect(hasState(stateEffect(TyString))).toBe(true));
  it('!hasState(IO)',         () => expect(hasState(IO)).toBe(false));
  it('hasExcept(exceptEffect)', () => expect(hasExcept(exceptEffect(TyString))).toBe(true));
  it('!hasExcept(IO)',        () => expect(hasExcept(IO)).toBe(false));
  it('hasIO(IO)',             () => expect(hasIO(IO)).toBe(true));
  it('!hasIO(Pure)',          () => expect(hasIO(Pure)).toBe(false));
});
