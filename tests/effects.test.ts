// Tests for the effect system.

import { describe, it, expect } from 'vitest';
import * as ts from 'typescript';
import {
  Pure, IO, Async,
  stateEffect, exceptEffect, combineEffects,
  isPure, hasAsync, hasState, hasExcept,
  TyString, TyFloat, TyNat, TyUnit,
  Effect,
} from '../src/ir/types.js';
import { inferNodeEffect, monadString, joinEffects, effectSubsumes, doMonadType } from '../src/effects/index.js';

// ─── Helpers ──────────────────────────────────────────────────────────────────

function inferFrom(src: string): Effect {
  const opts: ts.CompilerOptions = { strict: true, target: ts.ScriptTarget.ES2022, skipLibCheck: true };
  const host = ts.createCompilerHost(opts);
  const prog = ts.createProgram({
    rootNames: ['test.ts'], options: opts,
    host: {
      ...host,
      getSourceFile: (n, v) => n === 'test.ts' ? ts.createSourceFile(n, src, v, true) : host.getSourceFile(n, v),
      fileExists: f => f === 'test.ts' || host.fileExists(f),
      readFile:   f => f === 'test.ts' ? src : host.readFile(f),
    },
  });
  const checker = prog.getTypeChecker();
  const sf      = prog.getSourceFile('test.ts')!;
  return inferNodeEffect(sf.statements[0], checker);
}

// ─── Effect inference from AST ────────────────────────────────────────────────

describe('inferNodeEffect – pure functions', () => {
  it('arithmetic → Pure',   () => expect(isPure(inferFrom('function add(a: number, b: number): number { return a + b; }'))).toBe(true));
  it('string concat → Pure',() => expect(isPure(inferFrom('function hi(n: string): string { return "Hello " + n; }'))).toBe(true));
  it('conditional → Pure',  () => expect(isPure(inferFrom('function abs(n: number): number { if (n < 0) return -n; return n; }'))).toBe(true));
  it('recursive → Pure',    () => expect(isPure(inferFrom('function fact(n: number): number { if (n <= 1) return 1; return n * fact(n-1); }'))).toBe(true));
  it('no body (decl) → Pure', () => expect(isPure(inferFrom('function noop(): void {}'))).toBe(true));
});

describe('inferNodeEffect – throw → Except', () => {
  it('unconditional throw → non-Pure', () =>
    expect(isPure(inferFrom('function fail(): never { throw new Error("oops"); }'))).toBe(false));
  it('conditional throw → non-Pure', () =>
    expect(isPure(inferFrom('function div(a: number, b: number): number { if (b === 0) throw new Error("div0"); return a / b; }'))).toBe(false));
});

describe('inferNodeEffect – mutations → State', () => {
  it('assignment → non-Pure', () =>
    expect(isPure(inferFrom('function bump(obj: { n: number }): void { obj.n = obj.n + 1; }'))).toBe(false));
  it('++ → non-Pure', () =>
    expect(isPure(inferFrom('function inc(a: number[]): void { a[0]++; }'))).toBe(false));
  it('pure function stays Pure', () =>
    expect(isPure(inferFrom('function double(n: number): number { return n * 2; }'))).toBe(true));
});

describe('inferNodeEffect – async/await → Async', () => {
  it('await → Async', () =>
    expect(hasAsync(inferFrom('async function f(u: string): Promise<string> { const r = await Promise.resolve(u); return r; }'))).toBe(true));
  it('non-async → no Async', () =>
    expect(hasAsync(inferFrom('function id(x: string): string { return x; }'))).toBe(false));
});

describe('inferNodeEffect – IO effects', () => {
  it('console.log → IO',   () => expect(isPure(inferFrom('function log(m: string): void { console.log(m); }'))).toBe(false));
  it('Date.now() → IO',    () => expect(isPure(inferFrom('function now(): number { return Date.now(); }'))).toBe(false));
  it('Math.floor → Pure',  () => expect(isPure(inferFrom('function fl(x: number): number { return Math.floor(x); }'))).toBe(true));
});

// ─── monadString ──────────────────────────────────────────────────────────────

describe('monadString', () => {
  it('Pure → Id',    () => expect(monadString(Pure)).toBe('Id'));
  it('IO → IO',      () => expect(monadString(IO)).toBe('IO'));
  it('Async → IO',   () => expect(monadString(Async)).toBe('IO'));

  it('State String → StateT String IO', () => {
    const s = monadString(stateEffect(TyString));
    expect(s).toContain('StateT'); expect(s).toContain('String'); expect(s).toContain('IO');
  });

  it('Except String → ExceptT String IO', () => {
    const s = monadString(exceptEffect(TyString));
    expect(s).toContain('ExceptT'); expect(s).toContain('String'); expect(s).toContain('IO');
  });

  it('Combined State+Except → transformer stack', () => {
    const s = monadString(combineEffects([stateEffect(TyString), exceptEffect(TyFloat)]));
    expect(s).toContain('StateT'); expect(s).toContain('ExceptT'); expect(s).toContain('IO');
  });

  it('doMonadType', () => {
    const s = doMonadType('CounterState');
    expect(s).toContain('DOMonad'); expect(s).toContain('CounterState');
  });
});

// ─── Effect lattice ───────────────────────────────────────────────────────────

describe('joinEffects', () => {
  it('Pure ⊔ IO = IO',    () => expect(joinEffects(Pure, IO)).toEqual(IO));
  it('IO ⊔ Pure = IO',    () => expect(joinEffects(IO, Pure)).toEqual(IO));
  it('Pure ⊔ Pure = Pure', () => expect(joinEffects(Pure, Pure)).toEqual(Pure));
  it('IO ⊔ Async = Combined', () => expect(joinEffects(IO, Async).tag).toBe('Combined'));
  it('IO ⊔ IO = IO',      () => expect(joinEffects(IO, IO)).toEqual(IO));
});

describe('effectSubsumes', () => {
  it('anything subsumes Pure',   () => { expect(effectSubsumes(IO, Pure)).toBe(true); expect(effectSubsumes(Async, Pure)).toBe(true); });
  it('Pure subsumes Pure',       () => expect(effectSubsumes(Pure, Pure)).toBe(true));
  it('Pure does NOT subsume IO', () => expect(effectSubsumes(Pure, IO)).toBe(false));
  it('IO subsumes IO',           () => expect(effectSubsumes(IO, IO)).toBe(true));
  it('Combined subsumes members', () => {
    const e = combineEffects([IO, Async]);
    expect(effectSubsumes(e, IO)).toBe(true);
    expect(effectSubsumes(e, Async)).toBe(true);
  });
});
