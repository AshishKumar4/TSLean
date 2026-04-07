// Tests for the parser (TypeScript compiler API → IR).

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import { parseFile } from '../src/parser/index.js';
import { IRModule, IRDecl, hasAsync } from '../src/ir/types.js';

const FIX = path.join(process.cwd(), 'tests/fixtures');
const parse = (rel: string) => parseFile({ fileName: path.join(FIX, rel) });

function find(mod: IRModule, name: string): IRDecl | undefined {
  function search(ds: IRDecl[]): IRDecl | undefined {
    for (const d of ds) {
      if ('name' in d && d.name === name) return d;
      if (d.tag === 'Namespace') { const f = search(d.decls); if (f) return f; }
    }
  }
  return search(mod.decls);
}

// ─── basic/hello.ts ───────────────────────────────────────────────────────────

describe('Parser: basic/hello.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('basic/hello.ts'); });

  it('produces a module',   () => { expect(mod).toBeDefined(); expect(mod.decls.length).toBeGreaterThan(0); });
  it('parses greet',        () => { const d = find(mod, 'greet'); expect(d?.tag).toBe('FuncDef'); if (d?.tag === 'FuncDef') { expect(d.params[0].name).toBe('name'); expect(d.retType.tag).toBe('String'); } });
  it('parses add (2 params)', () => { const d = find(mod, 'add'); if (d?.tag === 'FuncDef') expect(d.params).toHaveLength(2); });
  it('parses isPositive → Bool', () => { const d = find(mod, 'isPositive'); if (d?.tag === 'FuncDef') expect(d.retType.tag).toBe('Bool'); });
  it('parses factorial',    () => { expect(find(mod, 'factorial')?.tag).toBe('FuncDef'); });
  it('parses PI constant',  () => { expect(find(mod, 'PI')).toBeDefined(); });
  it('no TS syntax leaks',  () => expect(mod.decls.some(d => d.tag === 'RawLean')).toBe(false));
});

// ─── basic/interfaces.ts ──────────────────────────────────────────────────────

describe('Parser: basic/interfaces.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('basic/interfaces.ts'); });

  it('Point → StructDef', () => {
    const d = find(mod, 'Point');
    expect(d?.tag).toBe('StructDef');
    if (d?.tag === 'StructDef') {
      const names = d.fields.map(f => f.name);
      expect(names).toContain('x');
      expect(names).toContain('y');
    }
  });
  it('Rectangle → StructDef', () => expect(find(mod, 'Rectangle')?.tag).toBe('StructDef'));
  it('Named has optional description', () => {
    const d = find(mod, 'Named');
    if (d?.tag === 'StructDef') {
      const desc = d.fields.find(f => f.name === 'description');
      expect(['Option', 'String']).toContain(desc?.type.tag);
    }
  });
  it('distance has 2 Point params', () => {
    const d = find(mod, 'distance');
    if (d?.tag === 'FuncDef') expect(d.params).toHaveLength(2);
  });
});

// ─── basic/classes.ts ─────────────────────────────────────────────────────────

describe('Parser: basic/classes.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('basic/classes.ts'); });

  it('Counter state struct emitted', () => {
    const d = mod.decls.find(d => d.tag === 'StructDef' && d.name === 'CounterState');
    expect(d).toBeDefined();
  });
  it('increment method defined', () => expect(find(mod, 'increment')).toBeDefined());
  it('BankAccount.deposit defined', () => expect(find(mod, 'deposit')).toBeDefined());
  it('BankAccount.withdraw defined', () => expect(find(mod, 'withdraw')).toBeDefined());
});

// ─── generics/discriminated-unions.ts ────────────────────────────────────────

describe('Parser: generics/discriminated-unions.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('generics/discriminated-unions.ts'); });

  it('Shape → InductiveDef with Circle/Rectangle/Triangle', () => {
    const d = find(mod, 'Shape');
    expect(d?.tag).toBe('InductiveDef');
    if (d?.tag === 'InductiveDef') {
      const names = d.ctors.map(c => c.name);
      expect(names).toContain('Circle');
      expect(names).toContain('Rectangle');
      expect(names).toContain('Triangle');
    }
  });
  it('Color → InductiveDef', () => expect(find(mod, 'Color')?.tag).toBe('InductiveDef'));
  it('Tree has type param', () => {
    const d = find(mod, 'Tree');
    if (d?.tag === 'InductiveDef') expect(d.typeParams.length).toBeGreaterThanOrEqual(1);
  });
  it('areaShape is FuncDef', () => expect(find(mod, 'areaShape')?.tag).toBe('FuncDef'));
});

// ─── generics/branded-types.ts ────────────────────────────────────────────────

describe('Parser: generics/branded-types.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('generics/branded-types.ts'); });

  it('UserId → branded StructDef or TypeDef', () => {
    const d = find(mod, 'UserId');
    expect(d).toBeDefined();
    expect(['StructDef', 'TypeAlias']).toContain(d?.tag);
  });
  it('RoomId defined',          () => expect(find(mod, 'RoomId')).toBeDefined());
  it('makeUserId → FuncDef',    () => expect(find(mod, 'makeUserId')?.tag).toBe('FuncDef'));
  it('UserProfile → StructDef', () => expect(find(mod, 'UserProfile')?.tag).toBe('StructDef'));
});

// ─── effects/async.ts ─────────────────────────────────────────────────────────

describe('Parser: effects/async.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('effects/async.ts'); });

  it('fetchUser is FuncDef', () => expect(find(mod, 'fetchUser')?.tag).toBe('FuncDef'));
  it('fetchUser has Async effect', () => {
    const d = find(mod, 'fetchUser');
    if (d?.tag === 'FuncDef') expect(hasAsync(d.effect)).toBe(true);
  });
  it('withRetry has type param', () => {
    const d = find(mod, 'withRetry');
    if (d?.tag === 'FuncDef') expect(d.typeParams.length).toBeGreaterThanOrEqual(1);
  });
});

// ─── effects/exceptions.ts ───────────────────────────────────────────────────

describe('Parser: effects/exceptions.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('effects/exceptions.ts'); });

  it('parseAge → FuncDef',     () => expect(find(mod, 'parseAge')?.tag).toBe('FuncDef'));
  it('divide → FuncDef',       () => expect(find(mod, 'divide')?.tag).toBe('FuncDef'));
  it('safeDivide → FuncDef',   () => expect(find(mod, 'safeDivide')?.tag).toBe('FuncDef'));
  it('validateEmail → FuncDef', () => expect(find(mod, 'validateEmail')?.tag).toBe('FuncDef'));
});

// ─── DO detection ─────────────────────────────────────────────────────────────

describe('Parser: DO detection', () => {
  it('counter.ts has DO imports', () => {
    const mod = parse('durable-objects/counter.ts');
    expect(mod.imports.some(i => i.module.includes('DurableObjects'))).toBe(true);
  });
  it('auth-do.ts has DO imports', () => {
    const mod = parse('durable-objects/auth-do.ts');
    expect(mod.imports.some(i => i.module.includes('DurableObjects'))).toBe(true);
  });
  it('hello.ts has no DO imports', () => {
    const mod = parse('basic/hello.ts');
    expect(mod.imports.some(i => i.module.includes('DurableObjects'))).toBe(false);
  });
});

// ─── Inline source parsing ────────────────────────────────────────────────────

describe('Parser: inline source', () => {
  it('parses const declarations', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'const x: number = 42;\nconst s = "hello";' });
    expect(mod.decls.length).toBeGreaterThanOrEqual(1);
  });

  it('parses enum', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'enum Dir { North, South, East, West }' });
    const d = mod.decls.find(d => d.tag === 'InductiveDef' && d.name === 'Dir');
    expect(d).toBeDefined();
    if (d?.tag === 'InductiveDef') {
      const names = d.ctors.map(c => c.name);
      expect(names).toContain('North');
      expect(names).toContain('South');
    }
  });

  it('parses namespace', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'namespace Utils { function id<T>(x: T): T { return x; } }' });
    const d = mod.decls.find(d => d.tag === 'Namespace' && d.name === 'Utils');
    expect(d).toBeDefined();
  });

  it('parses template literal', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'function greet(n: string): string { return `Hello, ${n}!`; }' });
    const d = mod.decls.find(d => d.tag === 'FuncDef' && d.name === 'greet');
    expect(d?.tag).toBe('FuncDef');
  });

  it('detects DO pattern in inline source', () => {
    const mod = parseFile({ fileName: 'do.ts', sourceText: 'class MyDO { state: DurableObjectState; constructor(state: DurableObjectState, env: Env) { this.state = state; } }' });
    expect(mod.imports.some(i => i.module.includes('DurableObjects'))).toBe(true);
  });

  it('parses for-loop', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'function sum(n: number): number { let t = 0; for (let i = 0; i < n; i++) { t += i; } return t; }' });
    const d = mod.decls.find(d => d.tag === 'FuncDef' && d.name === 'sum');
    expect(d?.tag).toBe('FuncDef');
  });

  it('parses while loop', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'function cd(n: number): number { let x = n; while (x > 0) { x = x - 1; } return x; }' });
    const d = mod.decls.find(d => d.tag === 'FuncDef' && d.name === 'cd');
    expect(d?.tag).toBe('FuncDef');
  });

  it('parses try-catch', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'function safe(): number { try { return 1; } catch(e) { return 0; } }' });
    const d = mod.decls.find(d => d.tag === 'FuncDef');
    expect(d).toBeDefined();
  });
});
