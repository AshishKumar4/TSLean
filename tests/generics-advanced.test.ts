// Phase 4: Comprehensive generics tests covering TypeParam, constraints,
// utility type resolution, and inexpressible type handling.

import { describe, it, expect } from 'vitest';
import { generateLean } from '../src/codegen/index.js';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import {
  IRModule, tp, IRDecl,
  TyString, TyNat, TyBool, TyFloat, TyUnit, TyRef, TyArray, TyOption, TyVar,
  Pure, IO,
  litNat, litStr, litBool, varExpr,
  TypeParam,
} from '../src/ir/types.js';
import { extractTypeParams } from '../src/typemap/index.js';
import * as ts from 'typescript';

function mod(decls: IRDecl[]): IRModule {
  return { name: 'TSLean.Test', imports: [{ module: 'TSLean.Runtime.Basic' }], decls, comments: [], sourceFile: 'test.ts' };
}

function inline(code: string): IRModule {
  return parseFile({ fileName: 'test.ts', sourceText: code });
}

function leanOf(code: string): string {
  return generateLean(rewriteModule(inline(code)));
}

// ─── TypeParam type ─────────────────────────────────────────────────────────────

describe('TypeParam type', () => {
  it('tp() creates bare TypeParam', () => {
    const p = tp('T');
    expect(p.name).toBe('T');
    expect(p.constraint).toBeUndefined();
    expect(p.default_).toBeUndefined();
  });

  it('TypeParam with constraint', () => {
    const p: TypeParam = { name: 'T', constraint: TyString };
    expect(p.name).toBe('T');
    expect(p.constraint?.tag).toBe('String');
  });

  it('TypeParam with default', () => {
    const p: TypeParam = { name: 'T', default_: TyNat };
    expect(p.default_?.tag).toBe('Nat');
  });
});

// ─── extractTypeParams with constraints ─────────────────────────────────────────

describe('extractTypeParams constraint extraction', () => {
  function makeProg(src: string) {
    const prog = ts.createProgram({
      rootNames: ['test.ts'],
      options: { target: ts.ScriptTarget.ES2022, strict: true, noEmit: true },
      host: {
        ...ts.createCompilerHost({ target: ts.ScriptTarget.ES2022 }),
        getSourceFile(name: string) {
          if (name === 'test.ts') return ts.createSourceFile(name, src, ts.ScriptTarget.ES2022, true);
          return undefined;
        },
        fileExists: (f: string) => f === 'test.ts',
        readFile: (f: string) => f === 'test.ts' ? src : undefined,
      },
    });
    return { prog, checker: prog.getTypeChecker() };
  }

  it('extracts constraint from <T extends string>', () => {
    const { prog, checker } = makeProg('function f<T extends string>(x: T): T { return x; }');
    const fn = prog.getSourceFile('test.ts')!.statements[0] as ts.FunctionDeclaration;
    const tps = extractTypeParams(fn, checker);
    expect(tps.length).toBe(1);
    expect(tps[0].name).toBe('T');
    expect(tps[0].constraint).toBeDefined();
    expect(tps[0].constraint?.tag).toBe('String');
  });

  it('extracts constraint from <T extends number>', () => {
    const { prog, checker } = makeProg('function f<T extends number>(x: T): T { return x; }');
    const fn = prog.getSourceFile('test.ts')!.statements[0] as ts.FunctionDeclaration;
    const tps = extractTypeParams(fn, checker);
    expect(tps[0].constraint?.tag).toBe('Float');
  });

  it('extracts default from <T = string>', () => {
    const { prog, checker } = makeProg('function f<T = string>(x: T): T { return x; }');
    const fn = prog.getSourceFile('test.ts')!.statements[0] as ts.FunctionDeclaration;
    const tps = extractTypeParams(fn, checker);
    expect(tps[0].name).toBe('T');
    expect(tps[0].default_).toBeDefined();
    expect(tps[0].default_?.tag).toBe('String');
  });

  it('extracts named interface constraint', () => {
    const { prog, checker } = makeProg(`
      interface Comparable { compareTo(other: any): number; }
      function sort<T extends Comparable>(arr: T[]): T[] { return arr; }
    `);
    const fn = prog.getSourceFile('test.ts')!.statements[1] as ts.FunctionDeclaration;
    const tps = extractTypeParams(fn, checker);
    expect(tps[0].constraint?.tag).toBe('TypeRef');
    if (tps[0].constraint?.tag === 'TypeRef') {
      expect(tps[0].constraint.name).toBe('Comparable');
    }
  });

  it('no constraint yields undefined', () => {
    const { prog, checker } = makeProg('function f<T>(x: T): T { return x; }');
    const fn = prog.getSourceFile('test.ts')!.statements[0] as ts.FunctionDeclaration;
    const tps = extractTypeParams(fn, checker);
    expect(tps[0].constraint).toBeUndefined();
    expect(tps[0].default_).toBeUndefined();
  });

  it('works without checker (backwards compat)', () => {
    const { prog } = makeProg('function f<T, U>(x: T): U { return x as any; }');
    const fn = prog.getSourceFile('test.ts')!.statements[0] as ts.FunctionDeclaration;
    const tps = extractTypeParams(fn);
    expect(tps.map(t => t.name)).toEqual(['T', 'U']);
    expect(tps[0].constraint).toBeUndefined();
  });
});

// ─── Constraint → type class lowering ───────────────────────────────────────────

describe('Constraint lowering to Lean type classes', () => {
  it('<T extends string> → [ToString T]', () => {
    const code = leanOf('function show<T extends string>(x: T): string { return String(x); }');
    expect(code).toContain('[ToString T]');
  });

  it('unconstrained <T> → no constraint', () => {
    const code = leanOf('function identity<T>(x: T): T { return x; }');
    expect(code).toContain('{T : Type}');
    expect(code).not.toContain('[');
  });

  it('basic polymorphic function', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'id', typeParams: [tp('T')],
      params: [{ name: 'x', type: TyVar('T') }],
      retType: TyVar('T'), effect: Pure, body: varExpr('x'),
    }]));
    expect(code).toContain('{T : Type}');
    expect(code).toContain('(x : T)');
    expect(code).toContain(': T');
  });

  it('generic struct', () => {
    const code = generateLean(mod([{
      tag: 'StructDef', name: 'Wrapper', typeParams: [tp('T')],
      fields: [{ name: 'value', type: TyVar('T') }],
    }]));
    expect(code).toContain('structure Wrapper (T : Type)');
    expect(code).toContain('value : T');
  });

  it('generic inductive', () => {
    const code = generateLean(mod([{
      tag: 'InductiveDef', name: 'Maybe', typeParams: [tp('T')],
      ctors: [
        { name: 'None_', fields: [] },
        { name: 'Some_', fields: [{ type: TyVar('T') }] },
      ],
    }]));
    expect(code).toContain('inductive Maybe (T : Type)');
  });

  it('constraint from IR TypeParam with constraint field', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'show',
      typeParams: [{ name: 'T', constraint: TyString }],
      params: [{ name: 'x', type: TyVar('T') }],
      retType: TyString, effect: Pure, body: varExpr('x'),
    }]));
    expect(code).toContain('[ToString T]');
  });

  it('named interface constraint from IR — unknown interfaces skipped', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'sort',
      typeParams: [{ name: 'T', constraint: TyRef('Comparable') }],
      params: [{ name: 'arr', type: TyArray(TyVar('T')) }],
      retType: TyArray(TyVar('T')), effect: Pure, body: varExpr('arr'),
    }]));
    // Unknown TS interfaces are not valid Lean typeclasses — constraint is dropped
    expect(code).toContain('{T : Type}');
    expect(code).not.toContain('[Comparable T]');
  });

  it('known typeclass constraint from IR', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'eq',
      typeParams: [{ name: 'T', constraint: TyRef('BEq') }],
      params: [{ name: 'a', type: TyVar('T') }],
      retType: TyBool, effect: Pure, body: litBool(true),
    }]));
    expect(code).toContain('[BEq T]');
  });
});

// ─── Utility types ──────────────────────────────────────────────────────────────

describe('Utility type handling', () => {
  it('Record<K,V> maps through IR to AssocMap', () => {
    // Test via IR directly since Record requires standard lib for parser resolution
    const code = generateLean(mod([{
      tag: 'VarDecl', name: 'x', mutable: false,
      type: { tag: 'Map', key: TyString, value: TyNat },
      value: litStr('{}'),
    }]));
    expect(code).toContain('AssocMap');
  });

  it('Readonly<T> is transparent', () => {
    const code = leanOf('function f(x: Readonly<string[]>): number { return x.length; }');
    // Readonly should pass through — the inner type (Array String) should appear
    expect(code).toContain('Array');
  });
});

// ─── Inexpressible types fallback ───────────────────────────────────────────────

describe('Inexpressible generic types', () => {
  it('Partial<T> with type var → String fallback', () => {
    const code = generateLean(mod([{
      tag: 'TypeAlias', name: 'PartialT', typeParams: [tp('T')],
      body: TyRef('Partial', [TyVar('T')]),
    }]));
    // Should not produce invalid Lean — either sorry or String
    expect(code).toContain('abbrev PartialT');
  });

  it('ReturnType<T> with type var → String fallback', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'test', typeParams: [tp('T')],
      params: [{ name: 'x', type: TyRef('ReturnType', [TyVar('T')]) }],
      retType: TyString, effect: Pure, body: varExpr('x'),
    }]));
    // The ReturnType<T> param should map to String (not invalid ReturnType identifier)
    expect(code).toContain('(x : String)');
  });
});

// ─── Multi-param generics ───────────────────────────────────────────────────────

describe('Multi-parameter generics', () => {
  it('<A, B> produces two implicit type params', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'pair',
      typeParams: [tp('A'), tp('B')],
      params: [
        { name: 'a', type: TyVar('A') },
        { name: 'b', type: TyVar('B') },
      ],
      retType: TyRef('Pair', [TyVar('A'), TyVar('B')]),
      effect: Pure,
      body: varExpr('a'),
    }]));
    expect(code).toContain('{A : Type}');
    expect(code).toContain('{B : Type}');
  });

  it('<A, B, C> from parsed source', () => {
    const code = leanOf(`
      function compose<A, B, C>(f: (b: B) => C, g: (a: A) => B, x: A): C {
        return f(g(x));
      }
    `);
    expect(code).toContain('{A : Type}');
    expect(code).toContain('{B : Type}');
    expect(code).toContain('{C : Type}');
  });
});
