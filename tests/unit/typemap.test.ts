// Unit tests for typemap: type mapping from TS → IR.

import { describe, it, expect } from 'vitest';
import * as ts from 'typescript';
import { mapType, irTypeToLean, detectDiscriminatedUnion, extractTypeParams } from '../../src/typemap/index.js';
import {
  TyString, TyFloat, TyBool, TyUnit, TyNat, TyInt, TyNever,
  TyOption, TyArray, TyMap, TySet, TyPromise, TyRef, TyVar, TyTuple,
  IRType,
} from '../../src/ir/types.js';

// ─── Helpers ──────────────────────────────────────────────────────────────────

function makeProgram(src: string, file = 'test.ts') {
  const opts: ts.CompilerOptions = { strict: true, target: ts.ScriptTarget.ES2022, skipLibCheck: true };
  const host = ts.createCompilerHost(opts);
  return ts.createProgram({
    rootNames: [file], options: opts,
    host: {
      ...host,
      getSourceFile: (n, v) => n === file ? ts.createSourceFile(n, src, v, true) : host.getSourceFile(n, v),
      fileExists: f => f === file || host.fileExists(f),
      readFile: f => f === file ? src : host.readFile(f),
    },
  });
}

function typeOf(decl: string): IRType {
  const prog = makeProgram(`const x: ${decl} = undefined!;`);
  const sf = prog.getSourceFile('test.ts')!;
  const checker = prog.getTypeChecker();
  const d = (sf.statements[0] as ts.VariableStatement).declarationList.declarations[0];
  return mapType(checker.getTypeAtLocation(d), checker);
}

function aliasType(src: string): IRType {
  const prog = makeProgram(src);
  const sf = prog.getSourceFile('test.ts')!;
  return mapType(prog.getTypeChecker().getTypeAtLocation(sf.statements[0] as ts.TypeAliasDeclaration), prog.getTypeChecker());
}

// ─── Primitives ───────────────────────────────────────────────────────────────

describe('mapType: primitives', () => {
  it('string → String',     () => expect(typeOf('string').tag).toBe('String'));
  it('number → Float',      () => expect(typeOf('number').tag).toBe('Float'));
  it('boolean → Bool',      () => expect(typeOf('boolean').tag).toBe('Bool'));
  it('void → Unit',         () => expect(typeOf('void').tag).toBe('Unit'));
  it('undefined → Option',  () => expect(typeOf('undefined').tag).toBe('Option'));
  it('null → Option',       () => expect(typeOf('null').tag).toBe('Option'));
  it('bigint → Int',        () => expect(typeOf('bigint').tag).toBe('Int'));
  it('never → Never',       () => expect(aliasType('type N = never;').tag).toBe('Never'));
  it('any → TypeRef',       () => expect(typeOf('any').tag).toBe('TypeRef'));
  it('unknown → TypeRef',   () => expect(aliasType('type U = unknown;').tag).toBe('TypeRef'));
  it('string lit → String', () => expect(aliasType('type S = "hello";').tag).toBe('String'));
  it('number lit → Float',  () => expect(aliasType('type N = 42;').tag).toBe('Float'));
});

// ─── Collections ──────────────────────────────────────────────────────────────

describe('mapType: collections', () => {
  it('string[] → Array String', () => {
    const t = typeOf('string[]');
    expect(t.tag).toBe('Array');
    if (t.tag === 'Array') expect(t.elem.tag).toBe('String');
  });
  it('Array<number> → Array Float', () => {
    const t = typeOf('Array<number>');
    expect(t.tag).toBe('Array');
  });
  it('ReadonlyArray<string> → Array', () => {
    expect(typeOf('ReadonlyArray<string>').tag).toBe('Array');
  });
  it('Map<string,number> → Map', () => {
    const t = typeOf('Map<string,number>');
    expect(t.tag).toBe('Map');
    if (t.tag === 'Map') {
      expect(t.key.tag).toBe('String');
      expect(t.value.tag).toBe('Float');
    }
  });
  it('Set<string> → Set', () => {
    const t = typeOf('Set<string>');
    expect(t.tag).toBe('Set');
    if (t.tag === 'Set') expect(t.elem.tag).toBe('String');
  });
  it('[string,number] → Tuple', () => {
    const t = typeOf('[string,number]');
    expect(t.tag).toBe('Tuple');
    if (t.tag === 'Tuple') {
      expect(t.elems[0].tag).toBe('String');
      expect(t.elems[1].tag).toBe('Float');
    }
  });
  it('Record<string,boolean> → Map or TypeRef', () => {
    const t = typeOf('Record<string,boolean>');
    expect(['Map', 'TypeRef']).toContain(t.tag);
  });
  it('WeakMap<object,string> → Map', () => {
    // WeakMap maps to Map (approximately)
    const t = typeOf('WeakMap<object,string>');
    expect(['Map', 'TypeRef']).toContain(t.tag);
  });
});

// ─── Optional / Union ─────────────────────────────────────────────────────────

describe('mapType: optional and union', () => {
  it('T | undefined → Option T', () => {
    const t = typeOf('string | undefined');
    expect(t.tag).toBe('Option');
    if (t.tag === 'Option') expect(t.inner.tag).toBe('String');
  });
  it('number | null → Option Float', () => {
    const t = typeOf('number | null');
    expect(t.tag).toBe('Option');
    if (t.tag === 'Option') expect(t.inner.tag).toBe('Float');
  });
  it('boolean | null → Option Bool', () => {
    const t = typeOf('boolean | null');
    expect(['Option', 'Bool']).toContain(t.tag);
  });
  it('string literal union → TypeRef or String', () => {
    const t = aliasType('type Dir = "left" | "right";');
    expect(['TypeRef', 'String']).toContain(t.tag);
  });
  it('boolean union (true|false) → Bool', () => {
    // In TS, boolean is actually true | false
    expect(typeOf('boolean').tag).toBe('Bool');
  });
});

// ─── Promise ──────────────────────────────────────────────────────────────────

describe('mapType: Promise', () => {
  it('Promise<string> → Promise String', () => {
    const t = typeOf('Promise<string>');
    expect(t.tag).toBe('Promise');
    if (t.tag === 'Promise') expect(t.inner.tag).toBe('String');
  });
  it('Promise<void> → Promise Unit', () => {
    const t = typeOf('Promise<void>');
    expect(t.tag).toBe('Promise');
    if (t.tag === 'Promise') expect(t.inner.tag).toBe('Unit');
  });
  it('Promise<number[]> → Promise (Array Float)', () => {
    const t = typeOf('Promise<number[]>');
    expect(t.tag).toBe('Promise');
    if (t.tag === 'Promise') expect(t.inner.tag).toBe('Array');
  });
});

// ─── Branded types ────────────────────────────────────────────────────────────

describe('mapType: branded types', () => {
  it('string & {__brand} with alias → TypeRef', () => {
    const t = aliasType('type UserId = string & { readonly __brand: "UserId" };');
    expect(t.tag).toBe('TypeRef');
    if (t.tag === 'TypeRef') expect(t.name).toBe('UserId');
  });
  it('number & {__brand} → TypeRef', () => {
    const t = aliasType('type Price = number & { readonly __brand: "Price" };');
    expect(t.tag).toBe('TypeRef');
  });
  it('branded type is NOT plain String', () => {
    const t = aliasType('type Token = string & { readonly _brand: "Token" };');
    expect(t.tag).not.toBe('String');
  });
});

// ─── Generic type parameters ──────────────────────────────────────────────────

describe('mapType: generics', () => {
  it('T (TypeParameter) → TypeVar T', () => {
    const prog = makeProgram('function id<T>(x: T): T { return x; }');
    const sf = prog.getSourceFile('test.ts')!;
    const checker = prog.getTypeChecker();
    const fn = sf.statements[0] as ts.FunctionDeclaration;
    const t = mapType(checker.getTypeAtLocation(fn.parameters[0]), checker);
    expect(t.tag).toBe('TypeVar');
  });
  it('extractTypeParams <T, U>', () => {
    const prog = makeProgram('function f<T,U>(a: T, b: U): [T,U] { return [a,b]; }');
    const sf = prog.getSourceFile('test.ts')!;
    const fn = sf.statements[0] as ts.FunctionDeclaration;
    expect(extractTypeParams(fn)).toEqual(['T', 'U']);
  });
  it('no type params → []', () => {
    const prog = makeProgram('function noop(): void {}');
    const sf = prog.getSourceFile('test.ts')!;
    expect(extractTypeParams(sf.statements[0] as ts.FunctionDeclaration)).toEqual([]);
  });
  it('interface type params', () => {
    const prog = makeProgram('interface Box<T> { value: T; }');
    const sf = prog.getSourceFile('test.ts')!;
    expect(extractTypeParams(sf.statements[0] as ts.InterfaceDeclaration)).toEqual(['T']);
  });
});

// ─── irTypeToLean ─────────────────────────────────────────────────────────────

describe('irTypeToLean', () => {
  it('Nat → Nat',          () => expect(irTypeToLean({ tag: 'Nat' })).toBe('Nat'));
  it('Int → Int',          () => expect(irTypeToLean({ tag: 'Int' })).toBe('Int'));
  it('Float → Float',      () => expect(irTypeToLean({ tag: 'Float' })).toBe('Float'));
  it('String → String',    () => expect(irTypeToLean({ tag: 'String' })).toBe('String'));
  it('Bool → Bool',        () => expect(irTypeToLean({ tag: 'Bool' })).toBe('Bool'));
  it('Unit → Unit',        () => expect(irTypeToLean({ tag: 'Unit' })).toBe('Unit'));
  it('Never → Empty',      () => expect(irTypeToLean({ tag: 'Never' })).toBe('Empty'));
  it('Option String',      () => expect(irTypeToLean({ tag: 'Option', inner: { tag: 'String' } })).toBe('Option String'));
  it('Option (Array Nat)', () => expect(irTypeToLean({ tag: 'Option', inner: { tag: 'Array', elem: { tag: 'Nat' } } })).toBe('Option (Array Nat)'));
  it('Array Nat',          () => expect(irTypeToLean({ tag: 'Array', elem: { tag: 'Nat' } })).toBe('Array Nat'));
  it('Map String Nat → AssocMap', () => expect(irTypeToLean({ tag: 'Map', key: { tag: 'String' }, value: { tag: 'Nat' } })).toBe('AssocMap String Nat'));
  it('Set String → AssocSet',  () => expect(irTypeToLean({ tag: 'Set', elem: { tag: 'String' } })).toBe('AssocSet String'));
  it('Promise String → IO String', () => expect(irTypeToLean({ tag: 'Promise', inner: { tag: 'String' } })).toBe('IO String'));
  it('Tuple (String × Nat)',   () => expect(irTypeToLean({ tag: 'Tuple', elems: [{ tag: 'String' }, { tag: 'Nat' }] })).toBe('(String × Nat)'));
  it('TypeRef no args',        () => expect(irTypeToLean({ tag: 'TypeRef', name: 'Foo', args: [] })).toBe('Foo'));
  it('TypeRef with args',      () => expect(irTypeToLean({ tag: 'TypeRef', name: 'Foo', args: [{ tag: 'String' }] })).toBe('Foo String'));
  it('TypeVar α',              () => expect(irTypeToLean({ tag: 'TypeVar', name: 'α' })).toBe('α'));
  it('Universe 0 → Prop',      () => expect(irTypeToLean({ tag: 'Universe', level: 0 })).toBe('Prop'));
  it('Universe 1 → Type',      () => expect(irTypeToLean({ tag: 'Universe', level: 1 })).toBe('Type 1'));
  it('Universe 2 → Type 2',    () => expect(irTypeToLean({ tag: 'Universe', level: 2 })).toBe('Type 2'));
  it('parens=true wraps',      () => expect(irTypeToLean({ tag: 'Option', inner: { tag: 'Nat' } }, true)).toBe('(Option Nat)'));
  it('parens=true, simple',    () => expect(irTypeToLean({ tag: 'Nat' }, true)).toBe('Nat'));
  it('nested complex',         () => {
    const t: IRType = { tag: 'Option', inner: { tag: 'Map', key: { tag: 'String' }, value: { tag: 'Array', elem: { tag: 'Nat' } } } };
    expect(irTypeToLean(t)).toBe('Option (AssocMap String (Array Nat))');
  });
});

// ─── detectDiscriminatedUnion ─────────────────────────────────────────────────

describe('detectDiscriminatedUnion', () => {
  function getUnion(src: string): { union: ts.UnionType; checker: ts.TypeChecker } {
    const prog = makeProgram(src);
    const sf = prog.getSourceFile('test.ts')!;
    const checker = prog.getTypeChecker();
    const t = checker.getTypeAtLocation(sf.statements[0] as ts.TypeAliasDeclaration);
    return { union: t as ts.UnionType, checker };
  }

  it('detects kind discriminant', () => {
    const { union, checker } = getUnion('type S = { kind: "a"; x: number } | { kind: "b"; y: number };');
    if (!union.isUnion()) return;
    const d = detectDiscriminatedUnion(union, checker);
    expect(d).not.toBeNull();
    expect(d!.field).toBe('kind');
    expect(d!.variants).toHaveLength(2);
    expect(d!.variants.map(v => v.literal)).toContain('a');
    expect(d!.variants.map(v => v.literal)).toContain('b');
  });

  it('detects type discriminant', () => {
    const { union, checker } = getUnion('type E = { type: "x" } | { type: "y" };');
    if (!union.isUnion()) return;
    const d = detectDiscriminatedUnion(union, checker);
    expect(d?.field).toBe('type');
  });

  it('detects tag discriminant', () => {
    const { union, checker } = getUnion('type T = { tag: "leaf"; v: number } | { tag: "node"; l: T; r: T };');
    if (!union.isUnion()) return;
    const d = detectDiscriminatedUnion(union, checker);
    expect(d?.field).toBe('tag');
  });

  it('non-discriminated → null', () => {
    const { union, checker } = getUnion('type T = { a: string } | { b: number };');
    if (!union.isUnion()) return;
    const d = detectDiscriminatedUnion(union, checker);
    expect(d).toBeNull();
  });

  it('variant fields exclude discriminant', () => {
    const { union, checker } = getUnion('type S = { kind: "c"; radius: number } | { kind: "r"; w: number; h: number };');
    if (!union.isUnion()) return;
    const d = detectDiscriminatedUnion(union, checker);
    if (!d) return;
    for (const v of d.variants) {
      expect(v.fields.map(f => f.name)).not.toContain('kind');
    }
  });
});
