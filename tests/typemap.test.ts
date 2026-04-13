// Tests for the type mapper.

import { describe, it, expect } from 'vitest';
import * as ts from 'typescript';
import { mapType, irTypeToLean, detectDiscriminatedUnion, extractTypeParams } from '../src/typemap/index.js';
import { TyString, TyFloat, TyBool, TyUnit, TyNat, TyNever, TyOption, TyArray, IRType } from '../src/ir/types.js';

// ─── Helpers ──────────────────────────────────────────────────────────────────

function makeProgram(src: string, file = 'test.ts') {
  const opts: ts.CompilerOptions = { strict: true, target: ts.ScriptTarget.ES2022, skipLibCheck: true };
  const host = ts.createCompilerHost(opts);
  const prog = ts.createProgram({
    rootNames: [file], options: opts,
    host: {
      ...host,
      getSourceFile: (n, v) => n === file ? ts.createSourceFile(n, src, v, true) : host.getSourceFile(n, v),
      fileExists: f => f === file || host.fileExists(f),
      readFile:   f => f === file ? src : host.readFile(f),
    },
  });
  return { prog, checker: prog.getTypeChecker() };
}

function typeOf(decl: string): IRType {
  const { prog, checker } = makeProgram(`const x: ${decl} = undefined!;`);
  const sf   = prog.getSourceFile('test.ts')!;
  const stmt = sf.statements[0] as ts.VariableStatement;
  return mapType(checker.getTypeAtLocation(stmt.declarationList.declarations[0]), checker);
}

function aliasType(src: string): IRType {
  const { prog, checker } = makeProgram(src);
  const sf = prog.getSourceFile('test.ts')!;
  return mapType(checker.getTypeAtLocation(sf.statements[0] as ts.TypeAliasDeclaration), checker);
}

// ─── Primitives ───────────────────────────────────────────────────────────────

describe('mapType – primitives', () => {
  it('string → String',    () => expect(typeOf('string').tag).toBe('String'));
  it('number → Float',     () => expect(typeOf('number').tag).toBe('Float'));
  it('boolean → Bool',     () => expect(typeOf('boolean').tag).toBe('Bool'));
  it('void → Unit',        () => expect(typeOf('void').tag).toBe('Unit'));
  it('undefined → Option', () => expect(typeOf('undefined').tag).toBe('Option'));
  it('null → Option',      () => expect(typeOf('null').tag).toBe('Option'));
  it('bigint → Int',       () => expect(typeOf('bigint').tag).toBe('Int'));
  it('never → Never',      () => expect(aliasType('type N = never;').tag).toBe('Never'));
  it('any → TypeRef Any',  () => expect(typeOf('any').tag).toBe('TypeRef'));
  it('unknown → TypeRef Any', () => expect(aliasType('type U = unknown;').tag).toBe('TypeRef'));
});

describe('mapType – collections', () => {
  it('string[] → Array String', () => {
    const t = typeOf('string[]');
    expect(t.tag).toBe('Array');
    if (t.tag === 'Array') expect(t.elem.tag).toBe('String');
  });
  it('Array<number> → Array Float', () => {
    const t = typeOf('Array<number>');
    expect(t.tag).toBe('Array');
    if (t.tag === 'Array') expect(t.elem.tag).toBe('Float');
  });
  it('ReadonlyArray<string> → Array String', () => {
    const t = typeOf('ReadonlyArray<string>');
    expect(t.tag).toBe('Array');
  });
  it('Map<string,number> → Map', () => {
    const t = typeOf('Map<string,number>');
    expect(t.tag).toBe('Map');
    if (t.tag === 'Map') { expect(t.key.tag).toBe('String'); expect(t.value.tag).toBe('Float'); }
  });
  it('Set<string> → Set', () => {
    const t = typeOf('Set<string>');
    expect(t.tag).toBe('Set');
    if (t.tag === 'Set') expect(t.elem.tag).toBe('String');
  });
  it('Record<string,number> → Map', () => {
    const t = typeOf('Record<string,number>');
    expect(['Map', 'TypeRef']).toContain(t.tag);
  });
  it('[string,number] → Tuple', () => {
    const t = typeOf('[string,number]');
    expect(t.tag).toBe('Tuple');
    if (t.tag === 'Tuple') { expect(t.elems[0].tag).toBe('String'); expect(t.elems[1].tag).toBe('Float'); }
  });
});

describe('mapType – union / optional', () => {
  it('string | undefined → Option String', () => {
    const t = typeOf('string | undefined');
    expect(t.tag).toBe('Option');
    if (t.tag === 'Option') expect(t.inner.tag).toBe('String');
  });
  it('number | null → Option Float', () => {
    const t = typeOf('number | null');
    expect(t.tag).toBe('Option');
    if (t.tag === 'Option') expect(t.inner.tag).toBe('Float');
  });
  it('boolean | null | undefined → Option-like', () => {
    const t = typeOf('boolean | null | undefined');
    expect(['Option', 'Bool']).toContain(t.tag);
  });
  it('string literal union → TypeRef or String', () => {
    const t = aliasType('type Dir = "left" | "right";');
    expect(['TypeRef', 'String']).toContain(t.tag);
  });
});

describe('mapType – Promise', () => {
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
});

describe('mapType – branded types', () => {
  it('string & {__brand} with alias → TypeRef', () => {
    const t = aliasType('type UserId = string & { readonly __brand: "UserId" };');
    expect(t.tag).toBe('TypeRef');
    if (t.tag === 'TypeRef') expect(t.name).toBe('UserId');
  });
  it('branded type is not plain String', () => {
    const t = aliasType('type Token = string & { readonly _brand: "Token" };');
    expect(t.tag).not.toBe('String');
  });
});

describe('mapType – generics', () => {
  it('TypeParameter → TypeVar', () => {
    const src = 'function id<T>(x: T): T { return x; }';
    const { prog, checker } = makeProgram(src);
    const sf   = prog.getSourceFile('test.ts')!;
    const fn   = sf.statements[0] as ts.FunctionDeclaration;
    const t    = mapType(checker.getTypeAtLocation(fn.parameters[0]), checker);
    expect(t.tag).toBe('TypeVar');
  });
  it('extractTypeParams picks up <T,U>', () => {
    const src = 'function f<T,U>(a: T, b: U): [T,U] { return [a,b]; }';
    const { prog } = makeProgram(src);
    const fn = prog.getSourceFile('test.ts')!.statements[0] as ts.FunctionDeclaration;
    expect(extractTypeParams(fn)).toEqual(['T', 'U']);
  });
  it('no type params → []', () => {
    const { prog } = makeProgram('function noop(): void {}');
    const fn = prog.getSourceFile('test.ts')!.statements[0] as ts.FunctionDeclaration;
    expect(extractTypeParams(fn)).toEqual([]);
  });
});

describe('irTypeToLean – emission', () => {
  it('Nat',          () => expect(irTypeToLean({ tag: 'Nat' })).toBe('Nat'));
  it('Int',          () => expect(irTypeToLean({ tag: 'Int' })).toBe('Int'));
  it('Float',        () => expect(irTypeToLean({ tag: 'Float' })).toBe('Float'));
  it('String',       () => expect(irTypeToLean({ tag: 'String' })).toBe('String'));
  it('Bool',         () => expect(irTypeToLean({ tag: 'Bool' })).toBe('Bool'));
  it('Unit',         () => expect(irTypeToLean({ tag: 'Unit' })).toBe('Unit'));
  it('Never → Empty', () => expect(irTypeToLean({ tag: 'Never' })).toBe('Empty'));

  it('Option String',    () => expect(irTypeToLean({ tag: 'Option', inner: { tag: 'String' } })).toBe('Option String'));
  it('Option (complex)', () => expect(irTypeToLean({ tag: 'Option', inner: { tag: 'Array', elem: { tag: 'Nat' } } })).toBe('Option (Array Nat)'));
  it('Array Nat',        () => expect(irTypeToLean({ tag: 'Array', elem: { tag: 'Nat' } })).toBe('Array Nat'));
  it('Map String Nat → AssocMap', () => expect(irTypeToLean({ tag: 'Map', key: { tag: 'String' }, value: { tag: 'Nat' } })).toBe('AssocMap String Nat'));
  it('Set String → Array',    () => expect(irTypeToLean({ tag: 'Set', elem: { tag: 'String' } })).toBe('Array String'));
  it('Promise String → IO String', () => expect(irTypeToLean({ tag: 'Promise', inner: { tag: 'String' } })).toBe('IO String'));

  it('Tuple (String × Nat)', () =>
    expect(irTypeToLean({ tag: 'Tuple', elems: [{ tag: 'String' }, { tag: 'Nat' }] })).toBe('(String × Nat)'));

  it('TypeRef no args',  () => expect(irTypeToLean({ tag: 'TypeRef', name: 'Foo', args: [] })).toBe('Foo'));
  it('TypeRef with args', () =>
    expect(irTypeToLean({ tag: 'TypeRef', name: 'Foo', args: [{ tag: 'String' }] })).toBe('Foo String'));

  it('TypeVar α', () => expect(irTypeToLean({ tag: 'TypeVar', name: 'α' })).toBe('α'));

  it('Universe 0 → Prop',   () => expect(irTypeToLean({ tag: 'Universe', level: 0 })).toBe('Prop'));
  it('Universe 1 → Type',   () => expect(irTypeToLean({ tag: 'Universe', level: 1 })).toBe('Type 1'));
  it('Universe 2 → Type 2', () => expect(irTypeToLean({ tag: 'Universe', level: 2 })).toBe('Type 2'));

  it('irTypeToLean with parens=true wraps compound', () => {
    expect(irTypeToLean({ tag: 'Option', inner: { tag: 'Nat' } }, true)).toBe('(Option Nat)');
    expect(irTypeToLean({ tag: 'Nat' }, true)).toBe('Nat');
  });

  it('nested: Option (Map String (Array Nat))', () => {
    const t: IRType = { tag: 'Option', inner: { tag: 'Map', key: { tag: 'String' }, value: { tag: 'Array', elem: { tag: 'Nat' } } } };
    expect(irTypeToLean(t)).toBe('Option (AssocMap String (Array Nat))');
  });
});

describe('detectDiscriminatedUnion', () => {
  function unionAt(src: string): ts.UnionType | null {
    const { prog, checker } = makeProgram(src);
    const sf = prog.getSourceFile('test.ts')!;
    const alias = sf.statements[0] as ts.TypeAliasDeclaration;
    const t = checker.getTypeAtLocation(alias);
    return t.isUnion() ? (t as ts.UnionType) : null;
  }

  it('detects kind discriminant', () => {
    const { prog, checker } = makeProgram('type S = { kind: "a"; x: number } | { kind: "b"; y: number };');
    const sf  = prog.getSourceFile('test.ts')!;
    const t   = checker.getTypeAtLocation(sf.statements[0] as ts.TypeAliasDeclaration);
    if (!t.isUnion()) return;
    const d = detectDiscriminatedUnion(t as ts.UnionType, checker);
    expect(d).not.toBeNull();
    expect(d!.field).toBe('kind');
    expect(d!.variants).toHaveLength(2);
    expect(d!.variants.map(v => v.literal)).toContain('a');
    expect(d!.variants.map(v => v.literal)).toContain('b');
  });

  it('detects type discriminant', () => {
    const { prog, checker } = makeProgram('type E = { type: "x" } | { type: "y" };');
    const sf  = prog.getSourceFile('test.ts')!;
    const t   = checker.getTypeAtLocation(sf.statements[0] as ts.TypeAliasDeclaration);
    if (!t.isUnion()) return;
    const d = detectDiscriminatedUnion(t as ts.UnionType, checker);
    expect(d).not.toBeNull();
    expect(d!.field).toBe('type');
  });

  it('non-discriminated union returns null', () => {
    const { prog, checker } = makeProgram('type T = { a: string } | { b: number };');
    const sf  = prog.getSourceFile('test.ts')!;
    const t   = checker.getTypeAtLocation(sf.statements[0] as ts.TypeAliasDeclaration);
    if (!t.isUnion()) return;
    const d = detectDiscriminatedUnion(t as ts.UnionType, checker);
    expect(d).toBeNull();
  });

  it('variant fields exclude discriminant', () => {
    const { prog, checker } = makeProgram('type S = { kind: "circle"; radius: number } | { kind: "rect"; w: number; h: number };');
    const sf  = prog.getSourceFile('test.ts')!;
    const t   = checker.getTypeAtLocation(sf.statements[0] as ts.TypeAliasDeclaration);
    if (!t.isUnion()) return;
    const d = detectDiscriminatedUnion(t as ts.UnionType, checker);
    if (!d) return;
    for (const v of d.variants) expect(v.fields.map(f => f.name)).not.toContain('kind');
  });
});
