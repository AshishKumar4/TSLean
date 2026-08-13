// Unit tests for typemap: type mapping from TS → IR.

import { describe, it, expect } from 'vitest';
import * as ts from 'typescript';
import { mapType, detectDiscriminatedUnion, extractTypeParams } from '../../src/typemap/index.js';
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
    expect(extractTypeParams(fn).map(t => t.name)).toEqual(['T', 'U']);
  });
  it('no type params → []', () => {
    const prog = makeProgram('function noop(): void {}');
    const sf = prog.getSourceFile('test.ts')!;
    expect(extractTypeParams(sf.statements[0] as ts.FunctionDeclaration)).toEqual([]);
  });
  it('interface type params', () => {
    const prog = makeProgram('interface Box<T> { value: T; }');
    const sf = prog.getSourceFile('test.ts')!;
    expect(extractTypeParams(sf.statements[0] as ts.InterfaceDeclaration).map(t => t.name)).toEqual(['T']);
  });
});

// ─── Types with no Lean carrier ───────────────────────────────────────────────
//
// This is where "does this type have a Lean carrier" is answered, so that the IR
// carries one answer for every consumer. Codegen cannot answer it: it sees a name
// where this layer sees a resolved symbol. Each of these reaches mapType by a
// different route, and a name that escapes all three is emitted verbatim — which
// `lake env lean` rejects, since none of them exists in Lean.

describe('mapType: types with no Lean carrier collapse to TSAny', () => {
  const isTSAny = (t: IRType) => t.tag === 'TypeRef' && t.name === 'TSAny' && t.args.length === 0;

  // Answered by where the type was declared, since each of these is TypeScript's
  // own and carries no type arguments to lose.
  it('PropertyDescriptor', () => expect(isTSAny(typeOf('PropertyDescriptor'))).toBe(true));
  it('Date',               () => expect(isTSAny(typeOf('Date'))).toBe(true));
  it('RegExp',             () => expect(isTSAny(typeOf('RegExp'))).toBe(true));

  // A union alias is neither an object nor a reference, so it reaches the check by
  // its own third route.
  it('PropertyKey',        () => expect(isTSAny(typeOf('PropertyKey'))).toBe(true));
  it('ArrayBufferLike',    () => expect(isTSAny(typeOf('ArrayBufferLike'))).toBe(true));

  // Generic, so provenance abstains — erasing one would discard its arguments.
  // These carry no carrier either, so they are named instead.
  it('PromiseLike<T>',     () => expect(isTSAny(typeOf('PromiseLike<string>'))).toBe(true));
  it('AsyncIterable<T>',   () => expect(isTSAny(typeOf('AsyncIterable<string>'))).toBe(true));
  it('ArrayBufferView',    () => expect(isTSAny(typeOf('ArrayBufferView'))).toBe(true));
  it('Uint8Array',         () => expect(isTSAny(typeOf('Uint8Array'))).toBe(true));

  // A generic whose arguments are read downstream keeps them: iteration takes the
  // element type out of `MapIterator<T>`, and erasing it loses the loop body.
  it('MapIterator keeps its element type', () => {
    const t = typeOf('ReturnType<Map<string, number>["values"]>');
    expect(t.tag).toBe('TypeRef');
    if (t.tag !== 'TypeRef') throw new Error('expected a TypeRef');
    expect(t.args.map(a => a.tag)).toEqual(['Float']);
  });

  // A type that does have a carrier keeps its name
  it('a local interface is untouched', () => {
    const t = aliasType('interface Conf { host: string }\ntype C = Conf;');
    expect(t.tag).toBe('TypeRef');
  });
});

// ─── Provenance, not name ─────────────────────────────────────────────────────
//
// "Has no Lean carrier" is decided by where a type was declared. These tests are
// the ones that can lie: if `typescript` fails to resolve, `ts.SourceFile` becomes
// an error type, maps to TSAny as `any` does, and the assertion passes for the
// wrong reason. So the program below is built with NodeNext resolution, and each
// test first requires that the module resolved and that the checker's view of the
// type is not `any`.

describe('mapType: provenance decides, not the name', () => {
  function resolvingProgram(src: string, file = 'provenance-test.ts') {
    const opts: ts.CompilerOptions = {
      strict: true, target: ts.ScriptTarget.ES2022, skipLibCheck: true,
      module: ts.ModuleKind.NodeNext, moduleResolution: ts.ModuleResolutionKind.NodeNext,
      lib: ['lib.es2022.d.ts'],
    };
    const host = ts.createCompilerHost(opts);
    const base = host.getSourceFile.bind(host);
    const prog = ts.createProgram({
      rootNames: [file], options: opts,
      host: {
        ...host,
        getSourceFile: (n, v, e, sc) => n === file ? ts.createSourceFile(n, src, v, true) : base(n, v, e, sc),
        fileExists: f => f === file || host.fileExists(f),
        readFile: f => f === file ? src : host.readFile(f),
      },
    });
    const sf = prog.getSourceFile(file);
    if (!sf) throw new Error('provenance test: no source file');
    // 2307 is "Cannot find module". Without this the whole describe could pass on
    // an unresolved import.
    const unresolved = prog.getSemanticDiagnostics(sf).filter(d => d.code === 2307);
    expect(unresolved.map(d => ts.flattenDiagnosticMessageText(d.messageText, ' '))).toEqual([]);
    return { prog, sf, checker: prog.getTypeChecker() };
  }

  function aliasNamed(src: string, name: string): { ir: IRType; shown: string } {
    const { sf, checker } = resolvingProgram(src);
    const alias = sf.statements.find(
      (st): st is ts.TypeAliasDeclaration => ts.isTypeAliasDeclaration(st) && st.name.text === name,
    );
    if (!alias) throw new Error(`provenance test: no alias ${name}`);
    const t = checker.getTypeAtLocation(alias.type);
    return { ir: mapType(t, checker), shown: checker.typeToString(t) };
  }

  const SRC = `import type * as ts from 'typescript';
    export interface Node { id: string }
    type FromCompiler = ts.Node;
    type FromProgram = Node;
    type CompilerFile = ts.SourceFile;
  `;

  it('a compiler API type resolves and then collapses', () => {
    const { ir, shown } = aliasNamed(SRC, 'FromCompiler');
    expect(shown).toBe('Node');                       // resolved, not `any`
    expect(ir).toEqual({ tag: 'TypeRef', name: 'TSAny', args: [] });
  });

  it('the same name declared by the program is kept', () => {
    const { ir, shown } = aliasNamed(SRC, 'FromProgram');
    expect(shown).toBe('Node');
    expect(ir).toEqual({ tag: 'TypeRef', name: 'Node', args: [] });
  });

  it('an unreferenced compiler API alias collapses too', () => {
    const { ir, shown } = aliasNamed(SRC, 'CompilerFile');
    expect(shown).toBe('SourceFile');
    expect(ir).toEqual({ tag: 'TypeRef', name: 'TSAny', args: [] });
  });

  // The allowlist has to win against provenance, or a type with a real Lean
  // carrier would be erased for having been declared by TypeScript. `Disposable`
  // is the case that can be resolved here, with the lib that declares it loaded.
  it('an allowlisted type keeps its name despite being TypeScript\'s own', () => {
    const file = 'provenance-carrier.ts';
    const src = 'export type D = Disposable;';
    const opts: ts.CompilerOptions = {
      strict: true, target: ts.ScriptTarget.ES2022, skipLibCheck: true,
      module: ts.ModuleKind.NodeNext, moduleResolution: ts.ModuleResolutionKind.NodeNext,
      lib: ['lib.es2022.d.ts', 'lib.esnext.disposable.d.ts'],
    };
    const host = ts.createCompilerHost(opts);
    const base = host.getSourceFile.bind(host);
    const prog = ts.createProgram({
      rootNames: [file], options: opts,
      host: {
        ...host,
        getSourceFile: (n, v, e, sc) => n === file ? ts.createSourceFile(n, src, v, true) : base(n, v, e, sc),
        fileExists: f => f === file || host.fileExists(f),
        readFile: f => f === file ? src : host.readFile(f),
      },
    });
    const sf = prog.getSourceFile(file);
    if (!sf) throw new Error('provenance test: no source file');
    const checker = prog.getTypeChecker();
    const alias = sf.statements.find(ts.isTypeAliasDeclaration);
    if (!alias) throw new Error('provenance test: no alias');
    const t = checker.getTypeAtLocation(alias.type);
    expect(checker.typeToString(t)).toBe('Disposable');   // resolved, and lib-declared
    expect(mapType(t, checker)).toEqual({ tag: 'TypeRef', name: 'Disposable', args: [] });
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
