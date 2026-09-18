// Unit tests for typemap: type mapping from TS → IR.

import { join } from 'node:path';
import { describe, it, expect } from 'vitest';
import * as ts from '../../src/typescript-api/index.js';
import { openProject, renderDiagnostic, type ReadProject } from '../../src/typescript-api/session.js';
import { mapType, detectDiscriminatedUnion, extractTypeParams } from '../../src/typemap/index.js';
import {
  IRType,
} from '../../src/ir/types.js';

// ─── Helpers ──────────────────────────────────────────────────────────────────

/**
 * The path a fixture is read as. No file lives there: the compiler session holds the text in its
 * overlay, and the path sits beside this test so a lookup starting from it reaches the same
 * `node_modules` a real source file here would.
 */
const FIXTURE = join(import.meta.dirname, 'typemap.fixture.ts');

/**
 * A project over one fixture, which the caller closes.
 *
 * Reading TypeScript is the session's half, which is TypeScript 7: it builds a program from a
 * configuration rather than from a compiler host, so the source travels as overlay text for a
 * path with no file behind it. The options are unchanged in meaning and respelled the way a
 * `tsconfig.json` writes them.
 */
function openFixture(src: string): ReadProject {
  return openProject({
    files: [FIXTURE],
    settings: { strict: true, target: 'es2022', skipLibCheck: true },
    virtual: new Map([[FIXTURE, src]]),
  });
}

/** The type at one node. The checker declines to answer for a node it never checked. */
function typeAt(checker: ts.Checker, node: ts.Node): ts.Type {
  const type = checker.getTypeAtLocation(node);
  if (type === undefined) throw new TypeError('the checker gave no type for the fixture node');
  return type;
}

function typeOf(decl: string): IRType {
  const project = openFixture(`const x: ${decl} = undefined!;`);
  try {
    const stmt = project.requireSourceFile(FIXTURE).statements[0] as ts.VariableStatement;
    const d = stmt.declarationList.declarations[0];
    return mapType(typeAt(project.checker, d), project.checker);
  } finally {
    project.close();
  }
}

function aliasType(src: string): IRType {
  const project = openFixture(src);
  try {
    const alias = project.requireSourceFile(FIXTURE).statements[0] as ts.TypeAliasDeclaration;
    return mapType(typeAt(project.checker, alias), project.checker);
  } finally {
    project.close();
  }
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
    const project = openFixture('function id<T>(x: T): T { return x; }');
    try {
      const fn = project.requireSourceFile(FIXTURE).statements[0] as ts.FunctionDeclaration;
      const t = mapType(typeAt(project.checker, fn.parameters[0]), project.checker);
      expect(t.tag).toBe('TypeVar');
    } finally {
      project.close();
    }
  });
  it('extractTypeParams <T, U>', () => {
    const project = openFixture('function f<T,U>(a: T, b: U): [T,U] { return [a,b]; }');
    try {
      const fn = project.requireSourceFile(FIXTURE).statements[0] as ts.FunctionDeclaration;
      expect(extractTypeParams(fn).map((t) => t.name)).toEqual(['T', 'U']);
    } finally {
      project.close();
    }
  });
  it('no type params → []', () => {
    const project = openFixture('function noop(): void {}');
    try {
      const sf = project.requireSourceFile(FIXTURE);
      expect(extractTypeParams(sf.statements[0] as ts.FunctionDeclaration)).toEqual([]);
    } finally {
      project.close();
    }
  });
  it('interface type params', () => {
    const project = openFixture('interface Box<T> { value: T; }');
    try {
      const sf = project.requireSourceFile(FIXTURE);
      expect(extractTypeParams(sf.statements[0] as ts.InterfaceDeclaration).map((t) => t.name)).toEqual(['T']);
    } finally {
      project.close();
    }
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
// the ones that can lie: if the compiler's own declarations fail to resolve,
// `ts.SourceFile` becomes an error type, maps to TSAny as `any` does, and the
// assertion passes for the wrong reason. So the project below is built with
// NodeNext resolution, and each test first requires that the module resolved and
// that the checker's view of the type is not `any`.

describe('mapType: provenance decides, not the name', () => {
  const PROVENANCE = join(import.meta.dirname, 'provenance.fixture.ts');

  /**
   * A project whose module resolution really runs, which the caller closes. The options are
   * unchanged in meaning and respelled the way a `tsconfig.json` writes them, because the
   * session parses what it is handed as configuration text.
   */
  function openResolving(file: string, src: string, lib: readonly string[] = ['es2022']): ReadProject {
    const project = openProject({
      files: [file],
      settings: {
        strict: true,
        target: 'es2022',
        skipLibCheck: true,
        module: 'nodenext',
        moduleResolution: 'nodenext',
        lib,
      },
      virtual: new Map([[file, src]]),
    });
    // 2307 is "Cannot find module". Without this the whole describe could pass on
    // an unresolved import.
    const unresolved = project.program.getSemanticDiagnostics(file).filter((d) => d.code === 2307);
    expect(unresolved.map((d) => renderDiagnostic(d, ' '))).toEqual([]);
    return project;
  }

  function aliasNamed(src: string, name: string): { ir: IRType; shown: string } {
    const project = openResolving(PROVENANCE, src);
    try {
      const alias = project
        .requireSourceFile(PROVENANCE)
        .statements.find((st): st is ts.TypeAliasDeclaration => ts.isTypeAliasDeclaration(st) && st.name.text === name);
      if (!alias) throw new Error(`provenance test: no alias ${name}`);
      const t = typeAt(project.checker, alias.type);
      return { ir: mapType(t, project.checker), shown: project.checker.typeToString(t) };
    } finally {
      project.close();
    }
  }

  // The compiler's syntax declarations, which under TypeScript 7 are `typescript/unstable/ast`:
  // the package's own entry point declares the version and nothing else.
  const SRC = `import type * as ts from 'typescript/unstable/ast';
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
    const file = join(import.meta.dirname, 'provenance-carrier.fixture.ts');
    const project = openResolving(file, 'export type D = Disposable;', ['es2022', 'esnext.disposable']);
    try {
      const alias = project.requireSourceFile(file).statements.find(ts.isTypeAliasDeclaration);
      if (!alias) throw new Error('provenance test: no alias');
      const t = typeAt(project.checker, alias.type);
      expect(project.checker.typeToString(t)).toBe('Disposable'); // resolved, and lib-declared
      expect(mapType(t, project.checker)).toEqual({ tag: 'TypeRef', name: 'Disposable', args: [] });
    } finally {
      project.close();
    }
  });
});

// ─── detectDiscriminatedUnion ─────────────────────────────────────────────────

describe('detectDiscriminatedUnion', () => {
  /** A project over one union alias and the type of that alias. The caller closes the project. */
  function openUnion(src: string): { project: ReadProject; union: ts.Type } {
    const project = openFixture(src);
    const alias = project.requireSourceFile(FIXTURE).statements[0] as ts.TypeAliasDeclaration;
    return { project, union: typeAt(project.checker, alias) };
  }

  it('detects kind discriminant', () => {
    const { project, union } = openUnion('type S = { kind: "a"; x: number } | { kind: "b"; y: number };');
    try {
      if (!union.isUnionType()) return;
      const d = detectDiscriminatedUnion(union, project.checker);
      expect(d).not.toBeNull();
      expect(d!.field).toBe('kind');
      expect(d!.variants).toHaveLength(2);
      expect(d!.variants.map((v) => v.literal)).toContain('a');
      expect(d!.variants.map((v) => v.literal)).toContain('b');
    } finally {
      project.close();
    }
  });

  it('detects type discriminant', () => {
    const { project, union } = openUnion('type E = { type: "x" } | { type: "y" };');
    try {
      if (!union.isUnionType()) return;
      expect(detectDiscriminatedUnion(union, project.checker)?.field).toBe('type');
    } finally {
      project.close();
    }
  });

  it('detects tag discriminant', () => {
    const { project, union } = openUnion('type T = { tag: "leaf"; v: number } | { tag: "node"; l: T; r: T };');
    try {
      if (!union.isUnionType()) return;
      expect(detectDiscriminatedUnion(union, project.checker)?.field).toBe('tag');
    } finally {
      project.close();
    }
  });

  it('non-discriminated → null', () => {
    const { project, union } = openUnion('type T = { a: string } | { b: number };');
    try {
      if (!union.isUnionType()) return;
      expect(detectDiscriminatedUnion(union, project.checker)).toBeNull();
    } finally {
      project.close();
    }
  });

  it('variant fields exclude discriminant', () => {
    const { project, union } = openUnion(
      'type S = { kind: "c"; radius: number } | { kind: "r"; w: number; h: number };',
    );
    try {
      if (!union.isUnionType()) return;
      const d = detectDiscriminatedUnion(union, project.checker);
      if (!d) return;
      for (const v of d.variants) {
        expect(v.fields.map((f) => f.name)).not.toContain('kind');
      }
    } finally {
      project.close();
    }
  });
});
