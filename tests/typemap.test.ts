// Tests for the type mapper.

import { join } from 'node:path';
import { describe, it, expect } from 'vitest';
import * as ts from '../src/typescript-api/index.js';
import { openProject, type ReadProject } from '../src/typescript-api/session.js';
import { mapType, detectDiscriminatedUnion, extractTypeParams } from '../src/typemap/index.js';
import { IRType } from '../src/ir/types.js';

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
function openFixture(src: string, file = FIXTURE): ReadProject {
  return openProject({
    files: [file],
    settings: { strict: true, target: 'es2022', skipLibCheck: true },
    virtual: new Map([[file, src]]),
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
    const declaration = stmt.declarationList.declarations[0];
    return mapType(typeAt(project.checker, declaration), project.checker);
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
    const project = openFixture('function id<T>(x: T): T { return x; }');
    try {
      const fn = project.requireSourceFile(FIXTURE).statements[0] as ts.FunctionDeclaration;
      const t = mapType(typeAt(project.checker, fn.parameters[0]), project.checker);
      expect(t.tag).toBe('TypeVar');
    } finally {
      project.close();
    }
  });
  it('extractTypeParams picks up <T,U>', () => {
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
      const fn = project.requireSourceFile(FIXTURE).statements[0] as ts.FunctionDeclaration;
      expect(extractTypeParams(fn)).toEqual([]);
    } finally {
      project.close();
    }
  });
});

describe('detectDiscriminatedUnion', () => {
  it('detects kind discriminant', () => {
    const project = openFixture('type S = { kind: "a"; x: number } | { kind: "b"; y: number };');
    try {
      const alias = project.requireSourceFile(FIXTURE).statements[0] as ts.TypeAliasDeclaration;
      const t = typeAt(project.checker, alias);
      if (!t.isUnionType()) return;
      const d = detectDiscriminatedUnion(t, project.checker);
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
    const project = openFixture('type E = { type: "x" } | { type: "y" };');
    try {
      const alias = project.requireSourceFile(FIXTURE).statements[0] as ts.TypeAliasDeclaration;
      const t = typeAt(project.checker, alias);
      if (!t.isUnionType()) return;
      const d = detectDiscriminatedUnion(t, project.checker);
      expect(d).not.toBeNull();
      expect(d!.field).toBe('type');
    } finally {
      project.close();
    }
  });

  it('non-discriminated union returns null', () => {
    const project = openFixture('type T = { a: string } | { b: number };');
    try {
      const alias = project.requireSourceFile(FIXTURE).statements[0] as ts.TypeAliasDeclaration;
      const t = typeAt(project.checker, alias);
      if (!t.isUnionType()) return;
      expect(detectDiscriminatedUnion(t, project.checker)).toBeNull();
    } finally {
      project.close();
    }
  });

  it('variant fields exclude discriminant', () => {
    const project = openFixture(
      'type S = { kind: "circle"; radius: number } | { kind: "rect"; w: number; h: number };',
    );
    try {
      const alias = project.requireSourceFile(FIXTURE).statements[0] as ts.TypeAliasDeclaration;
      const t = typeAt(project.checker, alias);
      if (!t.isUnionType()) return;
      const d = detectDiscriminatedUnion(t, project.checker);
      if (!d) return;
      for (const v of d.variants) expect(v.fields.map((f) => f.name)).not.toContain('kind');
    } finally {
      project.close();
    }
  });
});
