// Tests for the rewrite pass (discriminated union → inductive pattern matching).

import { describe, it, expect } from 'vitest';
import { rewriteModule } from '../src/rewrite/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyUnit, TyRef,
  Pure, litStr, varExpr,
} from '../src/ir/types.js';

function testMod(decls: IRDecl[]): IRModule {
  return { name: 'Test', imports: [], decls, comments: [] };
}

function matchExpr(scrutinee: IRExpr, cases: import('../src/ir/types.js').IRCase[]): IRExpr {
  return { tag: 'Match', scrutinee, cases, type: TyUnit, effect: Pure };
}

function fieldAccess(obj: IRExpr, field: string): IRExpr {
  return { tag: 'FieldAccess', obj, field, type: TyString, effect: Pure };
}

// ─── Basic rewrite tests ──────────────────────────────────────────────────────

describe('rewriteModule – structure preservation', () => {
  it('returns module unchanged if no Match', () => {
    const m = testMod([{ tag: 'TypeAlias', name: 'Foo', typeParams: [], body: TyString }]);
    const r = rewriteModule(m);
    expect(r.decls).toHaveLength(1);
    expect(r.decls[0].tag).toBe('TypeAlias');
  });

  it('collects InductiveDef info without error', () => {
    const m = testMod([{
      tag: 'InductiveDef', name: 'Shape', typeParams: [],
      ctors: [{ name: 'Circle', fields: [{ name: 'radius', type: TyFloat }] }],
    }]);
    expect(() => rewriteModule(m)).not.toThrow();
  });
});

describe('rewriteModule – string discriminant → PCtor', () => {
  const shapeModule: IRModule = {
    name: 'Test', imports: [], comments: [],
    decls: [
      {
        tag: 'InductiveDef', name: 'Shape', typeParams: [],
        ctors: [
          { name: 'Circle',    fields: [{ name: 'radius', type: TyFloat }] },
          { name: 'Rectangle', fields: [{ name: 'w', type: TyFloat }, { name: 'h', type: TyFloat }] },
        ],
      },
      {
        tag: 'FuncDef', name: 'area', typeParams: [],
        params: [{ name: 's', type: TyRef('Shape') }],
        retType: TyFloat, effect: Pure,
        body: matchExpr(
          fieldAccess(varExpr('s', TyRef('Shape')), 'kind'),
          [
            { pattern: { tag: 'PString', value: 'circle' },    body: litStr('circle area') },
            { pattern: { tag: 'PString', value: 'rectangle' }, body: litStr('rect area') },
          ]
        ),
      },
    ],
  };

  let result: IRModule;
  beforeAll(() => { result = rewriteModule(shapeModule); });

  it('scrutinee becomes the object (not field access)', () => {
    const fn = result.decls.find(d => d.tag === 'FuncDef' && d.name === 'area') as Extract<IRDecl, { tag: 'FuncDef' }>;
    const m  = fn.body as Extract<IRExpr, { tag: 'Match' }>;
    expect(m.scrutinee.tag).toBe('Var');
    if (m.scrutinee.tag === 'Var') expect(m.scrutinee.name).toBe('s');
  });

  it('patterns become PCtor', () => {
    const fn = result.decls.find(d => d.tag === 'FuncDef' && d.name === 'area') as Extract<IRDecl, { tag: 'FuncDef' }>;
    const m  = fn.body as Extract<IRExpr, { tag: 'Match' }>;
    for (const c of m.cases) expect(c.pattern.tag).toBe('PCtor');
  });

  it('"circle" → Shape.Circle', () => {
    const fn = result.decls.find(d => d.tag === 'FuncDef' && d.name === 'area') as Extract<IRDecl, { tag: 'FuncDef' }>;
    const m  = fn.body as Extract<IRExpr, { tag: 'Match' }>;
    const c  = m.cases[0];
    if (c.pattern.tag === 'PCtor') expect(c.pattern.ctor).toContain('Circle');
  });
});

describe('rewriteModule – "type" and "tag" discriminants', () => {
  function makeUnionMod(discField: string, literal: string, ctorName: string): IRModule {
    return testMod([
      {
        tag: 'InductiveDef', name: 'E', typeParams: [],
        ctors: [{ name: ctorName, fields: [] }],
      },
      {
        tag: 'FuncDef', name: 'handle', typeParams: [],
        params: [{ name: 'e', type: TyRef('E') }],
        retType: TyString, effect: Pure,
        body: matchExpr(
          fieldAccess(varExpr('e', TyRef('E')), discField),
          [{ pattern: { tag: 'PString', value: literal }, body: litStr('handled') }]
        ),
      },
    ]);
  }

  it('"type" discriminant is rewritten', () => {
    const r = rewriteModule(makeUnionMod('type', 'click', 'Click'));
    const fn = r.decls.find(d => d.tag === 'FuncDef') as Extract<IRDecl, { tag: 'FuncDef' }>;
    const m  = fn.body as Extract<IRExpr, { tag: 'Match' }>;
    expect(m.scrutinee.tag).toBe('Var');
    expect(m.cases[0].pattern.tag).toBe('PCtor');
  });

  it('"tag" discriminant is rewritten', () => {
    const r = rewriteModule(makeUnionMod('tag', 'leaf', 'Leaf'));
    const fn = r.decls.find(d => d.tag === 'FuncDef') as Extract<IRDecl, { tag: 'FuncDef' }>;
    const m  = fn.body as Extract<IRExpr, { tag: 'Match' }>;
    expect(m.scrutinee.tag).toBe('Var');
    expect(m.cases[0].pattern.tag).toBe('PCtor');
  });
});

describe('rewriteModule – recursive expression rewriting', () => {
  it('rewrites in IfThenElse branches', () => {
    const m = testMod([
      {
        tag: 'InductiveDef', name: 'C', typeParams: [],
        ctors: [{ name: 'A', fields: [] }, { name: 'B', fields: [] }],
      },
      {
        tag: 'FuncDef', name: 'test', typeParams: [], params: [], retType: TyUnit, effect: Pure,
        body: {
          tag: 'IfThenElse',
          cond: litStr('x') as any,
          then: matchExpr(
            fieldAccess(varExpr('c', TyRef('C')), 'kind'),
            [{ pattern: { tag: 'PString', value: 'a' }, body: litStr('a') }]
          ),
          else_: litStr('else') as any,
          type: TyUnit, effect: Pure,
        },
      },
    ]);
    const r = rewriteModule(m);
    const fn = r.decls.find(d => d.tag === 'FuncDef') as Extract<IRDecl, { tag: 'FuncDef' }>;
    const ifte = fn.body as Extract<IRExpr, { tag: 'IfThenElse' }>;
    const m2   = ifte.then as Extract<IRExpr, { tag: 'Match' }>;
    expect(m2.cases[0].pattern.tag).toBe('PCtor');
  });

  it('rewrites in Let body', () => {
    const m = testMod([
      { tag: 'InductiveDef', name: 'D', typeParams: [], ctors: [{ name: 'X', fields: [] }] },
      {
        tag: 'FuncDef', name: 'f', typeParams: [], params: [], retType: TyUnit, effect: Pure,
        body: {
          tag: 'Let', name: 'y', value: varExpr('z'),
          body: matchExpr(
            fieldAccess(varExpr('d', TyRef('D')), 'kind'),
            [{ pattern: { tag: 'PString', value: 'x' }, body: litStr('x') }]
          ),
          type: TyUnit, effect: Pure,
        },
      },
    ]);
    const r  = rewriteModule(m);
    const fn = r.decls.find(d => d.tag === 'FuncDef') as Extract<IRDecl, { tag: 'FuncDef' }>;
    const lt = fn.body as Extract<IRExpr, { tag: 'Let' }>;
    const m2 = lt.body as Extract<IRExpr, { tag: 'Match' }>;
    expect(m2.cases[0].pattern.tag).toBe('PCtor');
  });
});
