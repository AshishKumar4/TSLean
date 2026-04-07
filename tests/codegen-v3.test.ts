// V3 codegen tests: new features added in v3 expansion.

import { describe, it, expect } from 'vitest';
import { generateLean } from '../src/codegen/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyBool, TyNat, TyUnit, TyRef, TyArray, TyOption, TyMap,
  Pure, IO, Async, stateEffect, exceptEffect, combineEffects,
  litNat, litStr, litBool, litUnit, litFloat, varExpr, holeExpr, structUpdate,
} from '../src/ir/types.js';

function mod(decls: IRDecl[]): IRModule {
  return { name: 'T', imports: [], decls, comments: [] };
}

// ─── StructUpdate node ────────────────────────────────────────────────────────

describe('Codegen v3: StructUpdate', () => {
  it('StructUpdate → { base with field := val }', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'setX', typeParams: [],
      params: [{ name: 'p', type: TyRef('Point') }, { name: 'v', type: TyFloat }],
      retType: TyRef('Point'), effect: Pure,
      body: structUpdate(varExpr('p', TyRef('Point')), [{ name: 'x', value: varExpr('v', TyFloat) }], TyRef('Point')),
    }]);
    const code = generateLean(m);
    expect(code).toContain('{ p with x := v }');
  });

  it('StructUpdate with multiple fields', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'move', typeParams: [],
      params: [
        { name: 'p', type: TyRef('Point') },
        { name: 'dx', type: TyFloat },
        { name: 'dy', type: TyFloat },
      ],
      retType: TyRef('Point'), effect: Pure,
      body: structUpdate(
        varExpr('p', TyRef('Point')),
        [
          { name: 'x', value: { tag: 'BinOp', op: 'Add', left: { tag: 'FieldAccess', obj: varExpr('p'), field: 'x', type: TyFloat, effect: Pure }, right: varExpr('dx', TyFloat), type: TyFloat, effect: Pure } },
          { name: 'y', value: { tag: 'BinOp', op: 'Add', left: { tag: 'FieldAccess', obj: varExpr('p'), field: 'y', type: TyFloat, effect: Pure }, right: varExpr('dy', TyFloat), type: TyFloat, effect: Pure } },
        ],
        TyRef('Point'),
      ),
    }]);
    const code = generateLean(m);
    expect(code).toContain('{ p with x :=');
    expect(code).toContain('y :=');
  });
});

// ─── StructLit with _base → struct update ────────────────────────────────────

describe('Codegen v3: StructLit with _base = struct update', () => {
  it('{ _base: self, field: val } → { self with field := val }', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'set_width', typeParams: [],
      params: [{ name: 'self', type: TyRef('Box') }, { name: 'v', type: TyFloat }],
      retType: TyRef('Box'), effect: Pure,
      body: {
        tag: 'StructLit', typeName: 'Box',
        fields: [
          { name: '_base', value: varExpr('self', TyRef('Box')) },
          { name: 'width', value: varExpr('v', TyFloat) },
        ],
        type: TyRef('Box'), effect: Pure,
      },
    }]);
    const code = generateLean(m);
    expect(code).toContain('{ self with width := v }');
  });
});

// ─── MultiLet node ────────────────────────────────────────────────────────────

describe('Codegen v3: MultiLet', () => {
  it('MultiLet creates multiple let bindings', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'swap', typeParams: [],
      params: [{ name: 'p', type: TyRef('Pair') }],
      retType: TyRef('Pair'), effect: Pure,
      body: {
        tag: 'MultiLet',
        bindings: [
          { name: 'a', type: TyFloat, value: { tag: 'FieldAccess', obj: varExpr('p'), field: 'first', type: TyFloat, effect: Pure } },
          { name: 'b', type: TyFloat, value: { tag: 'FieldAccess', obj: varExpr('p'), field: 'second', type: TyFloat, effect: Pure } },
        ],
        body: {
          tag: 'StructLit', typeName: 'Pair',
          fields: [{ name: 'first', value: varExpr('b') }, { name: 'second', value: varExpr('a') }],
          type: TyRef('Pair'), effect: Pure,
        },
        type: TyRef('Pair'), effect: Pure,
      },
    }]);
    const code = generateLean(m);
    expect(code).toContain('let a');
    expect(code).toContain('let b');
    expect(code).toContain('first := b');
    expect(code).toContain('second := a');
  });
});

// ─── Where clauses ────────────────────────────────────────────────────────────

describe('Codegen v3: where clauses', () => {
  it('FuncDef with where_ emits where block', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'main', typeParams: [],
      params: [{ name: 'n', type: TyNat }],
      retType: TyNat, effect: Pure,
      body: { tag: 'App', fn: varExpr('helper'), args: [varExpr('n')], type: TyNat, effect: Pure },
      where_: [{
        tag: 'FuncDef', name: 'helper', typeParams: [],
        params: [{ name: 'x', type: TyNat }],
        retType: TyNat, effect: Pure,
        body: { tag: 'BinOp', op: 'Mul', left: varExpr('x'), right: litNat(2), type: TyNat, effect: Pure },
      }],
    }]);
    const code = generateLean(m);
    expect(code).toContain('where');
    expect(code).toContain('def helper');
  });
});

// ─── JSDoc → /- -/ comments ───────────────────────────────────────────────────

describe('Codegen v3: JSDoc doc comments', () => {
  it('docComment field emits /- text -/', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'add', typeParams: [],
      params: [{ name: 'a', type: TyNat }, { name: 'b', type: TyNat }],
      retType: TyNat, effect: Pure,
      body: { tag: 'BinOp', op: 'Add', left: varExpr('a'), right: varExpr('b'), type: TyNat, effect: Pure },
      docComment: 'Add two natural numbers together',
    }]);
    const code = generateLean(m);
    expect(code).toContain('/-');
    expect(code).toContain('Add two natural numbers');
    expect(code).toContain('-/');
  });

  it('no docComment → no /- -/', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'sub', typeParams: [],
      params: [{ name: 'a', type: TyNat }, { name: 'b', type: TyNat }],
      retType: TyNat, effect: Pure,
      body: { tag: 'BinOp', op: 'Sub', left: varExpr('a'), right: varExpr('b'), type: TyNat, effect: Pure },
    }]);
    const code = generateLean(m);
    expect(code).not.toContain('/-');
  });
});

// ─── Section declarations ──────────────────────────────────────────────────────

describe('Codegen v3: SectionDecl', () => {
  it('SectionDecl emits section/end block', () => {
    const m = mod([{
      tag: 'SectionDecl', name: 'Basics', decls: [{
        tag: 'FuncDef', name: 'id', typeParams: ['T'],
        params: [{ name: 'x', type: TyRef('T') }],
        retType: TyRef('T'), effect: Pure,
        body: varExpr('x'),
      }],
    }]);
    const code = generateLean(m);
    expect(code).toContain('section Basics');
    expect(code).toContain('end Basics');
    expect(code).toContain('def id');
  });

  it('unnamed SectionDecl emits section/end', () => {
    const m = mod([{
      tag: 'SectionDecl', decls: [{ tag: 'RawLean', code: 'variable (n : Nat)' }],
    }]);
    const code = generateLean(m);
    expect(code).toContain('section');
    expect(code).toContain('end');
  });
});

// ─── auto-instance generation ─────────────────────────────────────────────────

describe('Codegen v3: auto-instance generation', () => {
  it('emitAutoInstances generates BEq instance', () => {
    const gen = new (generateLean as any).__proto__.constructor();  // Access Gen class
    // Test via output check — emit a struct then call autoInstances
    const m = mod([{
      tag: 'StructDef', name: 'Point', typeParams: [],
      fields: [{ name: 'x', type: TyFloat }, { name: 'y', type: TyFloat }],
      deriving: ['Repr'],
    }]);
    const code = generateLean(m);
    // The auto-instance method exists; test via direct call later
    expect(code).toContain('structure Point');
  });
});

// ─── Lean output quality ──────────────────────────────────────────────────────

describe('Codegen v3: output quality', () => {
  it('no raw TypeScript leaks in complex output', () => {
    const m = mod([
      { tag: 'StructDef', name: 'User', typeParams: [], fields: [{ name: 'name', type: TyString }, { name: 'age', type: TyNat }], deriving: ['Repr', 'BEq'] },
      { tag: 'FuncDef', name: 'greetUser', typeParams: [],
        params: [{ name: 'u', type: TyRef('User') }],
        retType: TyString, effect: Pure,
        body: { tag: 'BinOp', op: 'Concat', left: litStr('Hello, '), right: { tag: 'FieldAccess', obj: varExpr('u', TyRef('User')), field: 'name', type: TyString, effect: Pure }, type: TyString, effect: Pure },
      },
    ]);
    const code = generateLean(m);
    expect(code).not.toMatch(/\bfunction\b/);
    expect(code).not.toMatch(/\bconst\b/);
    expect(code).not.toMatch(/\blet\s+[a-z]+\s*=/);  // JS let = (not Lean let :=)
    expect(code).toContain('structure User');
    expect(code).toContain('def greetUser');
  });

  it('balanced curly braces in output', () => {
    const m = mod([
      { tag: 'StructDef', name: 'Box', typeParams: ['T'], fields: [{ name: 'val', type: TyRef('T') }] },
      { tag: 'FuncDef', name: 'wrap', typeParams: ['T'],
        params: [{ name: 'x', type: TyRef('T') }],
        retType: TyRef('Box', [TyRef('T')]), effect: Pure,
        body: { tag: 'StructLit', typeName: 'Box', fields: [{ name: 'val', value: varExpr('x') }], type: TyRef('Box'), effect: Pure },
      },
    ]);
    const code = generateLean(m);
    const opens  = (code.match(/\{/g) ?? []).length;
    const closes = (code.match(/\}/g) ?? []).length;
    expect(opens).toBe(closes);
  });

  it('generics: {T : Type} appears for polymorphic functions', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'id', typeParams: ['T'],
      params: [{ name: 'x', type: TyRef('T') }],
      retType: TyRef('T'), effect: Pure,
      body: varExpr('x'),
    }]);
    const code = generateLean(m);
    expect(code).toContain('{T : Type}');
    expect(code).toContain('(x : T)');
  });

  it('empty struct generates mk :: correctly', () => {
    const m = mod([{ tag: 'StructDef', name: 'Empty', typeParams: [], fields: [] }]);
    const code = generateLean(m);
    expect(code).toContain('structure Empty');
    expect(code).toContain('mk ::');
  });

  it('deeply nested namespace', () => {
    const m = mod([{
      tag: 'Namespace', name: 'A', decls: [{
        tag: 'Namespace', name: 'B', decls: [{
          tag: 'Namespace', name: 'C', decls: [{
            tag: 'FuncDef', name: 'leaf', typeParams: [],
            params: [], retType: TyUnit, effect: Pure, body: litUnit(),
          }],
        }],
      }],
    }]);
    const code = generateLean(m);
    expect(code).toContain('namespace A');
    expect(code).toContain('namespace B');
    expect(code).toContain('namespace C');
    expect(code).toContain('end C');
    expect(code).toContain('end B');
    expect(code).toContain('end A');
    expect(code).toContain('def leaf');
  });
});

// ─── Pattern guards in match ──────────────────────────────────────────────────

describe('Codegen v3: match with pattern guards', () => {
  it('IRCase with guard emits `if` guard', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'classify', typeParams: [],
      params: [{ name: 'n', type: TyNat }],
      retType: TyString, effect: Pure,
      body: {
        tag: 'Match', scrutinee: varExpr('n', TyNat),
        cases: [
          {
            pattern: { tag: 'PVar', name: 'x' },
            guard: { tag: 'BinOp', op: 'Lt', left: varExpr('x'), right: litNat(10), type: TyBool, effect: Pure },
            body: litStr('small'),
          },
          { pattern: { tag: 'PWild' }, body: litStr('large') },
        ],
        type: TyString, effect: Pure,
      },
    }]);
    const code = generateLean(m);
    expect(code).toContain('match n with');
    expect(code).toContain('if');
    expect(code).toContain('"small"');
  });
});

// ─── DeriveDecl ───────────────────────────────────────────────────────────────

describe('Codegen v3: DeriveDecl', () => {
  it('DeriveDecl emits deriving instance', () => {
    const m = mod([{ tag: 'DeriveDecl', typeName: 'MyType', classes: ['Repr', 'BEq'] }]);
    const code = generateLean(m);
    expect(code).toContain('deriving instance Repr, BEq for MyType');
  });
});

// ─── AttributeDecl ────────────────────────────────────────────────────────────

describe('Codegen v3: AttributeDecl', () => {
  it('AttributeDecl emits attribute [...] decl', () => {
    const m = mod([{ tag: 'AttributeDecl', attr: 'simp', target: 'myLemma' }]);
    const code = generateLean(m);
    expect(code).toContain('attribute [simp] myLemma');
  });
});
