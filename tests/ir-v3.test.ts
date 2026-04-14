// V3 IR tests: new IR nodes and smart constructors.

import { describe, it, expect } from 'vitest';
import {
  Pure, IO, Async,
  stateEffect, exceptEffect, combineEffects,
  isPure, hasAsync, hasState, hasExcept, hasIO,
  TyNat, TyInt, TyFloat, TyString, TyBool, TyUnit, TyNever,
  TyOption, TyArray, TyTuple, TyFn, TyMap, TySet, TyRef, TyVar,
  litStr, litNat, litBool, litUnit, litFloat, litInt,
  varExpr, holeExpr, structUpdate, appExpr, seqExpr,
  IRType, IRExpr, IRDecl, IRModule,
} from '../src/ir/types.js';
import { generateLean } from '../src/codegen/index.js';

function mod(decls: IRDecl[]): IRModule {
  return { name: 'T', imports: [], decls, comments: [] };
}

// ─── New smart constructors ───────────────────────────────────────────────────

describe('IR v3: litFloat', () => {
  it('litFloat creates LitFloat node', () => {
    const e = litFloat(3.14);
    expect(e.tag).toBe('LitFloat');
    if (e.tag === 'LitFloat') expect(e.value).toBe(3.14);
    expect(e.type).toEqual(TyFloat);
    expect(e.effect).toEqual(Pure);
  });
});

describe('IR v3: litInt', () => {
  it('litInt creates LitInt node', () => {
    const e = litInt(-42);
    expect(e.tag).toBe('LitInt');
    if (e.tag === 'LitInt') expect(e.value).toBe(-42);
    expect(e.type).toEqual(TyInt);
  });
});

describe('IR v3: structUpdate', () => {
  it('structUpdate creates StructUpdate node', () => {
    const base = varExpr('p', TyRef('Point'));
    const e = structUpdate(base, [{ name: 'x', value: litFloat(1.0) }], TyRef('Point'));
    expect(e.tag).toBe('StructUpdate');
    if (e.tag === 'StructUpdate') {
      expect(e.base).toEqual(base);
      expect(e.fields).toHaveLength(1);
      expect(e.fields[0].name).toBe('x');
    }
  });

  it('structUpdate inherits base effect', () => {
    const base = varExpr('p', TyRef('P'));
    const e = structUpdate(base, [{ name: 'x', value: litNat(0) }], TyRef('P'));
    expect(e.effect).toEqual(Pure);
  });
});

describe('IR v3: appExpr', () => {
  it('appExpr creates App node', () => {
    const fn = varExpr('f', TyFn([TyNat], TyNat));
    const e = appExpr(fn, [litNat(42)]);
    expect(e.tag).toBe('App');
    if (e.tag === 'App') {
      expect(e.fn).toEqual(fn);
      expect(e.args).toHaveLength(1);
    }
  });

  it('appExpr with zero args', () => {
    const fn = varExpr('g', TyFn([], TyUnit));
    const e = appExpr(fn, []);
    if (e.tag === 'App') expect(e.args).toHaveLength(0);
  });
});

describe('IR v3: seqExpr', () => {
  it('seqExpr with empty list → litUnit', () => {
    const e = seqExpr([]);
    expect(e.tag).toBe('LitUnit');
  });

  it('seqExpr with one expr → that expr', () => {
    const x = litNat(1);
    expect(seqExpr([x])).toEqual(x);
  });

  it('seqExpr with two → Sequence', () => {
    const e = seqExpr([litNat(1), litNat(2)]);
    expect(e.tag).toBe('Sequence');
    if (e.tag === 'Sequence') expect(e.stmts).toHaveLength(2);
  });

  it('seqExpr has type of last element', () => {
    const e = seqExpr([litNat(1), litStr('end')]);
    expect(e.type).toEqual(TyString);
  });
});

// ─── StructUpdate codegen ─────────────────────────────────────────────────────

describe('IR v3: StructUpdate → { base with f := v }', () => {
  it('generates correct Lean syntax', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'test', typeParams: [],
      params: [{ name: 'p', type: TyRef('P') }],
      retType: TyRef('P'), effect: Pure,
      body: structUpdate(varExpr('p', TyRef('P')), [{ name: 'x', value: litNat(5) }], TyRef('P')),
    }]);
    const code = generateLean(m);
    expect(code).toContain('{ p with x := 5 }');
  });

  it('multiple fields update', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'reset', typeParams: [],
      params: [{ name: 'p', type: TyRef('P') }],
      retType: TyRef('P'), effect: Pure,
      body: structUpdate(
        varExpr('p', TyRef('P')),
        [{ name: 'x', value: litNat(0) }, { name: 'y', value: litNat(0) }],
        TyRef('P'),
      ),
    }]);
    const code = generateLean(m);
    expect(code).toContain('{ p with x := 0, y := 0 }');
  });
});

// ─── New IRDecl variants ──────────────────────────────────────────────────────

describe('IR v3: SectionDecl', () => {
  it('SectionDecl has tag SectionDecl', () => {
    const d: IRDecl = { tag: 'SectionDecl', name: 'Foo', decls: [] };
    expect(d.tag).toBe('SectionDecl');
  });
});

describe('IR v3: AttributeDecl', () => {
  it('AttributeDecl has correct fields', () => {
    const d: IRDecl = { tag: 'AttributeDecl', attr: 'simp', target: 'myLemma' };
    expect(d.tag).toBe('AttributeDecl');
    if (d.tag === 'AttributeDecl') {
      expect(d.attr).toBe('simp');
      expect(d.target).toBe('myLemma');
    }
  });
});

describe('IR v3: DeriveDecl', () => {
  it('DeriveDecl has typeName and classes', () => {
    const d: IRDecl = { tag: 'DeriveDecl', typeName: 'MyType', classes: ['BEq', 'Repr'] };
    if (d.tag === 'DeriveDecl') {
      expect(d.typeName).toBe('MyType');
      expect(d.classes).toContain('BEq');
      expect(d.classes).toContain('Repr');
    }
  });
});

// ─── New IRExpr variants ──────────────────────────────────────────────────────

describe('IR v3: TypeNarrow expr', () => {
  it('TypeNarrow has correct fields', () => {
    const e: IRExpr = {
      tag: 'TypeNarrow',
      expr: varExpr('x', TyRef('Any')),
      narrowedType: TyString,
      narrowKind: 'typeof',
      type: TyString,
      effect: Pure,
    };
    expect(e.tag).toBe('TypeNarrow');
    if (e.tag === 'TypeNarrow') {
      expect(e.narrowKind).toBe('typeof');
      expect(e.narrowedType).toEqual(TyString);
    }
  });
});

describe('IR v3: MultiLet expr', () => {
  it('MultiLet has bindings and body', () => {
    const e: IRExpr = {
      tag: 'MultiLet',
      bindings: [{ name: 'x', type: TyNat, value: litNat(1) }],
      body: varExpr('x', TyNat),
      type: TyNat, effect: Pure,
    };
    expect(e.tag).toBe('MultiLet');
    if (e.tag === 'MultiLet') {
      expect(e.bindings).toHaveLength(1);
      expect(e.body.tag).toBe('Var');
    }
  });
});

// ─── IR algebra unchanged after v3 additions ──────────────────────────────────

describe('IR v3: core algebra unchanged', () => {
  it('combineEffects still correct', () => {
    expect(combineEffects([Pure, IO])).toEqual(IO);
    expect(combineEffects([IO, IO])).toEqual(IO);
    expect(combineEffects([Pure, Pure])).toEqual(Pure);
    expect(combineEffects([IO, Async]).tag).toBe('Combined');
  });

  it('isPure/hasAsync/etc. unchanged', () => {
    expect(isPure(Pure)).toBe(true);
    expect(hasAsync(Async)).toBe(true);
    expect(hasState(stateEffect(TyString))).toBe(true);
    expect(hasExcept(exceptEffect(TyFloat))).toBe(true);
    expect(hasIO(IO)).toBe(true);
  });

  it('type constructors unchanged', () => {
    expect(TyOption(TyString).tag).toBe('Option');
    expect(TyArray(TyNat).tag).toBe('Array');
    expect(TyMap(TyString, TyNat).tag).toBe('Map');
    expect(TyTuple([TyString, TyNat]).tag).toBe('Tuple');
    expect(TyFn([TyString], TyBool).tag).toBe('Function');
    expect(TyRef('Foo').tag).toBe('TypeRef');
    expect(TyVar('T').tag).toBe('TypeVar');
  });
});

// ─── StructDef extends_ field ─────────────────────────────────────────────────

describe('IR v3: StructDef extends_', () => {
  it('StructDef with extends_ flattens parent fields when parent is known', () => {
    const m = mod([
      {
        tag: 'StructDef', name: 'Parent', typeParams: [],
        fields: [{ name: 'base', type: TyString }],
      },
      {
        tag: 'StructDef', name: 'Child', typeParams: [],
        fields: [{ name: 'extra', type: TyString }],
        extends_: 'Parent',
      },
    ]);
    const code = generateLean(m);
    // Parent fields are merged into child — both fields present
    expect(code).toContain('structure Child');
    expect(code).toContain('base');
    expect(code).toContain('extra');
  });

  it('StructDef without extends_ has no extends', () => {
    const m = mod([{
      tag: 'StructDef', name: 'Solo', typeParams: [],
      fields: [{ name: 'x', type: TyNat }],
    }]);
    const code = generateLean(m);
    expect(code).not.toContain('extends');
  });
});

// ─── FuncDef docComment ───────────────────────────────────────────────────────

describe('IR v3: FuncDef docComment field', () => {
  it('docComment is present in IR', () => {
    const d: IRDecl = {
      tag: 'FuncDef', name: 'greet', typeParams: [],
      params: [{ name: 'n', type: TyString }],
      retType: TyString, effect: Pure,
      body: varExpr('n'),
      docComment: 'Greet a user by name',
    };
    if (d.tag === 'FuncDef') expect(d.docComment).toBe('Greet a user by name');
  });

  it('docComment emits /- -/ in Lean output', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'greet', typeParams: [],
      params: [{ name: 'n', type: TyString }],
      retType: TyString, effect: Pure,
      body: varExpr('n'),
      docComment: 'Greet a user by name',
    }]);
    const code = generateLean(m);
    expect(code).toContain('/-- Greet a user by name -/');
  });
});
