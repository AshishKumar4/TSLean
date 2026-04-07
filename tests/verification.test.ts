// Tests for the verification / proof obligation generator.

import { describe, it, expect } from 'vitest';
import { generateVerification } from '../src/verification/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyNat, TyUnit, TyArray, TyOption, TyRef,
  Pure, litNat, litStr, varExpr, holeExpr,
} from '../src/ir/types.js';

function mod(decls: IRDecl[]): IRModule {
  return { name: 'Test', imports: [], decls, comments: [] };
}

function makeFn(name: string, body: IRExpr): IRDecl {
  return { tag: 'FuncDef', name, typeParams: [], params: [], retType: TyUnit, effect: Pure, body };
}

// ─── Array bounds ─────────────────────────────────────────────────────────────

describe('generateVerification – array bounds', () => {
  it('index access → ArrayBounds obligation', () => {
    const m = mod([makeFn('head', {
      tag: 'IndexAccess',
      obj: varExpr('arr', TyArray(TyNat)),
      index: litNat(0),
      type: TyNat, effect: Pure,
    })]);
    const { obligations, leanCode } = generateVerification(m);
    expect(obligations.some(o => o.kind === 'ArrayBounds')).toBe(true);
    expect(obligations.find(o => o.kind === 'ArrayBounds')?.funcName).toBe('head');
    expect(leanCode).toContain('theorem head_idx_in_bounds');
  });

  it('two index accesses → two obligations', () => {
    const m = mod([makeFn('two', {
      tag: 'Sequence',
      stmts: [
        { tag: 'IndexAccess', obj: varExpr('a', TyArray(TyNat)), index: litNat(0), type: TyNat, effect: Pure },
        { tag: 'IndexAccess', obj: varExpr('a', TyArray(TyNat)), index: litNat(1), type: TyNat, effect: Pure },
      ],
      type: TyNat, effect: Pure,
    })]);
    const { obligations } = generateVerification(m);
    expect(obligations.filter(o => o.kind === 'ArrayBounds').length).toBeGreaterThanOrEqual(2);
  });

  it('no index access → no ArrayBounds', () => {
    const m = mod([makeFn('add', {
      tag: 'BinOp', op: 'Add', left: litNat(1), right: litNat(2), type: TyNat, effect: Pure,
    })]);
    const { obligations } = generateVerification(m);
    expect(obligations.some(o => o.kind === 'ArrayBounds')).toBe(false);
  });
});

// ─── Division safety ──────────────────────────────────────────────────────────

describe('generateVerification – division', () => {
  it('Div → DivisionSafe', () => {
    const m = mod([makeFn('div', {
      tag: 'BinOp', op: 'Div', left: varExpr('a', TyFloat), right: varExpr('b', TyFloat), type: TyFloat, effect: Pure,
    })]);
    const { obligations, leanCode } = generateVerification(m);
    expect(obligations.some(o => o.kind === 'DivisionSafe')).toBe(true);
    expect(leanCode).toContain('divisor_nonzero');
  });

  it('Mod → DivisionSafe', () => {
    const m = mod([makeFn('mod', {
      tag: 'BinOp', op: 'Mod', left: litNat(10), right: litNat(3), type: TyNat, effect: Pure,
    })]);
    const { obligations } = generateVerification(m);
    expect(obligations.some(o => o.kind === 'DivisionSafe')).toBe(true);
  });

  it('Add → no DivisionSafe', () => {
    const m = mod([makeFn('add', {
      tag: 'BinOp', op: 'Add', left: litNat(1), right: litNat(2), type: TyNat, effect: Pure,
    })]);
    const { obligations } = generateVerification(m);
    expect(obligations.some(o => o.kind === 'DivisionSafe')).toBe(false);
  });
});

// ─── Option access ────────────────────────────────────────────────────────────

describe('generateVerification – option access', () => {
  it('.value on Option → OptionIsSome', () => {
    const m = mod([makeFn('unwrap', {
      tag: 'FieldAccess',
      obj: varExpr('opt', TyOption(TyString)),
      field: 'value',
      type: TyString, effect: Pure,
    })]);
    const { obligations, leanCode } = generateVerification(m);
    expect(obligations.some(o => o.kind === 'OptionIsSome')).toBe(true);
    expect(leanCode).toContain('val_is_some');
  });

  it('.value on non-Option → no obligation', () => {
    const m = mod([makeFn('f', {
      tag: 'FieldAccess', obj: varExpr('x', TyRef('Foo')), field: 'value', type: TyString, effect: Pure,
    })]);
    const { obligations } = generateVerification(m);
    expect(obligations.some(o => o.kind === 'OptionIsSome')).toBe(false);
  });
});

// ─── Namespace traversal ──────────────────────────────────────────────────────

describe('generateVerification – namespace traversal', () => {
  it('finds obligations in nested namespaces', () => {
    const m = mod([{
      tag: 'Namespace', name: 'NS', decls: [makeFn('risky', {
        tag: 'IndexAccess', obj: varExpr('arr', TyArray(TyNat)), index: litNat(0), type: TyNat, effect: Pure,
      })],
    }]);
    const { obligations } = generateVerification(m);
    expect(obligations.some(o => o.kind === 'ArrayBounds')).toBe(true);
  });
});

// ─── Pure function → no obligations ──────────────────────────────────────────

describe('generateVerification – trivial', () => {
  it('pure trivial → 0 obligations', () => {
    const m = mod([makeFn('trivial', { tag: 'LitUnit', type: TyUnit, effect: Pure })]);
    const { obligations } = generateVerification(m);
    expect(obligations).toHaveLength(0);
  });
});

// ─── Lean output format ───────────────────────────────────────────────────────

describe('generateVerification – output format', () => {
  it('emits valid theorem stubs', () => {
    const m = mod([makeFn('f', {
      tag: 'BinOp', op: 'Div', left: litNat(10), right: litNat(2), type: TyNat, effect: Pure,
    })]);
    const { leanCode } = generateVerification(m);
    expect(leanCode).toContain('theorem f_divisor_nonzero');
    expect(leanCode).toContain(':= ');
  });
});
