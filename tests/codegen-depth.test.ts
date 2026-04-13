// Deep codegen tests: output quality, edge cases, type formatting.

import { describe, it, expect } from 'vitest';
import { generateLean } from '../src/codegen/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyBool, TyNat, TyUnit, TyRef, TyArray, TyOption,
  TyMap, TySet, TyTuple, TyFn, TyVar, TyInt,
  Pure, IO, Async, stateEffect, exceptEffect, combineEffects,
  litNat, litStr, litBool, litUnit, litFloat, varExpr, holeExpr, structUpdate,
  seqExpr, appExpr,
} from '../src/ir/types.js';
import { irTypeToLean } from '../src/typemap/index.js';

function mod(decls: IRDecl[]): IRModule {
  return { name: 'T', imports: [], decls, comments: [], sourceFile: 'test.ts' };
}

// ─── Tuple type emission ──────────────────────────────────────────────────────

describe('Codegen depth: tuple types', () => {
  it('(String × Float) for 2-tuple', () => {
    expect(irTypeToLean(TyTuple([TyString, TyFloat]))).toBe('(String × Float)');
  });

  it('(String × Float × Bool) for 3-tuple', () => {
    expect(irTypeToLean(TyTuple([TyString, TyFloat, TyBool]))).toBe('(String × Float × Bool)');
  });

  it('Unit for empty tuple', () => {
    expect(irTypeToLean(TyTuple([]))).toBe('Unit');
  });

  it('single-element tuple same as element', () => {
    // In Lean 4, (String) is just String
    const r = irTypeToLean(TyTuple([TyString]));
    expect(r).toMatch(/String/);
  });

  it('nested tuple', () => {
    const t = TyTuple([TyString, TyTuple([TyNat, TyBool])]);
    expect(irTypeToLean(t)).toBe('(String × (Nat × Bool))');
  });

  it('TupleLit codegen → (a, b, c)', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'mkTriple', typeParams: [],
      params: [{ name: 'a', type: TyString }, { name: 'b', type: TyNat }, { name: 'c', type: TyBool }],
      retType: TyTuple([TyString, TyNat, TyBool]), effect: Pure,
      body: { tag: 'TupleLit', elems: [varExpr('a', TyString), varExpr('b', TyNat), varExpr('c', TyBool)], type: TyTuple([TyString, TyNat, TyBool]), effect: Pure },
    }]));
    expect(code).toContain('(a, b, c)');
  });
});

// ─── Complex type formatting ──────────────────────────────────────────────────

describe('Codegen depth: type formatting', () => {
  it('nested Option Array → Option (Array String)', () => {
    expect(irTypeToLean(TyOption(TyArray(TyString)))).toBe('Option (Array String)');
  });

  it('Map with complex value → AssocMap String (Array Nat)', () => {
    expect(irTypeToLean(TyMap(TyString, TyArray(TyNat)))).toBe('AssocMap String (Array Nat)');
  });

  it('Function type → A → B', () => {
    expect(irTypeToLean(TyFn([TyString], TyBool))).toBe('String → Bool');
  });

  it('Function with multiple params → A → B → C', () => {
    expect(irTypeToLean(TyFn([TyString, TyNat], TyBool))).toBe('String → Nat → Bool');
  });

  it('TypeRef with nested args → Foo (Array String) Nat', () => {
    expect(irTypeToLean(TyRef('Foo', [TyArray(TyString), TyNat]))).toBe('Foo (Array String) Nat');
  });

  it('Int type → Int', () => expect(irTypeToLean(TyInt)).toBe('Int'));

  it('Set String → Array String', () => {
    expect(irTypeToLean(TySet(TyString))).toBe('Array String');
  });

  it('Result String Nat → Except Nat String', () => {
    const t = { tag: 'Result' as const, ok: TyString, err: TyNat };
    expect(irTypeToLean(t)).toBe('Except Nat String');
  });

  it('Dependent type → (x : Nat) → Bool', () => {
    const t = { tag: 'Dependent' as const, param: 'x', paramType: TyNat, body: TyBool };
    expect(irTypeToLean(t)).toBe('(x : Nat) → Bool');
  });

  it('Subtype → {x : Nat // 0 < x}', () => {
    const t = { tag: 'Subtype' as const, base: TyNat, refinement: '0 < x' };
    expect(irTypeToLean(t)).toBe('{x : Nat // 0 < x}');
  });
});

// ─── Sequence and do-notation ─────────────────────────────────────────────────

describe('Codegen depth: sequences and do-notation', () => {
  it('pure sequence → semicolon separated', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'test', typeParams: [],
      params: [], retType: TyUnit, effect: Pure,
      body: seqExpr([litStr('a'), litStr('b'), litUnit()]),
    }]));
    expect(code).toContain('"a"');
    expect(code).toContain('"b"');
  });

  it('IO sequence → do block', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'ioTest', typeParams: [],
      params: [], retType: TyUnit, effect: IO,
      body: {
        tag: 'Sequence',
        stmts: [
          { tag: 'App', fn: varExpr('IO.println'), args: [litStr('hello')], type: TyUnit, effect: IO },
          { tag: 'App', fn: varExpr('IO.println'), args: [litStr('world')], type: TyUnit, effect: IO },
        ],
        type: TyUnit, effect: IO,
      },
    }]));
    expect(code).toContain('do');
    expect(code).toContain('IO.println "hello"');
    expect(code).toContain('IO.println "world"');
  });

  it('let-in chain in pure context', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'chain', typeParams: [],
      params: [{ name: 'x', type: TyNat }],
      retType: TyNat, effect: Pure,
      body: {
        tag: 'Let', name: 'a', annot: TyNat,
        value: { tag: 'BinOp', op: 'Add', left: varExpr('x'), right: litNat(1), type: TyNat, effect: Pure },
        body: {
          tag: 'Let', name: 'b', annot: TyNat,
          value: { tag: 'BinOp', op: 'Mul', left: varExpr('a'), right: litNat(2), type: TyNat, effect: Pure },
          body: varExpr('b', TyNat),
          type: TyNat, effect: Pure,
        },
        type: TyNat, effect: Pure,
      },
    }]));
    expect(code).toContain('let a : Nat := x + 1');
    expect(code).toContain('let b : Nat := a * 2');
    expect(code).toContain('b');
  });

  it('bind chain in IO context', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'fetchTwo', typeParams: [],
      params: [], retType: TyString, effect: Async,
      body: {
        tag: 'Bind', name: 'a',
        monad: { tag: 'App', fn: varExpr('fetchItem'), args: [litNat(1)], type: TyString, effect: Async },
        body: {
          tag: 'Bind', name: 'b',
          monad: { tag: 'App', fn: varExpr('fetchItem'), args: [litNat(2)], type: TyString, effect: Async },
          body: { tag: 'BinOp', op: 'Concat', left: varExpr('a', TyString), right: varExpr('b', TyString), type: TyString, effect: Pure },
          type: TyString, effect: Async,
        },
        type: TyString, effect: Async,
      },
    }]));
    expect(code).toContain('let a ←');
    expect(code).toContain('let b ←');
  });
});

// ─── StructUpdate ──────────────────────────────────────────────────────────────

describe('Codegen depth: StructUpdate', () => {
  it('single field update', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'setX', typeParams: [],
      params: [{ name: 'p', type: TyRef('Point') }, { name: 'v', type: TyFloat }],
      retType: TyRef('Point'), effect: Pure,
      body: structUpdate(varExpr('p', TyRef('Point')), [{ name: 'x', value: varExpr('v', TyFloat) }], TyRef('Point')),
    }]));
    expect(code).toContain('{ p with x := v }');
  });

  it('multi-field update', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'reset', typeParams: [],
      params: [{ name: 'p', type: TyRef('Point') }],
      retType: TyRef('Point'), effect: Pure,
      body: structUpdate(varExpr('p'), [{ name: 'x', value: litFloat(0) }, { name: 'y', value: litFloat(0) }], TyRef('Point')),
    }]));
    expect(code).toContain('{ p with x :=');
    expect(code).toContain('y :=');
  });
});

// ─── Complex expression patterns ──────────────────────────────────────────────

describe('Codegen depth: complex expressions', () => {
  it('nested if-then-else', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'classify', typeParams: [],
      params: [{ name: 'n', type: TyNat }],
      retType: TyString, effect: Pure,
      body: {
        tag: 'IfThenElse',
        cond: { tag: 'BinOp', op: 'Lt', left: varExpr('n'), right: litNat(10), type: TyBool, effect: Pure },
        then: litStr('small'),
        else_: {
          tag: 'IfThenElse',
          cond: { tag: 'BinOp', op: 'Lt', left: varExpr('n'), right: litNat(100), type: TyBool, effect: Pure },
          then: litStr('medium'),
          else_: litStr('large'),
          type: TyString, effect: Pure,
        },
        type: TyString, effect: Pure,
      },
    }]));
    expect(code).toContain('if n < 10 then');
    expect(code).toContain('"small"');
    expect(code).toContain('if n < 100 then');
    expect(code).toContain('"medium"');
    expect(code).toContain('"large"');
  });

  it('lambda with multiple params', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'apply', typeParams: [],
      params: [
        { name: 'f', type: TyFn([TyNat, TyNat], TyNat) },
        { name: 'a', type: TyNat },
        { name: 'b', type: TyNat },
      ],
      retType: TyNat, effect: Pure,
      body: appExpr(varExpr('f', TyFn([TyNat, TyNat], TyNat)), [varExpr('a'), varExpr('b')]),
    }]));
    expect(code).toContain('f a b');
  });

  it('match with multiple arms and guards', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'describe', typeParams: [],
      params: [{ name: 'n', type: TyNat }],
      retType: TyString, effect: Pure,
      body: {
        tag: 'Match', scrutinee: varExpr('n', TyNat),
        cases: [
          { pattern: { tag: 'PLit', value: 0 }, body: litStr('zero') },
          { pattern: { tag: 'PLit', value: 1 }, body: litStr('one') },
          {
            pattern: { tag: 'PVar', name: 'x' },
            guard: { tag: 'BinOp', op: 'Lt', left: varExpr('x'), right: litNat(10), type: TyBool, effect: Pure },
            body: litStr('small'),
          },
          { pattern: { tag: 'PWild' }, body: litStr('big') },
        ],
        type: TyString, effect: Pure,
      },
    }]));
    expect(code).toContain('match n with');
    expect(code).toContain('| 0');
    expect(code).toContain('| 1');
    expect(code).toContain('if');
    expect(code).toContain('"small"');
    expect(code).toContain('| _');
  });

  it('try-catch expression', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'safe', typeParams: [],
      params: [], retType: TyNat, effect: exceptEffect(TyString),
      body: {
        tag: 'TryCatch',
        body: { tag: 'App', fn: varExpr('riskyOp'), args: [], type: TyNat, effect: exceptEffect(TyString) },
        errName: 'e',
        handler: litNat(0),
        type: TyNat, effect: exceptEffect(TyString),
      },
    }]));
    expect(code).toContain('tryCatch');
    expect(code).toContain('fun e');
  });

  it('throw expression', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'failNow', typeParams: [],
      params: [], retType: TyUnit, effect: exceptEffect(TyString),
      body: { tag: 'Throw', error: litStr('fatal'), type: TyUnit, effect: exceptEffect(TyString) },
    }]));
    expect(code).toContain('throw "fatal"');
  });
});

// ─── Effect return types ──────────────────────────────────────────────────────

describe('Codegen depth: effect return type formatting', () => {
  it('Pure → plain type', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'f', typeParams: [], params: [], retType: TyNat, effect: Pure,
      body: litNat(0),
    }]));
    const line = code.split('\n').find(l => l.includes('def f'))!;
    expect(line).toMatch(/: Nat :=/);
    expect(line).not.toContain('IO');
  });

  it('IO → IO Nat', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'g', typeParams: [], params: [], retType: TyNat, effect: IO,
      body: litNat(0),
    }]));
    const line = code.split('\n').find(l => l.includes('def g'))!;
    expect(line).toContain('IO Nat');
  });

  it('Async → IO Nat', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'h', typeParams: [], params: [], retType: TyNat, effect: Async,
      body: litNat(0),
    }]));
    const line = code.split('\n').find(l => l.includes('def h'))!;
    expect(line).toContain('IO Nat');
  });

  it('State → StateT S IO Nat (IO as separate monad arg)', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'k', typeParams: [], params: [], retType: TyNat, effect: stateEffect(TyString),
      body: litNat(0),
    }]));
    const line = code.split('\n').find(l => l.includes('def k'))!;
    expect(line).toContain('StateT String IO Nat');
  });

  it('Except → ExceptT E IO Nat (IO as separate monad arg)', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'm', typeParams: [], params: [], retType: TyNat, effect: exceptEffect(TyString),
      body: litNat(0),
    }]));
    const line = code.split('\n').find(l => l.includes('def m'))!;
    expect(line).toContain('ExceptT String IO Nat');
  });

  it('Combined State+Except → StateT S (ExceptT E IO) T', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'n', typeParams: [], params: [], retType: TyNat,
      effect: combineEffects([stateEffect(TyString), exceptEffect(TyFloat)]),
      body: litNat(0),
    }]));
    const line = code.split('\n').find(l => l.includes('def n'))!;
    expect(line).toContain('StateT');
    expect(line).toContain('ExceptT');
    expect(line).toContain('IO');
  });
});

// ─── All Lean output features ─────────────────────────────────────────────────

describe('Codegen depth: comprehensive output features', () => {
  it('full program with structs, functions, match', () => {
    const code = generateLean(mod([
      { tag: 'StructDef', name: 'Point', typeParams: [], fields: [{ name: 'x', type: TyFloat }, { name: 'y', type: TyFloat }], deriving: ['Repr', 'BEq'] },
      { tag: 'FuncDef', name: 'origin', typeParams: [], params: [],
        retType: TyRef('Point'), effect: Pure,
        body: { tag: 'StructLit', typeName: 'Point', fields: [{ name: 'x', value: litFloat(0) }, { name: 'y', value: litFloat(0) }], type: TyRef('Point'), effect: Pure },
      },
      { tag: 'FuncDef', name: 'dist', typeParams: [], params: [{ name: 'p', type: TyRef('Point') }],
        retType: TyFloat, effect: Pure,
        body: {
          tag: 'App', fn: varExpr('Float.sqrt'),
          args: [{
            tag: 'BinOp', op: 'Add',
            left: { tag: 'BinOp', op: 'Mul', left: { tag: 'FieldAccess', obj: varExpr('p'), field: 'x', type: TyFloat, effect: Pure }, right: { tag: 'FieldAccess', obj: varExpr('p'), field: 'x', type: TyFloat, effect: Pure }, type: TyFloat, effect: Pure },
            right: { tag: 'BinOp', op: 'Mul', left: { tag: 'FieldAccess', obj: varExpr('p'), field: 'y', type: TyFloat, effect: Pure }, right: { tag: 'FieldAccess', obj: varExpr('p'), field: 'y', type: TyFloat, effect: Pure }, type: TyFloat, effect: Pure },
            type: TyFloat, effect: Pure,
          }],
          type: TyFloat, effect: Pure,
        },
      },
    ]));
    expect(code).toContain('structure Point');
    expect(code).toContain('x : Float');
    expect(code).toContain('y : Float');
    expect(code).toContain('def origin');
    expect(code).toContain('def dist');
    expect(code).toContain('Float.sqrt');
  });
});
