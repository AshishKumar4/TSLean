// Deep codegen tests: output quality, edge cases, type formatting.

import { describe, it, expect } from 'vitest';
import { generateLean } from '../src/codegen/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyBool, TyNat, TyUnit, TyNever, TyRef, TyArray, TyOption,
  TyMap, TySet, TyTuple, TyFn, TyVar, TyInt, TyPromise,
  Pure, IO, Async, stateEffect, exceptEffect, combineEffects,
  litNat, litStr, litBool, litUnit, litFloat, varExpr, holeExpr, structUpdate,
  seqExpr, appExpr,
} from '../src/ir/types.js';
import { leanAliasOf, leanTypeOf } from './helpers/lean-type.js';

function mod(decls: IRDecl[]): IRModule {
  return { name: 'T', imports: [], decls, comments: [], sourceFile: 'test.ts' };
}

// ─── Tuple type emission ──────────────────────────────────────────────────────

describe('Codegen depth: tuple types', () => {
  it('(String × Float) for 2-tuple', () => {
    expect(leanTypeOf(TyTuple([TyString, TyFloat]))).toBe('(String × Float)');
  });

  it('(String × Float × Bool) for 3-tuple', () => {
    expect(leanTypeOf(TyTuple([TyString, TyFloat, TyBool]))).toBe('(String × Float × Bool)');
  });

  it('Unit for empty tuple', () => {
    expect(leanTypeOf(TyTuple([]))).toBe('Unit');
  });

  it('single-element tuple same as element', () => {
    // In Lean 4, (String) is just String
    expect(leanTypeOf(TyTuple([TyString]))).toBe('String');
  });

  it('nested tuple', () => {
    const t = TyTuple([TyString, TyTuple([TyNat, TyBool])]);
    expect(leanTypeOf(t)).toBe('(String × (Nat × Bool))');
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
  it('Nat → Nat',       () => expect(leanTypeOf(TyNat)).toBe('Nat'));
  it('Int → Int',       () => expect(leanTypeOf(TyInt)).toBe('Int'));
  it('Float → Float',   () => expect(leanTypeOf(TyFloat)).toBe('Float'));
  it('String → String', () => expect(leanTypeOf(TyString)).toBe('String'));
  it('Bool → Bool',     () => expect(leanTypeOf(TyBool)).toBe('Bool'));
  it('Unit → Unit',     () => expect(leanTypeOf(TyUnit)).toBe('Unit'));
  it('Never → Empty',   () => expect(leanTypeOf(TyNever)).toBe('Empty'));

  it('Option String → Option String', () => {
    expect(leanTypeOf(TyOption(TyString))).toBe('Option String');
  });

  it('nested Option Array → Option (Array String)', () => {
    expect(leanTypeOf(TyOption(TyArray(TyString)))).toBe('Option (Array String)');
  });

  it('Array String → Array String', () => {
    expect(leanTypeOf(TyArray(TyString))).toBe('Array String');
  });

  it('Map String Nat → AssocMap String Nat', () => {
    expect(leanTypeOf(TyMap(TyString, TyNat))).toBe('AssocMap String Nat');
  });

  it('Map with complex value → AssocMap String (Array Nat)', () => {
    expect(leanTypeOf(TyMap(TyString, TyArray(TyNat)))).toBe('AssocMap String (Array Nat)');
  });

  it('Function type → A → B', () => {
    expect(leanTypeOf(TyFn([TyString], TyBool))).toBe('String → Bool');
  });

  it('Function with multiple params → A → B → C', () => {
    expect(leanTypeOf(TyFn([TyString, TyNat], TyBool))).toBe('String → Nat → Bool');
  });

  it('Function with no params → Unit → B', () => {
    expect(leanTypeOf(TyFn([], TyBool))).toBe('Unit → Bool');
  });

  it('TypeRef no args → the name', () => {
    expect(leanTypeOf(TyRef('Foo'))).toBe('Foo');
  });

  it('TypeRef with nested args → Foo (Array String) Nat', () => {
    expect(leanTypeOf(TyRef('Foo', [TyArray(TyString), TyNat]))).toBe('Foo (Array String) Nat');
  });

  it('TypeVar → the name', () => expect(leanTypeOf(TyVar('α'))).toBe('α'));

  it('Result String Nat → Except Nat String', () => {
    const t = { tag: 'Result' as const, ok: TyString, err: TyNat };
    expect(leanTypeOf(t)).toBe('Except Nat String');
  });

  it('Promise String → IO String', () => {
    expect(leanTypeOf(TyPromise(TyString))).toBe('IO String');
  });
});

// ─── Carrier decisions ────────────────────────────────────────────────────────
//
// One renderer means one answer per IR type. These cases are the ones where the
// two renderers this codebase used to have disagreed, each pinned to the answer
// that keeps the emitted Lean well-typed.

describe('Codegen depth: single-renderer carriers', () => {
  // Set operations are lowered to Array operations (`AssocSet.empty` → `#[]`,
  // `AssocSet.insert` → `Array.push`, `has` → `Array.contains`), so a `List T`
  // carrier makes every one of them ill-typed: `lake env lean` rejects both
  // `Array.push` on a `List String` and `List.size`, which does not exist.
  it('Set String → Array String', () => {
    expect(leanTypeOf(TySet(TyString))).toBe('Array String');
  });

  it('Set (Array Nat) → Array (Array Nat)', () => {
    expect(leanTypeOf(TySet(TyArray(TyNat)))).toBe('Array (Array Nat)');
  });

  // `Awaited<T>` unwraps recursively and one `await` on Promise<Promise<T>>
  // yields T, so the carrier is IO of the fully awaited type. With `IO (IO T)`
  // the single `←` bind lands one layer short and every use of the bound value
  // is at the wrong type — `lake env lean` rejects `s.length` for exactly that.
  it('Promise (Promise String) → IO String', () => {
    expect(leanTypeOf(TyPromise(TyPromise(TyString)))).toBe('IO String');
  });

  it('Promise (Promise (Promise String)) → IO String', () => {
    expect(leanTypeOf(TyPromise(TyPromise(TyPromise(TyString))))).toBe('IO String');
  });

  // `TSAny` is the carrier: the runtime keeps `abbrev Any := TSAny` only as a
  // legacy alias, and `TyRef('Any')` is the parser's IR spelling for a missing
  // symbol, never a Lean name.
  it('TypeRef Any → TSAny', () => expect(leanTypeOf(TyRef('Any'))).toBe('TSAny'));
  it('TypeRef TSAny → TSAny', () => expect(leanTypeOf(TyRef('TSAny'))).toBe('TSAny'));

  // An indexed access reaches the renderer as a TypeRef, never as a TypeVar, and
  // its name is not a Lean identifier — the printer sanitizes terms, never types.
  it('TypeRef of an indexed access → TSAny', () => {
    expect(leanTypeOf(TyRef('D["length"]'))).toBe('TSAny');
  });

  // Anonymous object types keep the field-accessible carrier the build gate
  // records for them.
  it('TypeRef __type → AssocMap String TSAny', () => {
    expect(leanTypeOf(TyRef('__type'))).toBe('AssocMap String TSAny');
  });

  // Normalisation: `Dependent`, `Subtype` and `Universe` have no producer.
  // `LeanTy` has no dependent arrow, so the binder is dropped — but the arity is
  // not, since dropping the parameter would change what the type accepts.
  it('Dependent type → the non-dependent arrow', () => {
    const t = { tag: 'Dependent' as const, param: 'x', paramType: TyNat, body: TyBool };
    expect(leanTypeOf(t)).toBe('Nat → Bool');
  });

  // The predicate is discarded and nothing records that it was.
  it('Subtype → its base carrier, predicate discarded', () => {
    const t = { tag: 'Subtype' as const, base: TyNat, refinement: '0 < x' };
    expect(leanTypeOf(t)).toBe('Nat');
  });

  // A universe level is an argument, so it survives being an argument itself.
  // `Option Type 1` parses as a two-argument application: `lake env lean` rejects
  // it with `Function expected at Option Type`.
  it('Universe in atom position keeps its level', () => {
    expect(leanTypeOf({ tag: 'Universe', level: 1 })).toBe('Type 1');
    expect(leanTypeOf(TyOption({ tag: 'Universe', level: 1 }))).toBe('Option (Type 1)');
    expect(leanTypeOf(TyArray({ tag: 'Universe', level: 2 }))).toBe('Array (Type 2)');
  });
});

// ─── Type aliases ─────────────────────────────────────────────────────────────
//
// `lowerTypeAlias` decides more than the renderer does: whether the body counts
// as erased, and how many type parameters reach the signature — which usage sites
// then consume through `typeAliases`. These are the declarations that changed when
// the two renderers were collapsed into one.

describe('Codegen depth: type alias declarations', () => {
  it('Set alias → the Array carrier', () => {
    expect(leanAliasOf('S', TySet(TyString))).toBe('abbrev S := Array String');
  });

  it('nested Promise alias → one IO', () => {
    expect(leanAliasOf('P', TyPromise(TyPromise(TyString)))).toBe('abbrev P := IO String');
  });

  it('Map alias keeps both arguments', () => {
    expect(leanAliasOf('M', TyMap(TyString, TyArray(TyNat)))).toBe('abbrev M := AssocMap String (Array Nat)');
  });

  // An erased body carries no type parameters, so the alias takes none and usage
  // sites pass none. A type with no Lean carrier must reach here already erased:
  // if it arrives as its own name the alias emits that name, and `lake env lean`
  // rejects it — an abbrev's value position has no auto-bound implicit to hide in.
  it('erased body drops the alias type parameters', () => {
    expect(leanAliasOf('W', TyRef('TSAny'), [{ name: 'T' }])).toBe('abbrev W := String');
    expect(leanAliasOf('W', TyString, [{ name: 'T' }])).toBe('abbrev W := String');
  });

  it('a body that uses its type parameter keeps it', () => {
    expect(leanAliasOf('Box', TyArray(TyVar('T')), [{ name: 'T' }])).toBe('abbrev Box {T : Type} := Array T');
  });

  it('a body that ignores its type parameter drops it', () => {
    expect(leanAliasOf('Box', TyArray(TyString), [{ name: 'T' }])).toBe('abbrev Box := Array String');
  });

  // Self-reference is judged on the rendered head so that `type F = (x: F) => void`
  // is caught too, which prints as `F → Unit`. Lean has no recursive abbrev.
  it('self-referencing alias becomes a structure', () => {
    expect(leanAliasOf('IRExpr', TyRef('IRExpr'))).toBe('structure IRExpr where');
    expect(leanAliasOf('Loop', TyRef('Loop'))).toBe('abbrev Loop := String');
    expect(leanAliasOf('F', TyFn([TyRef('F')], TyUnit))).toBe('abbrev F := String');
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
