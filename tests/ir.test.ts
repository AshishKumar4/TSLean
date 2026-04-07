// Tests for core IR types, effects, and smart constructors.

import { describe, it, expect } from 'vitest';
import {
  Pure, IO, Async,
  stateEffect, exceptEffect, combineEffects,
  isPure, hasAsync, hasState, hasExcept, hasIO,
  TyNat, TyInt, TyFloat, TyString, TyBool, TyUnit, TyNever,
  TyOption, TyArray, TyTuple, TyFn, TyMap, TySet, TyPromise,
  TyResult, TyRef, TyVar,
  litStr, litNat, litBool, litUnit, varExpr, holeExpr,
  IRType, Effect,
} from '../src/ir/types.js';

describe('Effects – constructors', () => {
  it('Pure.tag is Pure',   () => expect(Pure.tag).toBe('Pure'));
  it('IO.tag is IO',       () => expect(IO.tag).toBe('IO'));
  it('Async.tag is Async', () => expect(Async.tag).toBe('Async'));

  it('stateEffect creates State',  () => { const e = stateEffect(TyString); expect(e.tag).toBe('State'); });
  it('exceptEffect creates Except',() => { const e = exceptEffect(TyString); expect(e.tag).toBe('Except'); });
});

describe('Effects – predicates', () => {
  it('isPure(Pure) === true',   () => expect(isPure(Pure)).toBe(true));
  it('isPure(IO) === false',    () => expect(isPure(IO)).toBe(false));
  it('isPure(Async) === false', () => expect(isPure(Async)).toBe(false));

  it('hasAsync(Async)',            () => expect(hasAsync(Async)).toBe(true));
  it('hasAsync(Pure) === false',   () => expect(hasAsync(Pure)).toBe(false));
  it('hasAsync(IO) === false',     () => expect(hasAsync(IO)).toBe(false));
  it('hasAsync(Combined with Async)', () => expect(hasAsync(combineEffects([IO, Async]))).toBe(true));

  it('hasState(stateEffect)',      () => expect(hasState(stateEffect(TyString))).toBe(true));
  it('hasState(Pure) === false',   () => expect(hasState(Pure)).toBe(false));
  it('hasState(Combined)',         () => expect(hasState(combineEffects([stateEffect(TyNat), Async]))).toBe(true));

  it('hasExcept(exceptEffect)',    () => expect(hasExcept(exceptEffect(TyString))).toBe(true));
  it('hasExcept(Pure) === false',  () => expect(hasExcept(Pure)).toBe(false));
  it('hasExcept(Combined)',        () => expect(hasExcept(combineEffects([exceptEffect(TyString), Async]))).toBe(true));

  it('hasIO(IO)',                  () => expect(hasIO(IO)).toBe(true));
  it('hasIO(Pure) === false',      () => expect(hasIO(Pure)).toBe(false));
});

describe('combineEffects – algebraic laws', () => {
  it('[] → Pure',                  () => expect(combineEffects([])).toEqual(Pure));
  it('[Pure] → Pure',              () => expect(combineEffects([Pure])).toEqual(Pure));
  it('[IO] → IO',                  () => expect(combineEffects([IO])).toEqual(IO));
  it('[Pure, IO] → IO',            () => expect(combineEffects([Pure, IO])).toEqual(IO));
  it('[IO, Pure] → IO',            () => expect(combineEffects([IO, Pure])).toEqual(IO));
  it('[IO, IO] → IO (dedup)',      () => expect(combineEffects([IO, IO])).toEqual(IO));
  it('[Async, Async] → Async',     () => expect(combineEffects([Async, Async])).toEqual(Async));
  it('[IO, Async] → Combined',     () => expect(combineEffects([IO, Async]).tag).toBe('Combined'));
  it('Combined flat (no nesting)', () => {
    const inner = combineEffects([IO, Async]);
    const outer = combineEffects([inner, stateEffect(TyNat)]);
    expect(outer.tag).toBe('Combined');
    if (outer.tag === 'Combined') expect(outer.effects.every(e => e.tag !== 'Combined')).toBe(true);
  });
  it('Pure is identity element', () => {
    const e = stateEffect(TyString);
    expect(combineEffects([Pure, e])).toEqual(e);
    expect(combineEffects([e, Pure])).toEqual(e);
  });
});

describe('IRType primitives', () => {
  it('TyNat.tag',    () => expect(TyNat.tag).toBe('Nat'));
  it('TyInt.tag',    () => expect(TyInt.tag).toBe('Int'));
  it('TyFloat.tag',  () => expect(TyFloat.tag).toBe('Float'));
  it('TyString.tag', () => expect(TyString.tag).toBe('String'));
  it('TyBool.tag',   () => expect(TyBool.tag).toBe('Bool'));
  it('TyUnit.tag',   () => expect(TyUnit.tag).toBe('Unit'));
  it('TyNever.tag',  () => expect(TyNever.tag).toBe('Never'));
});

describe('IRType constructors', () => {
  it('TyOption wraps inner', () => {
    const t = TyOption(TyString);
    expect(t.tag).toBe('Option');
    if (t.tag === 'Option') expect(t.inner).toEqual(TyString);
  });

  it('TyArray wraps elem', () => {
    const t = TyArray(TyNat);
    expect(t.tag).toBe('Array');
    if (t.tag === 'Array') expect(t.elem).toEqual(TyNat);
  });

  it('TyTuple wraps elems', () => {
    const t = TyTuple([TyString, TyNat]);
    expect(t.tag).toBe('Tuple');
    if (t.tag === 'Tuple') expect(t.elems).toHaveLength(2);
  });

  it('TyMap(key, value)', () => {
    const t = TyMap(TyString, TyNat);
    expect(t.tag).toBe('Map');
    if (t.tag === 'Map') { expect(t.key).toEqual(TyString); expect(t.value).toEqual(TyNat); }
  });

  it('TySet(elem)', () => {
    const t = TySet(TyString);
    expect(t.tag).toBe('Set');
    if (t.tag === 'Set') expect(t.elem).toEqual(TyString);
  });

  it('TyPromise(inner)', () => {
    const t = TyPromise(TyBool);
    expect(t.tag).toBe('Promise');
    if (t.tag === 'Promise') expect(t.inner).toEqual(TyBool);
  });

  it('TyResult(ok, err)', () => {
    const t = TyResult(TyString, TyNat);
    expect(t.tag).toBe('Result');
    if (t.tag === 'Result') { expect(t.ok).toEqual(TyString); expect(t.err).toEqual(TyNat); }
  });

  it('TyRef(name, args)', () => {
    const t = TyRef('Foo', [TyString]);
    expect(t.tag).toBe('TypeRef');
    if (t.tag === 'TypeRef') { expect(t.name).toBe('Foo'); expect(t.args).toHaveLength(1); }
  });

  it('TyVar(name)', () => {
    const t = TyVar('T');
    expect(t.tag).toBe('TypeVar');
    if (t.tag === 'TypeVar') expect(t.name).toBe('T');
  });

  it('TyFn(params, ret, effect)', () => {
    const t = TyFn([TyString], TyBool, Pure);
    expect(t.tag).toBe('Function');
    if (t.tag === 'Function') {
      expect(t.params).toHaveLength(1);
      expect(t.ret).toEqual(TyBool);
      expect(t.effect).toEqual(Pure);
    }
  });
});

describe('IR expression smart constructors', () => {
  it('litStr', () => {
    const e = litStr('hello');
    expect(e.tag).toBe('LitString');
    if (e.tag === 'LitString') expect(e.value).toBe('hello');
    expect(e.type).toEqual(TyString);
    expect(e.effect).toEqual(Pure);
  });

  it('litNat', () => {
    const e = litNat(42);
    expect(e.tag).toBe('LitNat');
    if (e.tag === 'LitNat') expect(e.value).toBe(42);
    expect(e.type).toEqual(TyNat);
  });

  it('litBool(true)', () => {
    const e = litBool(true);
    expect(e.tag).toBe('LitBool');
    if (e.tag === 'LitBool') expect(e.value).toBe(true);
    expect(e.type).toEqual(TyBool);
  });

  it('litUnit', () => {
    const e = litUnit();
    expect(e.tag).toBe('LitUnit');
    expect(e.type).toEqual(TyUnit);
  });

  it('varExpr', () => {
    const e = varExpr('x', TyNat);
    expect(e.tag).toBe('Var');
    if (e.tag === 'Var') expect(e.name).toBe('x');
    expect(e.type).toEqual(TyNat);
    expect(e.effect).toEqual(Pure);
  });

  it('holeExpr', () => {
    const e = holeExpr(TyBool);
    expect(e.tag).toBe('Hole');
    expect(e.type).toEqual(TyBool);
    expect(e.effect).toEqual(Pure);
  });
});
