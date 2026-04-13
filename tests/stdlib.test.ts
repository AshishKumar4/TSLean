// Tests for stdlib mappings.

import { describe, it, expect } from 'vitest';
import { lookupMethod, lookupGlobal, translateBinOp, typeObjKind } from '../src/stdlib/index.js';
import { TyString, TyFloat, TyNat, TyArray } from '../src/ir/types.js';

describe('lookupMethod – String', () => {
  it('length',       () => expect(lookupMethod('String', 'length')?.leanFn).toBe('String.length'));
  it('toUpperCase',  () => expect(lookupMethod('String', 'toUpperCase')?.leanFn).toBe('String.toUpper'));
  it('toLowerCase',  () => expect(lookupMethod('String', 'toLowerCase')?.leanFn).toBe('String.toLower'));
  it('trim',         () => expect(lookupMethod('String', 'trim')?.leanFn).toBe('String.trim'));
  it('includes (flip)', () => { const t = lookupMethod('String', 'includes'); expect(t?.argOrder).toBe('flip'); });
  it('split',        () => expect(lookupMethod('String', 'split')?.leanFn).toBe('String.splitOn'));
  it('indexOf',      () => expect(lookupMethod('String', 'indexOf')?.leanFn).toBe('String.firstIndexOf'));
  it('unknown → undefined', () => expect(lookupMethod('String', 'nonExistent')).toBeUndefined());
});

describe('lookupMethod – Array', () => {
  it('map',         () => expect(lookupMethod('Array', 'map')?.leanFn).toBe('Array.map'));
  it('filter',      () => expect(lookupMethod('Array', 'filter')?.leanFn).toBe('Array.filter'));
  it('reduce',      () => expect(lookupMethod('Array', 'reduce')?.leanFn).toBe('Array.foldl'));
  it('find',        () => expect(lookupMethod('Array', 'find')?.leanFn).toBe('Array.find?'));
  it('forEach (io)',() => expect(lookupMethod('Array', 'forEach')?.io).toBe(true));
  it('some',        () => expect(lookupMethod('Array', 'some')?.leanFn).toBe('Array.any'));
  it('every',       () => expect(lookupMethod('Array', 'every')?.leanFn).toBe('Array.all'));
  it('includes',    () => expect(lookupMethod('Array', 'includes')?.leanFn).toBe('Array.contains'));
  it('length',      () => expect(lookupMethod('Array', 'length')?.leanFn).toBe('Array.size'));
  it('reverse',     () => expect(lookupMethod('Array', 'reverse')?.leanFn).toBe('Array.reverse'));
  it('flat',        () => expect(lookupMethod('Array', 'flat')?.leanFn).toBe('Array.join'));
});

describe('lookupMethod – Map', () => {
  it('get',    () => expect(lookupMethod('Map', 'get')?.leanFn).toBe('AssocMap.find?'));
  it('set',    () => expect(lookupMethod('Map', 'set')?.leanFn).toBe('AssocMap.insert'));
  it('has',    () => expect(lookupMethod('Map', 'has')?.leanFn).toBe('AssocMap.contains'));
  it('delete', () => expect(lookupMethod('Map', 'delete')?.leanFn).toBe('AssocMap.erase'));
  it('size',   () => expect(lookupMethod('Map', 'size')?.leanFn).toBe('AssocMap.size'));
});

describe('lookupMethod – Set', () => {
  it('add',    () => expect(lookupMethod('Set', 'add')?.leanFn).toBe('AssocSet.insert'));
  it('has',    () => expect(lookupMethod('Set', 'has')?.leanFn).toBe('AssocSet.contains'));
  it('delete', () => expect(lookupMethod('Set', 'delete')?.leanFn).toBe('AssocSet.erase'));
});

describe('lookupGlobal', () => {
  it('console.log (io)',   () => { const g = lookupGlobal('console.log'); expect(g?.leanExpr).toBe('IO.println'); expect(g?.io).toBe(true); });
  it('console.error (io)', () => expect(lookupGlobal('console.error')?.io).toBe(true));
  it('Math.floor (pure)',  () => { const g = lookupGlobal('Math.floor'); expect(g?.leanExpr).toBe('Float.floor'); expect(g?.io).toBeFalsy(); });
  it('Math.sqrt',          () => expect(lookupGlobal('Math.sqrt')?.leanFn ?? lookupGlobal('Math.sqrt')?.leanExpr).toBe('Float.sqrt'));
  it('Math.max',           () => expect(lookupGlobal('Math.max')?.leanExpr).toBe('max'));
  it('Math.random (io)',   () => expect(lookupGlobal('Math.random')?.io).toBe(true));
  it('Date.now (io)',      () => expect(lookupGlobal('Date.now')).toBeDefined());
  it('parseInt',           () => expect(lookupGlobal('parseInt')?.leanExpr).toBe('sorry'));
  it('JSON.stringify',     () => expect(lookupGlobal('JSON.stringify')?.leanExpr).toBe('serialize'));
  it('JSON.parse',         () => expect(lookupGlobal('JSON.parse')?.leanExpr).toBe('deserialize'));
  it('Object.keys',        () => expect(lookupGlobal('Object.keys')?.leanExpr).toBe('AssocMap.keys'));
  it('Array.from',         () => expect(lookupGlobal('Array.from')?.leanExpr).toBe('Array.ofList'));
  it('Promise.resolve',    () => expect(lookupGlobal('Promise.resolve')?.leanExpr).toBe('pure'));
  it('structuredClone',    () => expect(lookupGlobal('structuredClone')?.leanExpr).toBe('id'));
  it('unknown → undefined', () => expect(lookupGlobal('unknownFunction')).toBeUndefined());
});

describe('translateBinOp', () => {
  it('Add Float → +',      () => expect(translateBinOp('Add', TyFloat)).toBe('+'));
  it('Add String → ++',    () => expect(translateBinOp('Add', TyString)).toBe('++'));
  it('Sub',                () => expect(translateBinOp('Sub',  TyFloat)).toBe('-'));
  it('Mul',                () => expect(translateBinOp('Mul',  TyFloat)).toBe('*'));
  it('Div',                () => expect(translateBinOp('Div',  TyFloat)).toBe('/'));
  it('Mod',                () => expect(translateBinOp('Mod',  TyNat)).toBe('%'));
  it('Eq',                 () => expect(translateBinOp('Eq',   TyFloat)).toBe('=='));
  it('Ne',                 () => expect(translateBinOp('Ne',   TyFloat)).toBe('!='));
  it('Lt',                 () => expect(translateBinOp('Lt',   TyFloat)).toBe('<'));
  it('Le',                 () => expect(translateBinOp('Le',   TyFloat)).toBe('<='));
  it('Gt',                 () => expect(translateBinOp('Gt',   TyFloat)).toBe('>'));
  it('Ge',                 () => expect(translateBinOp('Ge',   TyFloat)).toBe('>='));
  it('And',                () => expect(translateBinOp('And',  TyFloat)).toBe('&&'));
  it('Or',                 () => expect(translateBinOp('Or',   TyFloat)).toBe('||'));
  it('Concat',             () => expect(translateBinOp('Concat', TyString)).toBe('++'));
  it('BitAnd',             () => expect(translateBinOp('BitAnd', TyNat)).toBe('&&&'));
  it('BitOr',              () => expect(translateBinOp('BitOr',  TyNat)).toBe('|||'));
  it('Shl',                () => expect(translateBinOp('Shl',  TyNat)).toBe('<<<'));
  it('Shr',                () => expect(translateBinOp('Shr',  TyNat)).toBe('>>>'));
});

describe('typeObjKind', () => {
  it('TyString → String',      () => expect(typeObjKind(TyString)).toBe('String'));
  it('TyArray → Array',        () => expect(typeObjKind(TyArray(TyNat))).toBe('Array'));
  it('TyFloat → unknown',      () => expect(typeObjKind(TyFloat)).toBe('unknown'));
  it('TypeRef Map → Map',      () => expect(typeObjKind({ tag: 'TypeRef', name: 'Map', args: [] })).toBe('Map'));
  it('TypeRef AssocMap → Map', () => expect(typeObjKind({ tag: 'TypeRef', name: 'AssocMap', args: [] })).toBe('Map'));
  it('TypeRef Set → Set',      () => expect(typeObjKind({ tag: 'TypeRef', name: 'Set', args: [] })).toBe('Set'));
  it('TypeRef AssocSet → Set', () => expect(typeObjKind({ tag: 'TypeRef', name: 'AssocSet', args: [] })).toBe('Set'));
});
