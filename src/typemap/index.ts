// Type mapper: TypeScript compiler types → IR types.
// Uses the TypeChecker for fully resolved types.

import * as ts from 'typescript';
import {
  IRType, Pure,
  TyNat, TyInt, TyFloat, TyString, TyBool, TyUnit, TyNever,
  TyOption, TyArray, TyTuple, TyFn, TyMap, TySet, TyPromise,
  TyRef, TyVar,
} from '../ir/types.js';

// ─── Main entry ───────────────────────────────────────────────────────────────

export function mapType(t: ts.Type, checker: ts.TypeChecker, depth = 0): IRType {
  if (depth > 20) return TyRef('Any');

  const f = t.flags;
  if (f & ts.TypeFlags.String)         return TyString;
  if (f & ts.TypeFlags.Number)         return TyFloat;
  if (f & ts.TypeFlags.Boolean)        return TyBool;
  if (f & ts.TypeFlags.Undefined)      return TyOption(TyUnit);
  if (f & ts.TypeFlags.Null)           return TyOption(TyUnit);
  if (f & ts.TypeFlags.Void)           return TyUnit;
  if (f & ts.TypeFlags.Never)          return TyNever;
  if (f & ts.TypeFlags.Any)            return TyRef('Any');
  if (f & ts.TypeFlags.Unknown)        return TyRef('Any');
  if (f & ts.TypeFlags.BigInt)         return TyInt;
  if (f & ts.TypeFlags.StringLiteral)  return TyString;
  if (f & ts.TypeFlags.NumberLiteral)  return TyFloat;
  if (f & ts.TypeFlags.BooleanLiteral) return TyBool;
  if (f & ts.TypeFlags.TypeParameter)  return TyVar(t.symbol?.name ?? 'α');

  if (t.isUnion())        return mapUnion(t, checker, depth);
  if (t.isIntersection()) return mapIntersection(t, checker, depth);

  if (checker.isArrayType(t)) {
    const elem = checker.getTypeArguments(t as ts.TypeReference)[0];
    return TyArray(elem ? mapType(elem, checker, depth + 1) : TyRef('Any'));
  }
  if (checker.isTupleType(t)) {
    const args = checker.getTypeArguments(t as ts.TypeReference);
    return TyTuple(args.map(a => mapType(a, checker, depth + 1)));
  }

  if (f & ts.TypeFlags.Object) return mapObject(t as ts.ObjectType, checker, depth);
  if (f & ts.TypeFlags.Conditional) {
    const c = t as ts.ConditionalType;
    return mapType((c as any).resolvedTrueType ?? c.checkType, checker, depth + 1);
  }
  if (f & ts.TypeFlags.Index) return TyString;

  return TyRef(checker.typeToString(t));
}

function mapUnion(t: ts.UnionType, checker: ts.TypeChecker, depth: number): IRType {
  const types = t.types;
  // Filter out undefined/null → Option T
  const withoutNil = types.filter(x => !(x.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null)));
  if (withoutNil.length === 1 && withoutNil.length < types.length)
    return TyOption(mapType(withoutNil[0], checker, depth + 1));

  // All string literals → alias name or string
  if (types.every(x => x.flags & ts.TypeFlags.StringLiteral)) {
    const alias = (t as any).aliasSymbol?.name;
    return alias ? TyRef(alias) : TyString;
  }

  // Boolean union
  if (types.length === 2 && types.every(x => x.flags & ts.TypeFlags.BooleanLiteral))
    return TyBool;

  // Named alias
  const alias = (t as any).aliasSymbol?.name;
  if (alias) return TyRef(alias);

  return withoutNil.length > 0 ? mapType(withoutNil[0], checker, depth + 1) : TyRef('Any');
}

function mapIntersection(t: ts.IntersectionType, checker: ts.TypeChecker, depth: number): IRType {
  // Branded type: string & { __brand: "X" }
  const base  = t.types.find(x => x.flags & (ts.TypeFlags.String | ts.TypeFlags.Number));
  const brand = t.types.find(x => (x.flags & ts.TypeFlags.Object) &&
    (x as ts.ObjectType).getProperties().some(p => p.name.startsWith('__brand') || p.name.startsWith('_brand')));
  if (base && brand) {
    const alias = (t as any).aliasSymbol?.name;
    return alias ? TyRef(alias) : (base.flags & ts.TypeFlags.String ? TyString : TyFloat);
  }

  const alias = (t as any).aliasSymbol?.name;
  if (alias) return TyRef(alias);

  const concrete = t.types.find(x => !(x.flags & ts.TypeFlags.Object) ||
    (x as ts.ObjectType).getProperties().length > 0);
  return concrete ? mapType(concrete, checker, depth + 1) : TyRef('Any');
}

function mapObject(t: ts.ObjectType, checker: ts.TypeChecker, depth: number): IRType {
  if (t.objectFlags & ts.ObjectFlags.Reference)
    return mapTypeRef(t as ts.TypeReference, checker, depth);

  const sym = t.symbol;
  if (!sym) return TyRef('Any');

  // Call signatures → function type
  const calls = checker.getSignaturesOfType(t, ts.SignatureKind.Call);
  if (calls.length > 0) {
    const sig = calls[0];
    const params = sig.getParameters().map(p => {
      const pt = checker.getTypeOfSymbolAtLocation(p, p.valueDeclaration ?? p.declarations?.[0]!);
      return mapType(pt, checker, depth + 1);
    });
    return TyFn(params, mapType(checker.getReturnTypeOfSignature(sig), checker, depth + 1), Pure);
  }

  return TyRef(sym.name === '__type' ? 'AnonStruct' : sym.name);
}

function mapTypeRef(t: ts.TypeReference, checker: ts.TypeChecker, depth: number): IRType {
  const name = t.target.symbol?.name ?? '';
  const args = checker.getTypeArguments(t);
  const map1 = () => args[0] ? mapType(args[0], checker, depth + 1) : TyRef('Any');
  const map2 = (i: number) => args[i] ? mapType(args[i], checker, depth + 1) : TyRef('Any');

  switch (name) {
    case 'Array':         case 'ReadonlyArray': return TyArray(map1());
    case 'Map':           case 'WeakMap':       return TyMap(map1(), map2(1));
    case 'Set':           case 'WeakSet':       return TySet(map1());
    case 'Promise':                             return TyPromise(map1());
    case 'Record':                              return TyMap(map1(), map2(1));
    case 'Readonly':                            return map1();
    case 'NonNullable':                         return map1();
    case 'Partial':
    case 'Required':
    case 'Pick':
    case 'Omit':
      return args.length === 0 ? TyRef(name) : TyRef(name, args.map(a => mapType(a, checker, depth + 1)));
    default:
      return args.length === 0 ? TyRef(name) : TyRef(name, args.map(a => mapType(a, checker, depth + 1)));
  }
}

// ─── irTypeToLean ─────────────────────────────────────────────────────────────

export function irTypeToLean(t: IRType, parens = false): string {
  const s = typeStr(t);
  return parens && s.includes(' ') ? `(${s})` : s;
}

function typeStr(t: IRType): string {
  switch (t.tag) {
    case 'Nat':    return 'Nat';
    case 'Int':    return 'Int';
    case 'Float':  return 'Float';
    case 'String': return 'String';
    case 'Bool':   return 'Bool';
    case 'Unit':   return 'Unit';
    case 'Never':  return 'Empty';
    case 'Option': return `Option ${irTypeToLean(t.inner, true)}`;
    case 'Array':  return `Array ${irTypeToLean(t.elem, true)}`;
    case 'Tuple':  return t.elems.length === 0 ? 'Unit' : `(${t.elems.map(e => typeStr(e)).join(' × ')})`;
    case 'Function': {
      const ps = t.params.map(p => irTypeToLean(p, true)).join(' → ');
      return `${ps} → ${typeStr(t.ret)}`;
    }
    case 'Map':      return `AssocMap ${irTypeToLean(t.key, true)} ${irTypeToLean(t.value, true)}`;
    case 'Set':      return `AssocSet ${irTypeToLean(t.elem, true)}`;
    case 'Promise':  return `IO ${irTypeToLean(t.inner, true)}`;
    case 'Result':   return `Except ${irTypeToLean(t.err, true)} ${irTypeToLean(t.ok, true)}`;
    case 'TypeRef':
      return t.args.length === 0 ? t.name : `${t.name} ${t.args.map(a => irTypeToLean(a, true)).join(' ')}`;
    case 'TypeVar':  return t.name;
    case 'Structure': return t.name;
    case 'Inductive': return t.name;
    case 'Dependent': return `(${t.param} : ${typeStr(t.paramType)}) → ${typeStr(t.body)}`;
    case 'Subtype':   return `{x : ${typeStr(t.base)} // ${t.refinement}}`;
    case 'Universe':
      return t.level === 0 ? 'Prop' : (t.level === 1 ? 'Type' : `Type ${t.level}`);
    default: return 'Any';
  }
}

// ─── Struct field extraction ──────────────────────────────────────────────────

export interface StructField { name: string; type: IRType; optional: boolean; mutable: boolean }

export function extractStructFields(
  node: ts.InterfaceDeclaration | ts.ClassDeclaration,
  checker: ts.TypeChecker
): StructField[] {
  const out: StructField[] = [];
  for (const m of node.members) {
    if (!ts.isPropertySignature(m) && !ts.isPropertyDeclaration(m)) continue;
    const name = m.name?.getText() ?? '';
    const sym  = checker.getSymbolAtLocation(m.name!);
    const ty   = sym ? checker.getTypeOfSymbol(sym) : checker.getAnyType();
    const opt  = !!m.questionToken;
    const mut  = !m.modifiers?.some(mod => mod.kind === ts.SyntaxKind.ReadonlyKeyword);
    out.push({ name, type: opt ? TyOption(mapType(ty, checker)) : mapType(ty, checker), optional: opt, mutable: mut });
  }
  return out;
}

// ─── Discriminated union detection ───────────────────────────────────────────

const DISC_FIELDS = ['kind', 'type', 'tag', 'ok', 'hasValue', '_type'];

export interface DiscriminantInfo {
  field: string;
  variants: Array<{ literal: string; fields: StructField[] }>;
}

export function detectDiscriminatedUnion(
  t: ts.UnionType,
  checker: ts.TypeChecker
): DiscriminantInfo | null {
  const objTypes = t.types.filter(x => x.flags & ts.TypeFlags.Object) as ts.ObjectType[];
  if (objTypes.length < 2) return null;

  for (const field of DISC_FIELDS) {
    const info = tryField(objTypes, field, checker);
    if (info) return info;
  }
  return null;
}

function tryField(types: ts.ObjectType[], field: string, checker: ts.TypeChecker): DiscriminantInfo | null {
  const variants: DiscriminantInfo['variants'] = [];
  for (const t of types) {
    const prop = t.getProperty(field);
    if (!prop) return null;
    const pt = checker.getTypeOfSymbol(prop);
    if (!(pt.flags & ts.TypeFlags.StringLiteral)) return null;
    const lit = (pt as ts.StringLiteralType).value;
    const fields: StructField[] = [];
    for (const sym of t.getProperties()) {
      if (sym.name === field) continue;
      const st = checker.getTypeOfSymbol(sym);
      const opt = !!(sym.flags & ts.SymbolFlags.Optional);
      fields.push({ name: sym.name, type: opt ? TyOption(mapType(st, checker)) : mapType(st, checker), optional: opt, mutable: true });
    }
    variants.push({ literal: lit, fields });
  }
  return variants.length === types.length ? { field, variants } : null;
}

// ─── Type param extraction ────────────────────────────────────────────────────

export function extractTypeParams(
  node: ts.InterfaceDeclaration | ts.ClassDeclaration | ts.TypeAliasDeclaration |
        ts.FunctionDeclaration | ts.MethodDeclaration | ts.ArrowFunction | ts.FunctionExpression
): string[] {
  return (node.typeParameters ?? []).map(tp => tp.name.text);
}
