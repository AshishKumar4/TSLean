/**
 * @module typemap
 *
 * Type mapper: TypeScript compiler types → IR types.
 *
 * Uses the TypeChecker for fully-resolved types, handling generics, mapped
 * types, branded newtypes, discriminated unions, and conditional types.
 *
 * Key mappings:
 *   `number`              → `Float` (default; `Nat`/`Int` when context implies)
 *   `string`              → `String`
 *   `boolean`             → `Bool`
 *   `T | undefined`       → `Option T`
 *   `Promise<T>`          → `IO T`
 *   `Map<K, V>`           → `AssocMap K V`
 *   `string & {__brand:X}`→ branded newtype (`TyRef(alias)`)
 *
 * Pipeline position:  TS AST → **Type Mapper** → IR types → Codegen
 */

import * as ts from 'typescript';
import {
  IRType, Pure,
  TyNat, TyInt, TyFloat, TyString, TyBool, TyUnit, TyNever,
  TyOption, TyArray, TyTuple, TyFn, TyMap, TySet, TyPromise,
  TyRef, TyVar,
} from '../ir/types.js';

// ─── Constants ──────────────────────────────────────────────────────────────────

/** Recursion depth limit to prevent infinite loops on circular types. */
const MAX_TYPE_DEPTH = 20;

/** Fallback name for type parameters when the symbol has no name. */
const FALLBACK_TYPE_VAR = 'α';

/** Sentinel name for anonymous object types (TypeScript uses `__type` internally). */
const TS_ANON_TYPE = '__type';

/**
 * Field names commonly used as discriminants in TypeScript discriminated unions.
 * Checked in order — the first matching field wins.
 */
const DISCRIMINANT_FIELDS = ['kind', 'type', 'tag', 'ok', 'hasValue', '_type'];

// ─── Main entry ─────────────────────────────────────────────────────────────────

/**
 * Map a TypeScript compiler type to an IR type.
 *
 * Handles primitives, unions, intersections, arrays, tuples, object types,
 * generic references, conditional types, and branded newtypes.
 *
 * @param t       - The TypeScript type from the type checker.
 * @param checker - The TypeChecker instance for the program.
 * @param depth   - Current recursion depth (guards against circular types).
 * @returns The corresponding IR type.
 */
export function mapType(t: ts.Type, checker: ts.TypeChecker, depth = 0): IRType {
  if (depth > MAX_TYPE_DEPTH) return TyRef('Any');

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
  if (f & ts.TypeFlags.TypeParameter)  return TyVar(t.symbol?.name ?? FALLBACK_TYPE_VAR);

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
    // Access the resolved true branch — this is an internal TS API property
    // that's stable across TS versions but not in the public typings.
    const c = t as ts.ConditionalType;
    const resolved = (c as { resolvedTrueType?: ts.Type }).resolvedTrueType;
    return mapType(resolved ?? c.checkType, checker, depth + 1);
  }
  if (f & ts.TypeFlags.Index) return TyString;

  return TyRef(checker.typeToString(t));
}

// ─── Union types ────────────────────────────────────────────────────────────────

function mapUnion(t: ts.UnionType, checker: ts.TypeChecker, depth: number): IRType {
  const types = t.types;

  // T | undefined/null → Option T
  const withoutNil = types.filter(x => !(x.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null)));
  if (withoutNil.length === 1 && withoutNil.length < types.length)
    return TyOption(mapType(withoutNil[0], checker, depth + 1));

  // All string literals → use the alias name if available
  if (types.every(x => x.flags & ts.TypeFlags.StringLiteral)) {
    const alias = getAliasName(t);
    return alias ? TyRef(alias) : TyString;
  }

  // true | false → Bool
  if (types.length === 2 && types.every(x => x.flags & ts.TypeFlags.BooleanLiteral))
    return TyBool;

  // Named alias (e.g. `type Status = "active" | "inactive"`, `Tree<T>`)
  const alias = getAliasName(t);
  if (alias) {
    // Propagate alias type arguments (e.g. Tree<T> → TyRef('Tree', [TyVar('T')]))
    const aliasArgs = (t as any).aliasTypeArguments as ts.Type[] | undefined;
    if (aliasArgs && aliasArgs.length > 0) {
      return TyRef(alias, aliasArgs.map(a => mapType(a, checker, depth + 1)));
    }
    return TyRef(alias);
  }

  return withoutNil.length > 0 ? mapType(withoutNil[0], checker, depth + 1) : TyRef('Any');
}

// ─── Intersection types ─────────────────────────────────────────────────────────

function mapIntersection(t: ts.IntersectionType, checker: ts.TypeChecker, depth: number): IRType {
  // Branded newtype: `string & { __brand: "UserId" }`
  const base  = t.types.find(x => x.flags & (ts.TypeFlags.String | ts.TypeFlags.Number));
  const brand = t.types.find(x => (x.flags & ts.TypeFlags.Object) &&
    (x as ts.ObjectType).getProperties().some(p => p.name.startsWith('__brand') || p.name.startsWith('_brand')));
  if (base && brand) {
    const alias = getAliasName(t);
    return alias ? TyRef(alias) : (base.flags & ts.TypeFlags.String ? TyString : TyFloat);
  }

  const alias = getAliasName(t);
  if (alias) return TyRef(alias);

  const concrete = t.types.find(x => !(x.flags & ts.TypeFlags.Object) ||
    (x as ts.ObjectType).getProperties().length > 0);
  return concrete ? mapType(concrete, checker, depth + 1) : TyRef('Any');
}

// ─── Object types ───────────────────────────────────────────────────────────────

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

  // Anonymous object types (e.g. { name: string }) can't be directly expressed in Lean.
  // Map them to String (serialised) as a compilable approximation.
  // Map well-known JS types to Lean equivalents
  const name = sym.name;
  if (name === TS_ANON_TYPE) return TyRef('String');
  if (name === 'Error' || name.endsWith('Error')) return TyString;  // JS Error → String for Lean
  return TyRef(name);
}

// ─── Generic type references ────────────────────────────────────────────────────

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
    case 'Readonly':      case 'NonNullable':   return map1();
    default:
      return args.length === 0 ? TyRef(name) : TyRef(name, args.map(a => mapType(a, checker, depth + 1)));
  }
}

// ─── IR type → Lean 4 syntax ────────────────────────────────────────────────────

/**
 * Convert an IR type to its Lean 4 syntax string.
 *
 * @param t      - The IR type to render.
 * @param parens - If true, wrap multi-word types in parentheses for
 *                 use as function arguments (e.g. `(Array Nat)`).
 * @returns A valid Lean 4 type expression.
 *
 * @example
 * irTypeToLean({ tag: 'Array', elem: { tag: 'Nat' } })       // "Array Nat"
 * irTypeToLean({ tag: 'Array', elem: { tag: 'Nat' } }, true) // "(Array Nat)"
 */
export function irTypeToLean(t: IRType, parens = false): string {
  const s = typeStr(t);
  return parens && s.includes(' ') ? `(${s})` : s;
}

function typeStr(t: IRType): string {
  switch (t.tag) {
    case 'Nat':       return 'Nat';
    case 'Int':       return 'Int';
    case 'Float':     return 'Float';
    case 'String':    return 'String';
    case 'Bool':      return 'Bool';
    case 'Unit':      return 'Unit';
    case 'Never':     return 'Empty';
    case 'Option':    return `Option ${irTypeToLean(t.inner, true)}`;
    case 'Array':     return `Array ${irTypeToLean(t.elem, true)}`;
    case 'Tuple':     return t.elems.length === 0 ? 'Unit' : `(${t.elems.map(typeStr).join(' × ')})`;
    case 'Function': {
      // Empty params () → T becomes Unit → T in Lean
      const paramStr = t.params.length === 0 ? 'Unit' : t.params.map(p => irTypeToLean(p, true)).join(' → ');
      return `${paramStr} → ${typeStr(t.ret)}`;
    }
    case 'Map':       return `AssocMap ${irTypeToLean(t.key, true)} ${irTypeToLean(t.value, true)}`;
    case 'Set':       return `AssocSet ${irTypeToLean(t.elem, true)}`;
    case 'Promise': {
      // Flatten nested IO: Promise<Promise<T>> → IO T (not IO (IO T))
      const inner = t.inner;
      if (inner.tag === 'Promise') return `IO ${irTypeToLean(inner.inner, true)}`;
      return `IO ${irTypeToLean(inner, true)}`;
    }
    case 'Result':    return `Except ${irTypeToLean(t.err, true)} ${irTypeToLean(t.ok, true)}`;
    case 'TypeRef': {
      // Map TS-specific types to Any (no Lean equivalent)
      const tsOnlyTypes = new Set(['CompilerHost', 'SourceFile', 'Program', 'TypeChecker',
        'Node', 'Statement', 'Declaration', 'Expression', 'FunctionDeclaration',
        'ClassDeclaration', 'InterfaceDeclaration', 'TypeAliasDeclaration',
        'VariableStatement', 'ModuleDeclaration', 'EnumDeclaration',
        'PropertyAccessExpression', 'CallExpression', 'BinaryExpression',
        'ReadableStream', 'ArrayBuffer', 'ArrayBufferView', 'IterableIterator',
        'Generator', 'AsyncGenerator', 'PromiseLike', 'RegExp',
        'SymbolConstructor', 'PropertyDescriptor', 'PropertyKey']);
      if (tsOnlyTypes.has(t.name)) return 'Any';
      return t.args.length === 0 ? t.name : `${t.name} ${t.args.map(a => irTypeToLean(a, true)).join(' ')}`;
    }
    case 'TypeVar':   return t.name;
    case 'Structure': return t.name;
    case 'Inductive': return t.name;
    case 'Dependent': return `(${t.param} : ${typeStr(t.paramType)}) → ${typeStr(t.body)}`;
    case 'Subtype':   return `{x : ${typeStr(t.base)} // ${t.refinement}}`;
    case 'Universe':  return t.level === 0 ? 'Prop' : `Type ${t.level}`;
    default:          return 'Any';
  }
}

// ─── Struct field extraction ────────────────────────────────────────────────────

/** A single field extracted from a TypeScript interface or class declaration. */
export interface StructField {
  name: string;
  type: IRType;
  optional: boolean;
  mutable: boolean;
}

/**
 * Extract struct fields from a TypeScript interface or class declaration.
 *
 * Handles optional fields (`?`), readonly modifiers, and resolves types
 * via the type checker.
 */
export function extractStructFields(
  node: ts.InterfaceDeclaration | ts.ClassDeclaration,
  checker: ts.TypeChecker,
): StructField[] {
  const out: StructField[] = [];
  for (const m of node.members) {
    if (!ts.isPropertySignature(m) && !ts.isPropertyDeclaration(m)) continue;
    const name = m.name?.getText() ?? '';
    const sym  = checker.getSymbolAtLocation(m.name!);
    const ty   = sym ? checker.getTypeOfSymbol(sym) : checker.getAnyType();
    const opt  = !!m.questionToken;
    const mut  = !m.modifiers?.some(mod => mod.kind === ts.SyntaxKind.ReadonlyKeyword);
    out.push({
      name,
      type: opt ? TyOption(mapType(ty, checker)) : mapType(ty, checker),
      optional: opt,
      mutable: mut,
    });
  }
  return out;
}

// ─── Discriminated union detection ──────────────────────────────────────────────

/** Result of detecting a discriminated union in a TypeScript union type. */
export interface DiscriminantInfo {
  /** The field name used as the discriminant (e.g. "kind"). */
  field: string;
  /** Each variant with its literal value and non-discriminant fields. */
  variants: Array<{ literal: string; fields: StructField[] }>;
}

/**
 * Detect whether a TypeScript union type is a discriminated union.
 *
 * Checks each known discriminant field name in priority order.  Returns
 * the first field for which every union member has a unique string literal value.
 *
 * @param t       - The TypeScript union type.
 * @param checker - The TypeChecker for resolving field types.
 * @returns Discriminant info if detected, or `null`.
 */
export function detectDiscriminatedUnion(
  t: ts.UnionType,
  checker: ts.TypeChecker,
): DiscriminantInfo | null {
  const objTypes = t.types.filter(x => x.flags & ts.TypeFlags.Object) as ts.ObjectType[];
  if (objTypes.length < 2) return null;

  for (const field of DISCRIMINANT_FIELDS) {
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
      fields.push({
        name: sym.name,
        type: opt ? TyOption(mapType(st, checker)) : mapType(st, checker),
        optional: opt,
        mutable: true,
      });
    }
    variants.push({ literal: lit, fields });
  }
  return variants.length === types.length ? { field, variants } : null;
}

// ─── Type parameter extraction ──────────────────────────────────────────────────

/**
 * Extract type parameter names from a TypeScript declaration.
 * @returns Array of parameter names (e.g. `["T", "U"]`).
 */
export function extractTypeParams(
  node: ts.InterfaceDeclaration | ts.ClassDeclaration | ts.TypeAliasDeclaration |
        ts.FunctionDeclaration | ts.MethodDeclaration | ts.ArrowFunction | ts.FunctionExpression,
): string[] {
  return (node.typeParameters ?? []).map(tp => tp.name.text);
}

// ─── Helpers ────────────────────────────────────────────────────────────────────

/**
 * Access the `aliasSymbol.name` on a TypeScript type.
 *
 * This property is not in the public TS API typings but is stable across
 * TypeScript versions (4.x–5.x).  It gives the user-defined alias name
 * for union and intersection types.
 */
function getAliasName(t: ts.Type): string | undefined {
  return (t as { aliasSymbol?: ts.Symbol }).aliasSymbol?.name;
}
