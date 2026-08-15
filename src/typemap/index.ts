/**
 * @module typemap
 *
 * Type mapper: TypeScript compiler types → IR types.
 *
 * Uses the TypeChecker for fully-resolved types, handling generics, mapped
 * types, branded newtypes, discriminated unions, and conditional types.
 *
 * Key mappings, into the IR — the Lean carrier for each is chosen later, by
 * `LowerCtx.lowerType` in `codegen/lower.ts`:
 *   `number`              → `TyFloat` (default; `TyNat`/`TyInt` when context implies)
 *   `string`              → `TyString`
 *   `boolean`             → `TyBool`
 *   `T | undefined`       → `TyOption`
 *   `Promise<T>`          → `TyPromise`
 *   `Map<K, V>`           → `TyMap`
 *   `string & {__brand:X}`→ branded newtype (`TyRef(alias)`)
 *
 * One carrier question does belong here, because it needs the checker rather than
 * a name: whether a TS type has a Lean carrier at all.  It is answered by asking
 * where the type was declared (`declaredByTypeScriptItself`), collapsing to
 * `TyRef('TSAny')`, so the IR carries one answer and every consumer agrees.
 *
 * Pipeline position:  TS AST → **Type Mapper** → IR types → Codegen
 */

import * as ts from 'typescript';
import {
  IRType, Pure,
  TyInt, TyFloat, TyString, TyBool, TyUnit, TyNever,
  TyOption, TyArray, TyTuple, TyFn, TyMap, TySet, TyPromise,
  TyRef, TyVar, TypeParam,
} from '../ir/types.js';
import { DISCRIMINANT_FIELDS } from '../utils.js';

// ─── Constants ──────────────────────────────────────────────────────────────────

/** Recursion depth limit to prevent infinite loops on circular types. */
const MAX_TYPE_DEPTH = 20;

/** Fallback name for type parameters when the symbol has no name. */
const FALLBACK_TYPE_VAR = 'α';

/** Sentinel names for anonymous object types (TypeScript uses these internally). */
const TS_ANON_NAMES = new Set(['__type', '__object']);

/**
 * The residue of "no Lean carrier" that `declaredByTypeScriptItself` below cannot
 * answer.  Measured, not guessed — of the 50 names the two former sets held,
 * provenance answers 13, so these remain, in three groups:
 *
 *   Generic, and erased anyway.  Provenance does not fire on a type that carries
 *     arguments (see below), so a typed array or `PromiseLike<T>` needs its name
 *     here to lose the carrier it never had.
 *   Reopened by the transpiled program.  The Durable Object ambient file declares
 *     `ArrayBuffer`, `ArrayBufferView`, `AbortSignal` and `ReadableStream`, giving
 *     each a declaration outside TypeScript's own files, so provenance abstains on
 *     purpose (see the `every` note below) and the name answers.
 *   Never resolvable here.  The parser loads `lib.es2022.d.ts` only, so the host
 *     and DOM names below have no declaration at all and arrive as `any`; these
 *     entries are inert for this transpiler and answer for a caller that loads
 *     `lib.dom`.  `console`, `Proxy` and `Reflect` name values rather than types,
 *     so they could not be measured either way and are kept as declared intent.
 *
 * Deliberately absent: `Generator`, `AsyncGenerator`, `IterableIterator`,
 * `AsyncIterableIterator` and TypeScript 6's `MapIterator`.  Iteration reads the
 * element type out of their arguments, so erasing them loses it — with
 * `MapIterator<Info>` collapsed, `for (const u of m.values())` lowers to
 * `pure ()`.  The former reference-path set omitted them for the same reason.
 *
 * The object and reference paths used to hold near-duplicate sets differing on
 * seven names; one set now serves both.
 */
const NO_LEAN_CARRIER_NAMES = new Set([
  // generic, so provenance abstains, but no carrier exists either
  'Uint8Array', 'Int8Array', 'Uint16Array', 'Int16Array', 'Uint32Array', 'Int32Array',
  'Float32Array', 'Float64Array', 'DataView', 'PromiseLike', 'AsyncIterable',
  'WeakSet', 'WeakMap', 'WeakRef', 'FinalizationRegistry',
  // reopened by the Durable Object ambient declarations
  'ArrayBuffer', 'ArrayBufferView', 'AbortSignal', 'ReadableStream',
  // never resolvable under `lib.es2022.d.ts`
  'WritableStream', 'TransformStream', 'ReadableStreamDefaultReader',
  'Blob', 'File', 'FormData', 'AbortController',
  'AsyncDisposable', 'EventTarget', 'Event',
  'TextEncoder', 'TextDecoder', 'SubtleCrypto', 'CryptoKey', 'CryptoKeyPair',
  'console', 'Proxy', 'Reflect',
]);

/**
 * External types that keep their own name because a Lean carrier exists for them.
 * Checked before any collapse, so being declared by TypeScript itself does not
 * erase them:
 *   - the Durable Object surface — `TSLean.DurableObjects.*` models each one, and
 *     `scanTypeImports` requests that module when one appears;
 *   - `Disposable` — `structure Disposable` in `TSLean/Stubs/WebAPIs.lean`;
 *   - `URL` — `structure URL` in `TSLean/Runtime/WebAPI.lean`, reachable because
 *     the lowerer maps `new URL(...)` and `.pathname`/`.searchParams` onto it.
 * `TextEncoder`, `TextDecoder` and `AbortController` deliberately stay out: their
 * Lean stubs exist, but no import path requests `TSLean.Stubs.WebAPIs` for a type
 * occurrence, so their own name would not resolve. See the note in
 * `codegen/lower.ts` on the set overlaps.
 */
const LEAN_CARRIER_TYPES = new Set([
  'DurableObjectNamespace', 'DurableObjectStub', 'DurableObjectId',
  'DurableObjectStorage', 'DurableObjectState',
  'Disposable',
  'URL',
]);

/** Files inside the TypeScript package: its standard library and its compiler API. */
const TYPESCRIPT_PACKAGE_FILE = /[/\\]node_modules[/\\]typescript[/\\]/;

/**
 * Is every declaration of this symbol TypeScript's own — its `lib.*.d.ts`
 * standard library, or the `typescript.d.ts` compiler API?
 *
 * This is the authoritative test for "has no Lean carrier", because it asks where
 * a type came from rather than what it is called. `ts.SourceFile` collapses while
 * a program's own `interface Node` does not, which no set of names can tell apart
 * — and getting that wrong erases a real user type, since the transpiler still
 * emits a `structure` for it.
 *
 * `every`, not `some`: a program may reopen a platform interface (the Durable
 * Object ambient file declares `ArrayBuffer`, `ArrayBufferView`, `AbortSignal` and
 * `ReadableStream`), and a program that loads `lib.dom` and declares its own
 * `Node` merges with the DOM one. Neither may be erased on account of the
 * declaration it does not own; the platform types that behave this way are named
 * in `NO_LEAN_CARRIER_NAMES` instead.
 *
 * Callers must not apply it to a type that carries type arguments, because
 * erasing one throws those arguments away and the pipeline reads them: with
 * `MapIterator<Info>` erased, `for (const u of m.values())` loses its element type
 * and the loop body lowers to `pure ()`. A generic type with no carrier is named
 * instead.
 *
 * When TypeScript is not installed under `node_modules` the test simply does not
 * fire, and the name set answers as it did before.
 */
function declaredByTypeScriptItself(sym: ts.Symbol | undefined): boolean {
  const decls = sym?.declarations;
  if (decls === undefined || decls.length === 0) return false;
  return decls.every(d => TYPESCRIPT_PACKAGE_FILE.test(d.getSourceFile().fileName));
}

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
  if (depth > MAX_TYPE_DEPTH) return TyRef('TSAny');

  const f = t.flags;
  if (f & ts.TypeFlags.String)         return TyString;
  if (f & ts.TypeFlags.Number)         return TyFloat;
  if (f & ts.TypeFlags.Boolean)        return TyBool;
  if (f & ts.TypeFlags.Undefined)      return TyOption(TyUnit);
  if (f & ts.TypeFlags.Null)           return TyOption(TyUnit);
  if (f & ts.TypeFlags.Void)           return TyUnit;
  if (f & ts.TypeFlags.Never)          return TyNever;
  if (f & ts.TypeFlags.Any)            return TyRef('TSAny');
  if (f & ts.TypeFlags.Unknown)        return TyRef('TSAny');
  if (f & ts.TypeFlags.BigInt)         return TyInt;
  if (f & ts.TypeFlags.StringLiteral)  return TyString;
  if (f & ts.TypeFlags.NumberLiteral)  return TyFloat;
  if (f & ts.TypeFlags.BooleanLiteral) return TyBool;
  if (f & ts.TypeFlags.TypeParameter)  return TyVar(t.symbol?.name ?? FALLBACK_TYPE_VAR);
  if (f & ts.TypeFlags.TemplateLiteral) return TyString;
  if (f & ts.TypeFlags.StringMapping)   return TyString;

  if (t.isUnion())        return mapUnion(t, checker, depth);
  if (t.isIntersection()) return mapIntersection(t, checker, depth);

  if (checker.isArrayType(t)) {
    const elem = checker.getTypeArguments(t as ts.TypeReference)[0];
    return TyArray(elem ? mapType(elem, checker, depth + 1) : TyRef('TSAny'));
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
  const aliasSymbol = getAliasSymbol(t);
  const alias = aliasSymbol?.name;
  if (alias) {
    // A union alias is neither an object nor a reference, so this is the only
    // place `PropertyKey` (string | number | symbol) and `ArrayBufferLike`
    // (ArrayBuffer | SharedArrayBuffer) can be collapsed.
    const aliasArgs = t.aliasTypeArguments;
    if (!LEAN_CARRIER_TYPES.has(alias) && (aliasArgs === undefined || aliasArgs.length === 0) &&
        declaredByTypeScriptItself(aliasSymbol)) return TyRef('TSAny');
    // Propagate alias type arguments (e.g. Tree<T> → TyRef('Tree', [TyVar('T')]))
    if (aliasArgs && aliasArgs.length > 0) {
      return TyRef(alias, aliasArgs.map(a => mapType(a, checker, depth + 1)));
    }
    return TyRef(alias);
  }

  return withoutNil.length > 0 ? mapType(withoutNil[0], checker, depth + 1) : TyRef('TSAny');
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
  return concrete ? mapType(concrete, checker, depth + 1) : TyRef('TSAny');
}

// ─── Object types ───────────────────────────────────────────────────────────────

function mapObject(t: ts.ObjectType, checker: ts.TypeChecker, depth: number): IRType {
  if (t.objectFlags & ts.ObjectFlags.Reference)
    return mapTypeRef(t as ts.TypeReference, checker, depth);

  const sym = t.symbol;
  if (!sym) return TyRef('TSAny');

  // Call signatures → function type
  const calls = checker.getSignaturesOfType(t, ts.SignatureKind.Call);
  if (calls.length > 0) {
    const sig = calls[0];
    const params = sig.getParameters().map(p => {
      const declaration = p.valueDeclaration ?? p.declarations?.[0];
      const pt = declaration
        ? checker.getTypeOfSymbolAtLocation(p, declaration)
        : checker.getTypeOfSymbol(p);
      return mapType(pt, checker, depth + 1);
    });
    return TyFn(params, mapType(checker.getReturnTypeOfSignature(sig), checker, depth + 1), Pure);
  }

  // Anonymous object types (e.g. { name: string }) → AssocMap String TSAny.
  // This allows field access via AssocMap.find? and is sound for heterogeneous objects.
  const name = sym.name;
  if (TS_ANON_NAMES.has(name)) {
    // Check if the type has named properties → use AssocMap for field access support
    const props = t.getProperties();
    if (props.length > 0) return TyMap(TyString, TyRef('TSAny'));
    // Check for index signatures (e.g. {[k: string]: T}) → Map
    const indexInfo = checker.getIndexInfosOfType(t);
    if (indexInfo.length > 0) {
      const valType = indexInfo[0].type ? mapType(indexInfo[0].type, checker, depth + 1) : TyRef('TSAny');
      return TyMap(TyString, valType);
    }
    // Check call signatures → function type (already handled above, this is fallback)
    return TyRef('TSAny');
  }
  if (name === 'Error' || name.endsWith('Error')) return TyString;  // JS Error → String for Lean
  if (LEAN_CARRIER_TYPES.has(name)) return TyRef(name);
  if (declaredByTypeScriptItself(sym)) return TyRef('TSAny');
  if (NO_LEAN_CARRIER_NAMES.has(name)) return TyRef('TSAny');
  return TyRef(name);
}

// ─── Generic type references ────────────────────────────────────────────────────

function mapTypeRef(t: ts.TypeReference, checker: ts.TypeChecker, depth: number): IRType {
  const name = t.target.symbol?.name ?? '';
  const args = checker.getTypeArguments(t);
  const map1 = () => args[0] ? mapType(args[0], checker, depth + 1) : TyRef('TSAny');
  const map2 = (i: number) => args[i] ? mapType(args[i], checker, depth + 1) : TyRef('TSAny');

  switch (name) {
    case 'Array':         case 'ReadonlyArray': return TyArray(map1());
    case 'Map':           case 'WeakMap':       return TyMap(map1(), map2(1));
    case 'Set':           case 'WeakSet':       return TySet(map1());
    case 'Promise':                             return TyPromise(map1());
    case 'Record':                              return TyMap(map1(), map2(1));
    case 'Readonly':      case 'NonNullable':   return map1();
    // Utility types that are transparent (pass through inner type)
    case 'Required':                            return map1();
    default: {
      if (LEAN_CARRIER_TYPES.has(name)) {
        return args.length === 0 ? TyRef(name) : TyRef(name, args.map(a => mapType(a, checker, depth + 1)));
      }
      // no arguments to lose, so provenance can answer; a generic one is named
      if (args.length === 0 && declaredByTypeScriptItself(t.target.symbol)) return TyRef('TSAny');
      if (NO_LEAN_CARRIER_NAMES.has(name)) return TyRef('TSAny');
      return args.length === 0 ? TyRef(name) : TyRef(name, args.map(a => mapType(a, checker, depth + 1)));
    }
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
    const isMethod = ts.isMethodSignature(m);
    if (!ts.isPropertySignature(m) && !ts.isPropertyDeclaration(m) && !isMethod) continue;
    const name = m.name?.getText() ?? '';
    const sym  = checker.getSymbolAtLocation(m.name);
    const ty   = sym ? checker.getTypeOfSymbol(sym) : checker.getAnyType();
    const opt  = !!m.questionToken;
    const mut  = !m.modifiers?.some(mod => mod.kind === ts.SyntaxKind.ReadonlyKeyword);
    // Method signatures: use actual function type if it's concrete (no universe issues),
    // fall back to TSAny for complex/generic methods
    let mapped: IRType;
    if (isMethod) {
      const sig = checker.getSignaturesOfType(ty, ts.SignatureKind.Call)[0];
      if (sig) {
        const params = sig.parameters.map(p => mapType(checker.getTypeOfSymbol(p), checker));
        const ret = mapType(checker.getReturnTypeOfSignature(sig), checker);
        // Only use concrete function type if params are simple (no TypeVars)
        const hasTypeVar = (t: IRType): boolean =>
          t.tag === 'TypeVar' || (t.tag === 'Array' && hasTypeVar(t.elem)) ||
          (t.tag === 'Option' && hasTypeVar(t.inner)) ||
          (t.tag === 'Function' && (t.params.some(hasTypeVar) || hasTypeVar(t.ret)));
        if ([...params, ret].some(hasTypeVar)) {
          mapped = TyRef('TSAny');
        } else {
          mapped = params.length === 0 ? TyFn([], ret) : TyFn(params, ret);
        }
      } else {
        mapped = TyRef('TSAny');
      }
    } else {
      mapped = mapType(ty, checker);
    }
    // Avoid Option double-wrapping: if TypeChecker already resolved T | undefined
    // as Option T, don't wrap again for questionToken
    const needsWrap = opt && mapped.tag !== 'Option';
    out.push({
      name,
      type: needsWrap ? TyOption(mapped) : (opt ? mapped : mapped),
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
      const mapped = mapType(st, checker);
      const needsWrap = opt && mapped.tag !== 'Option';
      fields.push({
        name: sym.name,
        type: needsWrap ? TyOption(mapped) : mapped,
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
 * Extract type parameters from a TypeScript declaration.
 * When a checker is provided, also extracts constraint and default types.
 */
export function extractTypeParams(
  node: ts.InterfaceDeclaration | ts.ClassDeclaration | ts.TypeAliasDeclaration |
        ts.FunctionDeclaration | ts.MethodDeclaration | ts.ArrowFunction | ts.FunctionExpression,
  checker?: ts.TypeChecker,
): TypeParam[] {
  return (node.typeParameters ?? []).map(tpNode => {
    const name = tpNode.name.text;
    const constraint = checker && tpNode.constraint
      ? safeMapType(checker, tpNode.constraint) : undefined;
    const default_ = checker && tpNode.default
      ? safeMapType(checker, tpNode.default) : undefined;
    return { name, constraint, default_ };
  });
}

// ─── Helpers ────────────────────────────────────────────────────────────────────

/**
 * Access the `aliasSymbol` on a TypeScript type.
 *
 * This property is not in the public TS API typings but is stable across
 * TypeScript versions (4.x–5.x).  It gives the declared alias for union and
 * intersection types — its name, and where it was declared.
 */
function getAliasSymbol(t: ts.Type): ts.Symbol | undefined {
  return (t as { aliasSymbol?: ts.Symbol }).aliasSymbol;
}

function getAliasName(t: ts.Type): string | undefined {
  return getAliasSymbol(t)?.name;
}

function safeMapType(checker: ts.TypeChecker, node: ts.TypeNode): IRType | undefined {
  const type = checker.getTypeAtLocation(node);
  return type ? mapType(type, checker, 0) : undefined;
}
