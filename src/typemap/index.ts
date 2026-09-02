/**
 * @module typemap
 *
 * Type mapper: TypeScript compiler types → IR types.
 *
 * Uses the checker for fully-resolved types, handling generics, mapped
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

import * as ts from '../typescript-api/index.js';
import {
  IRType, Pure,
  TyInt, TyFloat, TyString, TyBool, TyUnit, TyNever,
  TyOption, TyArray, TyTuple, TyFn, TyMap, TySet, TyPromise,
  TyRef, TyVar, TypeParam,
} from '../ir/types.js';
import { DISCRIMINANT_FIELDS, isLeanIdentifier } from '../utils.js';

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
 * `AsyncIterableIterator` and the standard library's `MapIterator`.  Iteration reads the
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

/**
 * Files TypeScript itself declares. The compiler ships in two packages: `typescript` holds the
 * compiler and its API declarations, and a per-platform `@typescript/typescript-<os>-<arch>`
 * holds the native compiler alongside the `lib.*.d.ts` standard library, so provenance has to
 * name both to mean "declared by TypeScript". The scope is matched as a whole path segment, so
 * a package that merely starts with the name — `typescript-eslint`, `@typescript-eslint/*` — is
 * a program's own dependency and stays a program's own type.
 */
const TYPESCRIPT_PACKAGE_FILE = /[/\\]node_modules[/\\](?:@typescript[/\\][^/\\]+[/\\]|typescript[/\\])/;

/**
 * Is every declaration of this symbol TypeScript's own — its `lib.*.d.ts`
 * standard library, or its compiler API declarations?
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
 * A declaration arrives as a handle rather than as a node, and the handle carries the path of
 * the file it was parsed from — the very path resolving it would look that file up by — so
 * provenance reads the path and never asks the compiler server for the node.
 *
 * When TypeScript is not installed under `node_modules` the test simply does not
 * fire, and the name set answers as it did before.
 */
function declaredByTypeScriptItself(sym: ts.Symbol | undefined): boolean {
  const decls = sym?.declarations;
  if (decls === undefined || decls.length === 0) return false;
  return decls.every(d => TYPESCRIPT_PACKAGE_FILE.test(d.path));
}

// ─── Main entry ─────────────────────────────────────────────────────────────────

/**
 * Map a TypeScript compiler type to an IR type.
 *
 * Handles primitives, unions, intersections, arrays, tuples, object types,
 * generic references, conditional types, and branded newtypes.
 *
 * @param t       - The TypeScript type from the type checker.
 * @param checker - The checker over the program the type belongs to.
 * @param depth   - Current recursion depth (guards against circular types).
 * @returns The corresponding IR type.
 */
export function mapType(t: ts.Type, checker: ts.Checker, depth = 0): IRType {
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
  if (f & ts.TypeFlags.TypeParameter)  return TyVar(t.getSymbol()?.name ?? FALLBACK_TYPE_VAR);
  if (f & ts.TypeFlags.TemplateLiteral) return TyString;
  if (f & ts.TypeFlags.StringMapping)   return TyString;

  if (t.isUnionType())        return mapUnion(t, checker, depth);
  if (t.isIntersectionType()) return mapIntersection(t, checker, depth);

  if (checker.isArrayType(t)) {
    // `getTypeArguments` is defined only for a reference — the compiler server faults when
    // handed anything else — and `isTypeReference` is itself that `ObjectFlags.Reference` test.
    const elem = ts.isTypeReference(t) ? checker.getTypeArguments(t)[0] : undefined;
    return TyArray(elem ? mapType(elem, checker, depth + 1) : TyRef('TSAny'));
  }
  if (checker.isTupleType(t)) {
    const args = ts.isTypeReference(t) ? checker.getTypeArguments(t) : [];
    return TyTuple(args.map(a => mapType(a, checker, depth + 1)));
  }

  if (t.isObjectType()) return mapObject(t, checker, depth);
  // The true branch, which the checker resolves on demand rather than holding on the type.
  if (t.isConditionalType()) return mapType(t.getTrueType(), checker, depth + 1);
  if (f & ts.TypeFlags.Index) return TyString;

  return TyRef(checker.typeToString(t));
}

// ─── Union types ────────────────────────────────────────────────────────────────

function mapUnion(t: ts.UnionType, checker: ts.Checker, depth: number): IRType {
  const types = t.getTypes() ?? [];

  // T | undefined/null → Option T. TypeScript flattens the union when T is itself a
  // union, so the members no longer say which alias was written; rebuilding the
  // non-nullable type recovers it, and recovers nothing when there was no alias.
  const withoutNil = types.filter(x => !(x.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null)));
  // `getNonNullableType` answers nothing when the checker cannot rebuild the type; the first
  // non-nil member is then the closest reading of what was written.
  if (withoutNil.length > 0 && withoutNil.length < types.length)
    return TyOption(mapType(checker.getNonNullableType(t) ?? withoutNil[0], checker, depth + 1));

  // The generated tagged encoding of `Option A` denotes the same Lean type as `A | undefined`.
  // Without this it would become a second, locally declared inductive that shadows Lean's own.
  const element = taggedOptionElement(t, checker);
  if (element !== null) return TyOption(mapType(element, checker, depth + 1));
  // All string literals → use the alias name if available
  if (types.every(x => x.flags & ts.TypeFlags.StringLiteral)) {
    const alias = t.getAliasSymbol()?.name;
    return alias ? TyRef(alias) : TyString;
  }

  // true | false → Bool
  if (types.length === 2 && types.every(x => x.flags & ts.TypeFlags.BooleanLiteral))
    return TyBool;

  // Named alias (e.g. `type Status = "active" | "inactive"`, `Tree<T>`)
  const aliasSymbol = t.getAliasSymbol();
  const alias = aliasSymbol?.name;
  if (alias) {
    // A union alias is neither an object nor a reference, so this is the only
    // place `PropertyKey` (string | number | symbol) and `ArrayBufferLike`
    // (ArrayBuffer | SharedArrayBuffer) can be collapsed.
    const aliasArgs = t.getAliasTypeArguments();
    if (!LEAN_CARRIER_TYPES.has(alias) && aliasArgs.length === 0 &&
        declaredByTypeScriptItself(aliasSymbol)) return TyRef('TSAny');
    // Propagate alias type arguments (e.g. Tree<T> → TyRef('Tree', [TyVar('T')]))
    if (aliasArgs.length > 0) {
      return TyRef(alias, aliasArgs.map(a => mapType(a, checker, depth + 1)));
    }
    return TyRef(alias);
  }

  return withoutNil.length > 0 ? mapType(withoutNil[0], checker, depth + 1) : TyRef('TSAny');
}

// ─── Intersection types ─────────────────────────────────────────────────────────

function mapIntersection(t: ts.IntersectionType, checker: ts.Checker, depth: number): IRType {
  const types = t.getTypes() ?? [];
  const alias = t.getAliasSymbol()?.name;

  // Branded newtype: `string & { __brand: "UserId" }`
  const base  = types.find(x => x.flags & (ts.TypeFlags.String | ts.TypeFlags.Number));
  const brand = types.find(x => (x.flags & ts.TypeFlags.Object) &&
    checker.getPropertiesOfType(x).some(p => p.name.startsWith('__brand') || p.name.startsWith('_brand')));
  if (base && brand) {
    return alias ? TyRef(alias) : (base.flags & ts.TypeFlags.String ? TyString : TyFloat);
  }

  if (alias) return TyRef(alias);

  const concrete = types.find(x => !(x.flags & ts.TypeFlags.Object) ||
    checker.getPropertiesOfType(x).length > 0);
  return concrete ? mapType(concrete, checker, depth + 1) : TyRef('TSAny');
}

// ─── Object types ───────────────────────────────────────────────────────────────

function mapObject(t: ts.ObjectType, checker: ts.Checker, depth: number): IRType {
  // A reference is an object type carrying `ObjectFlags.Reference`, which is exactly what this
  // predicate tests; asking it here also narrows `t`, which is what `getTypeArguments` demands.
  if (ts.isTypeReference(t)) return mapTypeRef(t, checker, depth);

  const sym = t.getSymbol();
  if (!sym) return TyRef('TSAny');

  // Call signatures → function type
  const calls = checker.getSignaturesOfType(t, ts.SignatureKind.Call);
  if (calls.length > 0) {
    const sig = calls[0];
    const params = sig.getParameters().map(p => {
      // A declaration is a handle into the program the symbol came from; one that no longer
      // resolves falls back to the symbol's own type, as a symbol with no declaration does.
      const declaration = (p.valueDeclaration ?? p.declarations[0])?.resolve();
      const pt = declaration
        ? checker.getTypeOfSymbolAtLocation(p, declaration)
        : checker.getTypeOfSymbol(p);
      return mapTypeOrAny(pt, checker, depth + 1);
    });
    return TyFn(params, mapTypeOrAny(checker.getReturnTypeOfSignature(sig), checker, depth + 1), Pure);
  }

  // Anonymous object types (e.g. { name: string }) → AssocMap String TSAny.
  // This allows field access via AssocMap.find? and is sound for heterogeneous objects.
  const name = sym.name;
  if (TS_ANON_NAMES.has(name)) {
    // Check if the type has named properties → use AssocMap for field access support
    const props = checker.getPropertiesOfType(t);
    if (props.length > 0) return TyMap(TyString, TyRef('TSAny'));
    // Check for index signatures (e.g. {[k: string]: T}) → Map
    const indexInfo = checker.getIndexInfosOfType(t);
    if (indexInfo.length > 0) {
      const valType = mapType(indexInfo[0].valueType, checker, depth + 1);
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

function mapTypeRef(t: ts.TypeReference, checker: ts.Checker, depth: number): IRType {
  const target = t.getTarget().getSymbol();
  const name = target?.name ?? '';
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
      if (args.length === 0 && declaredByTypeScriptItself(target)) return TyRef('TSAny');
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
  checker: ts.Checker,
): StructField[] {
  const out: StructField[] = [];
  for (const m of node.members) {
    const isMethod = ts.isMethodSignatureDeclaration(m);
    if (!ts.isPropertySignatureDeclaration(m) && !ts.isPropertyDeclaration(m) && !isMethod) continue;
    const name = m.name.getText();
    const sym  = checker.getSymbolAtLocation(m.name);
    const ty   = (sym ? checker.getTypeOfSymbol(sym) : undefined) ?? checker.getAnyType();
    // One postfix token spells both `?` and `!`, so only the question mark means optional.
    const opt  = m.postfixToken?.kind === ts.SyntaxKind.QuestionToken;
    const mut  = !m.modifiers?.some(mod => mod.kind === ts.SyntaxKind.ReadonlyKeyword);
    // Method signatures: use actual function type if it's concrete (no universe issues),
    // fall back to TSAny for complex/generic methods
    let mapped: IRType;
    if (isMethod) {
      const sig = checker.getSignaturesOfType(ty, ts.SignatureKind.Call)[0];
      if (sig) {
        const params = sig.getParameters().map(p => mapTypeOrAny(checker.getTypeOfSymbol(p), checker));
        const ret = mapTypeOrAny(checker.getReturnTypeOfSignature(sig), checker);
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
    // Avoid Option double-wrapping: when the checker already resolved T | undefined
    // as Option T, the postfix `?` must not wrap it a second time.
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
 * @param checker - The checker for resolving field types.
 * @returns Discriminant info if detected, or `null`.
 */
export function detectDiscriminatedUnion(
  t: ts.UnionType,
  checker: ts.Checker,
): DiscriminantInfo | null {
  const objTypes = (t.getTypes() ?? []).filter(x => (x.flags & ts.TypeFlags.Object) !== 0);
  if (objTypes.length < 2) return null;

  for (const field of DISCRIMINANT_FIELDS) {
    const info = tryField(objTypes, field, checker);
    if (info) return info;
  }
  return null;
}

// ─── String enumerations ────────────────────────────────────────────────────────

/** A named union of string literals and the constructors it names. */
export interface StringEnumeration {
  /** The alias the union is declared under, which is also the Lean type name. */
  readonly name: string;
  /** The literals, in declaration order. Each one is also a Lean constructor name. */
  readonly members: readonly string[];
}

/**
 * The literals of a union of string literals, or `null` when the union is something else.
 *
 * The literals are the constructor names. TypeScript and Lean therefore name the same
 * cases, and a value keeps its name through a compilation in either direction. A literal
 * that is not a Lean identifier cannot name a constructor, so the whole union stops being
 * an enumeration rather than getting a renamed case that no longer corresponds.
 */
export function stringEnumerationMembers(t: ts.Type): readonly string[] | null {
  if (!t.isUnionType()) return null;
  const members: string[] = [];
  for (const member of t.getTypes() ?? []) {
    if (!member.isStringLiteralType()) return null;
    const literal = member.value;
    if (!isLeanIdentifier(literal)) return null;
    members.push(literal);
  }
  return members.length > 0 ? members : null;
}

/**
 * The enumeration a type denotes, when it is a union of string literals behind a
 * name. An unnamed union has no Lean type to hang the constructors on, and a generic
 * alias is not an enumeration, so both answer `null`.
 */
export function describeStringEnumeration(t: ts.Type): StringEnumeration | null {
  const alias = t.getAliasSymbol();
  if (alias === undefined || !isLeanIdentifier(alias.name)) return null;
  if (t.getAliasTypeArguments().length > 0) return null;
  const members = stringEnumerationMembers(t);
  return members === null ? null : { name: alias.name, members };
}

/** How the Lean-to-TypeScript emitter spells an `Option`: the one source of truth for it. */
export const TAGGED_OPTION = Object.freeze({
  tag: 'kind',
  value: 'value',
  absent: 'none',
  present: 'some',
});

/**
 * The element type of the generated option encoding, or `null` when the type is not one.
 *
 * The Lean-to-TypeScript emitter writes `Option A` as a tagged union rather than as
 * `A | undefined`, so that a present `undefined` stays distinct from an absent value. Both
 * spellings denote the same Lean `Option`, so this recognises the tagged one structurally
 * and never by the name a module happened to give the alias.
 */
export function taggedOptionElement(t: ts.Type, checker: ts.Checker): ts.Type | null {
  if (!t.isUnionType()) return null;
  const members = t.getTypes() ?? [];
  if (members.length !== 2) return null;
  let absent = false;
  let present: ts.Type | null = null;
  for (const member of members) {
    const tag = checker.getPropertyOfType(member, TAGGED_OPTION.tag);
    if (tag === undefined) return null;
    const tagType = checker.getTypeOfSymbol(tag);
    if (tagType === undefined || !tagType.isStringLiteralType()) return null;
    const properties = checker.getPropertiesOfType(member);
    if (tagType.value === TAGGED_OPTION.absent && properties.length === 1) {
      absent = true;
      continue;
    }
    if (tagType.value !== TAGGED_OPTION.present || properties.length !== 2) return null;
    const value = checker.getPropertyOfType(member, TAGGED_OPTION.value);
    if (value === undefined) return null;
    // A value whose type the checker declines to give is not a recognisable encoding.
    const element = checker.getTypeOfSymbol(value);
    if (element === undefined) return null;
    present = element;
  }
  return absent && present !== null ? present : null;
}

/**
 * The enumeration a value at this position may name, looking through an optional wrapper.
 *
 * A position typed `E | undefined` still expects one of `E`'s cases whenever it is filled,
 * and TypeScript flattens that union so the members alone no longer name `E`. Rebuilding the
 * non-nullable type recovers the name.
 */
export function expectedStringEnumeration(t: ts.Type, checker: ts.Checker): StringEnumeration | null {
  const direct = describeStringEnumeration(t);
  if (direct !== null) return direct;
  if (!t.isUnionType()) return null;
  if (!(t.getTypes() ?? []).some((member) => (member.flags & ts.TypeFlags.Undefined) !== 0)) return null;
  const nonNullable = checker.getNonNullableType(t);
  return nonNullable === undefined ? null : describeStringEnumeration(nonNullable);
}

function tryField(types: readonly ts.Type[], field: string, checker: ts.Checker): DiscriminantInfo | null {
  const variants: DiscriminantInfo['variants'] = [];
  for (const t of types) {
    const prop = checker.getPropertyOfType(t, field);
    if (!prop) return null;
    const pt = checker.getTypeOfSymbol(prop);
    if (pt === undefined || !pt.isStringLiteralType()) return null;
    const lit = pt.value;
    const fields: StructField[] = [];
    for (const sym of checker.getPropertiesOfType(t)) {
      if (sym.name === field) continue;
      const opt = !!(sym.flags & ts.SymbolFlags.Optional);
      const mapped = mapTypeOrAny(checker.getTypeOfSymbol(sym), checker);
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
  checker?: ts.Checker,
): TypeParam[] {
  return (node.typeParameters ?? []).map(tpNode => {
    const name = tpNode.name.text;
    const constraint = checker && tpNode.constraint
      ? safeMapType(checker, tpNode.constraint) : undefined;
    const default_ = checker && tpNode.defaultType
      ? safeMapType(checker, tpNode.defaultType) : undefined;
    return { name, constraint, default_ };
  });
}

// ─── Helpers ────────────────────────────────────────────────────────────────────

/**
 * A type the checker declines to give maps as `TSAny`, which is where an unresolvable type
 * landed when the checker answered with its error type instead: that type's flags say `any`.
 */
function mapTypeOrAny(t: ts.Type | undefined, checker: ts.Checker, depth = 0): IRType {
  return t === undefined ? TyRef('TSAny') : mapType(t, checker, depth);
}

function safeMapType(checker: ts.Checker, node: ts.TypeNode): IRType | undefined {
  const type = checker.getTypeAtLocation(node);
  return type ? mapType(type, checker, 0) : undefined;
}
