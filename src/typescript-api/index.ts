/**
 * @module typescript-api
 *
 * The TypeScript compiler surface every TSLean stage reads and writes through.
 *
 * TypeScript 7 publishes no single module. Syntax lives under `typescript/unstable/ast`, the
 * factory under `typescript/unstable/ast/factory`, and the type model — checker, program,
 * symbols, types and their flag enums — under `typescript/unstable/sync`, which is a client to
 * a separate native compiler server rather than an in-process library. This module names that
 * union once, so a call site says `ts.SyntaxKind`, `ts.factory.createIdentifier` and
 * `ts.TypeFlags` without knowing which of the three subpaths each one comes from, and so a
 * compiler upgrade is read and reviewed here rather than in every stage.
 *
 * Nothing here adds behaviour: every name is the compiler's own. The one editorial decision is
 * `ModifierFlags`, which both the syntax and the type-model modules export; the syntax one is
 * re-exported, because a modifier is read off a node and the two enums agree bit for bit.
 *
 * {@link module:typescript-api/session} owns the server session those type-model classes need.
 */

export * from 'typescript/unstable/ast';
export * as factory from 'typescript/unstable/ast/factory';

export {
  Checker,
  ElementFlags,
  Emitter,
  ModuleKind,
  NodeBuilderFlags,
  NodeHandle,
  ObjectFlags,
  Program,
  Project,
  Signature,
  SignatureFlags,
  SignatureKind,
  Symbol,
  SymbolFlags,
  TypeFlags,
  isBigIntLiteralType,
  isBooleanLiteralType,
  isClassOrInterfaceType,
  isConditionalType,
  isErrorType,
  isIndexType,
  isIndexedAccessType,
  isIntersectionType,
  isIntrinsicType,
  isLiteralType,
  isNumberLiteralType,
  isObjectType,
  isStringLiteralType,
  isStringMappingType,
  isSubstitutionType,
  isTemplateLiteralType,
  isTupleType,
  isTypeParameter,
  isTypeReference,
  isUnionType,
} from 'typescript/unstable/sync';

export type {
  BigIntLiteralType,
  BooleanLiteralType,
  CompilerOptions,
  ConditionalType,
  Diagnostic,
  IndexInfo,
  IndexType,
  IndexedAccessType,
  InterfaceType,
  IntersectionType,
  IntrinsicType,
  LiteralType,
  NumberLiteralType,
  ObjectType,
  StringLiteralType,
  StringMappingType,
  SubstitutionType,
  TemplateLiteralType,
  TupleType,
  Type,
  TypeParameter,
  TypePredicate,
  TypeReference,
  UnionOrIntersectionType,
  UnionType,
} from 'typescript/unstable/sync';

/** The compiler version every attestation records. */
export { version } from 'typescript';
