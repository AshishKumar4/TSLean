/**
 * @module ir/types
 *
 * Core Intermediate Representation for the TS → Lean 4 transpiler.
 *
 * The IR is a System Fω with algebraic effect annotations.  Every expression
 * node carries both a resolved **type** and an **effect** signature, enabling
 * downstream passes (codegen, verification) to emit correct monad stacks
 * without re-analysing the AST.
 *
 * Pipeline position:  TS Source → Parser → **IR** → Rewrite → Codegen → Lean 4
 */

// ─── Effects ────────────────────────────────────────────────────────────────────
//
// Effects form a join-semilattice:  Pure ⊑ {IO, Async, State, Except} ⊑ Combined.
// `combineEffects` computes the join.  The codegen maps each effect to a Lean 4
// monad transformer stack (StateT / ExceptT / IO).

/**
 * Algebraic effect annotation carried by every IR expression.
 *
 * - `Pure`     — no side effects; maps to a plain Lean function.
 * - `State`    — reads/writes mutable state; maps to `StateT σ`.
 * - `IO`       — arbitrary IO (console, filesystem, Date.now); maps to `IO`.
 * - `Async`    — async/await; also maps to `IO` in Lean.
 * - `Except`   — can throw; maps to `ExceptT ε`.
 * - `Combined` — multiple effects; maps to a transformer stack.
 */
export type Effect =
  | { tag: 'Pure' }
  | { tag: 'State';    stateType: IRType }
  | { tag: 'IO' }
  | { tag: 'Async' }
  | { tag: 'Except';   errorType: IRType }
  | { tag: 'Combined'; effects: Effect[] };

/** The identity effect — no side effects. */
export const Pure:  Effect = { tag: 'Pure' };
/** Arbitrary IO effect. */
export const IO:    Effect = { tag: 'IO' };
/** Async/await effect (maps to IO in Lean). */
export const Async: Effect = { tag: 'Async' };

/** Construct a State effect over the given state type. */
export function stateEffect(stateType: IRType): Effect {
  return { tag: 'State', stateType };
}

/** Construct an Except effect over the given error type. */
export function exceptEffect(errorType: IRType): Effect {
  return { tag: 'Except', errorType };
}

/**
 * Compute the join of multiple effects in the effect lattice.
 *
 * Flattens nested `Combined`, removes `Pure`, and deduplicates structurally.
 * Returns `Pure` if all inputs are pure, a single effect if only one remains,
 * or `Combined` otherwise.
 */
export function combineEffects(effects: Effect[]): Effect {
  const flat = effects.flatMap(e => e.tag === 'Combined' ? e.effects : [e]);
  const noPure = flat.filter(e => e.tag !== 'Pure');
  const deduped = dedup(noPure);
  if (deduped.length === 0) return Pure;
  if (deduped.length === 1) return deduped[0];
  return { tag: 'Combined', effects: deduped };
}

/** Structural deduplication of effects using serialized keys. */
function dedup(effects: Effect[]): Effect[] {
  const seen = new Set<string>();
  return effects.filter(e => {
    const k = JSON.stringify(e);
    if (seen.has(k)) return false;
    seen.add(k);
    return true;
  });
}

// ─── Effect predicates ──────────────────────────────────────────────────────────

/** True when the effect is strictly `Pure`. */
export function isPure(e: Effect): boolean   { return e.tag === 'Pure'; }
/** True when the effect tree contains `Async` (recursively). */
export function hasAsync(e: Effect): boolean  { return e.tag === 'Async'  || (e.tag === 'Combined' && e.effects.some(hasAsync)); }
/** True when the effect tree contains `State` (recursively). */
export function hasState(e: Effect): boolean  { return e.tag === 'State'  || (e.tag === 'Combined' && e.effects.some(hasState)); }
/** True when the effect tree contains `Except` (recursively). */
export function hasExcept(e: Effect): boolean { return e.tag === 'Except' || (e.tag === 'Combined' && e.effects.some(hasExcept)); }
/** True when the effect tree contains `IO` (recursively). */
export function hasIO(e: Effect): boolean     { return e.tag === 'IO'     || (e.tag === 'Combined' && e.effects.some(hasIO)); }

// ─── Type parameters ────────────────────────────────────────────────────────────

/** A generic type parameter with optional constraint and default. */
export interface TypeParam {
  name: string;
  constraint?: IRType;    // from <T extends X>
  default_?: IRType;      // from <T = Y>
}

/** Create a TypeParam from a bare name (no constraint/default). */
export function tp(name: string): TypeParam { return { name }; }

// ─── Types ──────────────────────────────────────────────────────────────────────
//
// IRType is the type universe of the IR.  Primitive types map 1:1 to Lean 4 types.
// Compound types (Option, Array, Map, …) map to their Lean equivalents.
// `TypeRef` is the escape hatch for user-defined or unresolved types.

/**
 * IR type — the type universe of the intermediate representation.
 *
 * Primitives: `Nat`, `Int`, `Float`, `String`, `Bool`, `Unit`, `Never`.
 * Containers: `Option`, `Array`, `Tuple`, `Map`, `Set`, `Promise`, `Result`.
 * Named:      `Structure`, `Inductive`, `TypeRef`, `TypeVar`.
 * Advanced:   `Function`, `Dependent`, `Subtype`, `Universe`.
 */
export type IRType =
  | { tag: 'Nat' }
  | { tag: 'Int' }
  | { tag: 'Float' }
  | { tag: 'String' }
  | { tag: 'Bool' }
  | { tag: 'Unit' }
  | { tag: 'Never' }
  | { tag: 'Option';    inner: IRType }
  | { tag: 'Array';     elem: IRType }
  | { tag: 'Tuple';     elems: IRType[] }
  | { tag: 'Function';  params: IRType[]; ret: IRType; effect: Effect }
  | { tag: 'Structure'; name: string; fields: Array<{ name: string; type: IRType }> }
  | { tag: 'Inductive'; name: string; typeParams: TypeParam[]; ctors: Array<{ name: string; fields: IRType[] }> }
  | { tag: 'TypeRef';   name: string; args: IRType[] }
  | { tag: 'TypeVar';   name: string }
  | { tag: 'Map';       key: IRType; value: IRType }
  | { tag: 'Set';       elem: IRType }
  | { tag: 'Promise';   inner: IRType }
  | { tag: 'Result';    ok: IRType; err: IRType }
  | { tag: 'Dependent'; param: string; paramType: IRType; body: IRType }
  | { tag: 'Subtype';   base: IRType; refinement: string }
  | { tag: 'Universe';  level: number };

// ─── Primitive type singletons ──────────────────────────────────────────────────

export const TyNat:    IRType = { tag: 'Nat' };
export const TyInt:    IRType = { tag: 'Int' };
export const TyFloat:  IRType = { tag: 'Float' };
export const TyString: IRType = { tag: 'String' };
export const TyBool:   IRType = { tag: 'Bool' };
export const TyUnit:   IRType = { tag: 'Unit' };
export const TyNever:  IRType = { tag: 'Never' };

// ─── Type constructors ──────────────────────────────────────────────────────────

/** `T | undefined` → `Option T` */
export const TyOption  = (inner: IRType): IRType => ({ tag: 'Option', inner });
/** `T[]` → `Array T` */
export const TyArray   = (elem: IRType):  IRType => ({ tag: 'Array',  elem });
/** `[A, B, C]` → `A × B × C` */
export const TyTuple   = (elems: IRType[]): IRType => ({ tag: 'Tuple', elems });
/** `Map<K, V>` → `AssocMap K V` */
export const TyMap     = (key: IRType, value: IRType): IRType => ({ tag: 'Map', key, value });
/** `Set<T>` → `AssocSet T` */
export const TySet     = (elem: IRType):  IRType => ({ tag: 'Set',  elem });
/** `Promise<T>` → `IO T` */
export const TyPromise = (inner: IRType): IRType => ({ tag: 'Promise', inner });
/** `Result<T, E>` → `Except E T` */
export const TyResult  = (ok: IRType, err: IRType): IRType => ({ tag: 'Result', ok, err });
/** Named type reference with optional type arguments. */
export const TyRef     = (name: string, args: IRType[] = []): IRType => ({ tag: 'TypeRef', name, args });
/** Type variable (generic parameter). */
export const TyVar     = (name: string): IRType => ({ tag: 'TypeVar', name });
/** Function type `(p₁ → p₂ → … → ret)` with an effect annotation. */
export const TyFn      = (params: IRType[], ret: IRType, effect: Effect = Pure): IRType =>
  ({ tag: 'Function', params, ret, effect });

// ─── Expressions ────────────────────────────────────────────────────────────────
//
// Every IRExpr node carries `type: IRType` and `effect: Effect` via the IRNode
// mixin.  This is the key invariant: the IR is always fully typed and effected.

/** Source location for error messages and debugging. */
export interface Span { file: string; line: number; col: number }

/**
 * Base mixin for all IR expression nodes.
 * Every node carries a resolved type and effect — this is the central invariant.
 */
export interface IRNode { type: IRType; effect: Effect; span?: Span }

/**
 * IR expression — the core of the intermediate representation.
 *
 * Literals, variables, function application, let-binding, if-then-else, match,
 * do-notation, monadic bind, state/throw/try-catch, and structural operations.
 */
export type IRExpr =
  // Literals
  | ({ tag: 'LitNat';    value: number }    & IRNode)
  | ({ tag: 'LitInt';    value: number }    & IRNode)
  | ({ tag: 'LitFloat';  value: number }    & IRNode)
  | ({ tag: 'LitString'; value: string }    & IRNode)
  | ({ tag: 'LitBool';   value: boolean }   & IRNode)
  | ({ tag: 'LitUnit' }                     & IRNode)
  | ({ tag: 'LitNull' }                     & IRNode)
  // Variables and access
  | ({ tag: 'Var';         name: string }                                  & IRNode)
  | ({ tag: 'FieldAccess'; obj: IRExpr; field: string }                    & IRNode)
  | ({ tag: 'IndexAccess'; obj: IRExpr; index: IRExpr }                    & IRNode)
  // Functions
  | ({ tag: 'Lambda';  params: IRParam[]; body: IRExpr }                   & IRNode)
  | ({ tag: 'App';     fn: IRExpr; args: IRExpr[] }                        & IRNode)
  | ({ tag: 'TypeApp'; fn: IRExpr; typeArgs: IRType[] }                    & IRNode)
  // Bindings
  | ({ tag: 'Let';  name: string; annot?: IRType; value: IRExpr; body: IRExpr } & IRNode)
  | ({ tag: 'Bind'; name: string; monad: IRExpr; body: IRExpr }            & IRNode)
  // Control flow
  | ({ tag: 'IfThenElse'; cond: IRExpr; then: IRExpr; else_: IRExpr }      & IRNode)
  | ({ tag: 'Match';      scrutinee: IRExpr; cases: IRCase[] }             & IRNode)
  | ({ tag: 'Sequence';   stmts: IRExpr[] }                                & IRNode)
  | ({ tag: 'Return';     value: IRExpr }                                  & IRNode)
  // Constructors and literals (compound)
  | ({ tag: 'StructLit'; typeName: string; fields: Array<{ name: string; value: IRExpr }> } & IRNode)
  | ({ tag: 'CtorApp';   ctor: string; args: IRExpr[] }                    & IRNode)
  | ({ tag: 'ArrayLit';  elems: IRExpr[] }                                 & IRNode)
  | ({ tag: 'TupleLit';  elems: IRExpr[] }                                 & IRNode)
  // Monadic / do-notation
  | ({ tag: 'DoBlock';  stmts: DoStmt[] }                                  & IRNode)
  | ({ tag: 'Pure_';    value: IRExpr }                                    & IRNode)
  | ({ tag: 'StateGet' }                                                   & IRNode)
  | ({ tag: 'StateSet'; value: IRExpr }                                    & IRNode)
  // Error handling
  | ({ tag: 'Throw';    error: IRExpr }                                    & IRNode)
  | ({ tag: 'TryCatch'; body: IRExpr; errName: string; handler: IRExpr; finally_?: IRExpr } & IRNode)
  // Async
  | ({ tag: 'Await'; expr: IRExpr }                                        & IRNode)
  // Mutation
  | ({ tag: 'Assign'; target: IRExpr; value: IRExpr }                      & IRNode)
  // Operators
  | ({ tag: 'BinOp'; op: BinOp; left: IRExpr; right: IRExpr }             & IRNode)
  | ({ tag: 'UnOp';  op: UnOp;  operand: IRExpr }                         & IRNode)
  // Type operations
  | ({ tag: 'Cast';   expr: IRExpr; targetType: IRType }                   & IRNode)
  | ({ tag: 'IsType'; expr: IRExpr; testType: IRType }                     & IRNode)
  // Special
  | ({ tag: 'Panic'; msg: string }                                         & IRNode)
  | ({ tag: 'Hole' }                                                       & IRNode)
  // Structural operations (spread, with-update, optional chaining)
  | ({ tag: 'StructUpdate'; base: IRExpr; fields: Array<{ name: string; value: IRExpr }> } & IRNode)
  | ({ tag: 'OptChain';     expr: IRExpr }                                 & IRNode)
  // Type narrowing (typeof / instanceof / in / truthy guards)
  | ({ tag: 'TypeNarrow'; expr: IRExpr; narrowedType: IRType; narrowKind: 'typeof' | 'instanceof' | 'in' | 'truthy' } & IRNode)
  // Generators
  | ({ tag: 'YieldExpr'; value?: IRExpr }                                  & IRNode)
  // Multi-binding (const a=1, b=2)
  | ({ tag: 'MultiLet'; bindings: Array<{ name: string; type: IRType; value: IRExpr }>; body: IRExpr } & IRNode)
  // Labels and jumps
  | ({ tag: 'Labeled';  label: string; body: IRExpr }                      & IRNode)
  | ({ tag: 'Break';    label?: string }                                   & IRNode)
  | ({ tag: 'Continue'; label?: string }                                   & IRNode);

// ─── Supporting types ───────────────────────────────────────────────────────────

/** A function parameter in the IR.  May be implicit (Lean `{}`) or have a default value. */
export interface IRParam {
  name: string;
  type: IRType;
  /** Lean implicit parameter `{name : Type}` — used for type-class constraints. */
  implicit?: boolean;
  /** Default value expression — emitted as `(name : Type := default)`. */
  default_?: IRExpr;
}

/** A single case arm in a `match` expression. */
export interface IRCase { pattern: IRPattern; guard?: IRExpr; body: IRExpr }

/**
 * Pattern in a `match` expression.
 *
 * `PString` is a transitional node: the rewrite pass converts it to `PCtor`
 * when the match scrutinises a discriminant field (e.g. `s.kind`).
 */
export type IRPattern =
  | { tag: 'PVar';    name: string }
  | { tag: 'PLit';    value: string | number | boolean }
  | { tag: 'PCtor';   ctor: string; args: IRPattern[] }
  | { tag: 'PStruct'; fields: Array<{ name: string; pattern: IRPattern }> }
  | { tag: 'PTuple';  elems: IRPattern[] }
  | { tag: 'PWild' }
  | { tag: 'POr';     pats: IRPattern[] }
  | { tag: 'PAs';     pattern: IRPattern; name: string }
  | { tag: 'PString'; value: string }
  | { tag: 'PNone' }
  | { tag: 'PSome';   inner: IRPattern };

/** A statement inside a `do`-block (Lean do-notation). */
export type DoStmt =
  | { tag: 'DoBind';   name: string; expr: IRExpr }
  | { tag: 'DoLet';    name: string; value: IRExpr }
  | { tag: 'DoExpr';   expr: IRExpr }
  | { tag: 'DoReturn'; value: IRExpr };

/** Binary operators — arithmetic, comparison, logical, bitwise, string. */
export type BinOp =
  'Add' | 'Sub' | 'Mul' | 'Div' | 'Mod' |
  'Eq' | 'Ne' | 'Lt' | 'Le' | 'Gt' | 'Ge' |
  'And' | 'Or' |
  'BitAnd' | 'BitOr' | 'BitXor' | 'Shl' | 'Shr' |
  'Concat' | 'NullCoalesce';

/** Unary operators. */
export type UnOp = 'Not' | 'Neg' | 'BitNot';

// ─── Declarations ───────────────────────────────────────────────────────────────

/**
 * Top-level declaration in the IR.
 *
 * Each variant maps directly to a Lean 4 declaration form:
 * - `StructDef`    → `structure Foo where`
 * - `InductiveDef` → `inductive Foo where`
 * - `FuncDef`      → `def foo ...` or `partial def foo ...`
 * - `Namespace`    → `namespace Foo ... end Foo`
 */
export type IRDecl =
  | { tag: 'TypeAlias';    name: string; typeParams: TypeParam[]; body: IRType;  comment?: string }
  | { tag: 'StructDef';    name: string; typeParams: TypeParam[]; fields: Array<{ name: string; type: IRType; mutable?: boolean }>; deriving?: string[]; comment?: string; extends_?: string }
  | { tag: 'InductiveDef'; name: string; typeParams: TypeParam[]; ctors: Array<{ name: string; fields: Array<{ name?: string; type: IRType }> }>; comment?: string }
  | { tag: 'FuncDef';      name: string; typeParams: TypeParam[]; params: IRParam[]; retType: IRType; effect: Effect; body: IRExpr; comment?: string; isPartial?: boolean; where_?: IRDecl[]; docComment?: string }
  | { tag: 'InstanceDef';  typeClass: string; typeArgs: IRType[]; methods: IRDecl[]; comment?: string }
  | { tag: 'TheoremDef';   name: string; statement: string; proof: string; comment?: string }
  | { tag: 'ClassDecl';    name: string; typeParams: TypeParam[]; supers?: string[]; methods: Array<{ name: string; type: IRType; default_?: IRExpr }>; comment?: string }
  | { tag: 'Namespace';    name: string; decls: IRDecl[] }
  | { tag: 'RawLean';      code: string }
  | { tag: 'VarDecl';      name: string; type: IRType; value: IRExpr; mutable: boolean }
  | { tag: 'SectionDecl';  name?: string; decls: IRDecl[] }
  | { tag: 'AttributeDecl'; attr: string; target: string }
  | { tag: 'DeriveDecl';   typeName: string; classes: string[] };

// ─── Module ─────────────────────────────────────────────────────────────────────

/** A Lean 4 import — corresponds to `import Module.Path`. */
export interface IRImport {
  module: string;             // Lean module path (e.g., 'Project.Utils')
  names?: string[];           // specific named imports (for `open ... (X Y)`)
  isTypeOnly?: boolean;       // true for `import type { X } from '...'`
  isNamespace?: boolean;      // true for `import * as X from '...'`
  namespaceAlias?: string;    // the alias name for namespace imports
  isSideEffect?: boolean;     // true for `import './setup'` (no bindings)
  isReExport?: boolean;       // true for `export { X } from '...'`
  isReExportAll?: boolean;    // true for `export * from '...'`
}

/** An exported declaration from a module. */
export interface IRExport {
  name: string;
  isDefault: boolean;
  isType: boolean;
}

/** Top-level IR module — one per `.ts` source file. */
export interface IRModule {
  name: string;
  imports: IRImport[];
  exports?: IRExport[];
  decls: IRDecl[];
  comments: string[];
  sourceFile?: string;
}

// ─── Smart constructors ─────────────────────────────────────────────────────────
//
// Convenience functions for building IR nodes in the parser.  Each returns a
// fully-typed, effected node so callers never need to assemble IRNode fields.

/** String literal. */
export function litStr(v: string):   IRExpr { return { tag: 'LitString', value: v, type: TyString, effect: Pure }; }
/** Natural number literal. */
export function litNat(v: number):   IRExpr { return { tag: 'LitNat',    value: v, type: TyNat,    effect: Pure }; }
/** Boolean literal. */
export function litBool(v: boolean): IRExpr { return { tag: 'LitBool',   value: v, type: TyBool,   effect: Pure }; }
/** Unit literal `()`. */
export function litUnit():           IRExpr { return { tag: 'LitUnit',              type: TyUnit,   effect: Pure }; }
/** Float literal. */
export function litFloat(v: number): IRExpr { return { tag: 'LitFloat',  value: v, type: TyFloat,  effect: Pure }; }
/** Integer literal. */
export function litInt(v: number):   IRExpr { return { tag: 'LitInt',    value: v, type: TyInt,     effect: Pure }; }
/** Variable reference. */
export function varExpr(name: string, type: IRType = TyUnit): IRExpr {
  return { tag: 'Var', name, type, effect: Pure };
}
/** Placeholder for an unknown expression — emits `sorry` in Lean. */
export function holeExpr(type: IRType = TyUnit): IRExpr {
  return { tag: 'Hole', type, effect: Pure };
}
/** Type-appropriate default value for uninitialized variables. */
export function defaultForIRType(type: IRType): IRExpr {
  switch (type.tag) {
    case 'String':  return litStr('');
    case 'Nat':     return litNat(0);
    case 'Int':     return litNat(0);
    case 'Float':   return { tag: 'LitFloat', value: 0, type, effect: Pure };
    case 'Bool':    return litBool(false);
    case 'Unit':    return litUnit();
    case 'Option':  return { tag: 'LitNull', type, effect: Pure };
    case 'Array':   return { tag: 'ArrayLit', elems: [], type, effect: Pure };
    default:        return holeExpr(type);
  }
}
/** Struct update: `{ base with field₁ := v₁, … }`. */
export function structUpdate(base: IRExpr, fields: Array<{ name: string; value: IRExpr }>, type: IRType): IRExpr {
  return { tag: 'StructUpdate', base, fields, type, effect: base.effect };
}
/** Function application.  Effect is the join of fn and all arg effects. */
export function appExpr(fn: IRExpr, args: IRExpr[]): IRExpr {
  return { tag: 'App', fn, args, type: TyUnit, effect: combineEffects([fn.effect, ...args.map(a => a.effect)]) };
}
/** Sequence of expressions — last expression determines the type. */
export function seqExpr(stmts: IRExpr[]): IRExpr {
  if (stmts.length === 0) return litUnit();
  if (stmts.length === 1) return stmts[0];
  return { tag: 'Sequence', stmts, type: stmts[stmts.length - 1].type, effect: combineEffects(stmts.map(s => s.effect)) };
}
