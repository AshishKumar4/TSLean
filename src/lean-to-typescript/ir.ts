import ts from 'typescript';
import type { LeanToTypeScriptClosureEntry, LeanToTypeScriptDeclarationRole } from './artifact.js';
import { compareCodePoints } from './ordering.js';

export const LEAN_TO_TYPESCRIPT_SCHEMA_VERSION = 1;
export const LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION = 'tslean-semantic-typed-v5';

/**
 * The Lean module grammar the compiler admits: dot-separated segments beginning with `[A-Za-z_]`.
 * A module name selects the Lake module, the Lean import, the generated file path, and the
 * provenance identity, so it is validated once here and reused wherever a module name arrives.
 */
export function isLeanModuleName(value: string): boolean {
  return /^[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*$/u.test(value);
}

/**
 * Any name Lean can render for a declaration, which is a strictly larger language than the
 * TypeScript-safe subset the compiler is willing to emit. Lean's own generated auxiliaries use
 * numeric components and hygiene marks — `_private.M.0.f.match_1._@.M._hyg.297` at 4.16,
 * `M.instReprT.repr.match_1` at 4.29 — and a closure entry records such a name as provenance
 * without ever emitting it as an identifier. So this checks integrity, not emittability: no empty
 * component, no whitespace, no control character.
 */
export function isLeanDeclarationName(value: string): boolean {
  return /^[^\s.\p{Cc}]+(?:\.[^\s.\p{Cc}]+)*$/u.test(value);
}

/**
 * The types the fragment admits, each with one fixed TypeScript image:
 *
 * - `boolean` is `boolean`.
 * - `nat` is `bigint` restricted to the non-negative values; every admitted `nat` operation
 *   preserves that, which is why truncated subtraction is the only subtraction.
 * - `string` is `string`.
 * - `parameter` is the enclosing declaration's type parameter at that position. Type parameters
 *   are positional, never named, so a generated generic cannot drift with a Lean binder name.
 * - `named` is a data type this compilation exported, applied to exactly its declared arity.
 * - `option`, `except` and `list` are the three Lean data types the compiler maps rather than
 *   lowers: tagged unions for the first two, a readonly array for the third.
 * - `function` is an uncurried arrow at its full Lean arity. A partially applied function value
 *   has no image, so the exporter saturates it or refuses it.
 */
export type LeanType =
  | { readonly kind: 'boolean' }
  | { readonly kind: 'nat' }
  | { readonly kind: 'string' }
  | { readonly kind: 'parameter'; readonly index: number }
  | { readonly kind: 'named'; readonly name: string; readonly arguments: readonly LeanType[] }
  | { readonly kind: 'option'; readonly value: LeanType }
  | { readonly kind: 'except'; readonly error: LeanType; readonly value: LeanType }
  | { readonly kind: 'list'; readonly element: LeanType }
  | { readonly kind: 'function'; readonly parameters: readonly LeanType[]; readonly result: LeanType };

/**
 * The closed set of runtime operations the fragment admits. An opcode is an identity, not a name:
 * the exporter attaches it after matching an exact elaborated constant together with its exact
 * instance argument, the IR refuses any opcode outside this set, and the emitter has exactly one
 * TypeScript form per opcode. Nothing here is derived from a Lean or TypeScript identifier, so a
 * renamed constant cannot silently acquire an admitted meaning.
 */
export type LeanOpcode =
  | 'bool.and'
  | 'bool.or'
  | 'bool.not'
  | 'bool.equals'
  | 'nat.add'
  | 'nat.subtract'
  | 'nat.multiply'
  | 'nat.less'
  | 'nat.lessOrEqual'
  | 'nat.equals'
  | 'nat.successor'
  | 'string.append'
  | 'string.equals'
  | 'list.length'
  | 'list.isEmpty'
  | 'list.append'
  | 'list.reverse'
  | 'list.map'
  | 'list.filter'
  | 'list.foldLeft'
  | 'list.foldRight'
  | 'list.any'
  | 'list.all'
  | 'list.head'
  | 'list.first'
  | 'list.rest';

/**
 * The external facts a runtime opcode stands on, as a closed set so an opcode cannot quietly
 * acquire a new external dependency. Each identifier names a record the Lean semantics library
 * owns, and every admitted opcode's model theorem closes over exactly the ones its row lists.
 */
export type LeanRuntimeAssumption =
  | 'boolean.logical-operators'
  | 'strict-equality.same-type'
  | 'bigint.exact-arithmetic'
  | 'bigint.relational'
  | 'bigint.from-length'
  | 'conditional.truthy-selection'
  | 'string.utf16-concatenation'
  | 'array.dense-element-sequence'
  | 'option.tagged-object';

export const LEAN_RUNTIME_ASSUMPTIONS: Readonly<Record<LeanRuntimeAssumption, string>> = {
  'boolean.logical-operators': '&&, || and ! on JavaScript booleans are the Lean Bool operations',
  'strict-equality.same-type':
    '=== between two values of one primitive type decides Lean equality at that type',
  'bigint.exact-arithmetic': 'BigInt +, - and * are exact integer operations, with no overflow and no rounding',
  'bigint.relational': 'BigInt < and <= decide the integer order',
  'bigint.from-length': 'BigInt(length) is exact, because an array length is a safe integer',
  'conditional.truthy-selection': 'condition ? left : right selects left exactly when condition is true',
  'string.utf16-concatenation':
    '+ on strings concatenates their UTF-16 code unit sequences, which preserves the Unicode scalar sequence',
  'array.dense-element-sequence':
    'a readonly array is a dense sequence carrying the Lean List order and length, and its map, filter, some, every, reduce and reduceRight visit every index exactly once',
  'option.tagged-object': '{ kind: "none" } and { kind: "some", value } denote Option.none and Option.some',
};

/** Where the Lean semantics library declares the model theorem of every runtime opcode. */
const MODEL_NAMESPACE = 'TSLean.LeanToTypeScript.Semantics.Opcode';

/**
 * The two opcodes whose exact Lean semantics need a guard. A guard that appears at every use site
 * would exist many times, so the emitter puts it in one generated declaration and records the role
 * it plays. The role is abstract on purpose: the emitted identifier comes from the emitter's own
 * allocator, so a certificate binds the printed declaration rather than a name fixed here.
 */
export type LeanRuntimeHelperRole = 'nat-truncated-subtraction' | 'list-head-option';

/**
 * The certificate-facing identity of an opcode's target. An inline form binds to the canonical
 * source form in its opcode row; a helper form binds through the role-to-allocated-name map the
 * emitter reports after planning the program. Neither variant is a guessed TypeScript identifier.
 */
export type LeanRuntimeSymbol = `inline:${LeanOpcode}` | `helper:${LeanRuntimeHelperRole}`;

/** The helper role one tagged runtime symbol names, or none for an inline form. */
export function runtimeHelperRole(symbol: LeanRuntimeSymbol): LeanRuntimeHelperRole | undefined {
  switch (symbol) {
    case 'helper:nat-truncated-subtraction':
      return 'nat-truncated-subtraction';
    case 'helper:list-head-option':
      return 'list-head-option';
    default:
      return undefined;
  }
}

/**
 * One primitive or representation step inside a generated helper. This is separate from
 * `LeanRuntimeSymbol`: the primary helper symbol binds the declaration digest, while Formal proves
 * this ordered sequence gives the helper its source meaning. A component is never a second name for
 * a declaration and never a new assumption identifier.
 */
export type LeanRuntimeComponent =
  | 'inline:nat.less'
  | 'inline:list.isEmpty'
  | 'inline:list.first'
  | 'conditional:select'
  | 'primitive:bigint.subtract'
  | 'representation:option.tagged-option';

interface LeanRuntimeOpcodeBase {
  readonly opcode: LeanOpcode;
  /**
   * The Lean constant whose meaning the opcode fixes. For a destructuring opcode it is the
   * constructor whose field the emitted form reads.
   */
  readonly leanSymbol: string;
  /** The one TypeScript form the emitter produces, written over the opcode's own operands. */
  readonly runtimeForm: string;
  /**
   * The kernel-checked Lean theorem that relates `leanSymbol` to this runtime symbol. The compiler
   * guarantees the emitted TypeScript is exactly the row's inline form, or its tagged helper.
   */
  readonly modelTheorem: string;
  /** The assumption records that theorem closes over, in this order. */
  readonly assumptions: readonly LeanRuntimeAssumption[];
  /** How many type arguments the opcode takes, positionally. */
  readonly typeParameters: number;
  /** The operand types, in order, given the opcode's type arguments. */
  readonly parameters: (typeArguments: readonly LeanType[]) => readonly LeanType[];
  readonly result: (typeArguments: readonly LeanType[]) => LeanType;
}

/** An inline form binds its canonical source form and carries no helper composition. */
export interface LeanInlineRuntimeOpcode extends LeanRuntimeOpcodeBase {
  readonly runtimeSymbol: `inline:${LeanOpcode}`;
  readonly components?: never;
}

/** A helper binds one allocated declaration and lists Formal's ordered primitive composition. */
export interface LeanHelperRuntimeOpcode extends LeanRuntimeOpcodeBase {
  readonly runtimeSymbol: `helper:${LeanRuntimeHelperRole}`;
  readonly components: readonly LeanRuntimeComponent[];
}

export type LeanRuntimeOpcode = LeanInlineRuntimeOpcode | LeanHelperRuntimeOpcode;

const BOOLEAN: LeanType = { kind: 'boolean' };
const NAT: LeanType = { kind: 'nat' };
const STRING: LeanType = { kind: 'string' };

function typeArgument(typeArguments: readonly LeanType[], index: number): LeanType {
  const type = typeArguments[index];
  if (type === undefined) throw new TypeError(`runtime opcode is missing type argument ${index}`);
  return type;
}

/** The signature of an opcode over concrete types, which is every opcode outside the list family. */
function monomorphic(
  parameters: readonly LeanType[],
  result: LeanType,
): Pick<LeanRuntimeOpcode, 'typeParameters' | 'parameters' | 'result'> {
  return { typeParameters: 0, parameters: () => parameters, result: () => result };
}

/**
 * Every admitted runtime operation, its Lean meaning, the TypeScript form the emitter owes it, and
 * the certificate obligation it carries. The record is total over `LeanOpcode` and has no fallback
 * entry, so an operation either appears here with a fixed semantics or is refused before it reaches
 * a generated file.
 */
export const LEAN_RUNTIME_OPCODES: Readonly<Record<LeanOpcode, LeanRuntimeOpcode>> = {
  'bool.and': {
    opcode: 'bool.and',
    runtimeSymbol: 'inline:bool.and',
    leanSymbol: 'Bool.and',
    runtimeForm: 'left && right',
    modelTheorem: `${MODEL_NAMESPACE}.boolAndModelsAnd`,
    assumptions: ['boolean.logical-operators'],
    ...monomorphic([BOOLEAN, BOOLEAN], BOOLEAN),
  },
  'bool.or': {
    opcode: 'bool.or',
    runtimeSymbol: 'inline:bool.or',
    leanSymbol: 'Bool.or',
    runtimeForm: 'left || right',
    modelTheorem: `${MODEL_NAMESPACE}.boolOrModelsOr`,
    assumptions: ['boolean.logical-operators'],
    ...monomorphic([BOOLEAN, BOOLEAN], BOOLEAN),
  },
  'bool.not': {
    opcode: 'bool.not',
    runtimeSymbol: 'inline:bool.not',
    leanSymbol: 'Bool.not',
    runtimeForm: '!operand',
    modelTheorem: `${MODEL_NAMESPACE}.boolNotModelsNot`,
    assumptions: ['boolean.logical-operators'],
    ...monomorphic([BOOLEAN], BOOLEAN),
  },
  'bool.equals': {
    opcode: 'bool.equals',
    runtimeSymbol: 'inline:bool.equals',
    leanSymbol: 'instDecidableEqBool',
    runtimeForm: 'left === right',
    modelTheorem: `${MODEL_NAMESPACE}.boolEqualsModelsBEq`,
    assumptions: ['strict-equality.same-type'],
    ...monomorphic([BOOLEAN, BOOLEAN], BOOLEAN),
  },
  'nat.add': {
    opcode: 'nat.add',
    runtimeSymbol: 'inline:nat.add',
    leanSymbol: 'Nat.add',
    runtimeForm: 'left + right',
    modelTheorem: `${MODEL_NAMESPACE}.natAddModelsAdd`,
    assumptions: ['bigint.exact-arithmetic'],
    ...monomorphic([NAT, NAT], NAT),
  },
  'nat.subtract': {
    opcode: 'nat.subtract',
    runtimeSymbol: 'helper:nat-truncated-subtraction',
    components: ['inline:nat.less', 'conditional:select', 'primitive:bigint.subtract'],
    leanSymbol: 'Nat.sub',
    runtimeForm: 'left < right ? 0n : left - right',
    modelTheorem: `${MODEL_NAMESPACE}.natSubtractModelsSub`,
    // Ordered to match the components above: the comparison decides, the conditional selects, and
    // the subtraction runs only on the branch the comparison admitted.
    assumptions: ['bigint.relational', 'conditional.truthy-selection', 'bigint.exact-arithmetic'],
    ...monomorphic([NAT, NAT], NAT),
  },
  'nat.multiply': {
    opcode: 'nat.multiply',
    runtimeSymbol: 'inline:nat.multiply',
    leanSymbol: 'Nat.mul',
    runtimeForm: 'left * right',
    modelTheorem: `${MODEL_NAMESPACE}.natMultiplyModelsMul`,
    assumptions: ['bigint.exact-arithmetic'],
    ...monomorphic([NAT, NAT], NAT),
  },
  'nat.less': {
    opcode: 'nat.less',
    runtimeSymbol: 'inline:nat.less',
    leanSymbol: 'Nat.decLt',
    runtimeForm: 'left < right',
    modelTheorem: `${MODEL_NAMESPACE}.natLessModelsLt`,
    assumptions: ['bigint.relational'],
    ...monomorphic([NAT, NAT], BOOLEAN),
  },
  'nat.lessOrEqual': {
    opcode: 'nat.lessOrEqual',
    runtimeSymbol: 'inline:nat.lessOrEqual',
    leanSymbol: 'Nat.decLe',
    runtimeForm: 'left <= right',
    modelTheorem: `${MODEL_NAMESPACE}.natLessOrEqualModelsLe`,
    assumptions: ['bigint.relational'],
    ...monomorphic([NAT, NAT], BOOLEAN),
  },
  'nat.equals': {
    opcode: 'nat.equals',
    runtimeSymbol: 'inline:nat.equals',
    leanSymbol: 'instDecidableEqNat',
    runtimeForm: 'left === right',
    modelTheorem: `${MODEL_NAMESPACE}.natEqualsModelsBEq`,
    assumptions: ['strict-equality.same-type'],
    ...monomorphic([NAT, NAT], BOOLEAN),
  },
  'nat.successor': {
    opcode: 'nat.successor',
    runtimeSymbol: 'inline:nat.successor',
    leanSymbol: 'Nat.succ',
    runtimeForm: 'operand + 1n',
    modelTheorem: `${MODEL_NAMESPACE}.natSuccessorModelsSucc`,
    assumptions: ['bigint.exact-arithmetic'],
    ...monomorphic([NAT], NAT),
  },
  'string.append': {
    opcode: 'string.append',
    runtimeSymbol: 'inline:string.append',
    leanSymbol: 'String.append',
    runtimeForm: 'left + right',
    modelTheorem: `${MODEL_NAMESPACE}.stringAppendModelsAppend`,
    assumptions: ['string.utf16-concatenation'],
    ...monomorphic([STRING, STRING], STRING),
  },
  'string.equals': {
    opcode: 'string.equals',
    runtimeSymbol: 'inline:string.equals',
    leanSymbol: 'instDecidableEqString',
    runtimeForm: 'left === right',
    modelTheorem: `${MODEL_NAMESPACE}.stringEqualsModelsBEq`,
    assumptions: ['strict-equality.same-type'],
    ...monomorphic([STRING, STRING], BOOLEAN),
  },
  'list.length': {
    opcode: 'list.length',
    runtimeSymbol: 'inline:list.length',
    leanSymbol: 'List.length',
    runtimeForm: 'BigInt(value.length)',
    modelTheorem: `${MODEL_NAMESPACE}.listLengthModelsLength`,
    assumptions: ['bigint.from-length'],
    typeParameters: 1,
    parameters: (args) => [{ kind: 'list', element: typeArgument(args, 0) }],
    result: () => NAT,
  },
  'list.isEmpty': {
    opcode: 'list.isEmpty',
    runtimeSymbol: 'inline:list.isEmpty',
    leanSymbol: 'List.isEmpty',
    runtimeForm: 'value.length === 0',
    modelTheorem: `${MODEL_NAMESPACE}.listIsEmptyModelsIsEmpty`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 1,
    parameters: (args) => [{ kind: 'list', element: typeArgument(args, 0) }],
    result: () => BOOLEAN,
  },
  'list.append': {
    opcode: 'list.append',
    runtimeSymbol: 'inline:list.append',
    leanSymbol: 'List.append',
    runtimeForm: '[...left, ...right]',
    modelTheorem: `${MODEL_NAMESPACE}.listAppendModelsAppend`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 1,
    parameters: (args) => [
      { kind: 'list', element: typeArgument(args, 0) },
      { kind: 'list', element: typeArgument(args, 0) },
    ],
    result: (args) => ({ kind: 'list', element: typeArgument(args, 0) }),
  },
  'list.reverse': {
    opcode: 'list.reverse',
    runtimeSymbol: 'inline:list.reverse',
    leanSymbol: 'List.reverse',
    runtimeForm: '[...value].reverse()',
    modelTheorem: `${MODEL_NAMESPACE}.listReverseModelsReverse`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 1,
    parameters: (args) => [{ kind: 'list', element: typeArgument(args, 0) }],
    result: (args) => ({ kind: 'list', element: typeArgument(args, 0) }),
  },
  'list.map': {
    opcode: 'list.map',
    runtimeSymbol: 'inline:list.map',
    leanSymbol: 'List.map',
    runtimeForm: 'value.map((element) => transform(element))',
    modelTheorem: `${MODEL_NAMESPACE}.listMapModelsMap`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 2,
    parameters: (args) => [
      { kind: 'function', parameters: [typeArgument(args, 0)], result: typeArgument(args, 1) },
      { kind: 'list', element: typeArgument(args, 0) },
    ],
    result: (args) => ({ kind: 'list', element: typeArgument(args, 1) }),
  },
  'list.filter': {
    opcode: 'list.filter',
    runtimeSymbol: 'inline:list.filter',
    leanSymbol: 'List.filter',
    runtimeForm: 'value.filter((element) => keep(element))',
    modelTheorem: `${MODEL_NAMESPACE}.listFilterModelsFilter`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 1,
    parameters: (args) => [
      { kind: 'function', parameters: [typeArgument(args, 0)], result: BOOLEAN },
      { kind: 'list', element: typeArgument(args, 0) },
    ],
    result: (args) => ({ kind: 'list', element: typeArgument(args, 0) }),
  },
  'list.foldLeft': {
    opcode: 'list.foldLeft',
    runtimeSymbol: 'inline:list.foldLeft',
    leanSymbol: 'List.foldl',
    runtimeForm: 'value.reduce((accumulator, element) => step(accumulator, element), initial)',
    modelTheorem: `${MODEL_NAMESPACE}.listFoldLeftModelsFoldl`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 2,
    parameters: (args) => [
      { kind: 'function', parameters: [typeArgument(args, 1), typeArgument(args, 0)], result: typeArgument(args, 1) },
      typeArgument(args, 1),
      { kind: 'list', element: typeArgument(args, 0) },
    ],
    result: (args) => typeArgument(args, 1),
  },
  'list.foldRight': {
    opcode: 'list.foldRight',
    runtimeSymbol: 'inline:list.foldRight',
    leanSymbol: 'List.foldr',
    runtimeForm: 'value.reduceRight((accumulator, element) => step(element, accumulator), initial)',
    modelTheorem: `${MODEL_NAMESPACE}.listFoldRightModelsFoldr`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 2,
    parameters: (args) => [
      { kind: 'function', parameters: [typeArgument(args, 0), typeArgument(args, 1)], result: typeArgument(args, 1) },
      typeArgument(args, 1),
      { kind: 'list', element: typeArgument(args, 0) },
    ],
    result: (args) => typeArgument(args, 1),
  },
  'list.any': {
    opcode: 'list.any',
    runtimeSymbol: 'inline:list.any',
    leanSymbol: 'List.any',
    runtimeForm: 'value.some((element) => holds(element))',
    modelTheorem: `${MODEL_NAMESPACE}.listAnyModelsAny`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 1,
    parameters: (args) => [
      { kind: 'list', element: typeArgument(args, 0) },
      { kind: 'function', parameters: [typeArgument(args, 0)], result: BOOLEAN },
    ],
    result: () => BOOLEAN,
  },
  'list.all': {
    opcode: 'list.all',
    runtimeSymbol: 'inline:list.all',
    leanSymbol: 'List.all',
    runtimeForm: 'value.every((element) => holds(element))',
    modelTheorem: `${MODEL_NAMESPACE}.listAllModelsAll`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 1,
    parameters: (args) => [
      { kind: 'list', element: typeArgument(args, 0) },
      { kind: 'function', parameters: [typeArgument(args, 0)], result: BOOLEAN },
    ],
    result: () => BOOLEAN,
  },
  'list.head': {
    opcode: 'list.head',
    runtimeSymbol: 'helper:list-head-option',
    components: [
      'inline:list.isEmpty',
      'inline:list.first',
      'conditional:select',
      'representation:option.tagged-option',
    ],
    leanSymbol: 'List.head?',
    runtimeForm: 'value.length === 0 ? { kind: "none" } : { kind: "some", value: value[0] }',
    modelTheorem: `${MODEL_NAMESPACE}.listHeadModelsHead`,
    // Ordered to match the components above: the emptiness test reads the sequence, the conditional
    // selects, and only the non-empty branch builds the tagged object over the first element.
    assumptions: ['array.dense-element-sequence', 'conditional.truthy-selection', 'option.tagged-object'],
    typeParameters: 1,
    parameters: (args) => [{ kind: 'list', element: typeArgument(args, 0) }],
    result: (args) => ({ kind: 'option', value: typeArgument(args, 0) }),
  },
  'list.first': {
    opcode: 'list.first',
    runtimeSymbol: 'inline:list.first',
    leanSymbol: 'List.cons',
    runtimeForm: 'value[0]',
    modelTheorem: `${MODEL_NAMESPACE}.listFirstModelsHead`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 1,
    parameters: (args) => [{ kind: 'list', element: typeArgument(args, 0) }],
    result: (args) => typeArgument(args, 0),
  },
  'list.rest': {
    opcode: 'list.rest',
    runtimeSymbol: 'inline:list.rest',
    leanSymbol: 'List.cons',
    runtimeForm: 'value.slice(1)',
    modelTheorem: `${MODEL_NAMESPACE}.listRestModelsTail`,
    assumptions: ['array.dense-element-sequence'],
    typeParameters: 1,
    parameters: (args) => [{ kind: 'list', element: typeArgument(args, 0) }],
    result: (args) => ({ kind: 'list', element: typeArgument(args, 0) }),
  },
};

/**
 * The opcodes a `match` on one type spends, which is how a destructuring form stays accounted for
 * in the runtime opcode set without carrying an opcode of its own. A tag comparison spends none:
 * an option, an except, a user inductive and a structure are all decided by reading a discriminant
 * the representation already carries.
 */
export function matchRuntimeOpcodes(type: LeanType): readonly LeanOpcode[] {
  return type.kind === 'list' ? ['list.isEmpty', 'list.first', 'list.rest'] : [];
}

export type LeanExpression =
  | { readonly kind: 'variable'; readonly index: number }
  | { readonly kind: 'boolean'; readonly value: boolean }
  /** A `Nat` literal as decimal digits, so an arbitrary-precision value survives the IR. */
  | { readonly kind: 'nat'; readonly value: string }
  | { readonly kind: 'string'; readonly value: string }
  | { readonly kind: 'let'; readonly name: string; readonly value: LeanExpression; readonly body: LeanExpression }
  | { readonly kind: 'field'; readonly target: LeanExpression; readonly field: string }
  | {
      readonly kind: 'if';
      readonly condition: LeanExpression;
      readonly consequent: LeanExpression;
      readonly alternate: LeanExpression;
    }
  | {
      readonly kind: 'operation';
      readonly opcode: LeanOpcode;
      readonly typeArguments: readonly LeanType[];
      readonly arguments: readonly LeanExpression[];
    }
  | {
      readonly kind: 'variant';
      readonly type: LeanType;
      readonly name: string;
      readonly arguments: readonly LeanExpression[];
    }
  | {
      readonly kind: 'record';
      readonly type: LeanType;
      readonly fields: readonly { readonly name: string; readonly value: LeanExpression }[];
    }
  | {
      readonly kind: 'match';
      readonly type: LeanType;
      readonly scrutinee: LeanExpression;
      readonly cases: readonly { readonly constructor: string; readonly value: LeanExpression }[];
    }
  | {
      readonly kind: 'lambda';
      readonly parameters: readonly LeanParameter[];
      readonly body: LeanExpression;
    }
  | { readonly kind: 'apply'; readonly target: LeanExpression; readonly arguments: readonly LeanExpression[] }
  | {
      readonly kind: 'call';
      readonly function: string;
      readonly typeArguments: readonly LeanType[];
      readonly arguments: readonly LeanExpression[];
    };

export interface LeanDocumented {
  readonly doc?: string;
}

export interface LeanParameter {
  readonly name: string;
  readonly type: LeanType;
}

export interface LeanField extends LeanDocumented {
  readonly name: string;
  readonly type: LeanType;
}

export interface LeanEnumConstructor extends LeanDocumented {
  readonly name: string;
  readonly fields: readonly LeanField[];
}

/** Where a declaration is written, in its own Lean source. Lines are 1-based, columns 0-based. */
export interface LeanSpan {
  readonly startLine: number;
  readonly startColumn: number;
  readonly endLine: number;
  readonly endColumn: number;
}

interface LeanDeclared extends LeanDocumented {
  readonly name: string;
  /** The Lean module that declares it, which decides the generated file that carries it. */
  readonly module: string;
  /**
   * The Lean namespace that owns it, empty at the root. Method ownership is read from this and
   * from the receiver record below, never from the shape of the declaration's name.
   */
  readonly namespace: string;
  /** The Lean binder names of its type parameters, in order, for diagnostics only. */
  readonly typeParameters: readonly string[];
  readonly span: LeanSpan;
}

/**
 * Explicit dot-notation evidence. Lean resolves `value.f` by the namespace of the head symbol of
 * `value`'s elaborated type, so the exporter records which parameter is the receiver and which
 * data type it selects. The IR then checks that claim against the declaration's own namespace and
 * the parameter's own elaborated type.
 */
export interface LeanReceiver {
  readonly type: string;
  readonly parameter: number;
}

/**
 * How Lean discharged termination, and the exact evidence the compiler read.
 *
 * A single-declaration structural recursion is re-verified here against the emitted program: the
 * self-call has to pass a constructor field of the parameter Lean decreases on, so the generated
 * recursion terminates for the reason the Lean definition does. Every other recursive form —
 * well-founded recursion, or a mutual group — has a measure the emitted program cannot restate, so
 * the policy is narrower and explicit: the body is read from the kernel-checked unfolding equation
 * named here, the recursive group is recorded, and a recursive call outside that group is refused.
 */
export interface LeanTermination {
  readonly kind: 'structural' | 'wellFounded';
  /** The parameter the structural recursion decreases on. Present exactly for `structural`. */
  readonly argument?: number;
  /** Every declaration in Lean's recursive group, in Lean's own order, including this one. */
  readonly group: readonly string[];
  /** The unfolding theorem the exported body was read from. */
  readonly equation: string;
}

export type LeanDeclaration =
  | ({
      readonly kind: 'enum';
      readonly constructors: readonly LeanEnumConstructor[];
    } & LeanDeclared)
  | ({
      readonly kind: 'record';
      /** The Lean constructor a match on this structure decides. */
      readonly constructor: string;
      readonly fields: readonly LeanField[];
    } & LeanDeclared)
  | ({
      readonly kind: 'function';
      readonly parameters: readonly LeanParameter[];
      readonly result: LeanType;
      readonly receiver?: LeanReceiver;
      readonly termination?: LeanTermination;
      readonly body: LeanExpression;
    } & LeanDeclared);

export type LeanFunctionDeclaration = Extract<LeanDeclaration, { readonly kind: 'function' }>;
export type LeanDataDeclaration = Extract<LeanDeclaration, { readonly kind: 'enum' | 'record' }>;

export interface LeanSemanticProgram {
  readonly schemaVersion: 1;
  readonly fragmentVersion: typeof LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION;
  readonly roots: readonly string[];
  /**
   * Every constant reachable from the roots and what the compiler did with it. The exporter
   * refuses anything it can neither emit, erase, nor admit at the runtime boundary, so this
   * accounts for the whole closure rather than the part that reached a generated file.
   */
  readonly closure: readonly LeanToTypeScriptClosureEntry[];
  readonly declarations: readonly LeanDeclaration[];
}

/** One constructor of an admitted type, with its field types already instantiated. */
export interface LeanConstructorView {
  readonly name: string;
  readonly fields: readonly LeanField[];
}

export type LeanDeclarationIndex = ReadonlyMap<string, LeanDeclaration>;

/**
 * The constructors of a type, instantiated at that type's own arguments. A mapped Lean type gets
 * the constructor set its TypeScript representation carries, which is why `option`, `except`,
 * `list` can be matched with exactly the machinery a user inductive uses. `nat` has none: Lean
 * compiles a `0` pattern to an `OfNat` literal rather than to `Nat.zero`, so a `Nat` is decided
 * with the comparison opcodes instead of destructured.
 */
export function constructorsOf(type: LeanType, declarations: LeanDeclarationIndex): readonly LeanConstructorView[] {
  switch (type.kind) {
    case 'option':
      return [
        { name: 'none', fields: [] },
        { name: 'some', fields: [{ name: 'value', type: type.value }] },
      ];
    case 'except':
      return [
        { name: 'error', fields: [{ name: 'error', type: type.error }] },
        { name: 'ok', fields: [{ name: 'value', type: type.value }] },
      ];
    case 'list':
      return [
        { name: 'nil', fields: [] },
        {
          name: 'cons',
          fields: [
            { name: 'head', type: type.element },
            { name: 'tail', type },
          ],
        },
      ];
    case 'named': {
      const declaration = declarations.get(type.name);
      if (declaration === undefined || declaration.kind === 'function') return [];
      if (declaration.kind === 'record') {
        return [{ name: declaration.constructor, fields: substituteFields(declaration.fields, type.arguments) }];
      }
      return declaration.constructors.map((constructor) => ({
        name: constructor.name,
        fields: substituteFields(constructor.fields, type.arguments),
      }));
    }
    default:
      return [];
  }
}

/**
 * The free outer bindings an expression reads after dead-let elimination. The emitter and runtime
 * opcode traversal consume the same bottom-up result: a dead value emits no code, so it cannot keep
 * an outer binder, runtime helper, or certificate component alive.
 */
export interface LeanExpressionLiveness {
  uses(expression: LeanExpression, binding: number): boolean;
}

/**
 * Analyses one expression once, bottom-up. Each node gets one compact free-de-Bruijn set. A nested
 * chain of dead lets is therefore linear in its nodes rather than a repeated target query tree.
 */
export function analyzeExpressionLiveness(
  root: LeanExpression,
  declarations: LeanDeclarationIndex,
): LeanExpressionLiveness {
  const free = new WeakMap<object, ReadonlySet<number>>();
  const union = (...sets: readonly ReadonlySet<number>[]): ReadonlySet<number> => {
    const result = new Set<number>();
    for (const entries of sets) for (const entry of entries) result.add(entry);
    return result;
  };
  const unbind = (entries: ReadonlySet<number>, count: number): ReadonlySet<number> => {
    const result = new Set<number>();
    for (const entry of entries) if (entry >= count) result.add(entry - count);
    return result;
  };
  const visit = (expression: LeanExpression): ReadonlySet<number> => {
    const cached = free.get(expression);
    if (cached !== undefined) return cached;
    let result: ReadonlySet<number>;
    switch (expression.kind) {
      case 'variable':
        result = new Set([expression.index]);
        break;
      case 'boolean':
      case 'nat':
      case 'string':
        result = new Set();
        break;
      case 'let': {
        const body = visit(expression.body);
        // Only a live binding evaluates its value. If it is dead, omitting that value also omits
        // every outer reference and opcode nested in it.
        result = body.has(0) ? union(unbind(body, 1), visit(expression.value)) : unbind(body, 1);
        break;
      }
      case 'field':
        result = visit(expression.target);
        break;
      case 'if':
        result = union(visit(expression.condition), visit(expression.consequent), visit(expression.alternate));
        break;
      case 'operation':
      case 'variant':
      case 'call':
        result = union(...expression.arguments.map(visit));
        break;
      case 'record':
        result = union(...expression.fields.map((field) => visit(field.value)));
        break;
      case 'lambda':
        result = unbind(visit(expression.body), expression.parameters.length);
        break;
      case 'apply':
        result = union(visit(expression.target), ...expression.arguments.map(visit));
        break;
      case 'match': {
        const constructors = constructorsOf(expression.type, declarations);
        result = union(
          visit(expression.scrutinee),
          ...expression.cases.map((entry, index) => unbind(visit(entry.value), constructors[index]?.fields.length ?? 0)),
        );
        break;
      }
    }
    free.set(expression, result);
    return result;
  };
  visit(root);
  return { uses: (expression, binding) => visit(expression).has(binding) };
}

function substituteFields(fields: readonly LeanField[], typeArguments: readonly LeanType[]): readonly LeanField[] {
  return fields.map((field) => ({ ...field, type: substituteType(field.type, typeArguments) }));
}

/** Replaces each positional type parameter with the argument supplied at that position. */
export function substituteType(type: LeanType, typeArguments: readonly LeanType[]): LeanType {
  switch (type.kind) {
    case 'boolean':
    case 'nat':
    case 'string':
      return type;
    case 'parameter': {
      const argument = typeArguments[type.index];
      if (argument === undefined) throw new TypeError(`type parameter ${type.index} has no argument`);
      return argument;
    }
    case 'named':
      return { kind: 'named', name: type.name, arguments: type.arguments.map((a) => substituteType(a, typeArguments)) };
    case 'option':
      return { kind: 'option', value: substituteType(type.value, typeArguments) };
    case 'except':
      return {
        kind: 'except',
        error: substituteType(type.error, typeArguments),
        value: substituteType(type.value, typeArguments),
      };
    case 'list':
      return { kind: 'list', element: substituteType(type.element, typeArguments) };
    case 'function':
      return {
        kind: 'function',
        parameters: type.parameters.map((parameter) => substituteType(parameter, typeArguments)),
        result: substituteType(type.result, typeArguments),
      };
  }
}

export function sameType(left: LeanType, right: LeanType): boolean {
  if (left.kind !== right.kind) return false;
  switch (left.kind) {
    case 'boolean':
    case 'nat':
    case 'string':
      return true;
    case 'parameter':
      return right.kind === 'parameter' && left.index === right.index;
    case 'named':
      return (
        right.kind === 'named' &&
        left.name === right.name &&
        left.arguments.length === right.arguments.length &&
        left.arguments.every((argument, index) => sameType(argument, requiredType(right.arguments, index)))
      );
    case 'option':
      return right.kind === 'option' && sameType(left.value, right.value);
    case 'except':
      return right.kind === 'except' && sameType(left.error, right.error) && sameType(left.value, right.value);
    case 'list':
      return right.kind === 'list' && sameType(left.element, right.element);
    case 'function':
      return (
        right.kind === 'function' &&
        left.parameters.length === right.parameters.length &&
        left.parameters.every((parameter, index) => sameType(parameter, requiredType(right.parameters, index))) &&
        sameType(left.result, right.result)
      );
  }
}

function requiredType(types: readonly LeanType[], index: number): LeanType {
  const type = types[index];
  if (type === undefined) throw new TypeError(`type list has no entry at ${index}`);
  return type;
}

export function renderType(type: LeanType): string {
  switch (type.kind) {
    case 'boolean':
      return 'Bool';
    case 'nat':
      return 'Nat';
    case 'string':
      return 'String';
    case 'parameter':
      return `#${type.index}`;
    case 'named':
      return type.arguments.length === 0
        ? type.name
        : `${type.name} ${type.arguments.map((argument) => `(${renderType(argument)})`).join(' ')}`;
    case 'option':
      return `Option (${renderType(type.value)})`;
    case 'except':
      return `Except (${renderType(type.error)}) (${renderType(type.value)})`;
    case 'list':
      return `List (${renderType(type.element)})`;
    case 'function':
      return `${type.parameters.map((parameter) => `(${renderType(parameter)})`).join(' → ')} → ${renderType(type.result)}`;
  }
}

/**
 * Whether a type has a data image: a JSON-shaped value the generated package can decode at its
 * boundary and compare structurally. A type parameter has none, a function has none, and a user
 * data type applied to arguments has none, because a per-instantiation codec would be a second
 * representation of the same type. Recursion is admitted: a recursive type has a data image
 * exactly when its non-recursive parts do.
 */
export function hasDataImage(type: LeanType, declarations: LeanDeclarationIndex): boolean {
  const visiting = new Set<string>();
  const visit = (candidate: LeanType): boolean => {
    switch (candidate.kind) {
      case 'boolean':
      case 'nat':
      case 'string':
        return true;
      case 'parameter':
      case 'function':
        return false;
      case 'option':
        return visit(candidate.value);
      case 'except':
        return visit(candidate.error) && visit(candidate.value);
      case 'list':
        return visit(candidate.element);
      case 'named': {
        if (candidate.arguments.length > 0) return false;
        if (visiting.has(candidate.name)) return true;
        const declaration = declarations.get(candidate.name);
        if (declaration === undefined || declaration.kind === 'function') return false;
        visiting.add(candidate.name);
        const fields =
          declaration.kind === 'record'
            ? declaration.fields
            : declaration.constructors.flatMap((constructor) => constructor.fields);
        const decided = fields.every((field) => visit(field.type));
        visiting.delete(candidate.name);
        return decided;
      }
    }
  };
  return visit(type);
}

export function decodeLeanSemanticProgram(value: unknown): LeanSemanticProgram {
  const program = object(value, 'semantic program');
  exactKeys(program, ['schemaVersion', 'fragmentVersion', 'roots', 'closure', 'declarations'], 'semantic program');
  if (program['schemaVersion'] !== LEAN_TO_TYPESCRIPT_SCHEMA_VERSION) {
    throw new TypeError(`unsupported Lean semantic IR schema ${String(program['schemaVersion'])}`);
  }
  if (program['fragmentVersion'] !== LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION) {
    throw new TypeError(`unsupported Lean fragment ${String(program['fragmentVersion'])}`);
  }
  const roots = stringArray(program['roots'], 'semantic program roots');
  const declarations = array(program['declarations'], 'semantic program declarations').map((declaration, index) =>
    decodeDeclaration(declaration, `declarations[${index}]`),
  );
  requireUnique(roots, 'semantic program roots');
  requireUnique(
    declarations.map((declaration) => declaration.name),
    'semantic program declarations',
  );
  const closure = array(program['closure'], 'semantic program closure').map((entry, index) =>
    decodeClosureEntry(entry, `closure[${index}]`),
  );
  assertClosureAccountsFor(closure, declarations);
  const decoded: LeanSemanticProgram = {
    schemaVersion: LEAN_TO_TYPESCRIPT_SCHEMA_VERSION,
    fragmentVersion: LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
    roots,
    closure,
    declarations,
  };
  validateProgramReferences(decoded);
  return decoded;
}

/** Every runtime opcode the program names, including the ones its destructuring forms spend. */
export function referencedRuntimeOpcodes(program: LeanSemanticProgram): readonly LeanOpcode[] {
  const opcodes = new Set<LeanOpcode>();
  const declarations: LeanDeclarationIndex = new Map(
    program.declarations.map((declaration) => [declaration.name, declaration]),
  );
  const visit = (expression: LeanExpression, liveness: LeanExpressionLiveness): void => {
    switch (expression.kind) {
      case 'operation':
        opcodes.add(expression.opcode);
        expression.arguments.forEach((argument) => visit(argument, liveness));
        return;
      case 'match':
        for (const opcode of matchRuntimeOpcodes(expression.type)) opcodes.add(opcode);
        visit(expression.scrutinee, liveness);
        expression.cases.forEach((entry) => visit(entry.value, liveness));
        return;
      case 'let':
        // The emitter drops a pure value the body never reads, so its helper/opcode cannot be
        // advertised to a certificate that will bind only printed declarations.
        if (liveness.uses(expression.body, 0)) visit(expression.value, liveness);
        visit(expression.body, liveness);
        return;
      case 'field':
        visit(expression.target, liveness);
        return;
      case 'if':
        visit(expression.condition, liveness);
        visit(expression.consequent, liveness);
        visit(expression.alternate, liveness);
        return;
      case 'variant':
      case 'call':
        expression.arguments.forEach((argument) => visit(argument, liveness));
        return;
      case 'record':
        expression.fields.forEach((field) => visit(field.value, liveness));
        return;
      case 'lambda':
        visit(expression.body, liveness);
        return;
      case 'apply':
        visit(expression.target, liveness);
        expression.arguments.forEach((argument) => visit(argument, liveness));
        return;
      case 'variable':
      case 'boolean':
      case 'nat':
      case 'string':
        return;
    }
  };
  for (const declaration of program.declarations) {
    if (declaration.kind === 'function') {
      const liveness = analyzeExpressionLiveness(declaration.body, declarations);
      visit(declaration.body, liveness);
    }
  }
  return [...opcodes].sort(compareCodePoints);
}

function decodeClosureEntry(value: unknown, location: string): LeanToTypeScriptClosureEntry {
  const entry = object(value, location);
  exactKeys(entry, ['declaration', 'module', 'role', 'reason'], location);
  const role = entry['role'];
  if (role !== 'emitted' && role !== 'erased' && role !== 'runtime-boundary') {
    throw new TypeError(`${location}.role is unsupported: ${String(role)}`);
  }
  const reason = entry['reason'];
  if (typeof reason !== 'string') throw new TypeError(`${location}.reason must be a string`);
  if ((role === 'emitted') !== (reason === '')) {
    throw new TypeError(`${location}.reason must be empty exactly for an emitted declaration`);
  }
  const module = entry['module'];
  if (module !== '' && !isLeanModuleName(string(module, `${location}.module`))) {
    throw new TypeError(`${location}.module is not a Lean module name: ${String(module)}`);
  }
  const declaration = string(entry['declaration'], `${location}.declaration`);
  if (!isLeanDeclarationName(declaration)) {
    throw new TypeError(`${location}.declaration is not a Lean declaration name: ${declaration}`);
  }
  return {
    declaration,
    module: module === '' ? '' : string(module, `${location}.module`),
    role: role satisfies LeanToTypeScriptDeclarationRole,
    reason,
  };
}

/**
 * The closure is the compiler's own account of what it reached. It has to be ordered, unique, and
 * cover every emitted declaration exactly once under the `emitted` role, so a generated tree can
 * never carry a declaration the audit record does not mention.
 */
function assertClosureAccountsFor(
  closure: readonly LeanToTypeScriptClosureEntry[],
  declarations: readonly LeanDeclaration[],
): void {
  for (let index = 1; index < closure.length; index += 1) {
    const previous = closure[index - 1];
    const current = closure[index];
    if (previous === undefined || current === undefined) throw new TypeError('semantic program closure is sparse');
    if (compareCodePoints(previous.declaration, current.declaration) >= 0) {
      throw new TypeError('semantic program closure must be strictly ordered and unique');
    }
  }
  const emitted = new Set(closure.filter((entry) => entry.role === 'emitted').map((entry) => entry.declaration));
  for (const declaration of declarations) {
    if (!emitted.has(declaration.name)) {
      throw new TypeError(`semantic program closure does not record ${declaration.name} as emitted`);
    }
    const entry = closure.find((candidate) => candidate.declaration === declaration.name);
    if (entry !== undefined && entry.module !== declaration.module) {
      throw new TypeError(`semantic program closure disagrees on the module of ${declaration.name}`);
    }
  }
  if (emitted.size !== declarations.length) {
    throw new TypeError('semantic program closure records an emitted declaration that was not exported');
  }
}

/**
 * A qualified Lean name becomes its final component in TypeScript. No two declarations may claim
 * one emitted binding: cross-module aliases have no checked representation policy, and a malformed
 * IR that attributes both to one module would otherwise produce duplicate TS bindings. Refuse both
 * shapes before emission, naming the declarations rather than letting a Map choose one.
 */
function assertDistinctEmittedDeclarationNames(declarations: readonly LeanDeclaration[]): void {
  const owners = new Map<string, LeanDeclaration>();
  for (const declaration of [...declarations].sort((left, right) => compareCodePoints(left.name, right.name))) {
    const emitted = localName(declaration.name);
    const existing = owners.get(emitted);
    if (existing !== undefined) {
      const detail =
        existing.module === declaration.module
          ? `both are attributed to Lean module ${declaration.module}`
          : `are attributed to different Lean modules ${existing.module} and ${declaration.module}`;
      throw new TypeError(
        `${existing.name} and ${declaration.name} both emit ${emitted}; ${detail}; rename one before compiling this module tree`,
      );
    }
    owners.set(emitted, declaration);
  }
}

/** The namespace a declaration claims has to be the prefix its own qualified name spells. */
function assertNamespaceOwnership(declaration: LeanDeclaration): void {
  const expected = declaration.namespace === '' ? localName(declaration.name) : `${declaration.namespace}.${localName(declaration.name)}`;
  if (expected !== declaration.name) {
    throw new TypeError(
      `${declaration.name} claims Lean namespace ${declaration.namespace === '' ? '(root)' : declaration.namespace}, which its own name does not spell`,
    );
  }
}

/**
 * Dot-notation evidence, checked rather than trusted. A method has to live in its receiver type's
 * own namespace, its receiver parameter has to carry exactly that type at exactly the method's own
 * type parameters, and both have to be declared by one Lean module — a receiver in another module
 * would move code across the module boundary the generated tree preserves.
 */
function assertReceiverEvidence(declaration: LeanFunctionDeclaration, declarations: LeanDeclarationIndex): void {
  const receiver = declaration.receiver;
  if (receiver === undefined) return;
  const data = declarations.get(receiver.type);
  if (data === undefined || data.kind === 'function') {
    throw new TypeError(`${declaration.name} claims a receiver ${receiver.type} that is not an exported data type`);
  }
  if (declaration.namespace !== receiver.type) {
    throw new TypeError(
      `${declaration.name} claims ${receiver.type} as its receiver but is owned by namespace ${declaration.namespace === '' ? '(root)' : declaration.namespace}`,
    );
  }
  if (declaration.module !== data.module) {
    throw new TypeError(
      `${declaration.name} is declared by ${declaration.module} but its receiver ${receiver.type} is declared by ${data.module}; declare it beside its type`,
    );
  }
  const parameter = declaration.parameters[receiver.parameter];
  if (parameter === undefined) {
    throw new TypeError(`${declaration.name} claims receiver parameter ${receiver.parameter}, which it does not declare`);
  }
  const expected: LeanType = {
    kind: 'named',
    name: receiver.type,
    arguments: data.typeParameters.map((_, index) => ({ kind: 'parameter', index })),
  };
  if (!sameType(parameter.type, expected)) {
    throw new TypeError(
      `${declaration.name} receiver parameter has type ${renderType(parameter.type)}; dot notation requires ${renderType(expected)}`,
    );
  }
}

function validateProgramReferences(program: LeanSemanticProgram): void {
  const declarations: LeanDeclarationIndex = new Map(
    program.declarations.map((declaration) => [declaration.name, declaration]),
  );
  const functions = new Map(
    program.declarations
      .filter((declaration): declaration is LeanFunctionDeclaration => declaration.kind === 'function')
      .map((declaration) => [declaration.name, declaration]),
  );
  assertDistinctEmittedDeclarationNames(program.declarations);
  for (const declaration of program.declarations) {
    bindingIdentifier(localName(declaration.name), `declaration ${declaration.name}`);
    assertNamespaceOwnership(declaration);
  }

  const validateType = (type: LeanType, typeParameters: number, location: string): void => {
    switch (type.kind) {
      case 'boolean':
      case 'nat':
      case 'string':
        return;
      case 'parameter':
        if (type.index >= typeParameters) {
          throw new TypeError(`${location} references type parameter ${type.index}, which is not declared`);
        }
        return;
      case 'option':
        validateType(type.value, typeParameters, `${location}.value`);
        return;
      case 'except':
        validateType(type.error, typeParameters, `${location}.error`);
        validateType(type.value, typeParameters, `${location}.value`);
        return;
      case 'list':
        validateType(type.element, typeParameters, `${location}.element`);
        return;
      case 'function':
        if (type.parameters.length === 0) {
          throw new TypeError(`${location} is a function type with no parameters`);
        }
        type.parameters.forEach((parameter, index) =>
          validateType(parameter, typeParameters, `${location}.parameters[${index}]`),
        );
        validateType(type.result, typeParameters, `${location}.result`);
        return;
      case 'named': {
        const declaration = declarations.get(type.name);
        if (declaration === undefined || declaration.kind === 'function') {
          throw new TypeError(`${location} references unknown data type ${type.name}`);
        }
        if (declaration.typeParameters.length !== type.arguments.length) {
          throw new TypeError(
            `${location} applies ${type.name} to ${type.arguments.length} type arguments; it declares ${declaration.typeParameters.length}`,
          );
        }
        type.arguments.forEach((argument, index) =>
          validateType(argument, typeParameters, `${location}.arguments[${index}]`),
        );
        return;
      }
    }
  };

  const requireType = (actual: LeanType, expected: LeanType | undefined, location: string): LeanType => {
    if (expected !== undefined && !sameType(actual, expected)) {
      throw new TypeError(`${location} has type ${renderType(actual)}; expected ${renderType(expected)}`);
    }
    return actual;
  };

  const checkExpression = (
    expression: LeanExpression,
    scope: readonly LeanType[],
    expected: LeanType | undefined,
    location: string,
    typeParameters: number,
  ): LeanType => {
    const check = (
      inner: LeanExpression,
      innerScope: readonly LeanType[],
      innerExpected: LeanType | undefined,
      innerLocation: string,
    ): LeanType => checkExpression(inner, innerScope, innerExpected, innerLocation, typeParameters);
    switch (expression.kind) {
      case 'variable': {
        const type = scope[expression.index];
        if (type === undefined) {
          throw new TypeError(`${location} has unbound de Bruijn index ${expression.index}`);
        }
        return requireType(type, expected, location);
      }
      case 'boolean':
        return requireType(BOOLEAN, expected, location);
      case 'nat':
        return requireType(NAT, expected, location);
      case 'string':
        return requireType(STRING, expected, location);
      case 'let': {
        const valueType = check(expression.value, scope, undefined, `${location}.value`);
        return check(expression.body, [valueType, ...scope], expected, `${location}.body`);
      }
      case 'field': {
        const targetType = check(expression.target, scope, undefined, `${location}.target`);
        if (targetType.kind !== 'named') throw new TypeError(`${location}.target is not a record`);
        const declaration = declarations.get(targetType.name);
        if (declaration === undefined || declaration.kind !== 'record') {
          throw new TypeError(`${location}.target is not a record`);
        }
        const field = substituteFields(declaration.fields, targetType.arguments).find(
          (candidate) => candidate.name === expression.field,
        );
        if (field === undefined) {
          throw new TypeError(`${location} references unknown field ${targetType.name}.${expression.field}`);
        }
        return requireType(field.type, expected, location);
      }
      case 'if': {
        check(expression.condition, scope, BOOLEAN, `${location}.condition`);
        if (expected !== undefined) {
          check(expression.consequent, scope, expected, `${location}.consequent`);
          check(expression.alternate, scope, expected, `${location}.alternate`);
          return expected;
        }
        const consequent = check(expression.consequent, scope, undefined, `${location}.consequent`);
        check(expression.alternate, scope, consequent, `${location}.alternate`);
        return consequent;
      }
      case 'operation': {
        const signature = LEAN_RUNTIME_OPCODES[expression.opcode];
        if (signature.typeParameters !== expression.typeArguments.length) {
          throw new TypeError(
            `${location} passes ${expression.typeArguments.length} type arguments to ${expression.opcode}; expected ${signature.typeParameters}`,
          );
        }
        expression.typeArguments.forEach((argument, index) =>
          validateType(argument, typeParameters, `${location}.typeArguments[${index}]`),
        );
        const parameters = signature.parameters(expression.typeArguments);
        if (parameters.length !== expression.arguments.length) {
          throw new TypeError(
            `${location} passes ${expression.arguments.length} operands to ${expression.opcode}; expected ${parameters.length}`,
          );
        }
        expression.arguments.forEach((argument, index) =>
          check(argument, scope, requiredType(parameters, index), `${location}.arguments[${index}]`),
        );
        return requireType(signature.result(expression.typeArguments), expected, location);
      }
      case 'variant': {
        validateType(expression.type, typeParameters, `${location}.type`);
        if (expression.type.kind === 'nat') {
          throw new TypeError(`${location} constructs a Nat; a Nat arrives as a literal or through nat.successor`);
        }
        const constructors = constructorsOf(expression.type, declarations);
        if (constructors.length === 0) {
          throw new TypeError(`${location} constructs ${renderType(expression.type)}, which has no constructors`);
        }
        const constructor = constructors.find((candidate) => candidate.name === expression.name);
        if (constructor === undefined) {
          throw new TypeError(
            `${location} references unknown constructor ${renderType(expression.type)}.${expression.name}`,
          );
        }
        if (constructor.fields.length !== expression.arguments.length) {
          throw new TypeError(
            `${location} passes ${expression.arguments.length} fields to ${expression.name}; expected ${constructor.fields.length}`,
          );
        }
        expression.arguments.forEach((argument, index) =>
          check(argument, scope, requiredType(constructor.fields.map((field) => field.type), index), `${location}.arguments[${index}]`),
        );
        return requireType(expression.type, expected, location);
      }
      case 'match': {
        validateType(expression.type, typeParameters, `${location}.type`);
        if (expression.type.kind === 'nat') {
          throw new TypeError(`${location} matches a Nat; decide it with nat.equals, nat.less or nat.lessOrEqual`);
        }
        const constructors = constructorsOf(expression.type, declarations);
        if (constructors.length === 0) {
          throw new TypeError(`${location} matches ${renderType(expression.type)}, which has no constructors`);
        }
        check(expression.scrutinee, scope, expression.type, `${location}.scrutinee`);
        const decided = expression.cases.map((entry) => entry.constructor);
        if (
          decided.length !== constructors.length ||
          constructors.some((constructor, index) => constructor.name !== decided[index])
        ) {
          throw new TypeError(
            `${location} does not decide every constructor of ${renderType(expression.type)} exactly once in declaration order`,
          );
        }
        // A payload-carrying alternative binds its constructor's fields, innermost binder last,
        // so the arm's scope is the constructor's field types reversed onto the enclosing scope.
        const armScope = (index: number): readonly LeanType[] => {
          const constructor = constructors[index];
          if (constructor === undefined) throw new TypeError(`${location} has an unmatched alternative`);
          return constructor.fields
            .map((field) => field.type)
            .reverse()
            .concat(scope);
        };
        if (expected !== undefined) {
          expression.cases.forEach((entry, index) =>
            check(entry.value, armScope(index), expected, `${location}.cases[${index}].value`),
          );
          return expected;
        }
        const [first, ...rest] = expression.cases;
        if (first === undefined) throw new TypeError(`${location} decides no constructor`);
        const result = check(first.value, armScope(0), undefined, `${location}.cases[0].value`);
        rest.forEach((entry, index) =>
          check(entry.value, armScope(index + 1), result, `${location}.cases[${index + 1}].value`),
        );
        return result;
      }
      case 'record': {
        validateType(expression.type, typeParameters, `${location}.type`);
        if (expression.type.kind !== 'named') {
          throw new TypeError(`${location} constructs ${renderType(expression.type)}, which is not a record`);
        }
        const declaration = declarations.get(expression.type.name);
        if (declaration === undefined || declaration.kind !== 'record') {
          throw new TypeError(`${location} references unknown record ${expression.type.name}`);
        }
        const fields = substituteFields(declaration.fields, expression.type.arguments);
        const expectedFields = fields.map((field) => field.name).sort(compareCodePoints);
        const actualFields = expression.fields.map((field) => field.name).sort(compareCodePoints);
        if (
          expectedFields.length !== actualFields.length ||
          expectedFields.some((field, index) => field !== actualFields[index])
        ) {
          throw new TypeError(`${location} fields do not match record ${expression.type.name}`);
        }
        expression.fields.forEach((field, index) => {
          const fieldType = fields.find((candidate) => candidate.name === field.name)?.type;
          if (fieldType === undefined) throw new TypeError(`${location} has an unknown record field`);
          check(field.value, scope, fieldType, `${location}.fields[${index}].value`);
        });
        return requireType(expression.type, expected, location);
      }
      case 'lambda': {
        expression.parameters.forEach((parameter, index) =>
          validateType(parameter.type, typeParameters, `${location}.parameters[${index}].type`),
        );
        const inner = expression.parameters
          .map((parameter) => parameter.type)
          .reverse()
          .concat(scope);
        const expectedResult = expected?.kind === 'function' ? expected.result : undefined;
        const result = check(expression.body, inner, expectedResult, `${location}.body`);
        return requireType(
          { kind: 'function', parameters: expression.parameters.map((parameter) => parameter.type), result },
          expected,
          location,
        );
      }
      case 'apply': {
        const target = check(expression.target, scope, undefined, `${location}.target`);
        if (target.kind !== 'function') {
          throw new TypeError(`${location}.target has type ${renderType(target)}, which is not applicable`);
        }
        if (target.parameters.length !== expression.arguments.length) {
          throw new TypeError(
            `${location} applies ${expression.arguments.length} arguments to an arrow of arity ${target.parameters.length}`,
          );
        }
        expression.arguments.forEach((argument, index) =>
          check(argument, scope, requiredType(target.parameters, index), `${location}.arguments[${index}]`),
        );
        return requireType(target.result, expected, location);
      }
      case 'call': {
        const declaration = functions.get(expression.function);
        if (declaration === undefined) {
          throw new TypeError(`${location} references unknown function ${expression.function}`);
        }
        if (declaration.typeParameters.length !== expression.typeArguments.length) {
          throw new TypeError(
            `${location} passes ${expression.typeArguments.length} type arguments to ${expression.function}; expected ${declaration.typeParameters.length}`,
          );
        }
        expression.typeArguments.forEach((argument, index) =>
          validateType(argument, typeParameters, `${location}.typeArguments[${index}]`),
        );
        if (declaration.parameters.length !== expression.arguments.length) {
          throw new TypeError(
            `${location} passes ${expression.arguments.length} arguments to ${expression.function}; expected ${declaration.parameters.length}`,
          );
        }
        expression.arguments.forEach((argument, index) => {
          const parameter = declaration.parameters[index];
          if (parameter === undefined) throw new TypeError(`${location} has an unmatched argument`);
          check(
            argument,
            scope,
            substituteType(parameter.type, expression.typeArguments),
            `${location}.arguments[${index}]`,
          );
        });
        return requireType(substituteType(declaration.result, expression.typeArguments), expected, location);
      }
    }
  };

  for (const declaration of program.declarations) {
    const typeParameters = declaration.typeParameters.length;
    if (declaration.kind === 'record') {
      declaration.fields.forEach((field, index) =>
        validateType(field.type, typeParameters, `${declaration.name}.fields[${index}].type`),
      );
    }
    if (declaration.kind === 'enum') {
      for (const constructor of declaration.constructors) {
        constructor.fields.forEach((field, index) =>
          validateType(field.type, typeParameters, `${declaration.name}.${constructor.name}.fields[${index}].type`),
        );
      }
    }
    if (declaration.kind === 'function') {
      declaration.parameters.forEach((parameter, index) =>
        validateType(parameter.type, typeParameters, `${declaration.name}.parameters[${index}].type`),
      );
      validateType(declaration.result, typeParameters, `${declaration.name}.result`);
      assertReceiverEvidence(declaration, declarations);
      validateTermination(declaration, declarations, functions);
      checkExpression(
        declaration.body,
        declaration.parameters.map((parameter) => parameter.type).reverse(),
        declaration.result,
        `${declaration.name}.body`,
        typeParameters,
      );
    }
  }

  for (const root of program.roots) {
    const declaration = functions.get(root);
    if (declaration === undefined) throw new TypeError(`semantic program root is not a function: ${root}`);
    assertDecodableBoundary(declaration, declarations);
  }
}

/**
 * What an external caller has to be able to cross. A root is the generated package's callable
 * surface, so each of its parameters and its result has to have a data image. A generic type has
 * none: its decoder would have to be handed one decoder per type argument, which is a signature a
 * caller cannot use as an entry point, so the boundary is monomorphic and a generic type stays
 * usable everywhere inside the package instead.
 */
function assertDecodableBoundary(declaration: LeanFunctionDeclaration, declarations: LeanDeclarationIndex): void {
  if (declaration.typeParameters.length > 0) {
    throw new TypeError(
      `root ${declaration.name} is polymorphic in ${declaration.typeParameters.length} type parameter(s); a root's boundary is monomorphic`,
    );
  }
  const remedy = (type: LeanType): string =>
    type.kind === 'function'
      ? 'an arrow has no serialized form'
      : `${renderType(type)} has no data image; wrap it in a monomorphic structure at the boundary`;
  for (const [index, parameter] of declaration.parameters.entries()) {
    if (!hasDataImage(parameter.type, declarations)) {
      throw new TypeError(`root ${declaration.name} parameter ${index}: ${remedy(parameter.type)}`);
    }
  }
  if (!hasDataImage(declaration.result, declarations)) {
    throw new TypeError(`root ${declaration.name} result: ${remedy(declaration.result)}`);
  }
}

type RecursionSlot = 'other' | 'recursive' | 'smaller';

/**
 * The termination policy, applied to one declaration.
 *
 * A recursive group is admitted only as Lean recorded it: every member is exported, every member
 * agrees on the group, and no recursive call leaves it. On top of that, a single-declaration
 * structural recursion is re-verified against the emitted program — the self-call has to pass a
 * constructor field of the recursion parameter, taken from a match on it — so the common case
 * carries a decrease argument the generated TypeScript can be read against, not only Lean's word.
 */
function validateTermination(
  declaration: LeanFunctionDeclaration,
  declarations: LeanDeclarationIndex,
  functions: ReadonlyMap<string, LeanFunctionDeclaration>,
): void {
  const termination = declaration.termination;
  const called = calledDeclarations(declaration.body);
  if (termination === undefined) {
    if (called.has(declaration.name)) {
      throw new TypeError(`${declaration.name} calls itself without recorded termination evidence`);
    }
    return;
  }
  if (!termination.group.includes(declaration.name)) {
    throw new TypeError(`${declaration.name} is absent from its own recursive group`);
  }
  for (const member of termination.group) {
    const peer = functions.get(member);
    if (peer === undefined) {
      throw new TypeError(`${declaration.name} names ${member} in its recursive group, which is not an exported function`);
    }
    const peerGroup = peer.termination?.group;
    if (peerGroup === undefined || peerGroup.length !== termination.group.length) {
      throw new TypeError(`${declaration.name} and ${member} disagree on their recursive group`);
    }
    if (peerGroup.some((name, index) => name !== termination.group[index])) {
      throw new TypeError(`${declaration.name} and ${member} disagree on their recursive group`);
    }
  }
  const group = new Set(termination.group);
  const reachesBack = (name: string, seen: Set<string>): boolean => {
    if (name === declaration.name) return true;
    if (seen.has(name)) return false;
    seen.add(name);
    const peer = functions.get(name);
    if (peer === undefined) return false;
    return [...calledDeclarations(peer.body)].some((next) => reachesBack(next, seen));
  };
  for (const target of called) {
    if (group.has(target)) continue;
    if (reachesBack(target, new Set([declaration.name]))) {
      throw new TypeError(
        `${declaration.name} recurses through ${target}, which Lean did not record in its recursive group`,
      );
    }
  }
  if (termination.kind === 'structural') {
    if (termination.argument === undefined) {
      throw new TypeError(`${declaration.name} records structural recursion without a decreasing argument`);
    }
    if (termination.group.length === 1) {
      assertStructuralDecrease(declaration, termination.argument, declarations);
    }
    return;
  }
  if (termination.argument !== undefined) {
    throw new TypeError(`${declaration.name} records a decreasing argument for well-founded recursion`);
  }
  if (!termination.group.some((member) => called.has(member))) {
    throw new TypeError(`${declaration.name} records recursion evidence but never recurses`);
  }
}

function assertStructuralDecrease(
  declaration: LeanFunctionDeclaration,
  argument: number,
  declarations: LeanDeclarationIndex,
): void {
  const parameter = declaration.parameters[argument];
  if (parameter === undefined) {
    throw new TypeError(`${declaration.name} recurses on parameter ${argument}, which it does not declare`);
  }
  const recursiveType = parameter.type;
  if (constructorsOf(recursiveType, declarations).length === 0) {
    throw new TypeError(
      `${declaration.name} recurses on ${renderType(recursiveType)}, which carries no constructors to decrease on`,
    );
  }
  const initial: RecursionSlot[] = declaration.parameters.map((_, index) =>
    index === argument ? 'recursive' : 'other',
  );
  initial.reverse();
  let recursed = false;
  const visit = (expression: LeanExpression, scope: readonly RecursionSlot[]): void => {
    switch (expression.kind) {
      case 'call': {
        if (expression.function === declaration.name) {
          recursed = true;
          const decreasing = expression.arguments[argument];
          if (decreasing === undefined || decreasing.kind !== 'variable' || scope[decreasing.index] !== 'smaller') {
            throw new TypeError(
              `${declaration.name} recurses on a value that is not a constructor field of its ${renderType(recursiveType)} argument`,
            );
          }
        }
        expression.arguments.forEach((entry) => visit(entry, scope));
        return;
      }
      case 'match': {
        visit(expression.scrutinee, scope);
        const scrutinee = expression.scrutinee;
        const decides =
          sameType(expression.type, recursiveType) &&
          scrutinee.kind === 'variable' &&
          (scope[scrutinee.index] === 'recursive' || scope[scrutinee.index] === 'smaller');
        const constructors = constructorsOf(expression.type, declarations);
        expression.cases.forEach((entry, index) => {
          const fields = constructors[index]?.fields ?? [];
          const bindings: RecursionSlot[] = fields.map((field) =>
            decides && sameType(field.type, recursiveType) ? 'smaller' : 'other',
          );
          bindings.reverse();
          visit(entry.value, [...bindings, ...scope]);
        });
        return;
      }
      case 'let':
        visit(expression.value, scope);
        visit(expression.body, ['other', ...scope]);
        return;
      case 'lambda':
        visit(expression.body, [...expression.parameters.map((): RecursionSlot => 'other').reverse(), ...scope]);
        return;
      case 'apply':
        visit(expression.target, scope);
        expression.arguments.forEach((entry) => visit(entry, scope));
        return;
      case 'field':
        visit(expression.target, scope);
        return;
      case 'if':
        visit(expression.condition, scope);
        visit(expression.consequent, scope);
        visit(expression.alternate, scope);
        return;
      case 'operation':
      case 'variant':
        expression.arguments.forEach((entry) => visit(entry, scope));
        return;
      case 'record':
        expression.fields.forEach((field) => visit(field.value, scope));
        return;
      case 'variable':
      case 'boolean':
      case 'nat':
      case 'string':
        return;
    }
  };
  visit(declaration.body, initial);
  if (!recursed) {
    throw new TypeError(`${declaration.name} declares a structural recursion argument but never recurses`);
  }
}

/** Every function a body calls directly, which is what a recursive group has to account for. */
function calledDeclarations(expression: LeanExpression): ReadonlySet<string> {
  const names = new Set<string>();
  const visit = (node: LeanExpression): void => {
    switch (node.kind) {
      case 'call':
        names.add(node.function);
        node.arguments.forEach(visit);
        return;
      case 'operation':
      case 'variant':
        node.arguments.forEach(visit);
        return;
      case 'match':
        visit(node.scrutinee);
        node.cases.forEach((entry) => visit(entry.value));
        return;
      case 'let':
        visit(node.value);
        visit(node.body);
        return;
      case 'field':
        visit(node.target);
        return;
      case 'if':
        visit(node.condition);
        visit(node.consequent);
        visit(node.alternate);
        return;
      case 'record':
        node.fields.forEach((field) => visit(field.value));
        return;
      case 'lambda':
        visit(node.body);
        return;
      case 'apply':
        visit(node.target);
        node.arguments.forEach(visit);
        return;
      case 'variable':
      case 'boolean':
      case 'nat':
      case 'string':
        return;
    }
  };
  visit(expression);
  return names;
}

function decodeDeclaration(value: unknown, location: string): LeanDeclaration {
  const declaration = object(value, location);
  const kind = string(declaration['kind'], `${location}.kind`);
  const name = qualifiedName(declaration['name'], `${location}.name`);
  const module = moduleName(declaration['module'], `${location}.module`);
  const namespaceName = declarationNamespace(declaration['namespace'], `${location}.namespace`);
  const typeParameters = typeParameterNames(declaration['typeParameters'], `${location}.typeParameters`);
  const span = decodeSpan(declaration['span'], `${location}.span`);
  const shared = { name, module, namespace: namespaceName, typeParameters, span };
  switch (kind) {
    case 'enum': {
      exactKeys(
        declaration,
        ['kind', 'name', 'module', 'namespace', 'typeParameters', 'span', 'constructors'],
        location,
        ['doc'],
      );
      const constructors = array(declaration['constructors'], `${location}.constructors`).map(
        (constructor, index): LeanEnumConstructor => {
          const constructorLocation = `${location}.constructors[${index}]`;
          const decoded = object(constructor, constructorLocation);
          exactKeys(decoded, ['name', 'fields'], constructorLocation, ['doc']);
          return {
            name: identifier(decoded['name'], `${constructorLocation}.name`),
            fields: decodeFields(decoded['fields'], constructorLocation),
            ...documentation(decoded, constructorLocation),
          };
        },
      );
      if (constructors.length === 0) throw new TypeError(`${location} has no constructors`);
      requireUnique(
        constructors.map((constructor) => constructor.name),
        `${location}.constructors`,
      );
      return { kind, ...shared, constructors, ...documentation(declaration, location) };
    }
    case 'record': {
      exactKeys(
        declaration,
        ['kind', 'name', 'module', 'namespace', 'typeParameters', 'span', 'constructor', 'fields'],
        location,
        ['doc'],
      );
      return {
        kind,
        ...shared,
        constructor: identifier(declaration['constructor'], `${location}.constructor`),
        fields: decodeFields(declaration['fields'], location),
        ...documentation(declaration, location),
      };
    }
    case 'function': {
      exactKeys(
        declaration,
        ['kind', 'name', 'module', 'namespace', 'typeParameters', 'span', 'parameters', 'result', 'body'],
        location,
        ['doc', 'receiver', 'termination'],
      );
      const parameters = array(declaration['parameters'], `${location}.parameters`).map((parameter, index) => {
        const decoded = object(parameter, `${location}.parameters[${index}]`);
        exactKeys(decoded, ['name', 'type'], `${location}.parameters[${index}]`);
        return {
          name: string(decoded['name'], `${location}.parameters[${index}].name`),
          type: decodeType(decoded['type'], `${location}.parameters[${index}].type`),
        };
      });
      return {
        kind,
        ...shared,
        parameters,
        result: decodeType(declaration['result'], `${location}.result`),
        ...decodeReceiver(declaration, parameters.length, location),
        ...decodeTermination(declaration, parameters.length, location),
        body: decodeExpression(declaration['body'], `${location}.body`),
        ...documentation(declaration, location),
      };
    }
    default:
      throw new TypeError(`${location}.kind is unsupported: ${kind}`);
  }
}

function decodeSpan(value: unknown, location: string): LeanSpan {
  const span = object(value, location);
  exactKeys(span, ['startLine', 'startColumn', 'endLine', 'endColumn'], location);
  const decoded = {
    startLine: line(span['startLine'], `${location}.startLine`),
    startColumn: column(span['startColumn'], `${location}.startColumn`),
    endLine: line(span['endLine'], `${location}.endLine`),
    endColumn: column(span['endColumn'], `${location}.endColumn`),
  };
  if (
    decoded.endLine < decoded.startLine ||
    (decoded.endLine === decoded.startLine && decoded.endColumn < decoded.startColumn)
  ) {
    throw new TypeError(`${location} ends before it starts`);
  }
  return decoded;
}

function line(value: unknown, location: string): number {
  if (!Number.isSafeInteger(value) || Number(value) < 1) throw new TypeError(`${location} must be a 1-based line`);
  return Number(value);
}

function column(value: unknown, location: string): number {
  if (!Number.isSafeInteger(value) || Number(value) < 0) throw new TypeError(`${location} must be a column offset`);
  return Number(value);
}

function decodeReceiver(
  declaration: Record<string, unknown>,
  parameterCount: number,
  location: string,
): { readonly receiver?: LeanReceiver } {
  if (!Object.hasOwn(declaration, 'receiver')) return {};
  const receiver = object(declaration['receiver'], `${location}.receiver`);
  exactKeys(receiver, ['type', 'parameter'], `${location}.receiver`);
  const parameter = receiver['parameter'];
  if (!Number.isSafeInteger(parameter) || Number(parameter) < 0 || Number(parameter) >= parameterCount) {
    throw new TypeError(`${location}.receiver.parameter is not one of the declared parameters`);
  }
  return {
    receiver: {
      type: qualifiedName(receiver['type'], `${location}.receiver.type`),
      parameter: Number(parameter),
    },
  };
}

function decodeTermination(
  declaration: Record<string, unknown>,
  parameterCount: number,
  location: string,
): { readonly termination?: LeanTermination } {
  if (!Object.hasOwn(declaration, 'termination')) return {};
  const termination = object(declaration['termination'], `${location}.termination`);
  exactKeys(termination, ['kind', 'group', 'equation'], `${location}.termination`, ['argument']);
  const kind = string(termination['kind'], `${location}.termination.kind`);
  if (kind !== 'structural' && kind !== 'wellFounded') {
    throw new TypeError(`${location}.termination.kind is unsupported: ${kind}`);
  }
  const group = array(termination['group'], `${location}.termination.group`).map((member, index) =>
    qualifiedName(member, `${location}.termination.group[${index}]`),
  );
  if (group.length === 0) throw new TypeError(`${location}.termination.group is empty`);
  requireUnique(group, `${location}.termination.group`);
  const equation = string(termination['equation'], `${location}.termination.equation`);
  if (!isLeanDeclarationName(equation)) {
    throw new TypeError(`${location}.termination.equation is not a Lean declaration name: ${equation}`);
  }
  if (!Object.hasOwn(termination, 'argument')) {
    return { termination: { kind, group, equation } };
  }
  const argument = termination['argument'];
  if (!Number.isSafeInteger(argument) || Number(argument) < 0 || Number(argument) >= parameterCount) {
    throw new TypeError(`${location}.termination.argument is not one of the declared parameters`);
  }
  return { termination: { kind, argument: Number(argument), group, equation } };
}

function decodeFields(value: unknown, location: string): readonly LeanField[] {
  const fields = array(value, `${location}.fields`).map((field, index) => {
    const fieldLocation = `${location}.fields[${index}]`;
    const decoded = object(field, fieldLocation);
    exactKeys(decoded, ['name', 'type'], fieldLocation, ['doc']);
    return {
      name: identifier(decoded['name'], `${fieldLocation}.name`),
      type: decodeType(decoded['type'], `${fieldLocation}.type`),
      ...documentation(decoded, fieldLocation),
    };
  });
  requireUnique(
    fields.map((field) => field.name),
    `${location}.fields`,
  );
  return fields;
}

function decodeType(value: unknown, location: string): LeanType {
  const type = object(value, location);
  const kind = string(type['kind'], `${location}.kind`);
  switch (kind) {
    case 'boolean':
    case 'nat':
    case 'string':
      exactKeys(type, ['kind'], location);
      return { kind };
    case 'parameter': {
      exactKeys(type, ['kind', 'index'], location);
      const index = type['index'];
      if (!Number.isSafeInteger(index) || Number(index) < 0) {
        throw new TypeError(`${location}.index must be a nonnegative safe integer`);
      }
      return { kind, index: Number(index) };
    }
    case 'named':
      exactKeys(type, ['kind', 'name', 'arguments'], location);
      return {
        kind,
        name: qualifiedName(type['name'], `${location}.name`),
        arguments: array(type['arguments'], `${location}.arguments`).map((argument, index) =>
          decodeType(argument, `${location}.arguments[${index}]`),
        ),
      };
    case 'option':
      exactKeys(type, ['kind', 'value'], location);
      return { kind, value: decodeType(type['value'], `${location}.value`) };
    case 'except':
      exactKeys(type, ['kind', 'error', 'value'], location);
      return {
        kind,
        error: decodeType(type['error'], `${location}.error`),
        value: decodeType(type['value'], `${location}.value`),
      };
    case 'list':
      exactKeys(type, ['kind', 'element'], location);
      return { kind, element: decodeType(type['element'], `${location}.element`) };
    case 'function': {
      exactKeys(type, ['kind', 'parameters', 'result'], location);
      const parameters = array(type['parameters'], `${location}.parameters`).map((parameter, index) =>
        decodeType(parameter, `${location}.parameters[${index}]`),
      );
      if (parameters.length === 0) throw new TypeError(`${location} is a function type with no parameters`);
      const result = decodeType(type['result'], `${location}.result`);
      if (result.kind === 'function') {
        throw new TypeError(`${location} returns an arrow; a function value is admitted at its full Lean arity`);
      }
      return { kind, parameters, result };
    }
    default:
      throw new TypeError(`${location}.kind is unsupported: ${kind}`);
  }
}

function decodeExpression(value: unknown, location: string): LeanExpression {
  const expression = object(value, location);
  const kind = string(expression['kind'], `${location}.kind`);
  switch (kind) {
    case 'variable': {
      exactKeys(expression, ['kind', 'index'], location);
      const index = expression['index'];
      if (!Number.isSafeInteger(index) || Number(index) < 0) {
        throw new TypeError(`${location}.index must be a nonnegative safe integer`);
      }
      return { kind, index: Number(index) };
    }
    case 'boolean':
      exactKeys(expression, ['kind', 'value'], location);
      if (typeof expression['value'] !== 'boolean') {
        throw new TypeError(`${location}.value must be boolean`);
      }
      return { kind, value: expression['value'] };
    case 'nat': {
      exactKeys(expression, ['kind', 'value'], location);
      const digits = string(expression['value'], `${location}.value`);
      if (!/^(?:0|[1-9]\d*)$/u.test(digits)) {
        throw new TypeError(`${location}.value is not a canonical Nat literal: ${digits}`);
      }
      return { kind, value: digits };
    }
    case 'string': {
      exactKeys(expression, ['kind', 'value'], location);
      const text = expression['value'];
      if (typeof text !== 'string') throw new TypeError(`${location}.value must be a string`);
      return { kind, value: text };
    }
    case 'let':
      exactKeys(expression, ['kind', 'name', 'value', 'body'], location);
      return {
        kind,
        name: string(expression['name'], `${location}.name`),
        value: decodeExpression(expression['value'], `${location}.value`),
        body: decodeExpression(expression['body'], `${location}.body`),
      };
    case 'field':
      exactKeys(expression, ['kind', 'target', 'field'], location);
      return {
        kind,
        target: decodeExpression(expression['target'], `${location}.target`),
        field: identifier(expression['field'], `${location}.field`),
      };
    case 'if':
      exactKeys(expression, ['kind', 'condition', 'consequent', 'alternate'], location);
      return {
        kind,
        condition: decodeExpression(expression['condition'], `${location}.condition`),
        consequent: decodeExpression(expression['consequent'], `${location}.consequent`),
        alternate: decodeExpression(expression['alternate'], `${location}.alternate`),
      };
    case 'operation': {
      exactKeys(expression, ['kind', 'opcode', 'typeArguments', 'arguments'], location);
      const opcode = string(expression['opcode'], `${location}.opcode`);
      if (!Object.hasOwn(LEAN_RUNTIME_OPCODES, opcode)) {
        throw new TypeError(`${location}.opcode is not a registered runtime opcode: ${opcode}`);
      }
      // Both read a cons field, which is sound only under the emptiness test a match puts in front
      // of them, so only a match's own accounting may spend them.
      if (opcode === 'list.first' || opcode === 'list.rest') {
        throw new TypeError(`${location}.opcode ${opcode} is spent by a list match, never named by an operation`);
      }
      return {
        kind,
        opcode: opcode as LeanOpcode,
        typeArguments: decodeTypeList(expression['typeArguments'], `${location}.typeArguments`),
        arguments: decodeExpressionList(expression['arguments'], `${location}.arguments`),
      };
    }
    case 'variant':
      exactKeys(expression, ['kind', 'type', 'name', 'arguments'], location);
      return {
        kind,
        type: decodeType(expression['type'], `${location}.type`),
        name: identifier(expression['name'], `${location}.name`),
        arguments: decodeExpressionList(expression['arguments'], `${location}.arguments`),
      };
    case 'record': {
      exactKeys(expression, ['kind', 'type', 'fields'], location);
      const fields = array(expression['fields'], `${location}.fields`).map((field, index) => {
        const decoded = object(field, `${location}.fields[${index}]`);
        exactKeys(decoded, ['name', 'value'], `${location}.fields[${index}]`);
        return {
          name: identifier(decoded['name'], `${location}.fields[${index}].name`),
          value: decodeExpression(decoded['value'], `${location}.fields[${index}].value`),
        };
      });
      requireUnique(
        fields.map((field) => field.name),
        `${location}.fields`,
      );
      return { kind, type: decodeType(expression['type'], `${location}.type`), fields };
    }
    case 'match': {
      exactKeys(expression, ['kind', 'type', 'scrutinee', 'cases'], location);
      const cases = array(expression['cases'], `${location}.cases`).map((entry, index) => {
        const decoded = object(entry, `${location}.cases[${index}]`);
        exactKeys(decoded, ['constructor', 'value'], `${location}.cases[${index}]`);
        return {
          constructor: identifier(decoded['constructor'], `${location}.cases[${index}].constructor`),
          value: decodeExpression(decoded['value'], `${location}.cases[${index}].value`),
        };
      });
      if (cases.length === 0) throw new TypeError(`${location} decides no constructor`);
      requireUnique(
        cases.map((entry) => entry.constructor),
        `${location}.cases`,
      );
      return {
        kind,
        type: decodeType(expression['type'], `${location}.type`),
        scrutinee: decodeExpression(expression['scrutinee'], `${location}.scrutinee`),
        cases,
      };
    }
    case 'lambda': {
      exactKeys(expression, ['kind', 'parameters', 'body'], location);
      const parameters = array(expression['parameters'], `${location}.parameters`).map((parameter, index) => {
        const decoded = object(parameter, `${location}.parameters[${index}]`);
        exactKeys(decoded, ['name', 'type'], `${location}.parameters[${index}]`);
        return {
          name: string(decoded['name'], `${location}.parameters[${index}].name`),
          type: decodeType(decoded['type'], `${location}.parameters[${index}].type`),
        };
      });
      if (parameters.length === 0) throw new TypeError(`${location} abstracts no parameter`);
      return { kind, parameters, body: decodeExpression(expression['body'], `${location}.body`) };
    }
    case 'apply': {
      exactKeys(expression, ['kind', 'target', 'arguments'], location);
      const target = decodeExpression(expression['target'], `${location}.target`);
      // Only a bound function value is applied. A declared function is called through `call`, and
      // one used as a value is eta-expanded into a `lambda` around that call, so an application
      // never has to name a target the emitted program computes.
      if (target.kind !== 'variable') {
        throw new TypeError(`${location}.target is not a bound function value`);
      }
      return { kind, target, arguments: decodeExpressionList(expression['arguments'], `${location}.arguments`) };
    }
    case 'call':
      exactKeys(expression, ['kind', 'function', 'typeArguments', 'arguments'], location);
      return {
        kind,
        function: qualifiedName(expression['function'], `${location}.function`),
        typeArguments: decodeTypeList(expression['typeArguments'], `${location}.typeArguments`),
        arguments: decodeExpressionList(expression['arguments'], `${location}.arguments`),
      };
    default:
      throw new TypeError(`${location}.kind is unsupported: ${kind}`);
  }
}

function decodeTypeList(value: unknown, location: string): readonly LeanType[] {
  return array(value, location).map((type, index) => decodeType(type, `${location}[${index}]`));
}

function decodeExpressionList(value: unknown, location: string): readonly LeanExpression[] {
  return array(value, location).map((entry, index) => decodeExpression(entry, `${location}[${index}]`));
}

function object(value: unknown, location: string): Record<string, unknown> {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new TypeError(`${location} must be an object`);
  }
  return value as Record<string, unknown>;
}

function array(value: unknown, location: string): readonly unknown[] {
  if (!Array.isArray(value)) throw new TypeError(`${location} must be an array`);
  return value;
}

function string(value: unknown, location: string): string {
  if (typeof value !== 'string' || value.length === 0) {
    throw new TypeError(`${location} must be a nonempty string`);
  }
  return value;
}

function identifier(value: unknown, location: string): string {
  const decoded = string(value, location);
  if (!/^[$A-Z_a-z][$\w]*$/u.test(decoded)) {
    throw new TypeError(`${location} is not a TypeScript-safe identifier: ${decoded}`);
  }
  return decoded;
}

function bindingIdentifier(value: unknown, location: string): string {
  const decoded = identifier(value, location);
  const scanner = ts.createScanner(ts.ScriptTarget.Latest, false, ts.LanguageVariant.Standard, decoded);
  const token = scanner.scan();
  if (token !== ts.SyntaxKind.Identifier || scanner.scan() !== ts.SyntaxKind.EndOfFileToken) {
    throw new TypeError(`${location} is not a safe TypeScript binding name: ${decoded}`);
  }
  if (decoded === 'arguments' || decoded === 'eval') {
    throw new TypeError(`${location} is not a safe TypeScript binding name: ${decoded}`);
  }
  return decoded;
}

function qualifiedName(value: unknown, location: string): string {
  const decoded = string(value, location);
  for (const [index, part] of decoded.split('.').entries()) {
    identifier(part, `${location} part ${index}`);
  }
  return decoded;
}

function moduleName(value: unknown, location: string): string {
  const decoded = string(value, location);
  if (!isLeanModuleName(decoded)) throw new TypeError(`${location} is not a Lean module name: ${decoded}`);
  return decoded;
}

/** A namespace is either the Lean root, spelled as the empty string, or a qualified Lean name. */
function declarationNamespace(value: unknown, location: string): string {
  if (value === '') return '';
  return qualifiedName(value, location);
}

/**
 * Type parameter binder names, kept for diagnostics only. Lean libraries spell them `α β γ`, which
 * no generated identifier ever carries: the emitted generics are positional, so a binder name is
 * only required to be a single printable component.
 */
function typeParameterNames(value: unknown, location: string): readonly string[] {
  const names = array(value, location).map((name, index) => {
    const decoded = string(name, `${location}[${index}]`);
    if (/[\s.\p{Cc}]/u.test(decoded)) {
      throw new TypeError(`${location}[${index}] is not a Lean binder name: ${decoded}`);
    }
    return decoded;
  });
  requireUnique(names, location);
  return names;
}

function stringArray(value: unknown, location: string): readonly string[] {
  return array(value, location).map((item, index) => string(item, `${location}[${index}]`));
}

function exactKeys(
  value: Record<string, unknown>,
  required: readonly string[],
  location: string,
  optional: readonly string[] = [],
): void {
  const admitted = new Set([...required, ...optional]);
  const unexpected = Object.keys(value).some((key) => !admitted.has(key));
  const missing = required.some((key) => !Object.hasOwn(value, key));
  if (unexpected || missing) {
    const canonical = [...required].sort(compareCodePoints).join(', ');
    const admittedOptional = [...optional].sort(compareCodePoints).join(', ');
    const suffix = optional.length === 0 ? '' : ` with optional ${admittedOptional}`;
    throw new TypeError(`${location} fields must be exactly ${canonical}${suffix}`);
  }
}

function documentation(value: Record<string, unknown>, location: string): LeanDocumented {
  if (!Object.hasOwn(value, 'doc')) return {};
  const doc = string(value['doc'], `${location}.doc`);
  if (doc.length === 0) throw new TypeError(`${location}.doc must not be empty`);
  if (doc.includes('*/')) throw new TypeError(`${location}.doc must not close a block comment`);
  return { doc };
}

function requireUnique(values: readonly string[], location: string): void {
  if (new Set(values).size !== values.length) throw new TypeError(`${location} contains duplicates`);
}

function localName(name: string): string {
  const part = name.split('.').at(-1);
  if (part === undefined) throw new TypeError('empty Lean name');
  return part;
}
