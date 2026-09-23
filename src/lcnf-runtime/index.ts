/**
 * Runtime of the LCNF → TypeScript lowering (plan M2, vertical slice).
 *
 * Every module printed by `Lcnf.Print` imports this file as `rt`. This file is the single statement
 * of the runtime API the printer may call; the printer (`lean/TSLean/Lcnf/Lower.lean`) and this file
 * must agree on every name below.
 *
 * Representation (mirrors Lean's runtime as mono decided it):
 * - `Nat` is `bigint`.
 * - `Bool` (and `Decidable`, which mono erases to `Bool`) is `boolean`.
 * - An inductive whose constructors all have zero relevant fields is a `number`, the constructor
 *   index.
 * - Every other inductive is an `Obj`: `{ tag, fields }` holding the relevant fields only.
 * - Erased values are the single constant `undefined`: type arguments, irrelevant fields, and
 *   `let _x : lcErased := ◾`. The value is irrelevant, so any constant is sound (Lean IR uses
 *   `box(0)`).
 * - A closure is a `Closure`: a function, its arity and the arguments received so far.
 *
 * API used by printed code:
 * - Types: `Value`, `Obj`.
 * - Primitives (`@[extern]` leaves): `natAdd`, `natSub` (truncating), `natMul`, `natDecEq`,
 *   `natDecLt`.
 * - Closures: `pap(fn, arity, args)`, `apply(f, args)`.
 * - Checked views used by `cases`: `bool(v)`, `enumTag(v)`, `obj(v)`.
 * - Explicit stack: `pushFrame(ks, label)`, bounded by `limits.maxFrames`.
 * - Faults, thrown: `unreachable()`, `noAlt()`, `badTag()`.
 *
 * Outcomes: a run returns a `Value`, or throws `Fault` (the semantics' fault outcome) or
 * `ResourceExhausted` (the typed resource bound, never a V8 `RangeError`).
 */

export type Fn = (...args: Value[]) => Value;

export interface Obj {
  readonly tag: number;
  readonly fields: readonly Value[];
}

export class Closure {
  readonly fn: Fn;
  readonly arity: number;
  readonly args: readonly Value[];
  constructor(fn: Fn, arity: number, args: readonly Value[]) {
    this.fn = fn;
    this.arity = arity;
    this.args = args;
  }
}

export type Value = bigint | number | boolean | string | undefined | Obj | Closure;

/** The semantics' fault outcome: the program reached a state with no meaning. */
export class Fault extends Error {
  constructor(message: string) {
    super(message);
    this.name = "Fault";
  }
}

/** The typed resource bound: the explicit stack outgrew `limits.maxFrames`. */
export class ResourceExhausted extends Error {
  constructor(message: string) {
    super(message);
    this.name = "ResourceExhausted";
  }
}

export const limits = { maxFrames: 1 << 26 };

// ---- checked views ----------------------------------------------------------------------------

export function nat(v: Value): bigint {
  if (typeof v !== "bigint") throw new Fault(`expected a Nat, got ${describe(v)}`);
  return v;
}

export function bool(v: Value): boolean {
  if (typeof v !== "boolean") throw new Fault(`expected a Bool, got ${describe(v)}`);
  return v;
}

export function enumTag(v: Value): number {
  if (typeof v !== "number") throw new Fault(`expected an enumeration tag, got ${describe(v)}`);
  return v;
}

export function obj(v: Value): Obj {
  if (typeof v !== "object" || v instanceof Closure) {
    throw new Fault(`expected a constructor object, got ${describe(v)}`);
  }
  return v;
}

function closure(v: Value): Closure {
  if (!(v instanceof Closure)) throw new Fault(`application of a non-closure ${describe(v)}`);
  return v;
}

function describe(v: Value): string {
  if (v === undefined) return "an erased value";
  if (v instanceof Closure) return `a closure of arity ${v.arity}`;
  if (typeof v === "object") return `a constructor object with tag ${v.tag}`;
  return `a ${typeof v}`;
}

// ---- primitives -------------------------------------------------------------------------------

export function natAdd(a: Value, b: Value): Value {
  return nat(a) + nat(b);
}

export function natSub(a: Value, b: Value): Value {
  const x = nat(a);
  const y = nat(b);
  return x < y ? 0n : x - y;
}

export function natMul(a: Value, b: Value): Value {
  return nat(a) * nat(b);
}

export function natDecEq(a: Value, b: Value): Value {
  return nat(a) === nat(b);
}

export function natDecLt(a: Value, b: Value): Value {
  return nat(a) < nat(b);
}

// ---- closures (Lean's `pap` semantics) --------------------------------------------------------

/** A constant of arity `arity` applied to fewer arguments than its arity. */
export function pap(fn: Fn, arity: number, args: Value[]): Value {
  return new Closure(fn, arity, args);
}

/**
 * Apply `f` to `args`. With fewer arguments than the closure still needs, the result is a closure;
 * with exactly as many, the function runs; with more, it runs on the ones it needs and the result
 * is applied to the rest.
 */
export function apply(f: Value, args: Value[]): Value {
  let c = closure(f);
  let rest = args;
  for (;;) {
    const have = c.args.length + rest.length;
    if (have < c.arity) return new Closure(c.fn, c.arity, [...c.args, ...rest]);
    const need = c.arity - c.args.length;
    const r = c.fn(...c.args, ...rest.slice(0, need));
    if (have === c.arity) return r;
    c = closure(r);
    rest = rest.slice(need);
  }
}

// ---- explicit stack ---------------------------------------------------------------------------

export function pushFrame(ks: number[], label: number): void {
  if (ks.length >= limits.maxFrames) {
    throw new ResourceExhausted(`explicit stack exceeded ${limits.maxFrames} frames`);
  }
  ks.push(label);
}

// ---- faults -----------------------------------------------------------------------------------

export function unreachable(): Fault {
  return new Fault("unreachable code reached");
}

export function noAlt(): Fault {
  return new Fault("no alternative matches the constructor");
}

export function badTag(): Fault {
  return new Fault("dispatch reached an unknown tag");
}
