// 04-generics/generics.ts
// Generic functions and classes → Lean implicit type parameters + type classes.
//
// Run: npx tsx src/cli.ts examples/04-generics/generics.ts -o output.lean

// Generic identity → def identity {T : Type} (x : T) : T
function identity<T>(x: T): T {
  return x;
}

// Generic container → structure Box (T : Type) where value : T
interface Box<T> {
  value: T;
}

function wrap<T>(x: T): Box<T> {
  return { value: x };
}

function unwrap<T>(box: Box<T>): T {
  return box.value;
}

// Multiple type parameters → {A B : Type}
function pair<A, B>(a: A, b: B): [A, B] {
  return [a, b];
}

function mapArray<T, U>(arr: T[], fn: (x: T) => U): U[] {
  return arr.map(fn);
}

// Constrained generic → [ToString T] type class
function show<T extends string>(x: T): string {
  return String(x);
}
