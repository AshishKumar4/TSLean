// 01-hello-world/hello.ts
// The simplest TSLean example: pure functions that map directly to Lean 4.
//
// Run: npx tsx src/cli.ts examples/01-hello-world/hello.ts -o output.lean

// Pure function → def greet : String
function greet(name: string): string {
  return `Hello, ${name}!`;
}

// Numeric computation → def add : Float → Float → Float
function add(a: number, b: number): number {
  return a + b;
}

// Boolean logic → def isPositive : Float → Bool
function isPositive(x: number): boolean {
  return x > 0;
}

// Constants → def pi : Float
const pi = 3.14159;
const greeting = greet("world");
