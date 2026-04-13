// 08-discriminated-unions/shapes.ts
// Discriminated unions → Lean inductive types with pattern matching.
//
// Run: npx tsx src/cli.ts examples/08-discriminated-unions/shapes.ts -o output.lean

// Union with 'kind' discriminant → inductive Shape where | circle | rect | triangle
type Shape =
  | { kind: 'circle'; radius: number }
  | { kind: 'rect'; width: number; height: number }
  | { kind: 'triangle'; base: number; height: number };

// switch on discriminant → match s with | .circle ... | .rect ... | .triangle ...
function area(s: Shape): number {
  switch (s.kind) {
    case 'circle':
      return Math.PI * s.radius * s.radius;
    case 'rect':
      return s.width * s.height;
    case 'triangle':
      return 0.5 * s.base * s.height;
  }
}

function describe(s: Shape): string {
  switch (s.kind) {
    case 'circle':
      return `Circle with radius ${s.radius}`;
    case 'rect':
      return `Rectangle ${s.width}x${s.height}`;
    case 'triangle':
      return `Triangle with base ${s.base}`;
  }
}

// Result type — another common discriminated union
type Result<T> =
  | { ok: true; value: T }
  | { ok: false; error: string };

function getResult(x: number): Result<number> {
  if (x >= 0) return { ok: true, value: Math.sqrt(x) };
  return { ok: false, error: "negative input" };
}
