// 10-advanced/limitations.ts
// Demonstrates patterns that produce sorry — TSLean is honest about limits.
//
// Run: npx tsx src/cli.ts examples/10-advanced/limitations.ts -o output.lean
// Run with --strict to see errors: npx tsx src/cli.ts ... --strict

// typeof/instanceof → sorry (no Lean equivalent for runtime type checks)
function checkType(x: unknown): string {
  if (typeof x === 'string') return 'string';
  if (typeof x === 'number') return 'number';
  return 'other';
}

// Regex → stub (pattern matching not expressible in pure Lean)
function extractEmail(text: string): string | null {
  const match = text.match(/[\w.]+@[\w.]+/);
  return match ? match[0] : null;
}

// Workaround: use discriminated unions instead of typeof
type Value =
  | { type: 'string'; data: string }
  | { type: 'number'; data: number };

// This DOES work — discriminated union + switch → inductive + match
function processValue(v: Value): string {
  switch (v.type) {
    case 'string': return v.data.toUpperCase();
    case 'number': return String(v.data * 2);
  }
}
