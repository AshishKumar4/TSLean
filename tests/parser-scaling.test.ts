// Scaling guard: the parser must not pay for types it never reads.
//
// The parser resolves one checker type per expression node, and the cost of one
// `TypeChecker.getTypeAtLocation` call grows with the size of the node's own
// subtree rather than being flat.  A node that asks for a type its IR never
// carries therefore multiplies the cost of everything nested inside it, which
// turns nesting depth into a super-linear factor — a conditional cascade of 800
// arms took 31s before those branches stopped asking, and 94ms after.
//
// The probe below nests conditionals, a form the IR types from its own arms, so
// its parse time stays linear only while that branch stays silent.  Ratio-based
// rather than a wall-clock ceiling, in the style of `checkScaling` in
// lean/TSLean/Refinement/Tests/Array.lean: doubling the input must roughly double
// the cost, a quadratic regression shows about 4x, so a 3x envelope separates the
// two while tolerating timer noise.
//
// Deliberately *not* guarded here: an n-term `a + b + c + …` chain. Every node of
// that chain carries a checker-derived type in the IR, so its super-linear cost is
// inherent to the type query rather than waste, and a ratio assertion on it would
// pin that cost in place instead of guarding against a regression.

import { describe, expect, it } from 'vitest';
import { parseFile } from '../src/parser/index.js';

/** Absorbs the fixed per-parse cost (program creation) and timer noise. */
const MARGIN_MS = 250;

/** Samples per measurement; the median discards a single interrupted run. */
const SAMPLES = 3;

/**
 * `c0 ? v0 : c1 ? v1 : … : 0` — the right-nested cascade TypeScript parses
 * `cond ? a : cond ? b : c` into.  Nesting depth grows with `arms`; the sizes
 * used below stay well inside the recursion depth TypeScript's own parser
 * handles (it overflows the default stack around 1600 arms).
 */
function ternaryCascade(arms: number): string {
  const params = Array.from({ length: arms }, (_, i) => `c${i}: boolean, v${i}: number`).join(', ');
  let expr = '0';
  for (let i = arms - 1; i >= 0; i--) expr = `c${i} ? v${i} : ${expr}`;
  return `export function pick(${params}): number {\n  return ${expr};\n}\n`;
}

/** Median parse time of `SAMPLES` runs, in milliseconds. */
function parseMs(sourceText: string): number {
  const runs: number[] = [];
  for (let i = 0; i < SAMPLES; i++) {
    const start = performance.now();
    parseFile({ fileName: 'scaling.ts', sourceText });
    runs.push(performance.now() - start);
  }
  return runs.sort((a, b) => a - b)[Math.floor(SAMPLES / 2)];
}

describe('Parser scaling', () => {
  it('a conditional cascade parses in time linear in its depth', () => {
    const small = ternaryCascade(300);
    const large = ternaryCascade(600);
    parseMs(small);                       // warm up, so `small` is not a JIT baseline
    const smallMs = parseMs(small);
    const largeMs = parseMs(large);
    expect(
      largeMs,
      `300 arms took ${smallMs.toFixed(0)}ms, 600 arms took ${largeMs.toFixed(0)}ms`,
    ).toBeLessThanOrEqual(3 * smallMs + MARGIN_MS);
  });
});
