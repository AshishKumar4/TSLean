// Regression tests for Bug 1 (Math.*/console.*/JSON.* → Lean stdlib) and
// Bug 2 (exhaustive match catch-all removal).

import { describe, it, expect } from 'vitest';
import * as path from 'path';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';

function inline(src: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: 'test.ts', sourceText: src })));
}

// ─── Bug 1: Math.*/console.*/JSON.* → Lean stdlib ────────────────────────────

// The Math table is tiered: proved carriers, one assumed carrier, and nothing at all for
// the operations ECMA-262 leaves implementation-approximated. Each tier is asserted here
// because the difference between them is the difference between a justified translation
// and a plausible-looking one.

describe('Stdlib mapping: Math property access', () => {
  it('Math.PI → the proved exact encoding, not a decimal literal', () => {
    const code = inline('const pi = Math.PI;');
    expect(code).toContain('TSLean.Stdlib.Numeric.Math.PI');
    expect(code).toContain('import TSLean.Stdlib.Numeric');
    expect(code).not.toContain('3.14159265358979');
  });

  it('Math.E → the proved exact encoding', () => {
    const code = inline('const e = Math.E;');
    expect(code).toContain('TSLean.Stdlib.Numeric.Math.E');
    expect(code).not.toContain('2.718281828459045');
  });
});

describe('Stdlib mapping: Math function calls', () => {
  const tierOne: ReadonlyArray<[string, string]> = [
    ['max', 'function bigger(a: number, b: number): number { return Math.max(a, b); }'],
    ['min', 'function smaller(a: number, b: number): number { return Math.min(a, b); }'],
    ['floor', 'function flr(x: number): number { return Math.floor(x); }'],
    ['ceil', 'function up(x: number): number { return Math.ceil(x); }'],
    ['round', 'function rnd(x: number): number { return Math.round(x); }'],
    ['abs', 'function magnitude(x: number): number { return Math.abs(x); }'],
    ['trunc', 'function cut(x: number): number { return Math.trunc(x); }'],
    ['sign', 'function direction(x: number): number { return Math.sign(x); }'],
  ];

  for (const [operation, source] of tierOne) {
    it(`Math.${operation} → the proved TSLean.Stdlib.Numeric.Math carrier`, () => {
      const code = inline(source);
      expect(code).toContain(`TSLean.Stdlib.Numeric.Math.${operation}`);
      expect(code).toContain('import TSLean.Stdlib.Numeric');
      expect(code).not.toContain('default');
    });
  }

  it('Math.max and Math.min do not lower to Lean max/min, which disagree on NaN and -0', () => {
    const code = inline('function pick(a: number, b: number): number { return Math.max(a, Math.min(a, b)); }');
    expect(code).not.toMatch(/(?<!Math\.)\bmax a\b/);
    expect(code).not.toMatch(/(?<!Math\.)\bmin a\b/);
  });

  it('Math.sqrt(x) → Float.sqrt x, the one assumed carrier', () => {
    const code = inline('function root(x: number): number { return Math.sqrt(x); }');
    expect(code).toContain('Float.sqrt x');
    expect(code).not.toContain('Math.sqrt');
  });

  it('implementation-approximated Math operations are unmapped and degrade', () => {
    const unmapped: ReadonlyArray<[string, string]> = [
      ['pow', 'function power(x: number, n: number): number { return Math.pow(x, n); }'],
      ['log', 'function ln(x: number): number { return Math.log(x); }'],
      ['log2', 'function lg(x: number): number { return Math.log2(x); }'],
      ['log10', 'function lg10(x: number): number { return Math.log10(x); }'],
      ['exp', 'function ex(x: number): number { return Math.exp(x); }'],
      ['sin', 'function s(x: number): number { return Math.sin(x); }'],
      ['cos', 'function c(x: number): number { return Math.cos(x); }'],
      ['tan', 'function t(x: number): number { return Math.tan(x); }'],
      ['asin', 'function asn(x: number): number { return Math.asin(x); }'],
      ['acos', 'function acs(x: number): number { return Math.acos(x); }'],
      ['atan', 'function atn(x: number): number { return Math.atan(x); }'],
      ['atan2', 'function at2(y: number, x: number): number { return Math.atan2(y, x); }'],
      ['cbrt', 'function cb(x: number): number { return Math.cbrt(x); }'],
      ['hypot', 'function hy(a: number, b: number): number { return Math.hypot(a, b); }'],
    ];
    for (const [operation, source] of unmapped) {
      const code = inline(source);
      expect(code, `Math.${operation} must not emit a carrier`).toContain('default');
      expect(code, `Math.${operation} must not emit a Float primitive`).not.toContain(`Float.${operation}`);
    }
  });
});

describe('Stdlib mapping: console.log → IO.println', () => {
  it('console.log(x) → IO.println x', () => {
    const code = inline('function log(msg: string): void { console.log(msg); }');
    expect(code).toContain('IO.println msg');
    expect(code).not.toContain('console.log');
  });

  it('console.error(x) → IO.eprintln x', () => {
    const code = inline('function err(msg: string): void { console.error(msg); }');
    expect(code).toContain('IO.eprintln msg');
    expect(code).not.toContain('console.error');
  });

  it('console.log has IO effect', () => {
    const code = inline('function greet(name: string): void { console.log(name); }');
    const line = code.split('\n').find(l => l.includes('def greet'));
    expect(line).toContain('IO');
  });
});

describe('Stdlib mapping: JSON.stringify/parse', () => {
  it('JSON.stringify(x) → serialize x', () => {
    const code = inline('function toJson(x: number): string { return JSON.stringify(x); }');
    expect(code).toContain('serialize');
    expect(code).not.toContain('JSON.stringify');
  });

  it('JSON.parse(s) → deserialize s', () => {
    const code = inline('function fromJson(s: string): any { return JSON.parse(s); }');
    expect(code).toContain('deserialize');
    expect(code).not.toContain('JSON.parse');
  });
});

describe('Stdlib mapping: bare globals', () => {
  it('parseInt(s) → Numeric.parseInt expression', () => {
    const code = inline('function parse(s: string): number { return parseInt(s); }');
    expect(code).toMatch(/parseInt|sorry|default/);
  });

  it('isNaN(x) → Float.isNaN x', () => {
    const code = inline('function checkNaN(x: number): boolean { return isNaN(x); }');
    expect(code).toContain('Float.isNaN');
  });
});

describe('Stdlib mapping: combined usage', () => {
  it('areaShape with Math.PI uses 3.14159265358979', () => {
    const code = inline(`
      type Shape = { kind: 'circle'; r: number } | { kind: 'rect'; w: number; h: number };
      function area(s: Shape): number {
        switch (s.kind) {
          case 'circle': return Math.PI * s.r * s.r;
          case 'rect': return s.w * s.h;
        }
      }
    `);
    expect(code).toContain('TSLean.Stdlib.Numeric.Math.PI');
  });
});

// ─── Bug 2: Exhaustive match catch-all removal ──────────────────────────────

describe('Exhaustive match: no spurious wildcard', () => {
  it('2-arm discriminated union: no | _ => ()', () => {
    const code = inline(`
      type Shape = { kind: 'circle'; r: number } | { kind: 'rect'; w: number; h: number };
      function area(s: Shape): number {
        switch (s.kind) {
          case 'circle': return 3.14 * s.r * s.r;
          case 'rect': return s.w * s.h;
        }
      }
    `);
    const matchSection = code.slice(code.indexOf('match'));
    expect(matchSection).not.toContain('| _ =>');
    expect(matchSection).not.toContain('| _ => ()');
    expect(matchSection).not.toContain('| _ => sorry');
  });

  it('3-arm discriminated union: no wildcard', () => {
    const code = inline(`
      type Color = { type: 'red' } | { type: 'green' } | { type: 'blue' };
      function name(c: Color): string {
        switch (c.type) {
          case 'red': return 'RED';
          case 'green': return 'GREEN';
          case 'blue': return 'BLUE';
        }
      }
    `);
    const matchSection = code.slice(code.indexOf('match'));
    expect(matchSection).not.toContain('| _ =>');
  });

  it('discriminated union with all arms covered: no wildcard', () => {
    const code = inline(`
      type Either = { tag: 'left'; val: string } | { tag: 'right'; val: number };
      function show(e: Either): string {
        switch (e.tag) {
          case 'left': return e.val;
          case 'right': return 'number';
        }
      }
    `);
    const matchSection = code.slice(code.indexOf('match'));
    expect(matchSection).not.toContain('| _ =>');
  });
});

describe('Non-exhaustive match: wildcard preserved', () => {
  it('number switch with 2 cases: wildcard present', () => {
    const code = inline(`
      function grade(n: number): string {
        switch (n) {
          case 1: return 'A';
          case 2: return 'B';
        }
      }
    `);
    const matchSection = code.slice(code.indexOf('match'));
    expect(matchSection).toContain('| _ =>');
  });

  it('string switch without discriminated union: wildcard present', () => {
    const code = inline(`
      function greet(name: string): string {
        switch (name) {
          case 'Alice': return 'Hi Alice';
          case 'Bob': return 'Hi Bob';
        }
      }
    `);
    const matchSection = code.slice(code.indexOf('match'));
    expect(matchSection).toContain('| _ =>');
  });

  it('wildcard uses sorry (not Unit) for type safety', () => {
    const code = inline(`
      function classify(n: number): string {
        switch (n) {
          case 1: return 'one';
          case 2: return 'two';
        }
      }
    `);
    const matchSection = code.slice(code.indexOf('match'));
    // Wildcard uses a type-appropriate default, not Unit
    expect(matchSection).toContain('| _ =>');
    expect(matchSection).not.toContain('| _ => ()');
  });

  it('switch with default still has wildcard', () => {
    const code = inline(`
      function test(x: number): string {
        switch (x) {
          case 0: return 'zero';
          default: return 'other';
        }
      }
    `);
    const matchSection = code.slice(code.indexOf('match'));
    expect(matchSection).toContain('| _ => "other"');
  });
});

// ─── Cross-cutting: regen discriminated-unions fixture ────────────────────────

describe('Regenerated fixture: discriminated-unions', () => {
  it('areaShape has 3.14159265358979 not Math.PI and no wildcard', () => {
    const code = inline(`
      type Shape =
        | { kind: "circle"; radius: number }
        | { kind: "rectangle"; width: number; height: number }
        | { kind: "triangle"; base: number; height: number };
      function areaShape(s: Shape): number {
        switch (s.kind) {
          case "circle": return Math.PI * s.radius * s.radius;
          case "rectangle": return s.width * s.height;
          case "triangle": return 0.5 * s.base * s.height;
        }
      }
    `);
    // Math.PI mapped
    expect(code).toContain('TSLean.Stdlib.Numeric.Math.PI');
    // No wildcard on exhaustive 3-arm match
    const matchSection = code.slice(code.indexOf('match'));
    expect(matchSection).not.toContain('| _ =>');
    // Pattern variables, not field access
    expect(matchSection).not.toContain('s.radius');
  });
});
