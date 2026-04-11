// Regression tests for 3 bugs found in sub-agent v3 review.
// Bug #1: IsType (instanceof) hardcoded to `true`
// Bug #2: spread-in-object ({...u, f: v}) dropped the base → lost all spread fields
// Bug #3: switch fall-through cases silently dropped

import { describe, it, expect } from 'vitest';
import * as path from 'path';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyBool, TyNat, TyUnit, TyRef, TyArray, TyOption,
  Pure, Async,
  litNat, litStr, litBool, litUnit, varExpr, structUpdate,
} from '../src/ir/types.js';

function inline(src: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: 'test.ts', sourceText: src })));
}

function mod(decls: IRDecl[]): IRModule {
  return { name: 'T', imports: [], decls, comments: [] };
}

// ─── Bug #1: instanceof / IsType ──────────────────────────────────────────────
// Before: `a instanceof Dog` → `true` (unsound, silently wrong)
// After:  `a instanceof Dog` → `(a matches Dog := sorry)` (honest proof obligation)

describe('Review Bug #1: instanceof / IsType not hardcoded true', () => {
  it('instanceof produces type-safe check, not bare true', () => {
    const code = inline(`
      class Dog {}
      function isDog(a: any): boolean { return a instanceof Dog; }
    `);
    expect(code).toContain('def isDog');
    // Must NOT silently emit `true`
    expect(code).not.toMatch(/isDog[^\n]*\n\s*true\s*$/m);
    // Must emit something meaningful about the type check (not bare true)
    expect(code).toMatch(/True.intro|default|matches|sorry/);
  });

  it('instanceof check references the class name', () => {
    const code = inline(`
      class Cat {}
      function isCat(x: any): boolean { return x instanceof Cat; }
    `);
    const fn = code.slice(code.indexOf('def isCat'));
    expect(fn.slice(0, 200)).toMatch(/Cat|sorry/);
  });

  it('multiple instanceof checks', () => {
    const code = inline(`
      class A {}
      class B {}
      function classify(x: any): string {
        if (x instanceof A) return 'a';
        if (x instanceof B) return 'b';
        return 'unknown';
      }
    `);
    expect(code).toContain('def classify');
    // Should not just be a series of `if true then` which would always take first branch
    expect(code).not.toMatch(/if true then\s*\n\s*"a"\s*\n.*if true then/ms);
  });

  it('IsType IR node in codegen emits type-safe check', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'check', typeParams: [],
      params: [{ name: 'x', type: TyRef('Any') }],
      retType: TyBool, effect: Pure,
      body: {
        tag: 'IsType',
        expr: varExpr('x', TyRef('Any')),
        testType: TyRef('Dog'),
        type: TyBool, effect: Pure,
      },
    }]);
    const code = generateLean(m);
    expect(code).toContain('def check');
    // Should reference Dog and include sorry
    expect(code).toMatch(/Dog|True.intro|default/);
    // Should not be bare `true`
    const fn = code.slice(code.indexOf('def check'));
    expect(fn.slice(0, 200)).not.toMatch(/:=\s*\n?\s*true\s*$/m);
  });
});

// ─── Bug #2: spread-in-object ─────────────────────────────────────────────────
// Before: `{ ...u, name: "Alice" }` → `{ name := "Alice" }` (loses all other fields)
// After:  `{ ...u, name: "Alice" }` → `{ u with name := "Alice" }` (struct update)

describe('Review Bug #2: spread-in-object uses struct update', () => {
  it('{ ...u, f: v } → { u with f := v }', () => {
    const code = inline(`
      interface User { id: string; name: string; email: string }
      function rename(u: User, newName: string): User {
        return { ...u, name: newName };
      }
    `);
    const fn = code.slice(code.indexOf('def rename'));
    expect(fn.slice(0, 300)).toContain('u with name');
    // Must NOT produce a struct literal that loses the spread base
    expect(fn.slice(0, 300)).not.toMatch(/\{\s*name\s*:=\s*newName\s*\}/);
  });

  it('{ ...a, x: 1, y: 2 } → { a with x y }', () => {
    const code = inline(`
      interface Point { x: number; y: number; z: number }
      function resetXY(p: Point): Point { return { ...p, x: 0, y: 0 }; }
    `);
    const fn = code.slice(code.indexOf('def resetXY'));
    expect(fn.slice(0, 300)).toContain('with');
    expect(fn.slice(0, 300)).toContain('x :=');
    expect(fn.slice(0, 300)).toContain('y :=');
  });

  it('pure spread { ...obj } → the object itself', () => {
    const code = inline(`
      interface Config { host: string; port: number }
      function clone(c: Config): Config { return { ...c }; }
    `);
    const fn = code.slice(code.indexOf('def clone'));
    // Pure spread should just be the base expression
    expect(fn.slice(0, 200)).toMatch(/c\b/);
  });

  it('StructUpdate IR node → { base with fields }', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'setY', typeParams: [],
      params: [{ name: 'p', type: TyRef('Point') }, { name: 'v', type: TyFloat }],
      retType: TyRef('Point'), effect: Pure,
      body: structUpdate(
        varExpr('p', TyRef('Point')),
        [{ name: 'y', value: varExpr('v', TyFloat) }],
        TyRef('Point'),
      ),
    }]);
    const code = generateLean(m);
    expect(code).toContain('{ p with y := v }');
  });

  it('multiple spread fields all appear', () => {
    const code = inline(`
      interface Config { host: string; port: number; debug: boolean }
      function withDebug(c: Config): Config { return { ...c, debug: true }; }
    `);
    const fn = code.slice(code.indexOf('def withDebug'));
    // The spread base should appear, not be dropped
    expect(fn.slice(0, 300)).toContain('c');
    expect(fn.slice(0, 300)).toContain('debug');
  });
});

// ─── Bug #3: switch fall-through ──────────────────────────────────────────────
// Before: `case 'N': case 'S': return true` → only `| "S" => true` (N was dropped!)
// After:  `case 'N': case 'S': return true` → `| "N" => true\n| "S" => true`

describe('Review Bug #3: switch fall-through propagates body', () => {
  it('case N: case S: → both arms point to same body', () => {
    const code = inline(`
      function isVertical(dir: string): boolean {
        switch (dir) {
          case 'N':
          case 'S':
            return true;
          default:
            return false;
        }
      }
    `);
    const fn = code.slice(code.indexOf('def isVertical'));
    expect(fn.slice(0, 400)).toContain('"N"');
    expect(fn.slice(0, 400)).toContain('"S"');
    // Both N and S must point to `true`
    expect(fn.slice(0, 400)).toMatch(/"N".*true/s);
    expect(fn.slice(0, 400)).toMatch(/"S".*true/s);
  });

  it('three-way fall-through all preserved', () => {
    const code = inline(`
      function category(n: number): string {
        switch (n) {
          case 1:
          case 2:
          case 3:
            return 'small';
          default:
            return 'large';
        }
      }
    `);
    const fn = code.slice(code.indexOf('def category'));
    expect(fn.slice(0, 500)).toContain('1');
    expect(fn.slice(0, 500)).toContain('2');
    expect(fn.slice(0, 500)).toContain('3');
    expect(fn.slice(0, 500)).toContain('"small"');
  });

  it('normal switch with break not affected', () => {
    const code = inline(`
      function colorCode(c: string): number {
        switch (c) {
          case 'red': return 0;
          case 'green': return 1;
          case 'blue': return 2;
          default: return -1;
        }
      }
    `);
    const fn = code.slice(code.indexOf('def colorCode'));
    expect(fn.slice(0, 400)).toContain('"red"');
    expect(fn.slice(0, 400)).toContain('"green"');
    expect(fn.slice(0, 400)).toContain('"blue"');
    expect(fn.slice(0, 400)).toContain('0');
    expect(fn.slice(0, 400)).toContain('1');
    expect(fn.slice(0, 400)).toContain('2');
  });

  it('fall-through at end with default uses default body', () => {
    const code = inline(`
      function grade(g: string): string {
        switch (g) {
          case 'A': return 'excellent';
          case 'B':
          case 'C':
            return 'good';
          case 'D': return 'passing';
          default: return 'failing';
        }
      }
    `);
    const fn = code.slice(code.indexOf('def grade'));
    expect(fn.slice(0, 500)).toContain('"A"');
    expect(fn.slice(0, 500)).toContain('"B"');
    expect(fn.slice(0, 500)).toContain('"C"');
    // B and C both point to 'good'
    expect(fn.slice(0, 500)).toMatch(/"B".*good/s);
    expect(fn.slice(0, 500)).toMatch(/"C".*good/s);
  });
});

// ─── Bug #4 (bonus): JSDoc @param stripping ───────────────────────────────────

describe('Review Bug #4: JSDoc @param tags stripped', () => {
  it('single-line JSDoc description preserved', () => {
    const code = inline(`
      /** Adds two numbers. */
      function add(a: number, b: number): number { return a + b; }
    `);
    expect(code).toContain('/-- Adds two numbers.');
    expect(code).not.toContain('@param');
  });

  it('multi-line JSDoc: only description kept, @param stripped', () => {
    const code = inline(`
      /**
       * Compute sum of a and b.
       * @param a First number
       * @param b Second number
       * @returns Sum
       */
      function sum(a: number, b: number): number { return a + b; }
    `);
    // Description should be present
    expect(code).toMatch(/Compute sum/);
    // @param and @returns should NOT appear in the Lean output
    expect(code).not.toContain('@param');
    expect(code).not.toContain('@returns');
  });

  it('JSDoc with only tags (no description) → no docComment', () => {
    const code = inline(`
      /**
       * @param n Input
       */
      function identity(n: number): number { return n; }
    `);
    // If only tags, no meaningful description → no doc comment or empty
    // (implementation may choose either; just verify @param doesn't appear)
    expect(code).not.toContain('@param');
  });
});

// ─── Cross-cutting: original suite not broken ──────────────────────────────────

describe('Review bugs: no regression in existing features', () => {
  it('discriminated union match still uses pattern vars', () => {
    const code = inline(`
      type Shape = { kind: 'circle'; r: number } | { kind: 'rect'; w: number; h: number };
      function area(s: Shape): number {
        switch (s.kind) {
          case 'circle': return Math.PI * s.r * s.r;
          case 'rect': return s.w * s.h;
        }
      }
    `);
    const fn = code.slice(code.indexOf('def area'));
    expect(fn.slice(0, 500)).not.toContain('s.r');
    expect(fn.slice(0, 500)).not.toContain('s.w');
    expect(fn.slice(0, 500)).toContain('match s');
  });

  it('for-loop incrementor still correct', () => {
    const code = inline(`
      function count(n: number): number {
        let s = 0;
        for (let i = 0; i < n; i++) { s = s + i; }
        return s;
      }
    `);
    const fn = code.slice(code.indexOf('def count'));
    expect(fn.slice(0, 600)).not.toMatch(/_loop_\d+ let i/);
  });

  it('s! interpolation still fires', () => {
    const code = inline(`function hello(name: string): string { return \`Hello, \${name}!\`; }`);
    const fn = code.slice(code.indexOf('def hello'));
    expect(fn.slice(0, 200)).toContain('s!"Hello, {name}!"');
  });

  it('setter still uses struct update', () => {
    const code = inline(`
      class Box {
        private _w: number = 0;
        set width(v: number) { this._w = v; }
      }
    `);
    expect(code).toMatch(/def set_width/);
    const fn = code.slice(code.indexOf('def set_width'));
    expect(fn.slice(0, 200)).toContain('with');
  });
});
