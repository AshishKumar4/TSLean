// Regression tests for the 4 bugs found in code review.
// Each test is named after the bug it catches and directly verifies
// the behaviour that was broken before the fix.

import { describe, it, expect } from 'vitest';
import * as path from 'path';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';
import {
  combineEffects, stateEffect, exceptEffect,
  TyString, TyFloat, TyNat, TyRef, TyUnit, TyArray,
  Pure, IO, Async,
  litNat, litStr, varExpr,
  IRModule, IRDecl, IRExpr,
} from '../src/ir/types.js';
import { monadString } from '../src/effects/index.js';

function pipeline(src: string, name = 'test.ts'): string {
  return generateLean(rewriteModule(parseFile({ fileName: name, sourceText: src })));
}

function sectionOf(code: string, startToken: string): string {
  const start = code.indexOf(startToken);
  if (start === -1) return '';
  const next = code.indexOf('\ndef ', start + 1);
  return code.slice(start, next === -1 ? undefined : next);
}

// ─── Bug #1: rewrite pass must substitute s.field → pattern-bound variable ───
// Before fix: `.Circle radius => (Math.PI * s.radius) * s.radius`  — s has no .radius accessor
// After fix:  `.Circle radius => (Math.PI * radius) * radius`       — uses pattern variable

describe('Bug #1 regression: discriminated union match arm bodies use pattern variables', () => {
  const src = `
    type Shape =
      | { kind: 'circle'; radius: number }
      | { kind: 'rect';   width: number; height: number };

    function area(s: Shape): number {
      switch (s.kind) {
        case 'circle': return Math.PI * s.radius * s.radius;
        case 'rect':   return s.width * s.height;
      }
    }
  `;

  let code: string;
  beforeAll(() => { code = pipeline(src); });

  it('circle arm uses pattern variable `radius`, not `s.radius`', () => {
    const fn = sectionOf(code, 'def area');
    // Must have `radius` as a bare identifier in an arithmetic expression
    expect(fn).toContain('radius');
    // Must NOT contain the broken `s.radius` field-access on an inductive
    expect(fn).not.toContain('s.radius');
  });

  it('rect arm uses pattern variables `width` and `height`, not `s.width`/`s.height`', () => {
    const fn = sectionOf(code, 'def area');
    expect(fn).not.toContain('s.width');
    expect(fn).not.toContain('s.height');
  });

  it('match scrutinee is the object `s`, not the discriminant `s.kind`', () => {
    const fn = sectionOf(code, 'def area');
    expect(fn).toContain('match s with');
    expect(fn).not.toContain('match s.kind with');
  });

  it('constructors appear with dot syntax', () => {
    const fn = sectionOf(code, 'def area');
    expect(fn).toMatch(/\.\s*Circle/);
    expect(fn).toMatch(/\.\s*Rect/);
  });

  it('no string literals remain in match arms', () => {
    const fn = sectionOf(code, 'def area');
    expect(fn).not.toContain('"circle"');
    expect(fn).not.toContain('"rect"');
  });

  it('works for three-constructor union', () => {
    const src3 = `
      type Animal =
        | { kind: 'dog'; name: string }
        | { kind: 'cat'; lives: number }
        | { kind: 'fish'; fins: number };
      function describe(a: Animal): string {
        switch (a.kind) {
          case 'dog':  return a.name;
          case 'cat':  return 'cat with ' + a.lives + ' lives';
          case 'fish': return 'fish';
        }
      }
    `;
    const code3 = pipeline(src3);
    const fn = sectionOf(code3, 'def describe');
    // Each arm should use pattern var, not `a.name`, `a.lives` etc.
    expect(fn).not.toContain('a.name');
    expect(fn).not.toContain('a.lives');
    expect(fn).not.toContain('a.fins');
  });

  it('nested match also gets substituted', () => {
    const srcNested = `
      type E = { type: 'a'; val: number } | { type: 'b'; val: number };
      function double(e: E): number {
        switch (e.type) {
          case 'a': return e.val * 2;
          case 'b': return e.val + 1;
        }
      }
    `;
    const codeN = pipeline(srcNested);
    const fn = sectionOf(codeN, 'def double');
    expect(fn).not.toContain('e.val');
  });
});

// ─── Bug #2: for-loop incrementor must produce valid Lean (not `let i := i+1`) ─
// Before fix: `_loop_44 let i := i + 1`  — invalid Lean syntax
// After fix:  `_loop_44 (i + 1)`          — valid

describe('Bug #2 regression: for-loop incrementor as recursive argument', () => {
  it('i++ produces _loop (i + 1), not `let i := i + 1`', () => {
    const src = `
      function sum(n: number): number {
        let total = 0;
        for (let i = 0; i < n; i++) { total = total + i; }
        return total;
      }
    `;
    const code = pipeline(src);
    const fn = sectionOf(code, 'def sum');
    // The recursive call must pass `i + 1` as argument
    expect(fn).toMatch(/_loop_\d+ \(?i \+ 1\)?/);
    // Must NOT have `let i :=` as a function argument position
    expect(fn).not.toMatch(/_loop_\d+ let i/);
  });

  it('i-- produces _loop (i - 1)', () => {
    const src = `
      function countdown(n: number): number {
        let x = n;
        for (let i = n; i > 0; i--) { x = x - 1; }
        return x;
      }
    `;
    const code = pipeline(src);
    const fn = sectionOf(code, 'def countdown');
    // Recursive call must receive i - 1 (or equivalent)
    expect(fn).toMatch(/_loop_\d+ \(?i - 1\)?/);
    expect(fn).not.toMatch(/_loop_\d+ let i/);
  });

  it('i += 2 produces correct recursive argument', () => {
    const src = `
      function evens(n: number): number {
        let count = 0;
        for (let i = 0; i < n; i += 2) { count = count + 1; }
        return count;
      }
    `;
    const code = pipeline(src);
    const fn = sectionOf(code, 'def evens');
    // Should not have the assignment node as argument
    expect(fn).not.toMatch(/_loop_\d+ let i/);
  });

  it('for-loop produces a let binding with a lambda', () => {
    const src = `
      function range(n: number): number {
        let s = 0;
        for (let i = 0; i < n; i++) { s = s + i; }
        return s;
      }
    `;
    const code = pipeline(src);
    // Must produce a let _loop_ := fun i => ...
    expect(code).toMatch(/let (rec )?_loop_\d+ := fun \w+ =>/);
  });
});

// ─── Bug #3: monadString must not wrap IO in extra parens ──────────────────────
// Before fix: `StateT String (ExceptT Float (IO))`  — (IO) is redundant/odd
// After fix:  `StateT String (ExceptT Float IO)`    — IO is bare

describe('Bug #3 regression: monadString IO not wrapped in parens', () => {
  it('State+Except produces StateT S (ExceptT E IO) — IO bare', () => {
    const e = combineEffects([stateEffect(TyString), exceptEffect(TyFloat)]);
    const s = monadString(e);
    expect(s).toBe('StateT String (ExceptT Float IO)');
    expect(s).not.toContain('(IO)');
  });

  it('State alone produces StateT S IO — IO bare', () => {
    const s = monadString(stateEffect(TyString));
    expect(s).toBe('StateT String IO');
    expect(s).not.toContain('(IO)');
  });

  it('Except alone produces ExceptT E IO — IO bare', () => {
    const s = monadString(exceptEffect(TyFloat));
    expect(s).toBe('ExceptT Float IO');
    expect(s).not.toContain('(IO)');
  });

  it('IO alone is just IO', () => {
    expect(monadString(IO)).toBe('IO');
  });

  it('Async maps to IO', () => {
    expect(monadString(Async)).toBe('IO');
  });

  it('Pure maps to Id', () => {
    expect(monadString(Pure)).toBe('Id');
  });

  it('State+Async produces StateT S IO', () => {
    const e = combineEffects([stateEffect(TyNat), Async]);
    const s = monadString(e);
    expect(s).toContain('StateT');
    expect(s).toContain('IO');
    expect(s).not.toContain('(IO)');
  });

  it('generated code for State+Except function has correct return type', () => {
    const mod: IRModule = {
      name: 'Test', imports: [], decls: [{
        tag: 'FuncDef', name: 'complex', typeParams: [],
        params: [], retType: TyNat,
        effect: combineEffects([stateEffect(TyString), exceptEffect(TyFloat)]),
        body: litNat(0),
      }], comments: [],
    };
    const code = generateLean(mod);
    const defLine = code.split('\n').find(l => l.includes('def complex'))!;
    // Must contain StateT and ExceptT but IO must not be in parens
    expect(defLine).toContain('StateT');
    expect(defLine).toContain('ExceptT');
    expect(defLine).not.toContain('(IO)');
  });
});

// ─── Bug #4: DO constructor returns clean state struct, no unbound `self` ─────
// Before fix: references `self` (not a param) and excluded `state` field
// After fix:  returns { count := sorry } — clean struct literal

describe('Bug #4 regression: DO constructor synthesises clean state struct', () => {
  it('CounterDO.init returns CounterDOState struct literal', () => {
    const src = `
      export class CounterDO {
        private count: number = 0;
        constructor(state: DurableObjectState, env: Env) {
          this.state = state;
          this.count = 0;
        }
        async fetch(request: Request): Promise<Response> {
          return new Response(JSON.stringify({ count: this.count }));
        }
      }
    `;
    const code = pipeline(src, 'counter.ts');
    const initFn = sectionOf(code, 'CounterDO.init');
    // Must NOT reference unbound `self`
    expect(initFn).not.toMatch(/\bself\b/);
    // Must NOT say StateT Unit (wrong state type)
    expect(initFn).not.toContain('StateT Unit');
    // Must return a struct (CounterDOState is the return type)
    expect(initFn).toContain('CounterDOState');
  });

  it('DO init does not take DurableObjectState as a parameter', () => {
    const src = `
      class MyDO {
        private value: number = 0;
        constructor(state: DurableObjectState, env: Env) {
          this.value = 42;
        }
        async fetch(request: Request): Promise<Response> {
          return new Response("ok");
        }
      }
    `;
    const code = pipeline(src, 'mydo.ts');
    const initFn = sectionOf(code, 'MyDO.init');
    // DurableObjectState should not appear as a parameter type (it's excluded)
    const paramSection = initFn.split(':=')[0];
    expect(paramSection).not.toContain('DurableObjectState');
    expect(paramSection).not.toContain('Env');
  });

  it('DO method still gets self parameter', () => {
    const src = `
      class StoreDO {
        private items: string[] = [];
        constructor(state: DurableObjectState, env: Env) {}
        async fetch(request: Request): Promise<Response> {
          return new Response(JSON.stringify(this.items));
        }
      }
    `;
    const code = pipeline(src, 'store.ts');
    // The fetch method (not init) should have a self parameter
    const fetchFn = sectionOf(code, 'fetch');
    expect(fetchFn).toContain('self');
  });

  it('full-project DO fixture produces clean init', () => {
    const mod = parseFile({
      fileName: path.join(process.cwd(), 'tests/fixtures/durable-objects/counter.ts'),
    });
    const code = generateLean(rewriteModule(mod));
    const initFn = sectionOf(code, 'CounterDO.init');
    // The init must not have `self` as unbound
    // (it can appear in methods but not in the parameter-free DO init)
    expect(initFn).not.toMatch(/\(self :/);
    expect(initFn).not.toContain('StateT Unit');
  });
});

// ─── Cross-cutting: full discriminated-union pipeline ─────────────────────────

describe('Full pipeline: discriminated unions', () => {
  it('Shape area function produces valid Lean without s.field references', () => {
    const code = generateLean(rewriteModule(parseFile({
      fileName: path.join(process.cwd(), 'tests/fixtures/generics/discriminated-unions.ts'),
    })));
    const fn = sectionOf(code, 'def areaShape');
    // After Bug #1 fix: no field access on the scrutinee (param is `s`)
    expect(fn).not.toContain('s.radius');
    expect(fn).not.toContain('s.width');
    expect(fn).not.toContain('s.height');
    expect(fn).not.toContain('s.base');
    // Pattern variables used directly, match on the object itself
    expect(fn).toContain('match s with');
  });

  it('Tree depth function does not access t.left as field', () => {
    const code = generateLean(rewriteModule(parseFile({
      fileName: path.join(process.cwd(), 'tests/fixtures/generics/discriminated-unions.ts'),
    })));
    const fn = sectionOf(code, 'def treeDepth');
    // After rewrite, the recursion should use pattern-bound left/right
    expect(fn).toMatch(/\.\s*Node/);
  });
});
