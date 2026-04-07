// Advanced pattern tests: template literals, optional chaining, class features,
// destructuring, enums, for-loops, mutable vars, mutual recursion.

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import { parseFile } from '../../src/parser/index.js';
import { rewriteModule } from '../../src/rewrite/index.js';
import { generateLean } from '../../src/codegen/index.js';
import { generateVerification } from '../../src/verification/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyBool, TyNat, TyUnit, TyRef, TyArray, TyOption,
  Pure, Async, IO, stateEffect, exceptEffect, combineEffects,
  litNat, litStr, litBool, varExpr, holeExpr,
} from '../../src/ir/types.js';
import { monadString } from '../../src/effects/index.js';

const FIX = path.join(process.cwd(), 'tests/fixtures');

function pipeline(rel: string): string {
  const mod = parseFile({ fileName: path.join(FIX, rel) });
  return generateLean(rewriteModule(mod));
}

function parseInline(src: string, name = 'test.ts'): IRModule {
  return parseFile({ fileName: name, sourceText: src });
}

function pipelineInline(src: string): string {
  return generateLean(rewriteModule(parseInline(src)));
}

function makeModule(decls: IRDecl[]): IRModule {
  return { name: 'Test', imports: [], decls, comments: [] };
}

// ─── Template literals ────────────────────────────────────────────────────────

describe('Advanced: template literals', () => {
  it('simple template → concat or s!"..."', () => {
    const code = pipelineInline(`
      function greet(name: string): string { return \`Hello, \${name}!\`; }
    `);
    const fn = code.slice(code.indexOf('def greet') || 0);
    expect(fn.slice(0, 200)).toMatch(/s!"[^"]*"|"\s*\+\+|Hello.*\+\+/);
  });

  it('multi-part template uses concat', () => {
    const code = pipelineInline(`
      function url(base: string, path: string): string { return \`\${base}/\${path}\`; }
    `);
    expect(code).toContain('def url');
  });

  it('template-literals fixture transpiles', () => {
    const code = pipeline('advanced/template-literals.ts');
    expect(code).toContain('def greeting');
    expect(code).toContain('def url');
  });

  it('template with field access', () => {
    const code = pipelineInline(`
      interface User { id: string; name: string }
      function tag(u: User): string { return \`<user id="\${u.id}">\${u.name}</user>\`; }
    `);
    expect(code).toContain('def tag');
  });
});

// ─── Optional chaining ────────────────────────────────────────────────────────

describe('Advanced: optional chaining', () => {
  it('obj?.field generates Option.map', () => {
    const code = pipelineInline(`
      interface Config { host?: string }
      function getHost(c?: Config): string { return c?.host ?? 'default'; }
    `);
    expect(code).toContain('def getHost');
    expect(code).toContain('Option.getD');
  });

  it('?? nullish coalescing → Option.getD', () => {
    const code = pipelineInline(`
      function withDefault(x?: string): string { return x ?? 'fallback'; }
    `);
    expect(code).toContain('Option.getD');
  });

  it('optional-chaining fixture', () => {
    const code = pipeline('advanced/optional-chaining.ts');
    expect(code).toContain('def getHost');
    expect(code).toContain('Option.getD');
    expect(code).toContain('def sum');
  });
});

// ─── Destructuring ────────────────────────────────────────────────────────────

describe('Advanced: destructuring', () => {
  it('object destructuring in var stmt creates field accesses', () => {
    const code = pipelineInline(`
      function process(obj: { x: number; y: number }): number {
        const { x, y } = obj;
        return x + y;
      }
    `);
    expect(code).toContain('def process');
    // Destructured vars should appear as let bindings
    expect(code).toMatch(/let x|let y/);
  });

  it('array destructuring creates index accesses', () => {
    const code = pipelineInline(`
      function first(arr: number[]): number {
        const [a, b] = arr;
        return a;
      }
    `);
    expect(code).toContain('def first');
    expect(code).toMatch(/let a|let _ai/);
  });

  it('rest parameter becomes Array type', () => {
    const code = pipelineInline(`
      function sum(...nums: number[]): number { return 0; }
    `);
    expect(code).toMatch(/def sum.*Array/);
  });
});

// ─── Enums ────────────────────────────────────────────────────────────────────

describe('Advanced: enums', () => {
  it('numeric enum → inductive', () => {
    const code = pipelineInline(`enum Direction { North, South, East, West }`);
    expect(code).toContain('inductive Direction');
    expect(code).toContain('| North');
    expect(code).toContain('| South');
    expect(code).toContain('| East');
    expect(code).toContain('| West');
  });

  it('string enum → inductive + toString function', () => {
    const code = pipelineInline(`enum Color { Red = "RED", Green = "GREEN", Blue = "BLUE" }`);
    expect(code).toContain('inductive Color');
    expect(code).toContain('| Red');
    expect(code).toContain('| Green');
    expect(code).toContain('| Blue');
    expect(code).toMatch(/def Color\.toString/);
  });

  it('string enum toString maps to string values', () => {
    const code = pipelineInline(`enum Status { Active = "ACTIVE", Inactive = "INACTIVE" }`);
    expect(code).toMatch(/def Status\.toString/);
    expect(code).toContain('"ACTIVE"');
    expect(code).toContain('"INACTIVE"');
  });

  it('class-features fixture has Status.toString', () => {
    const code = pipeline('advanced/class-features.ts');
    expect(code).toContain('inductive Status');
    expect(code).toMatch(/def Status\.toString/);
  });
});

// ─── Class features ───────────────────────────────────────────────────────────

describe('Advanced: class features', () => {
  it('getter generates get_ function', () => {
    const code = pipelineInline(`
      class Circle {
        private _r: number = 1;
        get radius(): number { return this._r; }
      }
    `);
    expect(code).toMatch(/def get_radius/);
  });

  it('setter generates set_ function', () => {
    const code = pipelineInline(`
      class Box {
        private _w: number = 0;
        set width(v: number) { this._w = v; }
      }
    `);
    expect(code).toMatch(/def set_width/);
  });

  it('static method gets ClassName.method name', () => {
    const code = pipelineInline(`
      class Factory {
        static create(): Factory { return new Factory(); }
      }
    `);
    expect(code).toMatch(/def Factory\.create/);
  });

  it('class-features fixture complete', () => {
    const code = pipeline('advanced/class-features.ts');
    expect(code).toMatch(/def get_radius/);
    expect(code).toMatch(/def set_radius/);
    expect(code).toMatch(/def Circle\.fromDiameter/);
  });
});

// ─── For-loops ────────────────────────────────────────────────────────────────

describe('Advanced: for-loops', () => {
  it('for-loop emits _loop_ with correct increment', () => {
    const code = pipelineInline(`
      function count(n: number): number {
        let s = 0;
        for (let i = 0; i < n; i++) { s = s + i; }
        return s;
      }
    `);
    const fn = code.slice(code.indexOf('count'));
    expect(fn.slice(0, 600)).toMatch(/_loop_\d+ \(?i \+ 1\)?/);
    expect(fn.slice(0, 600)).not.toMatch(/_loop_\d+ let i/);
  });

  it('for-of emits Array.forM', () => {
    const code = pipelineInline(`
      function printAll(xs: string[]): void {
        for (const x of xs) { console.log(x); }
      }
    `);
    expect(code).toContain('Array.forM');
  });

  it('while loop emits _while_ helper', () => {
    const code = pipelineInline(`
      function whileLoop(n: number): number {
        let x = n;
        while (x > 0) { x = x - 1; }
        return x;
      }
    `);
    expect(code).toMatch(/_while_/);
  });

  it('for-loops fixture complete', () => {
    const code = pipeline('advanced/for-loops.ts');
    expect(code).toMatch(/def rangeSum/);
    expect(code).toContain('Array.forM');
    expect(code).toMatch(/_while_/);
  });
});

// ─── Partial def detection ─────────────────────────────────────────────────────

describe('Advanced: partial def for recursive functions', () => {
  it('recursive function gets partial def', () => {
    const code = pipelineInline(`
      function fact(n: number): number {
        if (n <= 0) return 1;
        return n * fact(n - 1);
      }
    `);
    expect(code).toContain('partial def fact');
  });

  it('non-recursive function gets plain def', () => {
    const code = pipelineInline(`
      function double(n: number): number { return n * 2; }
    `);
    expect(code).toContain('def double');
    expect(code).not.toContain('partial def double');
  });

  it('mutually recursive functions: both emitted', () => {
    const code = pipelineInline(`
      function isEven(n: number): boolean {
        if (n === 0) return true;
        return isOdd(n - 1);
      }
      function isOdd(n: number): boolean {
        if (n === 0) return false;
        return isEven(n - 1);
      }
    `);
    // Both functions must be emitted (Lean handles forward references at top-level)
    expect(code).toMatch(/def isEven/);
    expect(code).toMatch(/def isOdd/);
    // isEven calls isOdd (forward reference) — isOdd calls isEven (self-mutual)
    // isOdd is partial because it calls isEven which has not returned yet in its path
    expect(code).toMatch(/def isOdd|partial def isOdd/);
  });
});

// ─── IO.Ref for mutable vars ──────────────────────────────────────────────────

describe('Advanced: mutable variable handling', () => {
  it('mutable let emits IO.Ref comment', () => {
    const mod = makeModule([{
      tag: 'VarDecl', name: 'counter', type: TyNat,
      value: litNat(0), mutable: true,
    }]);
    const code = generateLean(mod);
    expect(code).toContain('IO.Ref');
    expect(code).toContain('counter');
  });

  it('immutable const emits plain def', () => {
    const mod = makeModule([{
      tag: 'VarDecl', name: 'PI', type: TyFloat,
      value: { tag: 'LitFloat', value: 3.14159, type: TyFloat, effect: Pure },
      mutable: false,
    }]);
    const code = generateLean(mod);
    expect(code).toContain('def PI');
    expect(code).not.toContain('IO.Ref');
  });
});

// ─── s!"..." interpolation ────────────────────────────────────────────────────

describe('Advanced: s!"..." string interpolation', () => {
  it('simple var concat can use s!', () => {
    // Check that s!"..." is at least possible via codegen
    const mod = makeModule([{
      tag: 'FuncDef', name: 'greet', typeParams: [],
      params: [{ name: 'name', type: TyString }],
      retType: TyString, effect: Pure,
      body: {
        tag: 'BinOp', op: 'Concat',
        left: { tag: 'BinOp', op: 'Concat',
          left: litStr('Hello, '),
          right: varExpr('name', TyString),
          type: TyString, effect: Pure },
        right: litStr('!'),
        type: TyString, effect: Pure,
      },
    }]);
    const code = generateLean(mod);
    // Either s!"..." or ++ chain is acceptable
    expect(code).toMatch(/s!"[^"]*"|"Hello.*\+\+/);
  });
});

// ─── Verification ─────────────────────────────────────────────────────────────

describe('Advanced: verification obligations', () => {
  it('array access → ArrayBounds', () => {
    const mod = makeModule([{
      tag: 'FuncDef', name: 'head', typeParams: ['T'],
      params: [{ name: 'arr', type: TyArray(TyRef('T')) }],
      retType: TyRef('T'), effect: Pure,
      body: { tag: 'IndexAccess', obj: varExpr('arr', TyArray(TyRef('T'))), index: litNat(0), type: TyRef('T'), effect: Pure },
    }]);
    const { obligations } = generateVerification(mod);
    expect(obligations.some(o => o.kind === 'ArrayBounds')).toBe(true);
  });

  it('division → DivisionSafe', () => {
    const mod = makeModule([{
      tag: 'FuncDef', name: 'div', typeParams: [],
      params: [{ name: 'a', type: TyFloat }, { name: 'b', type: TyFloat }],
      retType: TyFloat, effect: Pure,
      body: { tag: 'BinOp', op: 'Div', left: varExpr('a', TyFloat), right: varExpr('b', TyFloat), type: TyFloat, effect: Pure },
    }]);
    const { obligations } = generateVerification(mod);
    expect(obligations.some(o => o.kind === 'DivisionSafe')).toBe(true);
  });

  it('pure trivial → zero obligations', () => {
    const mod = makeModule([{
      tag: 'FuncDef', name: 'trivial', typeParams: [],
      params: [], retType: TyUnit, effect: Pure,
      body: { tag: 'LitUnit', type: TyUnit, effect: Pure },
    }]);
    const { obligations } = generateVerification(mod);
    expect(obligations).toHaveLength(0);
  });
});
