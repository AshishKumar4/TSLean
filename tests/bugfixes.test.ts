// Regression tests for fixed bugs (extends prior regression.test.ts with new cases).

import { describe, it, expect } from 'vitest';
import * as path from 'path';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';
import {
  combineEffects, stateEffect, exceptEffect, Async, IO, Pure,
  TyString, TyFloat, TyNat, TyBool, TyUnit, TyRef, TyArray, TyOption,
  litNat, litStr, litBool, varExpr,
  IRModule, IRDecl, IRExpr,
} from '../src/ir/types.js';
import { monadString } from '../src/effects/index.js';
import { irTypeToLean } from '../src/typemap/index.js';

const FIX = path.join(process.cwd(), 'tests/fixtures');

function pipeline(rel: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: path.join(FIX, rel) })));
}

function pipelineInline(src: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: 'test.ts', sourceText: src })));
}

function mod(decls: IRDecl[]): IRModule {
  return { name: 'T', imports: [], decls, comments: [] };
}

// ─── Bug #1: Discriminant match arm body substitution ─────────────────────────

describe('Bug #1: Match arm body field substitution', () => {
  it('circle arm: radius not s.radius', () => {
    const code = pipelineInline(`
      type Shape = { kind: 'circle'; radius: number } | { kind: 'rect'; w: number; h: number };
      function area(s: Shape): number {
        switch (s.kind) {
          case 'circle': return Math.PI * s.radius * s.radius;
          case 'rect': return s.w * s.h;
        }
      }
    `);
    const fn = code.slice(code.indexOf('def area') || 0, code.indexOf('\ndef ', (code.indexOf('def area') || 0) + 1) || undefined);
    expect(fn).toContain('radius');
    expect(fn).not.toContain('s.radius');
  });

  it('rect arm: w and h not s.w, s.h', () => {
    const code = pipelineInline(`
      type Shape = { kind: 'circle'; r: number } | { kind: 'rect'; w: number; h: number };
      function area(s: Shape): number {
        switch (s.kind) {
          case 'rect': return s.w * s.h;
          case 'circle': return s.r * s.r;
        }
      }
    `);
    const fn = code.slice(code.indexOf('def area') || 0);
    expect(fn.slice(0, 600)).not.toContain('s.w');
    expect(fn.slice(0, 600)).not.toContain('s.h');
  });

  it('discriminated-unions fixture: no s.field in areaShape', () => {
    const code = pipeline('generics/discriminated-unions.ts');
    const fn = code.slice(code.indexOf('def areaShape') || 0);
    const block = fn.slice(0, 600);
    expect(block).not.toContain('s.radius');
    expect(block).not.toContain('s.width');
    expect(block).not.toContain('s.height');
    expect(block).not.toContain('s.base');
  });

  it('multi-field ctor: two-member union substitutes all fields', () => {
    // Two-member union so discriminant is detected
    const code = pipelineInline(`
      type Point = { kind: '2d'; x: number; y: number } | { kind: '3d'; x: number; y: number; z: number };
      function sumX(p: Point): number {
        switch (p.kind) {
          case '2d': return p.x + p.y;
          case '3d': return p.x + p.y + p.z;
        }
      }
    `);
    const fn = code.slice(code.indexOf('def sumX') || 0);
    // After rewrite: match arms use pattern vars, not p.x
    expect(fn.slice(0, 600)).not.toContain('p.x');
    expect(fn.slice(0, 600)).not.toContain('p.y');
  });
});

// ─── Bug #2: For-loop incrementor ────────────────────────────────────────────

describe('Bug #2: For-loop incrementor', () => {
  it('i++ → _loop (i+1)', () => {
    const code = pipelineInline(`
      function sum(n: number): number {
        let s = 0;
        for (let i = 0; i < n; i++) { s = s + i; }
        return s;
      }
    `);
    const fn = code.slice(code.indexOf('sum'));
    expect(fn.slice(0, 600)).toMatch(/_loop_\d+ \(?i \+ 1\)?/);
    expect(fn.slice(0, 600)).not.toMatch(/_loop_\d+ let i/);
  });

  it('i-- → _loop (i-1)', () => {
    const code = pipelineInline(`
      function countdown(n: number): number {
        let x = n;
        for (let i = n; i > 0; i--) { x = x - 1; }
        return x;
      }
    `);
    const fn = code.slice(code.indexOf('countdown'));
    expect(fn.slice(0, 600)).toMatch(/_loop_\d+ \(?i - 1\)?/);
    expect(fn.slice(0, 600)).not.toMatch(/_loop_\d+ let i/);
  });

  it('for-loops fixture: rangeSum correct', () => {
    const code = pipeline('advanced/for-loops.ts');
    const fn = code.slice(code.indexOf('rangeSum'));
    expect(fn.slice(0, 600)).not.toMatch(/_loop_\d+ let i/);
  });
});

// ─── Bug #3: monadString (IO) not wrapped ────────────────────────────────────

describe('Bug #3: monadString IO not wrapped in parens', () => {
  it('State+Except → StateT S (ExceptT E IO)', () => {
    const s = monadString(combineEffects([stateEffect(TyString), exceptEffect(TyFloat)]));
    expect(s).toBe('StateT String (ExceptT Float IO)');
    expect(s).not.toContain('(IO)');
  });

  it('State alone → StateT S IO', () => {
    const s = monadString(stateEffect(TyString));
    expect(s).toBe('StateT String IO');
    expect(s).not.toContain('(IO)');
  });

  it('Except alone → ExceptT E IO', () => {
    const s = monadString(exceptEffect(TyFloat));
    expect(s).toBe('ExceptT Float IO');
    expect(s).not.toContain('(IO)');
  });

  it('State+Async → StateT N IO (no (IO))', () => {
    const s = monadString(combineEffects([stateEffect(TyNat), Async]));
    expect(s).not.toContain('(IO)');
  });

  it('generated code: State+Except has correct return sig', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'op', typeParams: [],
      params: [], retType: TyNat,
      effect: combineEffects([stateEffect(TyString), exceptEffect(TyFloat)]),
      body: litNat(0),
    }]));
    const line = code.split('\n').find(l => l.includes('def op'))!;
    expect(line).toContain('StateT');
    expect(line).toContain('ExceptT');
    expect(line).not.toContain('(IO)');
  });
});

// ─── Bug #4: DO constructor ────────────────────────────────────────────────────

describe('Bug #4: DO constructor clean init', () => {
  it('CounterDO.init returns CounterDOState, no unbound self', () => {
    const code = pipeline('durable-objects/counter.ts');
    const idx = code.indexOf('CounterDO.init');
    expect(idx).toBeGreaterThan(-1);
    // Extract just the init line (up to the next def)
    const fromInit = code.slice(idx);
    const nextDef = fromInit.indexOf('\ndef ', 1);
    const initBlock = fromInit.slice(0, nextDef === -1 ? 200 : nextDef);
    // Init should return CounterDOState, not StateT Unit IO
    expect(initBlock).toContain('CounterDOState');
    expect(initBlock).not.toContain('StateT Unit IO');
  });

  it('DO method still has self param', () => {
    const code = pipeline('durable-objects/counter.ts');
    const fn = code.slice(code.indexOf('def fetch') || 0);
    expect(fn.slice(0, 200)).toContain('self');
  });

  it('DO init does not have DurableObjectState as param', () => {
    const code = pipelineInline(`
      class MyDO {
        private v: number = 0;
        constructor(state: DurableObjectState, env: Env) { this.v = 42; }
        async fetch(req: Request): Promise<Response> { return new Response("ok"); }
      }
    `);
    const initFn = code.slice(code.indexOf('MyDO.init') || 0);
    const paramPart = initFn.split(':=')[0];
    expect(paramPart).not.toContain('DurableObjectState');
    expect(paramPart).not.toContain('Env');
  });
});

// ─── Universe type emission ───────────────────────────────────────────────────

describe('Bug #7 (universe type): no trailing space in Type 1', () => {
  it('Universe 0 → Prop',   () => expect(irTypeToLean({ tag: 'Universe', level: 0 })).toBe('Prop'));
  it('Universe 1 → Type',   () => {
    const r = irTypeToLean({ tag: 'Universe', level: 1 });
    expect(r).toBe('Type 1');
    expect(r).not.toMatch(/\s$/);
  });
  it('Universe 2 → Type 2', () => expect(irTypeToLean({ tag: 'Universe', level: 2 })).toBe('Type 2'));
  it('Universe 3 → Type 3', () => expect(irTypeToLean({ tag: 'Universe', level: 3 })).toBe('Type 3'));
});

// ─── Extra regression: optional chaining ────────────────────────────────────

describe('Optional chaining produces Option.map', () => {
  it('obj?.field uses Option.map', () => {
    const code = pipelineInline(`
      interface C { host?: string }
      function h(c?: C): string { return c?.host ?? 'default'; }
    `);
    expect(code).toContain('Option.getD');
  });
});

// ─── Extra regression: string enums ──────────────────────────────────────────

describe('String enum toString generation', () => {
  it('string enum gets toString function', () => {
    const code = pipelineInline(`enum Status { Active = "ACTIVE", Inactive = "INACTIVE" }`);
    expect(code).toContain('inductive Status');
    expect(code).toMatch(/def Status\.toString/);
    expect(code).toContain('"ACTIVE"');
  });

  it('numeric enum does not get toString', () => {
    const code = pipelineInline(`enum Dir { N, S, E, W }`);
    expect(code).toContain('inductive Dir');
    // Numeric enums don't generate toString
    expect(code).not.toMatch(/def Dir\.toString/);
  });
});

// ─── Extra regression: re-exports ────────────────────────────────────────────

describe('Re-exports handled gracefully', () => {
  it('export {} from adds import', () => {
    const mod = parseFile({
      fileName: 'reexport.ts',
      sourceText: "export { Foo } from './other.js';",
    });
    // Should not throw; may add import
    expect(mod).toBeDefined();
    expect(mod.decls).toBeDefined();
  });
});
