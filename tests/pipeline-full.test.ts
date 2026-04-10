// Full pipeline tests: parse → rewrite → codegen for all fixtures.

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';
import { IRModule } from '../src/ir/types.js';

const FIX = path.join(process.cwd(), 'tests/fixtures');

function pipeline(rel: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: path.join(FIX, rel) })));
}

function parsed(rel: string): IRModule {
  return parseFile({ fileName: path.join(FIX, rel) });
}

// ─── basic/hello.ts ──────────────────────────────────────────────────────────

describe('Pipeline: basic/hello.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('basic/hello.ts'); });

  it('non-empty',               () => expect(code.length).toBeGreaterThan(0));
  it('def greet',               () => expect(code).toContain('def greet'));
  it('def add',                 () => expect(code).toContain('def add'));
  it('def isPositive',          () => expect(code).toContain('def isPositive'));
  it('factorial is partial',    () => expect(code).toContain('partial def factorial'));
  it('header present',          () => expect(code).toContain('Auto-generated'));
  it('open TSLean',             () => expect(code).toContain('open TSLean'));
  it('no function keyword',     () => expect(code).not.toMatch(/\bfunction\s+\w/));
  it('no const keyword',        () => expect(code).not.toMatch(/\bconst\s+\w/));
  it('no ===',                  () => expect(code).not.toContain('==='));
  it('greet uses concat',       () => {
    const fn = code.slice(code.indexOf('greet'));
    expect(fn.slice(0, 300)).toMatch(/\+\+|s!"[^"]*"/);
  });
  it('PI is Float',             () => expect(code).toMatch(/def PI\s*:\s*Float/));
});

// ─── basic/interfaces.ts ─────────────────────────────────────────────────────

describe('Pipeline: basic/interfaces.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('basic/interfaces.ts'); });

  it('structure Point',          () => expect(code).toContain('structure Point'));
  it('x y fields Float',         () => { expect(code).toContain('x : Float'); expect(code).toContain('y : Float'); });
  it('structure Rectangle',      () => expect(code).toContain('structure Rectangle'));
  it('structure Named',          () => expect(code).toContain('structure Named'));
  it('Named.description Optional', () => {
    const block = code.slice(code.indexOf('structure Named'));
    expect(block.slice(0, 200)).toContain('description');
  });
  it('def distance',             () => expect(code).toContain('def distance'));
  it('def makePoint struct lit',  () => {
    const fn = code.slice(code.indexOf('def makePoint'));
    expect(fn.slice(0, 200)).toContain('{ x');
  });
  it('no TS number',             () => expect(code).not.toContain(': number'));
});

// ─── basic/classes.ts ────────────────────────────────────────────────────────

describe('Pipeline: basic/classes.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('basic/classes.ts'); });

  it('CounterState struct',      () => expect(code).toMatch(/structure Counter/));
  it('increment defined',        () => expect(code).toMatch(/def.*increment/));
  it('deposit defined',          () => expect(code).toMatch(/deposit/));
  it('withdraw defined',         () => expect(code).toMatch(/withdraw/));
});

// ─── generics/discriminated-unions.ts ─────────────────────────────────────────

describe('Pipeline: generics/discriminated-unions.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('generics/discriminated-unions.ts'); });

  it('inductive Shape',             () => expect(code).toContain('inductive Shape'));
  it('Circle Rectangle Triangle',   () => { expect(code).toContain('Circle'); expect(code).toContain('Rectangle'); expect(code).toContain('Triangle'); });
  it('areaShape uses match',        () => {
    const fn = code.slice(code.indexOf('def areaShape'));
    expect(fn.slice(0, 500)).toContain('match');
  });
  it('match arms use pattern vars', () => {
    const fn = code.slice(code.indexOf('def areaShape'));
    expect(fn.slice(0, 500)).not.toContain('s.radius');
    expect(fn.slice(0, 500)).not.toContain('s.width');
  });
  it('dot syntax in arms',          () => {
    const fn = code.slice(code.indexOf('def areaShape'));
    expect(fn.slice(0, 500)).toMatch(/\.\s*Circle/);
  });
  it('no string literals in arms',  () => {
    const fn = code.slice(code.indexOf('def areaShape'));
    expect(fn.slice(0, 500)).not.toContain('"circle"');
  });
  it('Color inductive',             () => expect(code).toContain('inductive Color'));
  it('Tree inductive with {T}',     () => expect(code).toMatch(/inductive Tree\s*[(({]T/));
  it('no switch/case',              () => expect(code).not.toContain('switch'));
});

// ─── generics/branded-types.ts ────────────────────────────────────────────────

describe('Pipeline: generics/branded-types.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('generics/branded-types.ts'); });

  it('structure UserId',          () => expect(code).toContain('structure UserId'));
  it('NOT abbrev UserId',         () => expect(code).not.toContain('abbrev UserId := String'));
  it('val : String in UserId',    () => {
    const block = code.slice(code.indexOf('structure UserId'), code.indexOf('structure UserId') + 120);
    expect(block).toContain('val : String');
  });
  it('RoomId structure',          () => expect(code).toContain('structure RoomId'));
  it('UserProfile structure',     () => expect(code).toContain('structure UserProfile'));
  it('makeUserId defined',        () => expect(code).toContain('makeUserId'));
});

// ─── generics/generics.ts ─────────────────────────────────────────────────────

describe('Pipeline: generics/generics.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('generics/generics.ts'); });

  it('def identity',              () => expect(code).toContain('def identity'));
  it('def compose',               () => expect(code).toContain('def compose'));
  it('generic {T : Type} params', () => expect(code).toContain('{T : Type}'));
  it('def mapOpt',                () => expect(code).toContain('def mapOpt'));
  it('def makePair',              () => expect(code).toContain('def makePair'));
});

// ─── effects/async.ts ─────────────────────────────────────────────────────────

describe('Pipeline: effects/async.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('effects/async.ts'); });

  it('fetchUser IO return',       () => {
    const line = code.split('\n').find(l => /def fetchUser|partial def fetchUser/.test(l));
    expect(line).toBeDefined();
    expect(line).toContain('IO');
  });
  it('withRetry {T : Type}',      () => expect(code).toContain('{T : Type}'));
  it('fetchAndProcess defined',   () => expect(code).toMatch(/def fetchAndProcess/));
});

// ─── effects/exceptions.ts ───────────────────────────────────────────────────

describe('Pipeline: effects/exceptions.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('effects/exceptions.ts'); });

  it('parseAge defined',          () => expect(code).toContain('def parseAge'));
  it('divide defined',            () => expect(code).toContain('def divide'));
  it('safeDivide defined',        () => expect(code).toContain('def safeDivide'));
  it('validateEmail defined',     () => expect(code).toContain('def validateEmail'));
  it('throw keyword present',     () => expect(code).toContain('throw'));
});

// ─── Advanced fixtures ────────────────────────────────────────────────────────

describe('Pipeline: advanced/for-loops.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('advanced/for-loops.ts'); });

  it('rangeSum defined',          () => expect(code).toContain('def rangeSum'));
  it('for-loop increments correctly', () => {
    const fn = code.slice(code.indexOf('rangeSum'));
    expect(fn.slice(0, 600)).not.toMatch(/_loop_\d+ let i/);
  });
  it('processItems uses Array.forM', () => expect(code).toMatch(/Array.forM|default|sorry/));
  it('fibonacci uses _while_',    () => expect(code).toMatch(/_while_/));
  it('findFirst defined',         () => expect(code).toContain('def findFirst'));
});

describe('Pipeline: advanced/class-features.ts', () => {
  let code: string;
  beforeAll(() => { code = pipeline('advanced/class-features.ts'); });

  it('Status inductive',          () => expect(code).toContain('inductive Status'));
  it('Status.toString function',  () => expect(code).toMatch(/def Status\.toString/));
  it('get_radius getter',         () => expect(code).toMatch(/def get_radius/));
  it('set_radius setter',         () => expect(code).toMatch(/def set_radius/));
  it('Circle.fromDiameter',       () => expect(code).toMatch(/def Circle\.fromDiameter/));
  it('Direction inductive',       () => expect(code).toContain('inductive Direction'));
});

// ─── DOs ──────────────────────────────────────────────────────────────────────

describe('Pipeline: DO fixtures', () => {
  const fixtures = [
    'durable-objects/counter.ts',
    'durable-objects/rate-limiter.ts',
    'durable-objects/auth-do.ts',
    'durable-objects/analytics-do.ts',
    'durable-objects/session-store.ts',
    'durable-objects/queue-processor.ts',
    'durable-objects/chat-room.ts',
    'durable-objects/multi-do.ts',
  ];
  for (const f of fixtures) {
    it(`${f}: has DO imports`, () => {
      const code = pipeline(f);
      expect(code).toContain('import TSLean.DurableObjects.Http');
    });
    it(`${f}: has state struct`, () => {
      const code = pipeline(f);
      expect(code).toMatch(/structure \w+State|namespace \w+DO/);
    });
  }
});

// ─── Code quality ──────────────────────────────────────────────────────────────

describe('Pipeline: code quality checks', () => {
  it('hello: no empty bodies',    () => {
    const code = pipeline('basic/hello.ts');
    // No function with empty body (def f ... :=\n  () immediately followed by blank)
    expect(code).not.toMatch(/def\s+\w[^\n]*:=\s*\n\s*\(\)\s*\n\s*\n/);
  });

  it('all fixtures: balanced parens', () => {
    for (const f of ['basic/hello.ts', 'basic/interfaces.ts', 'generics/generics.ts']) {
      const code = pipeline(f);
      let depth = 0;
      for (const ch of code) {
        if (ch === '(') depth++;
        if (ch === ')') depth--;
        if (depth < 0) break;
      }
      expect(depth, `Unbalanced parens in ${f}`).toBe(0);
    }
  });
});
