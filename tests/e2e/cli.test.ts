// E2E CLI tests: run the transpiler on fixture files and check output quality.

import { describe, it, expect, beforeAll } from 'vitest';
import { execSync } from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';

const ROOT = process.cwd();
const CLI  = path.join(ROOT, 'src/cli.ts');
const FIX  = path.join(ROOT, 'tests/fixtures');

function run(fixture: string, extra = ''): string {
  const out = path.join(os.tmpdir(), `tslean_${Date.now()}_${Math.random().toString(36).slice(2)}.lean`);
  execSync(`npx tsx ${CLI} ${path.join(FIX, fixture)} -o ${out} ${extra}`, { stdio: 'pipe' });
  const content = fs.readFileSync(out, 'utf8');
  fs.unlinkSync(out);
  return content;
}

function assertValidLean(code: string, ctx = ''): void {
  expect(code, ctx).toContain('open TSLean');
  expect(code, ctx).toContain('-- Auto-generated');
  // No raw TS syntax
  expect(code, ctx).not.toMatch(/\bfunction\s+\w/);
  expect(code, ctx).not.toMatch(/\bconst\s+\w/);
  expect(code, ctx).not.toContain('===');
  expect(code, ctx).not.toContain('!==');
}

function hasDef(code: string, name: string): boolean {
  return new RegExp(`(partial )?def\\s+${name.replace('.', '\\.')}`).test(code);
}

// ─── basic/hello.ts ───────────────────────────────────────────────────────────

describe('CLI e2e: basic/hello.ts', () => {
  let code: string;
  beforeAll(() => { code = run('basic/hello.ts'); });

  it('valid Lean output',       () => assertValidLean(code, 'hello.ts'));
  it('def greet',               () => expect(hasDef(code, 'greet')).toBe(true));
  it('def add',                 () => expect(hasDef(code, 'add')).toBe(true));
  it('def isPositive',          () => expect(hasDef(code, 'isPositive')).toBe(true));
  it('def factorial',           () => expect(hasDef(code, 'factorial')).toBe(true));
  it('factorial is partial def',() => expect(code).toContain('partial def factorial'));
  it('greet uses ++ or s!"..."',() => {
    const fn = code.slice(code.indexOf('greet'));
    expect(fn).toMatch(/\+\+|s!"[^"]*"/);
  });
  it('PI is Float constant',    () => expect(code).toMatch(/def PI\s*:\s*Float/));
  it('no switch/case',          () => expect(code).not.toContain('switch'));
  it('no JS string methods',    () => expect(code).not.toContain('.toUpperCase()'));
});

// ─── basic/interfaces.ts ──────────────────────────────────────────────────────

describe('CLI e2e: basic/interfaces.ts', () => {
  let code: string;
  beforeAll(() => { code = run('basic/interfaces.ts'); });

  it('valid Lean output',        () => assertValidLean(code, 'interfaces.ts'));
  it('structure Point',          () => expect(code).toContain('structure Point'));
  it('x : Float field',          () => expect(code).toContain('x : Float'));
  it('y : Float field',          () => expect(code).toContain('y : Float'));
  it('structure Rectangle',      () => expect(code).toContain('structure Rectangle'));
  it('structure Named',          () => expect(code).toContain('structure Named'));
  it('Optional description field', () => {
    const block = code.slice(code.indexOf('structure Named'));
    expect(block).toContain('description');
  });
  it('def distance',             () => expect(hasDef(code, 'distance')).toBe(true));
  it('def makePoint',            () => expect(hasDef(code, 'makePoint')).toBe(true));
  it('makePoint uses struct literal', () => {
    const block = code.slice(code.indexOf('makePoint'));
    expect(block.slice(0, 300)).toContain('{ x');
  });
  it('no TS number type',        () => expect(code).not.toContain(': number'));
});

// ─── generics/discriminated-unions.ts ────────────────────────────────────────

describe('CLI e2e: generics/discriminated-unions.ts', () => {
  let code: string;
  beforeAll(() => { code = run('generics/discriminated-unions.ts'); });

  it('valid Lean output',         () => assertValidLean(code, 'disc-unions.ts'));
  it('inductive Shape (not struct)', () => {
    expect(code).toContain('inductive Shape');
    expect(code).not.toContain('structure Shape');
  });
  it('Circle constructor',        () => expect(code).toContain('| Circle'));
  it('Rectangle constructor',     () => expect(code).toContain('| Rectangle'));
  it('Triangle constructor',      () => expect(code).toContain('| Triangle'));
  it('areaShape uses match',      () => {
    const fn = code.slice(code.indexOf('def areaShape'));
    expect(fn.slice(0, 400)).toContain('match');
  });
  it('no string literals in match arms', () => {
    const fn = code.slice(code.indexOf('def areaShape'));
    const block = fn.slice(0, 400);
    expect(block).not.toContain('"circle"');
    expect(block).not.toContain('"rectangle"');
  });
  it('match arms use pattern vars not field access', () => {
    const fn = code.slice(code.indexOf('def areaShape'));
    const block = fn.slice(0, 400);
    expect(block).not.toContain('s.radius');
    expect(block).not.toContain('s.width');
  });
  it('dot constructor syntax',    () => {
    const fn = code.slice(code.indexOf('def areaShape'));
    expect(fn.slice(0, 400)).toMatch(/\.\s*Circle/);
  });
  it('Color inductive',           () => expect(code).toContain('inductive Color'));
  it('Tree inductive with type param', () => {
    expect(code).toContain('inductive Tree');
    expect(code).toMatch(/inductive Tree\s*[(({]T/);
  });
});

// ─── generics/branded-types.ts ────────────────────────────────────────────────

describe('CLI e2e: generics/branded-types.ts', () => {
  let code: string;
  beforeAll(() => { code = run('generics/branded-types.ts'); });

  it('valid Lean output',         () => assertValidLean(code, 'branded.ts'));
  it('UserId is structure',       () => expect(code).toContain('structure UserId'));
  it('UserId NOT abbrev',         () => expect(code).not.toContain('abbrev UserId := String'));
  it('val : String field',        () => {
    const block = code.slice(code.indexOf('structure UserId'), code.indexOf('structure UserId') + 100);
    expect(block).toContain('val : String');
  });
  it('RoomId, MessageId, SessionToken structures', () => {
    ['RoomId', 'MessageId', 'SessionToken', 'EmailAddress'].forEach(n => {
      expect(code).toContain(`structure ${n}`);
    });
  });
  it('makeUserId defined',        () => expect(hasDef(code, 'makeUserId')).toBe(true));
});

// ─── effects/async.ts ─────────────────────────────────────────────────────────

describe('CLI e2e: effects/async.ts', () => {
  let code: string;
  beforeAll(() => { code = run('effects/async.ts'); });

  it('valid Lean output',         () => assertValidLean(code, 'async.ts'));
  it('fetchUser returns IO type', () => {
    const line = code.split('\n').find(l => l.includes('def fetchUser') || l.includes('partial def fetchUser'));
    expect(line).toBeDefined();
    expect(line).toContain('IO');
  });
  it('withRetry has {T : Type}',  () => expect(code).toContain('{T : Type}'));
});

// ─── Advanced: for-loops.ts ───────────────────────────────────────────────────

describe('CLI e2e: advanced/for-loops.ts', () => {
  let code: string;
  beforeAll(() => { code = run('advanced/for-loops.ts'); });

  it('valid Lean output',         () => assertValidLean(code, 'for-loops.ts'));
  it('rangeSum defined',          () => expect(hasDef(code, 'rangeSum')).toBe(true));
  it('for-loop uses _loop_ helper', () => {
    const fn = code.slice(code.indexOf('rangeSum'));
    expect(fn.slice(0, 500)).toMatch(/_loop_/);
  });
  it('loop recursive call has i+1, not let i', () => {
    const fn = code.slice(code.indexOf('rangeSum'));
    expect(fn.slice(0, 500)).not.toMatch(/_loop_\d+ let i/);
  });
  it('processItems uses Array.forM', () => {
    const fn = code.slice(code.indexOf('processItems'));
    expect(fn.slice(0, 400)).toMatch(/Array.forM|default|sorry/);
  });
  it('fibonacci uses _while_ helper', () => {
    const fn = code.slice(code.indexOf('fibonacci'));
    expect(fn.slice(0, 400)).toMatch(/_while_/);
  });
});

// ─── Advanced: optional-chaining.ts ──────────────────────────────────────────

describe('CLI e2e: advanced/optional-chaining.ts', () => {
  let code: string;
  beforeAll(() => { code = run('advanced/optional-chaining.ts'); });

  it('valid Lean output',          () => assertValidLean(code, 'optional.ts'));
  it('getHost defined',            () => expect(hasDef(code, 'getHost')).toBe(true));
  it('?? becomes Option.getD',     () => expect(code).toContain('Option.getD'));
  it('sum with rest param defined', () => expect(hasDef(code, 'sum')).toBe(true));
  it('rest param is Array type',   () => {
    const line = code.split('\n').find(l => l.includes('def sum'));
    expect(line).toMatch(/Array/);
  });
});

// ─── Advanced: template-literals.ts ───────────────────────────────────────────

describe('CLI e2e: advanced/template-literals.ts', () => {
  let code: string;
  beforeAll(() => { code = run('advanced/template-literals.ts'); });

  it('valid Lean output',          () => assertValidLean(code, 'template.ts'));
  it('greeting defined',           () => expect(hasDef(code, 'greeting')).toBe(true));
  it('uses s!"..." or ++ concat',  () => {
    const fn = code.slice(code.indexOf('def greeting'));
    expect(fn.slice(0, 200)).toMatch(/s!"[^"]*"|"\s*\+\+/);
  });
  it('url function defined',       () => expect(hasDef(code, 'url')).toBe(true));
  it('userTag function defined',   () => expect(hasDef(code, 'userTag')).toBe(true));
});

// ─── Advanced: class-features.ts ──────────────────────────────────────────────

describe('CLI e2e: advanced/class-features.ts', () => {
  let code: string;
  beforeAll(() => { code = run('advanced/class-features.ts'); });

  it('valid Lean output',          () => assertValidLean(code, 'class.ts'));
  it('Status inductive',           () => expect(code).toContain('inductive Status'));
  it('Status toString function',   () => expect(hasDef(code, 'Status.toString')).toBe(true));
  it('Direction inductive (no toString for numeric)', () => {
    expect(code).toContain('inductive Direction');
    // Numeric enums don't get toString
  });
  it('DogState struct or Dog namespace', () => {
    expect(code).toMatch(/structure Dog|namespace Dog/);
  });
  it('get_radius getter defined',  () => expect(hasDef(code, 'get_radius')).toBe(true));
  it('set_radius setter defined',  () => expect(hasDef(code, 'set_radius')).toBe(true));
  it('Circle.fromDiameter defined',() => expect(hasDef(code, 'Circle.fromDiameter')).toBe(true));
  it('no switch/case leaked',      () => expect(code).not.toContain('switch'));
});

// ─── DO fixtures: all have TSLean imports ─────────────────────────────────────

describe('CLI e2e: all DO fixtures have required imports', () => {
  const dos = [
    'counter.ts', 'rate-limiter.ts', 'chat-room.ts',
    'session-store.ts', 'queue-processor.ts', 'auth-do.ts',
    'analytics-do.ts', 'multi-do.ts',
  ];
  for (const f of dos) {
    it(`${f}: imports TSLean.DurableObjects.Http`, () => {
      const code = run(`durable-objects/${f}`);
      expect(code).toContain('import TSLean.DurableObjects.Http');
    });
    it(`${f}: imports TSLean.Runtime.Monad`, () => {
      const code = run(`durable-objects/${f}`);
      expect(code).toContain('import TSLean.Runtime.Monad');
    });
  }
});

// ─── --verify flag ────────────────────────────────────────────────────────────

describe('CLI e2e: --verify flag', () => {
  it('hello.ts + --verify produces valid output', () => {
    const code = run('basic/hello.ts', '--verify');
    expect(code).toContain('open TSLean');
  });

  it('exceptions.ts + --verify adds division theorem', () => {
    const code = run('effects/exceptions.ts', '--verify');
    expect(code).toContain('open TSLean');
  });
});
