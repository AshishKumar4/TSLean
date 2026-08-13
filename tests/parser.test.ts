// Tests for the parser (TypeScript compiler API → IR).

import { execFileSync } from 'node:child_process';
import { describe, it, expect, beforeAll } from 'vitest';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { parseFile } from '../src/parser/index.js';
import { IRModule, IRDecl, IRExpr, Span, hasAsync } from '../src/ir/types.js';

const FIX = path.join(process.cwd(), 'tests/fixtures');
const parse = (rel: string) => parseFile({ fileName: path.join(FIX, rel) });

function isSpan(value: unknown): value is Span {
  return typeof value === 'object' && value !== null &&
    'file' in value && 'line' in value && 'col' in value;
}

function isIRExpr(value: object): value is IRExpr {
  return 'tag' in value && 'type' in value && 'effect' in value;
}

/**
 * Every distinct object in a module's IR graph.
 *
 * The IR is a DAG — a desugaring can reference one subexpression from two places
 * — so objects are visited by identity and yielded once each, which a serializing
 * walk would not do.
 */
function irObjects(mod: IRModule): object[] {
  const out: object[] = [];
  const seen = new Set<object>();
  const stack: unknown[] = [mod];
  while (stack.length > 0) {
    const value = stack.pop();
    if (typeof value !== 'object' || value === null || seen.has(value)) continue;
    seen.add(value);
    if (Array.isArray(value)) { stack.push(...value); continue; }
    out.push(value);
    const entries: [string, unknown][] = Object.entries(value);
    for (const [, child] of entries) stack.push(child);
  }
  return out;
}

/** Every span in a module. */
function collectSpans(mod: IRModule): Span[] {
  return irObjects(mod).flatMap(node =>
    'span' in node && isSpan(node.span) ? [node.span] : []);
}

/** Every expression node in a module. */
function collectExprs(mod: IRModule): IRExpr[] {
  return irObjects(mod).filter(isIRExpr);
}

/**
 * The span of `greet` in `basic/hello.ts` as reported by a parser running in
 * `cwd` — a separate process, because the question is what the compiler reports
 * when its binary is invoked from somewhere else.
 */
function spanFromCwd(cwd: string): unknown {
  const script = `import(${JSON.stringify(path.join(process.cwd(), 'src/parser/index.ts'))}).then(m => {
    const decl = m.parseFile({ fileName: ${JSON.stringify(path.join(FIX, 'basic/hello.ts'))} })
      .decls.find(d => d.tag === 'FuncDef' && d.name === 'greet');
    process.stdout.write(JSON.stringify(decl.span));
  });`;
  return JSON.parse(execFileSync('bun', ['-e', script], { cwd, encoding: 'utf8' }));
}

function find(mod: IRModule, name: string): IRDecl | undefined {
  function search(ds: IRDecl[]): IRDecl | undefined {
    for (const d of ds) {
      if ('name' in d && d.name === name) return d;
      if (d.tag === 'Namespace') { const f = search(d.decls); if (f) return f; }
    }
  }
  return search(mod.decls);
}

// ─── basic/hello.ts ───────────────────────────────────────────────────────────

describe('Parser: basic/hello.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('basic/hello.ts'); });

  it('produces a module',   () => { expect(mod).toBeDefined(); expect(mod.decls.length).toBeGreaterThan(0); });
  it('parses greet',        () => { const d = find(mod, 'greet'); expect(d?.tag).toBe('FuncDef'); if (d?.tag === 'FuncDef') { expect(d.params[0].name).toBe('name'); expect(d.retType.tag).toBe('String'); } });
  it('parses add (2 params)', () => { const d = find(mod, 'add'); if (d?.tag === 'FuncDef') expect(d.params).toHaveLength(2); });
  it('parses isPositive → Bool', () => { const d = find(mod, 'isPositive'); if (d?.tag === 'FuncDef') expect(d.retType.tag).toBe('Bool'); });
  it('parses factorial',    () => { expect(find(mod, 'factorial')?.tag).toBe('FuncDef'); });
  it('parses PI constant',  () => { expect(find(mod, 'PI')).toBeDefined(); });
  it('no TS syntax leaks',  () => expect(mod.decls.some(d => d.tag === 'RawLean')).toBe(false));
});

// ─── basic/interfaces.ts ──────────────────────────────────────────────────────

describe('Parser: basic/interfaces.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('basic/interfaces.ts'); });

  it('Point → StructDef', () => {
    const d = find(mod, 'Point');
    expect(d?.tag).toBe('StructDef');
    if (d?.tag === 'StructDef') {
      const names = d.fields.map(f => f.name);
      expect(names).toContain('x');
      expect(names).toContain('y');
    }
  });
  it('Rectangle → StructDef', () => expect(find(mod, 'Rectangle')?.tag).toBe('StructDef'));
  it('Named has optional description', () => {
    const d = find(mod, 'Named');
    if (d?.tag === 'StructDef') {
      const desc = d.fields.find(f => f.name === 'description');
      expect(['Option', 'String']).toContain(desc?.type.tag);
    }
  });
  it('distance has 2 Point params', () => {
    const d = find(mod, 'distance');
    if (d?.tag === 'FuncDef') expect(d.params).toHaveLength(2);
  });
});

// ─── basic/classes.ts ─────────────────────────────────────────────────────────

describe('Parser: basic/classes.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('basic/classes.ts'); });

  it('Counter state struct emitted', () => {
    const d = mod.decls.find(d => d.tag === 'StructDef' && d.name === 'CounterState');
    expect(d).toBeDefined();
  });
  it('increment method defined', () => expect(find(mod, 'Counter.increment') ?? find(mod, 'increment')).toBeDefined());
  it('BankAccount.deposit defined', () => expect(find(mod, 'BankAccount.deposit') ?? find(mod, 'deposit')).toBeDefined());
  it('BankAccount.withdraw defined', () => expect(find(mod, 'BankAccount.withdraw') ?? find(mod, 'withdraw')).toBeDefined());
});

// ─── generics/discriminated-unions.ts ────────────────────────────────────────

describe('Parser: generics/discriminated-unions.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('generics/discriminated-unions.ts'); });

  it('Shape → InductiveDef with Circle/Rectangle/Triangle', () => {
    const d = find(mod, 'Shape');
    expect(d?.tag).toBe('InductiveDef');
    if (d?.tag === 'InductiveDef') {
      const names = d.ctors.map(c => c.name);
      expect(names).toContain('Circle');
      expect(names).toContain('Rectangle');
      expect(names).toContain('Triangle');
    }
  });
  it('Color → InductiveDef', () => expect(find(mod, 'Color')?.tag).toBe('InductiveDef'));
  it('Tree has type param', () => {
    const d = find(mod, 'Tree');
    if (d?.tag === 'InductiveDef') expect(d.typeParams.length).toBeGreaterThanOrEqual(1);
  });
  it('areaShape is FuncDef', () => expect(find(mod, 'areaShape')?.tag).toBe('FuncDef'));
});

// ─── generics/branded-types.ts ────────────────────────────────────────────────

describe('Parser: generics/branded-types.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('generics/branded-types.ts'); });

  it('UserId → branded StructDef or TypeDef', () => {
    const d = find(mod, 'UserId');
    expect(d).toBeDefined();
    expect(['StructDef', 'TypeAlias']).toContain(d?.tag);
  });
  it('RoomId defined',          () => expect(find(mod, 'RoomId')).toBeDefined());
  it('makeUserId → FuncDef',    () => expect(find(mod, 'makeUserId')?.tag).toBe('FuncDef'));
  it('UserProfile → StructDef', () => expect(find(mod, 'UserProfile')?.tag).toBe('StructDef'));
});

// ─── effects/async.ts ─────────────────────────────────────────────────────────

describe('Parser: effects/async.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('effects/async.ts'); });

  it('fetchUser is FuncDef', () => expect(find(mod, 'fetchUser')?.tag).toBe('FuncDef'));
  it('fetchUser has Async effect', () => {
    const d = find(mod, 'fetchUser');
    if (d?.tag === 'FuncDef') expect(hasAsync(d.effect)).toBe(true);
  });
  it('withRetry has type param', () => {
    const d = find(mod, 'withRetry');
    if (d?.tag === 'FuncDef') expect(d.typeParams.length).toBeGreaterThanOrEqual(1);
  });
});

// ─── effects/exceptions.ts ───────────────────────────────────────────────────

describe('Parser: effects/exceptions.ts', () => {
  let mod: IRModule;
  beforeAll(() => { mod = parse('effects/exceptions.ts'); });

  it('parseAge → FuncDef',     () => expect(find(mod, 'parseAge')?.tag).toBe('FuncDef'));
  it('divide → FuncDef',       () => expect(find(mod, 'divide')?.tag).toBe('FuncDef'));
  it('safeDivide → FuncDef',   () => expect(find(mod, 'safeDivide')?.tag).toBe('FuncDef'));
  it('validateEmail → FuncDef', () => expect(find(mod, 'validateEmail')?.tag).toBe('FuncDef'));
});

// ─── DO detection ─────────────────────────────────────────────────────────────

describe('Parser: DO detection', () => {
  it('counter.ts has DO imports', () => {
    const mod = parse('durable-objects/counter.ts');
    expect(mod.imports.some(i => i.module.includes('DurableObjects'))).toBe(true);
  });
  it('auth-do.ts has DO imports', () => {
    const mod = parse('durable-objects/auth-do.ts');
    expect(mod.imports.some(i => i.module.includes('DurableObjects'))).toBe(true);
  });
  it('hello.ts has no DO imports', () => {
    const mod = parse('basic/hello.ts');
    expect(mod.imports.some(i => i.module.includes('DurableObjects'))).toBe(false);
  });
});

// ─── Inline source parsing ────────────────────────────────────────────────────

describe('Parser: inline source', () => {
  it('parses const declarations', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'const x: number = 42;\nconst s = "hello";' });
    expect(mod.decls.length).toBeGreaterThanOrEqual(1);
  });

  it('parses enum', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'enum Dir { North, South, East, West }' });
    const d = mod.decls.find(d => d.tag === 'InductiveDef' && d.name === 'Dir');
    expect(d).toBeDefined();
    if (d?.tag === 'InductiveDef') {
      const names = d.ctors.map(c => c.name);
      expect(names).toContain('North');
      expect(names).toContain('South');
    }
  });

  it('parses namespace', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'namespace Utils { function id<T>(x: T): T { return x; } }' });
    const d = mod.decls.find(d => d.tag === 'Namespace' && d.name === 'Utils');
    expect(d).toBeDefined();
  });

  it('parses template literal', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'function greet(n: string): string { return `Hello, ${n}!`; }' });
    const d = mod.decls.find(d => d.tag === 'FuncDef' && d.name === 'greet');
    expect(d?.tag).toBe('FuncDef');
  });

  it('detects DO pattern in inline source', () => {
    const mod = parseFile({ fileName: 'do.ts', sourceText: 'class MyDO { state: DurableObjectState; constructor(state: DurableObjectState, env: Env) { this.state = state; } }' });
    expect(mod.imports.some(i => i.module.includes('DurableObjects'))).toBe(true);
  });

  it('parses for-loop', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'function sum(n: number): number { let t = 0; for (let i = 0; i < n; i++) { t += i; } return t; }' });
    const d = mod.decls.find(d => d.tag === 'FuncDef' && d.name === 'sum');
    expect(d?.tag).toBe('FuncDef');
  });

  it('parses while loop', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'function cd(n: number): number { let x = n; while (x > 0) { x = x - 1; } return x; }' });
    const d = mod.decls.find(d => d.tag === 'FuncDef' && d.name === 'cd');
    expect(d?.tag).toBe('FuncDef');
  });

  it('parses try-catch', () => {
    const mod = parseFile({ fileName: 'test.ts', sourceText: 'function safe(): number { try { return 1; } catch(e) { return 0; } }' });
    const d = mod.decls.find(d => d.tag === 'FuncDef');
    expect(d).toBeDefined();
  });
});

// ─── Source spans ─────────────────────────────────────────────────────────────
//
// `Span` is 1-based on both line and column and names the file relative to the
// project root.  Diagnostics quote these numbers, so an off-by-one here is a wrong
// error message, and a path that depends on the working directory is a span that
// differs between machines and between invocations of the same binary.

describe('Parser: source spans', () => {
  const HELLO = path.join('tests', 'fixtures', 'basic', 'hello.ts');
  const CLASSES = path.join('tests', 'fixtures', 'basic', 'classes.ts');

  it('a function declaration spans its first line, 1-based', () => {
    const d = find(parse('basic/hello.ts'), 'greet');   // hello.ts:3, first column
    expect(d?.tag).toBe('FuncDef');
    if (d?.tag === 'FuncDef') expect(d.span).toEqual({ file: HELLO, line: 3, col: 1 });
  });

  it('a variable declaration spans its declarator, not the statement', () => {
    const d = find(parse('basic/hello.ts'), 'PI');      // `const PI = …` — PI is column 7
    expect(d?.tag).toBe('VarDecl');
    if (d?.tag === 'VarDecl') expect(d.span).toEqual({ file: HELLO, line: 20, col: 7 });
  });

  it('a constructor and a method of the same class are both located', () => {
    const mod = parse('basic/classes.ts');
    const ctor = find(mod, 'Counter.init');
    const method = find(mod, 'Counter.getCount');
    expect(ctor?.tag).toBe('FuncDef');
    expect(method?.tag).toBe('FuncDef');
    if (ctor?.tag === 'FuncDef')   expect(ctor.span).toEqual({ file: CLASSES, line: 6, col: 3 });
    if (method?.tag === 'FuncDef') expect(method.span).toEqual({ file: CLASSES, line: 10, col: 3 });
  });

  it('an accessor is located at its own `get`', () => {
    const d = find(parse('advanced/class-features.ts'), 'get_fullDescription');
    expect(d?.tag).toBe('FuncDef');
    if (d?.tag === 'FuncDef')
      expect(d.span).toEqual({ file: path.join('tests', 'fixtures', 'advanced', 'class-features.ts'), line: 36, col: 3 });
  });

  it('expressions carry the span of their own source node', () => {
    const d = find(parse('basic/hello.ts'), 'add');     // `  return a + b;` — `a` is column 10
    expect(d?.tag).toBe('FuncDef');
    if (d?.tag !== 'FuncDef') return;
    expect(d.body.tag).toBe('Return');
    if (d.body.tag === 'Return')
      expect(d.body.value.span).toEqual({ file: HELLO, line: 8, col: 10 });
  });

  it('a body-less declaration locates its own hole', () => {
    const mod = parseFile({ fileName: 'decl.ts', sourceText: 'declare function opaque(n: number): number;\n' });
    const d = mod.decls.find(x => x.tag === 'FuncDef' && x.name === 'opaque');
    expect(d?.tag).toBe('FuncDef');
    if (d?.tag !== 'FuncDef') return;
    expect(d.body.tag).toBe('Hole');
    expect(d.body.span).toEqual({ file: 'decl.ts', line: 1, col: 1 });
  });

  it('a pass-through form reports the inner expression it resolves to', () => {
    // `((1 + 2))` is one IR node; the useful location is the addition at column 13.
    const mod = parseFile({ fileName: 'inline.ts', sourceText: 'const y = ((1 + 2));\n' });
    const d = mod.decls.find(x => x.tag === 'VarDecl' && x.name === 'y');
    expect(d?.tag).toBe('VarDecl');
    if (d?.tag === 'VarDecl') expect(d.value.span).toEqual({ file: 'inline.ts', line: 1, col: 13 });
  });

  it('statements are located: a return, a throw and a let', () => {
    // 1 export function f(n: number): number {
    // 2   let x = n;
    // 3   if (x < 0) throw new Error('neg');
    // 4   return x;
    const source = 'export function f(n: number): number {\n  let x = n;\n  if (x < 0) throw new Error("neg");\n  return x;\n}\n';
    const d = parseFile({ fileName: 'stmts.ts', sourceText: source }).decls
      .find(x => x.tag === 'FuncDef' && x.name === 'f');
    expect(d?.tag).toBe('FuncDef');
    if (d?.tag !== 'FuncDef') return;
    const at = (line: number, col: number): Span => ({ file: 'stmts.ts', line, col });
    expect(d.body.tag).toBe('Let');
    expect(d.body.span).toEqual(at(2, 3));
    if (d.body.tag !== 'Let') return;
    expect(d.body.body.tag).toBe('IfThenElse');
    expect(d.body.body.span).toEqual(at(3, 3));
    if (d.body.body.tag !== 'IfThenElse') return;
    expect(d.body.body.then.span).toEqual(at(3, 14));       // the `throw`
    expect(d.body.body.else_.span).toEqual(at(4, 3));       // the `return`
  });

  it('every `sorry` the parser emits is located', () => {
    // A Hole prints `sorry`, the location a diagnostic most needs: an abstract
    // method, a constructor that leaves a state field unset, the wildcard arm a
    // non-exhaustive switch gets, and a method declared with no body at all.
    const modules = [
      ...['basic/classes.ts', 'advanced/class-features.ts',
        'durable-objects/counter.ts', 'projects/todo-app/store.ts'].map(rel => parse(rel)),
      ...['export default { fetch(req: string): string; };\n', 'const o = { m(): number; };\n']
        .map(sourceText => parseFile({ fileName: 'holes.ts', sourceText })),
    ];
    const holes = modules.flatMap(mod => collectExprs(mod).filter(e => e.tag === 'Hole'));
    expect(holes.length).toBeGreaterThanOrEqual(5);
    expect(holes.filter(hole => !('span' in hole))).toEqual([]);
  });

  it('spans stay inside the file and never go absolute', () => {
    const mod = parse('projects/todo-app/store.ts');
    const rel = path.join('tests', 'fixtures', 'projects', 'todo-app', 'store.ts');
    const lines = fs.readFileSync(path.join(FIX, 'projects/todo-app/store.ts'), 'utf-8').split('\n').length;
    const spans = collectSpans(mod);
    expect(spans.length).toBeGreaterThan(50);
    for (const s of spans) {
      expect(s.file).toBe(rel);
      expect(s.line).toBeGreaterThanOrEqual(1);
      expect(s.line).toBeLessThanOrEqual(lines);
      expect(s.col).toBeGreaterThanOrEqual(1);
    }
  });

  it('the same file yields the same span from any working directory', () => {
    // The regression this guards is a cwd-relative path: run from outside the
    // repository it would read `../../Users/<someone>/…`, which is neither inside
    // the project nor the same on another machine.
    const outside = fs.mkdtempSync(path.join(fs.realpathSync(os.tmpdir()), 'tslean-span-'));
    try {
      const greet = { file: HELLO, line: 3, col: 1 };
      expect(spanFromCwd(process.cwd())).toEqual(greet);        // repository root
      expect(spanFromCwd(FIX)).toEqual(greet);                  // a subdirectory
      expect(spanFromCwd(outside)).toEqual(greet);              // outside the repository
    } finally {
      fs.rmSync(outside, { recursive: true, force: true });
    }
  });

  it('an explicit project root decides what the span is relative to', () => {
    const mod = parseFile({ fileName: path.join(FIX, 'basic/hello.ts'), projectRoot: FIX });
    const d = find(mod, 'greet');
    expect(d?.tag).toBe('FuncDef');
    if (d?.tag === 'FuncDef')
      expect(d.span).toEqual({ file: path.join('basic', 'hello.ts'), line: 3, col: 1 });
  });
});
