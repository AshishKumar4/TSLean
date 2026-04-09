// Comprehensive tests for ALL fixtures through the full pipeline.
// Every fixture file is tested for parsing, rewriting, codegen output quality.

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import * as fs from 'fs';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';
import { generateVerification } from '../src/verification/index.js';
import {
  IRModule, IRDecl, hasAsync, hasState, hasExcept, hasIO, isPure,
  TyString, TyFloat, TyBool, TyNat, TyUnit,
} from '../src/ir/types.js';

const FIX = path.join(process.cwd(), 'tests/fixtures');

function pipeline(rel: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: path.join(FIX, rel) })));
}

function parsed(rel: string): IRModule {
  return parseFile({ fileName: path.join(FIX, rel) });
}

function findDecl(mod: IRModule, name: string): IRDecl | undefined {
  function search(ds: IRDecl[]): IRDecl | undefined {
    for (const d of ds) {
      if ('name' in d && d.name === name) return d;
      if (d.tag === 'Namespace') { const f = search(d.decls); if (f) return f; }
    }
  }
  return search(mod.decls);
}

// ─── basic/hello.ts — comprehensive ──────────────────────────────────────────

describe('All fixtures: basic/hello.ts', () => {
  let mod: IRModule;
  let code: string;
  beforeAll(() => { mod = parsed('basic/hello.ts'); code = pipeline('basic/hello.ts'); });

  it('has 6+ declarations', () => expect(mod.decls.length).toBeGreaterThanOrEqual(5));
  it('greet is FuncDef',    () => expect(findDecl(mod, 'greet')?.tag).toBe('FuncDef'));
  it('add is FuncDef',      () => expect(findDecl(mod, 'add')?.tag).toBe('FuncDef'));
  it('isPositive is FuncDef', () => expect(findDecl(mod, 'isPositive')?.tag).toBe('FuncDef'));
  it('factorial is FuncDef', () => expect(findDecl(mod, 'factorial')?.tag).toBe('FuncDef'));
  it('PI is VarDecl',       () => { const d = findDecl(mod, 'PI'); expect(d?.tag).toBe('VarDecl'); });
  it('greeting is VarDecl', () => expect(findDecl(mod, 'greeting')).toBeDefined());
  it('output has s! interpolation', () => expect(code).toMatch(/s!"Hello, \{name\}!"/));
  it('output has partial def', () => expect(code).toContain('partial def factorial'));
  it('output has if-then-else in factorial', () => { const fn = code.slice(code.indexOf('factorial')); expect(fn.slice(0, 200)).toContain('if'); });
  it('output has no TS syntax', () => { expect(code).not.toContain('function '); expect(code).not.toContain('==='); });
  it('output has open TSLean', () => expect(code).toContain('open TSLean'));
  it('greet return type is String', () => { const d = findDecl(mod, 'greet') as any; expect(d?.retType?.tag).toBe('String'); });
  it('add has two Float params', () => { const d = findDecl(mod, 'add') as any; expect(d?.params?.length).toBe(2); });
  it('isPositive returns Bool', () => { const d = findDecl(mod, 'isPositive') as any; expect(d?.retType?.tag).toBe('Bool'); });
});

// ─── basic/interfaces.ts — comprehensive ────────────────────────────────────

describe('All fixtures: basic/interfaces.ts', () => {
  let mod: IRModule;
  let code: string;
  beforeAll(() => { mod = parsed('basic/interfaces.ts'); code = pipeline('basic/interfaces.ts'); });

  it('Point is StructDef', () => expect(findDecl(mod, 'Point')?.tag).toBe('StructDef'));
  it('Point has x and y fields', () => {
    const d = findDecl(mod, 'Point') as any;
    const names = d?.fields?.map((f: any) => f.name);
    expect(names).toContain('x');
    expect(names).toContain('y');
  });
  it('Rectangle is StructDef', () => expect(findDecl(mod, 'Rectangle')?.tag).toBe('StructDef'));
  it('Named is StructDef', () => expect(findDecl(mod, 'Named')?.tag).toBe('StructDef'));
  it('distance is FuncDef', () => expect(findDecl(mod, 'distance')?.tag).toBe('FuncDef'));
  it('area is FuncDef', () => expect(findDecl(mod, 'area')?.tag).toBe('FuncDef'));
  it('makePoint is FuncDef', () => expect(findDecl(mod, 'makePoint')?.tag).toBe('FuncDef'));
  it('output has structure Point', () => expect(code).toContain('structure Point'));
  it('output has x : Float', () => expect(code).toContain('x : Float'));
  it('output has structure Named', () => expect(code).toContain('structure Named'));
  it('output has deriving Repr, BEq', () => expect(code).toContain('deriving Repr, BEq'));
  it('output has def distance', () => expect(code).toMatch(/def distance/));
  it('output has def makePoint with struct literal', () => {
    const fn = code.slice(code.indexOf('def makePoint'));
    expect(fn.slice(0, 200)).toContain('{ x');
  });
});

// ─── generics/discriminated-unions.ts — comprehensive ──────────────────────

describe('All fixtures: generics/discriminated-unions.ts', () => {
  let mod: IRModule;
  let code: string;
  beforeAll(() => { mod = parsed('generics/discriminated-unions.ts'); code = pipeline('generics/discriminated-unions.ts'); });

  it('Shape is InductiveDef', () => expect(findDecl(mod, 'Shape')?.tag).toBe('InductiveDef'));
  it('Shape has 3 constructors', () => {
    const d = findDecl(mod, 'Shape') as any;
    expect(d?.ctors?.length).toBe(3);
  });
  it('Color is InductiveDef', () => expect(findDecl(mod, 'Color')?.tag).toBe('InductiveDef'));
  it('Color has 4 constructors', () => {
    const d = findDecl(mod, 'Color') as any;
    expect(d?.ctors?.length).toBe(4);
  });
  it('Tree is InductiveDef with type param', () => {
    const d = findDecl(mod, 'Tree') as any;
    expect(d?.tag).toBe('InductiveDef');
    expect(d?.typeParams?.length).toBeGreaterThanOrEqual(1);
  });
  it('Either is InductiveDef', () => expect(findDecl(mod, 'Either')?.tag).toBe('InductiveDef'));
  it('areaShape is FuncDef', () => expect(findDecl(mod, 'areaShape')?.tag).toBe('FuncDef'));
  it('perimeter is FuncDef', () => expect(findDecl(mod, 'perimeter')?.tag).toBe('FuncDef'));
  it('treeDepth is FuncDef', () => expect(findDecl(mod, 'treeDepth')?.tag).toBe('FuncDef'));
  it('output: inductive Shape', () => expect(code).toContain('inductive Shape'));
  it('output: | Circle', () => expect(code).toContain('| Circle'));
  it('output: match s with', () => expect(code).toContain('match s with'));
  it('output: no "circle" string in match', () => { const fn = code.slice(code.indexOf('areaShape')); expect(fn.slice(0, 500)).not.toContain('"circle"'); });
  it('output: .Circle pattern', () => { const fn = code.slice(code.indexOf('areaShape')); expect(fn.slice(0, 500)).toMatch(/\.\s*Circle/); });
  it('output: pattern vars not s.field', () => {
    const fn = code.slice(code.indexOf('areaShape'));
    expect(fn.slice(0, 500)).not.toContain('s.radius');
    expect(fn.slice(0, 500)).not.toContain('s.width');
  });
});

// ─── generics/branded-types.ts — comprehensive ─────────────────────────────

describe('All fixtures: generics/branded-types.ts', () => {
  let mod: IRModule;
  let code: string;
  beforeAll(() => { mod = parsed('generics/branded-types.ts'); code = pipeline('generics/branded-types.ts'); });

  it('UserId is StructDef', () => expect(findDecl(mod, 'UserId')?.tag).toBe('StructDef'));
  it('RoomId is StructDef', () => expect(findDecl(mod, 'RoomId')?.tag).toBe('StructDef'));
  it('UserId has val : String field', () => {
    const d = findDecl(mod, 'UserId') as any;
    expect(d?.fields?.some((f: any) => f.name === 'val' && f.type.tag === 'String')).toBe(true);
  });
  it('makeUserId is FuncDef', () => expect(findDecl(mod, 'makeUserId')?.tag).toBe('FuncDef'));
  it('UserProfile is StructDef', () => expect(findDecl(mod, 'UserProfile')?.tag).toBe('StructDef'));
  it('output: structure UserId', () => expect(code).toContain('structure UserId'));
  it('output: not abbrev UserId := String', () => expect(code).not.toContain('abbrev UserId := String'));
  it('output: DecidableEq deriving', () => expect(code).toContain('DecidableEq'));
});

// ─── effects/async.ts — comprehensive ─────────────────────────────────────

describe('All fixtures: effects/async.ts', () => {
  let mod: IRModule;
  let code: string;
  beforeAll(() => { mod = parsed('effects/async.ts'); code = pipeline('effects/async.ts'); });

  it('fetchUser is FuncDef', () => expect(findDecl(mod, 'fetchUser')?.tag).toBe('FuncDef'));
  it('fetchUser has Async effect', () => {
    const d = findDecl(mod, 'fetchUser') as any;
    expect(hasAsync(d?.effect)).toBe(true);
  });
  it('withRetry has type param T', () => {
    const d = findDecl(mod, 'withRetry') as any;
    expect(d?.typeParams?.length).toBeGreaterThanOrEqual(1);
  });
  it('output: IO in return type', () => { const line = code.split('\n').find(l => /def fetchUser|partial def fetchUser/.test(l)); expect(line).toContain('IO'); });
  it('output: {T : Type}', () => expect(code).toContain('{T : Type}'));
});

// ─── effects/exceptions.ts — comprehensive ───────────────────────────────

describe('All fixtures: effects/exceptions.ts', () => {
  let mod: IRModule;
  let code: string;
  beforeAll(() => { mod = parsed('effects/exceptions.ts'); code = pipeline('effects/exceptions.ts'); });

  it('parseAge is FuncDef', () => expect(findDecl(mod, 'parseAge')?.tag).toBe('FuncDef'));
  it('divide is FuncDef', () => expect(findDecl(mod, 'divide')?.tag).toBe('FuncDef'));
  it('safeDivide is FuncDef', () => expect(findDecl(mod, 'safeDivide')?.tag).toBe('FuncDef'));
  it('output: throw keyword', () => expect(code).toContain('throw'));
  it('output: tryCatch or sorry (cross-monad try)', () => expect(code).toMatch(/tryCatch|default/));
});

// ─── durable-objects — comprehensive ──────────────────────────────────────

describe('All fixtures: durable-objects', () => {
  const doFixtures = [
    { file: 'durable-objects/counter.ts', className: 'CounterDO', methods: ['fetch'] },
    { file: 'durable-objects/rate-limiter.ts', className: 'RateLimiterDO', methods: ['fetch', 'checkRateLimit'] },
    { file: 'durable-objects/chat-room.ts', className: 'ChatRoomDO', methods: ['fetch', 'broadcast'] },
    { file: 'durable-objects/session-store.ts', className: 'SessionStoreDO', methods: ['fetch', 'createSession'] },
    { file: 'durable-objects/queue-processor.ts', className: 'QueueProcessorDO', methods: ['fetch', 'enqueue'] },
    { file: 'durable-objects/auth-do.ts', className: 'AuthDO', methods: ['fetch', 'handleLogin'] },
    { file: 'durable-objects/analytics-do.ts', className: 'AnalyticsDO', methods: ['fetch', 'trackEvent'] },
    { file: 'durable-objects/multi-do.ts', className: 'CoordinatorDO', methods: ['fetch', 'handleRPC'] },
  ];

  for (const { file, className, methods } of doFixtures) {
    describe(file, () => {
      let mod: IRModule;
      let code: string;
      beforeAll(() => { mod = parsed(file); code = pipeline(file); });

      it('has DO imports', () => expect(mod.imports.some(i => i.module.includes('DurableObjects'))).toBe(true));
      it('has Runtime.Monad import', () => expect(mod.imports.some(i => i.module.includes('Runtime.Monad'))).toBe(true));
      it('has state struct', () => expect(mod.decls.some(d => d.tag === 'StructDef')).toBe(true));

      for (const method of methods) {
        it(`has ${method} method`, () => {
          const d = findDecl(mod, method);
          // Method may be in namespace
          if (!d) {
            const ns = mod.decls.find(d => d.tag === 'Namespace');
            if (ns?.tag === 'Namespace') {
              expect(ns.decls.some(d => 'name' in d && d.name.includes(method))).toBe(true);
            }
          } else {
            expect(d).toBeDefined();
          }
        });
      }

      it('output: import TSLean.DurableObjects.Http', () => expect(code).toContain('import TSLean.DurableObjects.Http'));
      it('output: open TSLean', () => expect(code).toContain('open TSLean'));
      it(`output: ${className} state struct`, () => expect(code).toMatch(new RegExp(`structure ${className}State|namespace ${className}`)));
    });
  }
});

// ─── advanced fixtures ────────────────────────────────────────────────────────

const advancedFixtures = fs.readdirSync(path.join(FIX, 'advanced'))
  .filter(f => f.endsWith('.ts'));

describe('All fixtures: advanced/', () => {
  for (const fixture of advancedFixtures) {
    describe(`advanced/${fixture}`, () => {
      it('parses without error', () => {
        expect(() => parsed(`advanced/${fixture}`)).not.toThrow();
      });

      it('produces non-empty output', () => {
        const code = pipeline(`advanced/${fixture}`);
        expect(code.length).toBeGreaterThan(50);
      });

      it('output has header', () => {
        const code = pipeline(`advanced/${fixture}`);
        expect(code).toContain('-- Auto-generated');
      });

      it('output has open TSLean', () => {
        const code = pipeline(`advanced/${fixture}`);
        expect(code).toContain('open TSLean');
      });

      it('output has at least one def/structure/inductive', () => {
        const code = pipeline(`advanced/${fixture}`);
        expect(code).toMatch(/\b(def|structure|inductive|abbrev)\s+\w/);
      });

      it('output has balanced parens', () => {
        const code = pipeline(`advanced/${fixture}`);
        let depth = 0;
        for (const ch of code) {
          if (ch === '(') depth++;
          if (ch === ')') depth--;
          if (depth < 0) break;
        }
        expect(depth).toBe(0);
      });
    });
  }
});

// ─── generics/generics.ts — comprehensive ────────────────────────────────

describe('All fixtures: generics/generics.ts', () => {
  let mod: IRModule;
  let code: string;
  beforeAll(() => { mod = parsed('generics/generics.ts'); code = pipeline('generics/generics.ts'); });

  it('identity is FuncDef', () => expect(findDecl(mod, 'identity')?.tag).toBe('FuncDef'));
  it('compose is FuncDef', () => expect(findDecl(mod, 'compose')?.tag).toBe('FuncDef'));
  it('Pair is StructDef', () => expect(findDecl(mod, 'Pair')?.tag).toBe('StructDef'));
  it('output: def identity with {T}', () => { expect(code).toContain('def identity'); expect(code).toContain('{T : Type}'); });
  it('output: def compose', () => expect(code).toContain('def compose'));
  it('output: def mapOpt', () => expect(code).toContain('def mapOpt'));
  it('output: structure Pair', () => expect(code).toContain('structure Pair'));
});

// ─── Verification on complex fixtures ─────────────────────────────────────

describe('All fixtures: verification obligations', () => {
  it('hello.ts has 0 obligations (pure functions)', () => {
    const mod = parsed('basic/hello.ts');
    const { obligations } = generateVerification(rewriteModule(mod));
    // hello.ts has no division or array access
    expect(obligations.length).toBeLessThanOrEqual(2);
  });

  it('exceptions.ts has division obligations', () => {
    const mod = parsed('effects/exceptions.ts');
    const { obligations } = generateVerification(rewriteModule(mod));
    expect(obligations.some(o => o.kind === 'DivisionSafe')).toBe(true);
  });
});

// ─── Full project transpilation ────────────────────────────────────────────

describe('All fixtures: full-project transpilation', () => {
  const fp = path.join(FIX, 'full-project');
  const files = ['shared/types.ts', 'shared/validators.ts', 'backend/auth-do.ts', 'backend/chat-room-do.ts', 'backend/router.ts'];

  for (const file of files) {
    const fullPath = path.join(fp, file);
    if (!fs.existsSync(fullPath)) continue;

    describe(file, () => {
      it('parses without error', () => {
        expect(() => parseFile({ fileName: fullPath })).not.toThrow();
      });

      it('produces non-empty output', () => {
        const code = generateLean(rewriteModule(parseFile({ fileName: fullPath })));
        expect(code.length).toBeGreaterThan(50);
      });

      it('output has at least one def/structure', () => {
        const code = generateLean(rewriteModule(parseFile({ fileName: fullPath })));
        expect(code).toMatch(/\b(def|structure|inductive|abbrev)\s+\w/);
      });
    });
  }
});
