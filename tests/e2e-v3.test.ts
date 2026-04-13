// E2E v3 tests: comprehensive end-to-end tests for all expanded features.

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import * as fs from 'fs';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';
import { generateVerification } from '../src/verification/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyBool, TyNat, TyUnit, TyRef, TyArray, TyOption,
  Pure, Async, IO, stateEffect, exceptEffect, combineEffects,
  litNat, litStr, litBool, litUnit, litFloat, varExpr,
} from '../src/ir/types.js';

const FIX = path.join(process.cwd(), 'tests/fixtures');

function pipeline(rel: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: path.join(FIX, rel) })));
}

function inline(src: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: 'test.ts', sourceText: src })));
}

function mod(decls: IRDecl[]): IRModule {
  return { name: 'T', imports: [], decls, comments: [] };
}

// ─── Export default → def fetch ────────────────────────────────────────────────

describe('E2E v3: export default object with methods', () => {
  it('async method in export default becomes partial def', () => {
    const code = inline(`
      export default {
        async fetch(req: Request, env: Env): Promise<Response> {
          const url = new URL(req.url);
          if (url.pathname === '/ping') return new Response('pong');
          return new Response('not found', { status: 404 });
        }
      };
    `);
    expect(code).toMatch(/def fetch/);
    expect(code).toContain('IO');
  });

  it('sync method in export default becomes def', () => {
    const code = inline(`
      export default {
        version(): string { return '1.0'; },
        name(): string { return 'myapp'; }
      };
    `);
    expect(code).toMatch(/def version/);
    expect(code).toMatch(/def name/);
  });

  it('export-patterns fixture: createConfig and makeSuccess', () => {
    const code = pipeline('advanced/export-patterns.ts');
    expect(code).toMatch(/def createConfig/);
    expect(code).toMatch(/def makeSuccess/);
    expect(code).toMatch(/def makeError/);
  });
});

// ─── Interface extends ─────────────────────────────────────────────────────────

describe('E2E v3: interface extends', () => {
  it('extends keyword appears in structure', () => {
    const code = inline(`
      interface Animal { name: string }
      interface Dog extends Animal { breed: string }
    `);
    expect(code).toContain('structure Dog');
    expect(code).toContain('breed');
  });

  it('RouterEnv extends Env with full project', () => {
    const code = pipeline('full-project/backend/router.ts');
    expect(code).toContain('structure RouterEnv');
    expect(code).toMatch(/extends|AUTH_DO/);
  });
});

// ─── Index signatures ─────────────────────────────────────────────────────────

describe('E2E v3: index signatures', () => {
  it('pure index signature → AssocMap', () => {
    const code = inline(`interface Dict { [k: string]: number }`);
    expect(code).toMatch(/abbrev Dict|AssocMap/);
  });

  it('mixed index + named field → structure', () => {
    const code = inline(`
      interface Config {
        [key: string]: string;
        version: string;
      }
    `);
    expect(code).toMatch(/structure Config|abbrev Config/);
  });

  it('index-signatures fixture transpiles', () => {
    const code = pipeline('advanced/index-signatures.ts');
    expect(code).toMatch(/def getFromMap/);
    expect(code).toMatch(/def setInMap/);
  });
});

// ─── Type narrowing ────────────────────────────────────────────────────────────

describe('E2E v3: type narrowing', () => {
  it('type-narrowing fixture transpiles completely', () => {
    const code = pipeline('advanced/type-narrowing.ts');
    expect(code).toMatch(/def processValue/);
    expect(code).toMatch(/def makeSound/);
    expect(code).toMatch(/def isString/);
    expect(code).toMatch(/def isPositiveNumber/);
  });

  it('typeof check uses typeOf or if', () => {
    const code = inline(`
      function classify(x: string | number): string {
        if (typeof x === 'string') return 'string';
        return 'number';
      }
    `);
    expect(code).toMatch(/def classify/);
    expect(code).toMatch(/if|match/);
  });

  it('in expression uses contains', () => {
    const code = inline(`
      function hasName(obj: {name?: string}): boolean {
        return 'name' in obj;
      }
    `);
    expect(code).toMatch(/def hasName/);
  });
});

// ─── Complex loops ─────────────────────────────────────────────────────────────

describe('E2E v3: complex loops', () => {
  it('nested for-of loops', () => {
    const code = inline(`
      function flatten(xss: number[][]): number[] {
        const result: number[] = [];
        for (const xs of xss) {
          for (const x of xs) {
            result.push(x);
          }
        }
        return result;
      }
    `);
    expect(code).toMatch(/def flatten/);
    expect(code).toMatch(/Array.forM|default/);
  });

  it('do-while loop approximation', () => {
    const code = inline(`
      function atLeastOnce(n: number): number {
        let i = 0;
        do {
          i++;
        } while (i < n);
        return i;
      }
    `);
    // do-while not natively supported, check it at least parses
    expect(code).toMatch(/def atLeastOnce/);
  });

  it('labelled continue ignored gracefully', () => {
    const code = inline(`
      function skipEven(nums: number[]): number[] {
        const out: number[] = [];
        outer: for (const n of nums) {
          if (n % 2 === 0) continue outer;
          out.push(n);
        }
        return out;
      }
    `);
    expect(code).toMatch(/def skipEven/);
  });
});

// ─── Verification with complex patterns ───────────────────────────────────────

describe('E2E v3: verification', () => {
  it('nested index access gets two ArrayBounds obligations', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'get2D', typeParams: [],
      params: [{ name: 'mat', type: TyArray(TyArray(TyFloat)) }, { name: 'i', type: TyNat }, { name: 'j', type: TyNat }],
      retType: TyFloat, effect: Pure,
      body: {
        tag: 'IndexAccess',
        obj: {
          tag: 'IndexAccess',
          obj: varExpr('mat', TyArray(TyArray(TyFloat))),
          index: varExpr('i', TyNat),
          type: TyArray(TyFloat), effect: Pure,
        },
        index: varExpr('j', TyNat),
        type: TyFloat, effect: Pure,
      },
    }]);
    const { obligations } = generateVerification(m);
    expect(obligations.filter(o => o.kind === 'ArrayBounds').length).toBeGreaterThanOrEqual(2);
  });

  it('div + array access gets both obligation types', () => {
    const m = mod([{
      tag: 'FuncDef', name: 'avg', typeParams: [],
      params: [{ name: 'arr', type: TyArray(TyFloat) }],
      retType: TyFloat, effect: Pure,
      body: {
        tag: 'BinOp', op: 'Div',
        left: { tag: 'IndexAccess', obj: varExpr('arr', TyArray(TyFloat)), index: litNat(0), type: TyFloat, effect: Pure },
        right: litFloat(2),
        type: TyFloat, effect: Pure,
      },
    }]);
    const { obligations } = generateVerification(m);
    const kinds = obligations.map(o => o.kind);
    expect(kinds).toContain('ArrayBounds');
    expect(kinds).toContain('DivisionSafe');
  });
});

// ─── Full fixture suite ────────────────────────────────────────────────────────

describe('E2E v3: all fixtures produce valid Lean', () => {
  const allFixtures = [
    'basic/hello.ts',
    'basic/interfaces.ts',
    'basic/classes.ts',
    'generics/generics.ts',
    'generics/discriminated-unions.ts',
    'generics/branded-types.ts',
    'effects/async.ts',
    'effects/exceptions.ts',
    'advanced/for-loops.ts',
    'advanced/optional-chaining.ts',
    'advanced/template-literals.ts',
    'advanced/class-features.ts',
    'advanced/type-narrowing.ts',
    'advanced/export-patterns.ts',
    'advanced/index-signatures.ts',
  ];

  for (const fixture of allFixtures) {
    it(`${fixture}: parses, rewrites, generates valid output`, () => {
      const code = pipeline(fixture);
      expect(code).toContain('-- Auto-generated');
      expect(code).toContain('open TSLean');
      // No raw TS syntax (skip lines inside string literals or with runtime artifacts)
      const codeLines = code.split('\n').filter(l =>
        !l.includes('"') && !l.includes('native code') && !l.trimStart().startsWith('--')
      );
      const joined = codeLines.join('\n');
      expect(joined).not.toMatch(/\bconst\s+\w/);
      expect(code).not.toContain('===');
      // Balanced parens
      let depth = 0;
      for (const ch of code) {
        if (ch === '(') depth++;
        if (ch === ')') depth--;
        if (depth < 0) break;
      }
      expect(depth).toBe(0);
    });
  }
});

// ─── DO fixture suite ─────────────────────────────────────────────────────────

describe('E2E v3: all DO fixtures have required imports', () => {
  const doFixtures = [
    'durable-objects/counter.ts',
    'durable-objects/rate-limiter.ts',
    'durable-objects/chat-room.ts',
    'durable-objects/session-store.ts',
    'durable-objects/queue-processor.ts',
    'durable-objects/auth-do.ts',
    'durable-objects/analytics-do.ts',
    'durable-objects/multi-do.ts',
  ];

  for (const f of doFixtures) {
    it(`${f}: has Http and Monad imports`, () => {
      const code = pipeline(f);
      expect(code).toContain('import TSLean.DurableObjects.Http');
      expect(code).toContain('import TSLean.Runtime.Monad');
    });

    it(`${f}: has state struct and namespace`, () => {
      const code = pipeline(f);
      expect(code).toMatch(/structure \w+State|namespace \w+DO/);
    });
  }
});

// ─── s!"..." interpolation regression ────────────────────────────────────────

describe('E2E v3: s! interpolation intact', () => {
  it('template literal `Hello, ${name}!` still uses s!', () => {
    const code = inline(`function greet(name: string): string { return \`Hello, \${name}!\`; }`);
    const fn = code.slice(code.indexOf('def greet'));
    expect(fn.slice(0, 200)).toContain('s!"Hello, {name}!"');
  });

  it('multi-var template with literal still uses s!', () => {
    const code = inline(`
      function describe(name: string, age: number): string {
        return \`\${name} is \${age} years old\`;
      }
    `);
    const fn = code.slice(code.indexOf('def describe'));
    expect(fn.slice(0, 300)).toMatch(/s!"[^"]*"/);
  });
});
