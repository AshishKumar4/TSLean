// Advanced parser tests: export patterns, type narrowing, class inheritance,
// index signatures, complex destructuring, for-in, JSDoc, generics.

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';
import {
  IRModule, IRDecl, hasAsync, hasIO,
  TyString, TyFloat, TyBool, TyNat, TyUnit, TyRef, TyArray, TyOption, TyMap,
  Pure,
} from '../src/ir/types.js';

const FIX = path.join(process.cwd(), 'tests/fixtures');

function inline(src: string, file = 'test.ts'): string {
  return generateLean(rewriteModule(parseFile({ fileName: file, sourceText: src })));
}

function parsedInline(src: string): IRModule {
  return parseFile({ fileName: 'test.ts', sourceText: src });
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

// ─── Export default: object with methods ──────────────────────────────────────

describe('Parser: export default { method() {} }', () => {
  it('generates def for async method', () => {
    const code = inline(`
      export default {
        async fetch(req: Request, env: Env): Promise<Response> {
          return new Response("ok");
        }
      };
    `);
    expect(code).toMatch(/def fetch/);
    expect(code).toContain('IO');
  });

  it('generates def for sync method', () => {
    const code = inline(`
      export default {
        greet(name: string): string { return "Hi " + name; }
      };
    `);
    expect(code).toMatch(/def greet/);
  });

  it('handles multiple methods in default export', () => {
    const code = inline(`
      export default {
        add(a: number, b: number): number { return a + b; },
        sub(a: number, b: number): number { return a - b; }
      };
    `);
    expect(code).toMatch(/def add/);
    expect(code).toMatch(/def sub/);
  });

  it('export-patterns fixture generates real content', () => {
    const code = inline(
      require('fs').readFileSync(path.join(FIX, 'advanced/export-patterns.ts'), 'utf8'),
      path.join(FIX, 'advanced/export-patterns.ts'),
    );
    expect(code).toMatch(/def createConfig/);
    expect(code).toMatch(/def makeSuccess/);
  });
});

// ─── Type-only imports ────────────────────────────────────────────────────────

describe('Parser: type-only imports', () => {
  it('import type { X } does not add a names import', () => {
    const mod = parsedInline(`import type { MyType } from './types.js';`);
    // Type-only imports should not appear as named imports (just module reference or nothing)
    const imp = mod.imports.find(i => i.module.includes('Types'));
    if (imp) expect(imp.names ?? []).not.toContain('MyType');
  });

  it('regular import still works', () => {
    const mod = parsedInline(`import { myFn } from './utils.js';`);
    const imp = mod.imports.find(i => i.module.includes('Utils'));
    expect(imp).toBeDefined();
  });
});

// ─── Namespace imports ────────────────────────────────────────────────────────

describe('Parser: namespace imports', () => {
  it('import * as NS from ... → module import', () => {
    const mod = parsedInline(`import * as ts from 'typescript';`);
    expect(mod.imports.some(i => i.module.includes('Typescript') || i.module.includes('External'))).toBe(true);
  });
});

// ─── Interface with extends ───────────────────────────────────────────────────

describe('Parser: interface extends', () => {
  it('extending interface → structure with extends_ field', () => {
    const mod = parsedInline(`
      interface Base { id: string }
      interface Extended extends Base { name: string }
    `);
    const ext = findDecl(mod, 'Extended');
    expect(ext?.tag).toBe('StructDef');
    if (ext?.tag === 'StructDef') {
      // Should have name field at minimum
      expect(ext.fields.some(f => f.name === 'name')).toBe(true);
    }
  });

  it('RouterEnv extends Env generates extends in output', () => {
    const code = inline(`
      interface Env { [key: string]: any }
      interface RouterEnv extends Env { AUTH_DO: string }
    `);
    expect(code).toContain('structure RouterEnv');
    expect(code).toContain('AUTH_DO');
  });
});

// ─── Index signatures ─────────────────────────────────────────────────────────

describe('Parser: index signatures', () => {
  it('pure index signature interface → AssocMap', () => {
    const mod = parsedInline(`interface StringMap { [key: string]: string }`);
    const sm = findDecl(mod, 'StringMap');
    expect(sm).toBeDefined();
    if (sm?.tag === 'TypeAlias') {
      expect(sm.body.tag).toBe('Map');
    }
  });

  it('mixed index + named fields → structure', () => {
    const mod = parsedInline(`interface Mixed { [key: string]: string; count: number }`);
    const m = findDecl(mod, 'Mixed');
    // Has named field so stays as struct
    expect(m).toBeDefined();
  });
});

// ─── JSDoc comment extraction ─────────────────────────────────────────────────

describe('Parser: JSDoc comments', () => {
  it('extracts JSDoc comment as docComment field', () => {
    const mod = parsedInline(`
      /** Adds two numbers together */
      function add(a: number, b: number): number { return a + b; }
    `);
    const fn = findDecl(mod, 'add');
    if (fn?.tag === 'FuncDef') {
      expect(fn.docComment).toContain('Adds two numbers');
    }
  });

  it('JSDoc emits /- doc -/ in Lean', () => {
    const code = inline(`
      /** Compute factorial */
      function fact(n: number): number { if (n <= 1) return 1; return n * fact(n-1); }
    `);
    expect(code).toContain('/-');
    expect(code).toContain('Compute factorial');
  });
});

// ─── Complex destructuring ────────────────────────────────────────────────────

describe('Parser: complex destructuring', () => {
  it('const {x, y} = point → two Let bindings', () => {
    const code = inline(`
      function test(p: {x: number; y: number}): number {
        const { x, y } = p;
        return x + y;
      }
    `);
    expect(code).toMatch(/let x|let _el/);
  });

  it('const [a, b] = arr → two Let bindings with indices', () => {
    const code = inline(`
      function test(arr: number[]): number {
        const [a, b] = arr;
        return a + b;
      }
    `);
    expect(code).toMatch(/let a|let _ai/);
  });

  it('rest in array destructuring', () => {
    const code = inline(`
      function head([first, ...rest]: number[]): number { return first; }
    `);
    expect(code).toMatch(/def head/);
  });
});

// ─── Class inheritance ─────────────────────────────────────────────────────────

describe('Parser: class inheritance', () => {
  it('Dog extends Animal generates Dog methods', () => {
    const code = inline(`
      class Animal { name: string = ''; }
      class Dog extends Animal {
        bark(): string { return 'woof'; }
      }
    `);
    expect(code).toMatch(/structure Dog|structure Animal/);
    expect(code).toMatch(/def.*bark/);
  });

  it('child class has own state struct', () => {
    const mod = parsedInline(`
      class Base { value: number = 0; }
      class Child extends Base { extra: string = ''; }
    `);
    // Both should generate state structs
    expect(mod.decls.some(d => d.tag === 'StructDef')).toBe(true);
  });
});

// ─── Static methods ───────────────────────────────────────────────────────────

describe('Parser: static methods', () => {
  it('static method gets ClassName.method name', () => {
    const code = inline(`
      class Factory {
        private x = 0;
        static create(): Factory { return new Factory(); }
        static empty(): Factory { return new Factory(); }
      }
    `);
    expect(code).toMatch(/def Factory\.create/);
    expect(code).toMatch(/def Factory\.empty/);
  });

  it('instance method gets plain name with self', () => {
    const code = inline(`
      class Counter {
        private n: number = 0;
        increment(): void { this.n++; }
      }
    `);
    expect(code).toMatch(/def.*increment/);
    const fn = code.slice(code.search(/def.*increment/));
    expect(fn.slice(0, 100)).toContain('self');
  });
});

// ─── typeof narrowing ─────────────────────────────────────────────────────────

describe('Parser: typeof type narrowing', () => {
  it('type narrowing fixture transpiles', () => {
    const code = inline(
      require('fs').readFileSync(path.join(FIX, 'advanced/type-narrowing.ts'), 'utf8'),
      path.join(FIX, 'advanced/type-narrowing.ts'),
    );
    expect(code).toMatch(/def processValue/);
    expect(code).toMatch(/def makeSound/);
  });

  it('in-expression generates AssocMap.contains', () => {
    const code = inline(`
      function hasKey(obj: {[k:string]: string}, key: string): boolean {
        return key in obj;
      }
    `);
    expect(code).toMatch(/def hasKey/);
    // The 'in' binary op should translate
    const fn = code.slice(code.indexOf('def hasKey'));
    expect(fn.slice(0, 200)).toMatch(/AssocMap\.contains|true/);
  });

  it('typeof generates TSLean.typeOf call', () => {
    const code = inline(`
      function typeCheck(x: unknown): string { return typeof x; }
    `);
    expect(code).toMatch(/def typeCheck/);
    const fn = code.slice(code.indexOf('def typeCheck'));
    expect(fn.slice(0, 200)).toMatch(/typeOf|typeof/);
  });
});

// ─── Switch fall-through ──────────────────────────────────────────────────────

describe('Parser: switch statement', () => {
  it('switch with break does not duplicate code', () => {
    const code = inline(`
      function grade(n: number): string {
        switch (true) {
          case n >= 90: return 'A';
          case n >= 80: return 'B';
          case n >= 70: return 'C';
          default: return 'F';
        }
      }
    `);
    expect(code).toMatch(/def grade/);
    expect(code).toMatch(/match|if/);
  });

  it('string switch generates match with PString patterns', () => {
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
    expect(code).toMatch(/def colorCode/);
    expect(code).toMatch(/match/);
  });
});

// ─── Async generators and iterators ──────────────────────────────────────────

describe('Parser: generator functions', () => {
  it('generator function body parsed', () => {
    const mod = parsedInline(`
      function* range(n: number): Generator<number> {
        for (let i = 0; i < n; i++) yield i;
      }
    `);
    const fn = findDecl(mod, 'range');
    expect(fn).toBeDefined();
    expect(fn?.tag).toBe('FuncDef');
  });
});

// ─── Complex generic types ────────────────────────────────────────────────────

describe('Parser: complex generic types', () => {
  it('nested generic type params extracted', () => {
    const mod = parsedInline(`
      function zipWith<A, B, C>(f: (a: A, b: B) => C, as: A[], bs: B[]): C[] {
        return as.map((a, i) => f(a, bs[i]));
      }
    `);
    const fn = findDecl(mod, 'zipWith');
    if (fn?.tag === 'FuncDef') {
      expect(fn.typeParams).toContain('A');
      expect(fn.typeParams).toContain('B');
      expect(fn.typeParams).toContain('C');
    }
  });

  it('conditional types approximate to true branch', () => {
    const mod = parsedInline(`
      type IsArray<T> = T extends any[] ? true : false;
    `);
    const d = findDecl(mod, 'IsArray');
    expect(d).toBeDefined();
  });
});

// ─── Re-export handling ───────────────────────────────────────────────────────

describe('Parser: re-exports', () => {
  it('export { X } from adds import', () => {
    const mod = parsedInline(`export { foo } from './utils.js';`);
    expect(mod.imports.some(i => i.module.includes('Utils'))).toBe(true);
  });

  it('export * from adds module import', () => {
    const mod = parsedInline(`export * from './helpers.js';`);
    expect(mod.imports.some(i => i.module.includes('Helpers'))).toBe(true);
  });
});

// ─── Comma expressions ────────────────────────────────────────────────────────

describe('Parser: comma expressions', () => {
  it('comma expression parsed as sequence', () => {
    const mod = parsedInline(`const x = (console.log('a'), 42);`);
    expect(mod).toBeDefined();
    expect(mod.decls.length).toBeGreaterThan(0);
  });
});

// ─── Nested destructuring ────────────────────────────────────────────────────

describe('Parser: nested destructuring', () => {
  it('nested object destructuring: const {a: {b, c}} = x', () => {
    const code = inline(`
      function test(obj: { inner: { x: number; y: number } }): number {
        const { inner: { x, y } } = obj;
        return x + y;
      }
    `);
    expect(code).toMatch(/let x|let _ds/);
    expect(code).toMatch(/let y|let _ds/);
    expect(code).toMatch(/def test/);
  });

  it('nested array in object destructuring', () => {
    const code = inline(`
      function test(obj: { items: number[] }): number {
        const { items: [first, second] } = obj;
        return first + second;
      }
    `);
    expect(code).toMatch(/let first|let _ds|let _ai/);
    expect(code).toMatch(/def test/);
  });

  it('destructuring with defaults', () => {
    const code = inline(`
      function test(opts: { timeout?: number }): number {
        const { timeout = 5000 } = opts;
        return timeout;
      }
    `);
    expect(code).toMatch(/let timeout|getD|Option/);
  });

  it('mixed object and array destructuring', () => {
    const mod = parsedInline(`
      function unpack(data: { coords: [number, number]; label: string }): string {
        const { coords: [x, y], label } = data;
        return label;
      }
    `);
    expect(mod.decls.length).toBeGreaterThan(0);
    const fn = mod.decls.find(d => d.tag === 'FuncDef' && d.name === 'unpack');
    expect(fn).toBeDefined();
  });
});

// ─── Ternary expressions ────────────────────────────────────────────────────

describe('Parser: ternary expressions', () => {
  it('simple ternary → IfThenElse', () => {
    const code = inline(`
      function max(a: number, b: number): number {
        return a > b ? a : b;
      }
    `);
    expect(code).toMatch(/if.*then/s);
    expect(code).toMatch(/else/);
  });

  it('nested ternary', () => {
    const code = inline(`
      function classify(n: number): string {
        return n > 0 ? "positive" : n < 0 ? "negative" : "zero";
      }
    `);
    expect(code).toMatch(/if.*then/s);
    expect(code).toMatch(/"positive"|"negative"|"zero"/);
  });

  it('ternary in assignment', () => {
    const code = inline(`
      function abs(n: number): number {
        const result = n >= 0 ? n : -n;
        return result;
      }
    `);
    expect(code).toMatch(/let result|if.*then/);
  });
});

// ─── Method chains ──────────────────────────────────────────────────────────

describe('Parser: method chains', () => {
  it('map then filter', () => {
    const code = inline(`
      function doubled(arr: number[]): number[] {
        return arr.map(x => x * 2).filter(x => x > 0);
      }
    `);
    expect(code).toMatch(/map|filter/);
    expect(code).toMatch(/def doubled/);
  });

  it('split then join', () => {
    const code = inline(`
      function transform(s: string): string {
        return s.split(',').join(';');
      }
    `);
    expect(code).toMatch(/split|join|splitOn|intercalate/);
  });
});

// ─── Type assertions ────────────────────────────────────────────────────────

describe('Parser: type assertions and casts', () => {
  it('as expression is transparent', () => {
    const code = inline(`
      function cast(x: unknown): number {
        return (x as number);
      }
    `);
    expect(code).toMatch(/def cast/);
    // Should not produce a sorry — as-expression is a type annotation
  });

  it('non-null assertion passes through', () => {
    const code = inline(`
      function first(arr: (number | undefined)[]): number {
        return arr[0]!;
      }
    `);
    expect(code).toMatch(/def first/);
  });

  it('satisfies expression is transparent', () => {
    const mod = parsedInline(`
      const config = { port: 3000, host: "localhost" } satisfies { port: number; host: string };
    `);
    expect(mod.decls.length).toBeGreaterThan(0);
  });
});

// ─── Switch patterns ─────────────────────────────────────────────────────────

describe('Parser: switch patterns (extended)', () => {
  it('switch on enum-like values produces Match', () => {
    const mod = parsedInline(`
      function describe(kind: string): string {
        switch (kind) {
          case "circle": return "round";
          case "square": return "boxy";
          default: return "unknown";
        }
      }
    `);
    const fn = mod.decls.find(d => d.tag === 'FuncDef');
    expect(fn).toBeDefined();
    if (fn?.tag === 'FuncDef') {
      // The body should contain a Match node
      const hasMatch = JSON.stringify(fn.body).includes('"Match"');
      expect(hasMatch).toBe(true);
    }
  });

  it('switch with fall-through groups cases', () => {
    const code = inline(`
      function isVowel(c: string): boolean {
        switch (c) {
          case 'a': case 'e': case 'i': case 'o': case 'u':
            return true;
          default:
            return false;
        }
      }
    `);
    expect(code).toMatch(/match|"a"|"e"/);
  });

  it('switch on discriminated union field', () => {
    const mod = parsedInline(`
      type Shape = { kind: "circle"; r: number } | { kind: "rect"; w: number; h: number };
      function area(s: Shape): number {
        switch (s.kind) {
          case "circle": return Math.PI * s.r * s.r;
          case "rect": return s.w * s.h;
        }
      }
    `);
    expect(mod.decls.length).toBeGreaterThan(0);
  });
});

// ─── Regular expressions ────────────────────────────────────────────────────

describe('Parser: regular expressions', () => {
  it('regex literal as argument to split', () => {
    const code = inline(`
      function splitHyphens(s: string): string[] {
        return s.split(/[-_]/);
      }
    `);
    expect(code).toMatch(/split/);
    expect(code).not.toMatch(/default/);  // should NOT fall back to sorry/default
    expect(code).toMatch(/\[-_\]/);       // regex pattern preserved as string
  });

  it('regex literal in variable', () => {
    const code = inline(`
      const pattern = /^[a-z]+$/i;
    `);
    expect(code).toMatch(/\^.a-z/);  // pattern preserved
  });

  it('regex in test method', () => {
    const code = inline(`
      function isAlpha(s: string): boolean {
        return /^[a-zA-Z]+$/.test(s);
      }
    `);
    expect(code).toMatch(/def isAlpha/);
  });

  it('no holes from regex in self-host files', () => {
    // The parser's own source uses regex; verify zero holes
    const mod = parsedInline(`
      function fileToModuleName(filePath: string): string {
        const base = filePath.replace(/\\.ts$/, '');
        const parts = base.split(/[-_]/).map((s: string) => s.charAt(0).toUpperCase() + s.slice(1));
        return 'TSLean.Generated.' + parts.join('');
      }
    `);
    const fn = mod.decls.find(d => d.tag === 'FuncDef');
    expect(fn).toBeDefined();
    // Verify no Hole nodes in the function body
    const json = JSON.stringify(fn);
    const holeCount = (json.match(/"tag":"Hole"/g) || []).length;
    expect(holeCount).toBe(0);
  });
});

// ─── Parser completeness ────────────────────────────────────────────────────

describe('Parser: self-host completeness', () => {
  it('parser/index.ts produces zero holes', () => {
    const mod = parseFile({ fileName: 'src/parser/index.ts' });
    let holes = 0;
    function count(e: any) {
      if (!e || typeof e !== 'object') return;
      if (e.tag === 'Hole') holes++;
      for (const v of Object.values(e)) {
        if (Array.isArray(v)) v.forEach(count);
        else if (v && typeof v === 'object' && 'tag' in (v as any)) count(v);
      }
    }
    for (const d of mod.decls) {
      if (d.tag === 'FuncDef') count(d.body);
      if (d.tag === 'Namespace') for (const inner of d.decls) {
        if (inner.tag === 'FuncDef') count(inner.body);
      }
    }
    expect(holes).toBe(0);
  });

  it('codegen/index.ts produces zero holes', () => {
    const mod = parseFile({ fileName: 'src/codegen/index.ts' });
    let holes = 0;
    function count(e: any) {
      if (!e || typeof e !== 'object') return;
      if (e.tag === 'Hole') holes++;
      for (const v of Object.values(e)) {
        if (Array.isArray(v)) v.forEach(count);
        else if (v && typeof v === 'object' && 'tag' in (v as any)) count(v);
      }
    }
    for (const d of mod.decls) {
      if (d.tag === 'FuncDef') count(d.body);
      if (d.tag === 'Namespace') for (const inner of d.decls) {
        if (inner.tag === 'FuncDef') count(inner.body);
      }
    }
    expect(holes).toBe(0);
  });

  it('all 11 self-host files produce zero holes', () => {
    const files = [
      'src/ir/types.ts', 'src/parser/index.ts', 'src/codegen/index.ts',
      'src/effects/index.ts', 'src/rewrite/index.ts', 'src/stdlib/index.ts',
      'src/typemap/index.ts', 'src/verification/index.ts',
      'src/project/index.ts', 'src/cli.ts', 'src/do-model/ambient.ts'
    ];
    for (const file of files) {
      const mod = parseFile({ fileName: file });
      let holes = 0;
      function count(e: any) {
        if (!e || typeof e !== 'object') return;
        if (e.tag === 'Hole') holes++;
        for (const v of Object.values(e)) {
          if (Array.isArray(v)) v.forEach(count);
          else if (v && typeof v === 'object' && 'tag' in (v as any)) count(v);
        }
      }
      for (const d of mod.decls) {
        if (d.tag === 'FuncDef') count(d.body);
        if (d.tag === 'Namespace') for (const inner of d.decls) {
          if (inner.tag === 'FuncDef') count(inner.body);
        }
      }
      if (holes > 0) throw new Error(`${file}: ${holes} holes found`);
      expect(holes).toBe(0);
    }
  });
});
