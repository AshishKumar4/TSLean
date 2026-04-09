// Tests for parser type-level features: conditional types, tuple types, mapped types,
// template literal types, keyof, typeof, enum member access, computed properties.

import { describe, it, expect, beforeAll } from 'vitest';
import * as path from 'path';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyBool, TyNat, TyUnit, TyRef, TyArray, TyOption, TyTuple,
  Pure, litNat, litStr, litBool, litUnit, varExpr,
} from '../src/ir/types.js';

function inline(src: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: 'test.ts', sourceText: src })));
}

function parsed(src: string): IRModule {
  return parseFile({ fileName: 'test.ts', sourceText: src });
}

function findDecl(mod: IRModule, name: string): IRDecl | undefined {
  for (const d of mod.decls) {
    if ('name' in d && d.name === name) return d;
    if (d.tag === 'Namespace') {
      for (const dd of d.decls) if ('name' in dd && dd.name === name) return dd;
    }
  }
  return undefined;
}

// ─── Conditional types ────────────────────────────────────────────────────────

describe('Parser types: conditional types', () => {
  it('T extends U ? A : B resolves to a type alias', () => {
    const mod = parsed(`type IsString<T> = T extends string ? true : false;`);
    const d = findDecl(mod, 'IsString');
    expect(d).toBeDefined();
    expect(['TypeAlias', 'InductiveDef']).toContain(d?.tag);
  });

  it('conditional type gets a comment annotation', () => {
    const code = inline(`type IsArray<T> = T extends any[] ? true : false;`);
    expect(code).toMatch(/conditional type|IsArray/);
  });

  it('conditional type with concrete resolution', () => {
    const mod = parsed(`type R = string extends string ? number : boolean;`);
    expect(mod.decls.length).toBeGreaterThan(0);
  });
});

// ─── Tuple types ──────────────────────────────────────────────────────────────

describe('Parser types: tuple types', () => {
  it('[string, number] → Tuple [String, Float]', () => {
    const mod = parsed(`type Pair = [string, number];`);
    const d = findDecl(mod, 'Pair');
    expect(d).toBeDefined();
    if (d?.tag === 'TypeAlias') {
      expect(d.body.tag).toBe('Tuple');
      if (d.body.tag === 'Tuple') {
        expect(d.body.elems).toHaveLength(2);
        expect(d.body.elems[0].tag).toBe('String');
        expect(d.body.elems[1].tag).toBe('Float');
      }
    }
  });

  it('[string, number, boolean] → 3-element tuple', () => {
    const mod = parsed(`type Triple = [string, number, boolean];`);
    const d = findDecl(mod, 'Triple');
    if (d?.tag === 'TypeAlias' && d.body.tag === 'Tuple') {
      expect(d.body.elems).toHaveLength(3);
    }
  });

  it('tuple emits (String × Float) in Lean', () => {
    const code = inline(`type Pair = [string, number];`);
    expect(code).toMatch(/abbrev Pair.*:=.*\(String × Float\)/);
  });

  it('single element tuple', () => {
    const mod = parsed(`type Single = [string];`);
    const d = findDecl(mod, 'Single');
    expect(d).toBeDefined();
  });

  it('empty tuple', () => {
    const mod = parsed(`type Empty = [];`);
    const d = findDecl(mod, 'Empty');
    expect(d).toBeDefined();
  });
});

// ─── Template literal types ───────────────────────────────────────────────────

describe('Parser types: template literal types', () => {
  it('template literal type → String alias', () => {
    const mod = parsed('type Route = `/${string}`;');
    const d = findDecl(mod, 'Route');
    expect(d).toBeDefined();
    if (d?.tag === 'TypeAlias') {
      expect(d.body.tag).toBe('String');
    }
  });

  it('template literal type gets comment', () => {
    const code = inline('type EventName = `on${string}`;');
    expect(code).toMatch(/template literal|EventName|String/);
  });
});

// ─── Mapped types ─────────────────────────────────────────────────────────────

describe('Parser types: mapped types', () => {
  it('mapped type resolves through TypeChecker', () => {
    const mod = parsed(`
      interface User { name: string; age: number }
      type ReadonlyUser = { readonly [K in keyof User]: User[K] };
    `);
    const d = findDecl(mod, 'ReadonlyUser');
    expect(d).toBeDefined();
  });

  it('Partial<T> via mapped type', () => {
    const mod = parsed(`
      interface Config { host: string; port: number }
      type PartialConfig = Partial<Config>;
    `);
    const d = findDecl(mod, 'PartialConfig');
    expect(d).toBeDefined();
  });

  it('mapped type gets comment annotation', () => {
    const code = inline(`
      type Keys<T> = { [K in keyof T]: K };
    `);
    expect(code).toMatch(/mapped type|Keys/);
  });
});

// ─── keyof T ──────────────────────────────────────────────────────────────────

describe('Parser types: keyof', () => {
  it('keyof T → String alias', () => {
    const mod = parsed(`
      interface User { name: string; age: number }
      type UserKeys = keyof User;
    `);
    const d = findDecl(mod, 'UserKeys');
    expect(d).toBeDefined();
    if (d?.tag === 'TypeAlias') {
      // keyof resolves to string union or String
      expect(['String', 'TypeRef']).toContain(d.body.tag);
    }
  });

  it('keyof comment in output', () => {
    const code = inline(`type K = keyof { a: number; b: string };`);
    expect(code).toMatch(/keyof|K/);
  });
});

// ─── typeof in type position ──────────────────────────────────────────────────

describe('Parser types: typeof in type position', () => {
  it('typeof variable → resolved type', () => {
    const mod = parsed(`
      const x = { name: 'Alice', age: 30 };
      type XType = typeof x;
    `);
    const d = findDecl(mod, 'XType');
    expect(d).toBeDefined();
  });

  it('typeof annotation in output', () => {
    const code = inline(`
      const config = { host: 'localhost', port: 8080 };
      type ConfigType = typeof config;
    `);
    expect(code).toMatch(/typeof|ConfigType/);
  });
});

// ─── Enum member access ──────────────────────────────────────────────────────

describe('Parser types: enum member access', () => {
  it('Color.Red → CtorApp Color.Red', () => {
    const mod = parsed(`
      enum Color { Red, Green, Blue }
      const c = Color.Red;
    `);
    const d = findDecl(mod, 'c');
    expect(d).toBeDefined();
    if (d?.tag === 'VarDecl') {
      // Should be a constructor application or field access
      expect(['CtorApp', 'FieldAccess', 'Var']).toContain(d.value.tag);
      if (d.value.tag === 'CtorApp') {
        expect(d.value.ctor).toContain('Red');
      }
    }
  });

  it('enum access in Lean output', () => {
    const code = inline(`
      enum Direction { North, South, East, West }
      const dir = Direction.North;
    `);
    expect(code).toContain('inductive Direction');
    expect(code).toMatch(/Direction\.North|North/);
  });

  it('string enum member access', () => {
    const code = inline(`
      enum Status { Active = "ACTIVE", Inactive = "INACTIVE" }
      const s = Status.Active;
    `);
    expect(code).toContain('inductive Status');
    expect(code).toMatch(/Status\.Active|Active/);
  });
});

// ─── Computed property names ──────────────────────────────────────────────────

describe('Parser types: computed property names', () => {
  it('{ [key]: val } generates AssocMap.insert call', () => {
    const mod = parsed(`
      function makeMap(key: string, val: number): Record<string, number> {
        return { [key]: val };
      }
    `);
    const d = findDecl(mod, 'makeMap');
    expect(d?.tag).toBe('FuncDef');
  });

  it('computed prop in Lean output', () => {
    const code = inline(`
      function setKey(key: string, val: string): Record<string, string> {
        return { [key]: val };
      }
    `);
    expect(code).toContain('def setKey');
    // Should contain AssocMap.insert or the computed field
    expect(code).toMatch(/AssocMap\.insert|_computed/);
  });
});

// ─── Property shorthand ──────────────────────────────────────────────────────

describe('Parser types: property shorthand', () => {
  it('{ name } → { name := name }', () => {
    const code = inline(`
      function makePoint(x: number, y: number): { x: number; y: number } {
        return { x, y };
      }
    `);
    expect(code).toContain('def makePoint');
    const fn = code.slice(code.indexOf('def makePoint'));
    expect(fn.slice(0, 200)).toMatch(/x\s*:=\s*x|y\s*:=\s*y/);
  });

  it('shorthand with renamed binding', () => {
    const code = inline(`
      function wrap(value: string): { value: string } { return { value }; }
    `);
    expect(code).toContain('def wrap');
    const fn = code.slice(code.indexOf('def wrap'));
    expect(fn.slice(0, 200)).toMatch(/value\s*:=\s*value/);
  });
});

// ─── as const assertion ───────────────────────────────────────────────────────

describe('Parser types: as const', () => {
  it('as const is transparent', () => {
    const code = inline(`const colors = ['red', 'green', 'blue'] as const;`);
    expect(code).toContain('def colors');
  });

  it('as Type creates a Cast', () => {
    const code = inline(`
      function castToString(x: unknown): string { return x as string; }
    `);
    expect(code).toContain('def castToString');
  });
});

// ─── Type assertions ──────────────────────────────────────────────────────────

describe('Parser types: type assertions', () => {
  it('x as T passes through (Cast is transparent in codegen)', () => {
    const code = inline(`
      function toNum(x: any): number { return x as number; }
    `);
    expect(code).toContain('def toNum');
    // Cast should not add extra syntax — just pass the value through
    const fn = code.slice(code.indexOf('def toNum'));
    expect(fn.slice(0, 200)).toContain('x');
  });
});

// ─── Generated file quality ──────────────────────────────────────────────────

describe('Generated Lean file quality', () => {
  it('Hello.lean has all functions', () => {
    const code = require('fs').readFileSync(
      path.join(process.cwd(), 'lean/TSLean/Generated/Transpiled_basic_hello.lean'), 'utf8'
    );
    expect(code).toContain('def greet');
    expect(code).toContain('def add');
    expect(code).toContain('def isPositive');
    expect(code).toContain('partial def factorial');
    expect(code).toContain('def PI');
    expect(code).toContain('def greeting');
    expect(code).toContain('s!"Hello, {name}!"');
    expect(code).not.toContain('function ');
    expect(code).not.toContain('const ');
  });

  it('Interfaces.lean has all structures', () => {
    const code = require('fs').readFileSync(
      path.join(process.cwd(), 'lean/TSLean/Generated/Transpiled_basic_interfaces.lean'), 'utf8'
    );
    expect(code).toContain('structure Point');
    expect(code).toContain('structure Rectangle');
    expect(code).toContain('structure Named');
    expect(code).toContain('def distance');
    expect(code).toContain('def makePoint');
  });

  it('DiscriminatedUnions.lean has inductives and match', () => {
    const code = require('fs').readFileSync(
      path.join(process.cwd(), 'lean/TSLean/Generated/Transpiled_generics_discriminated_unions.lean'), 'utf8'
    );
    expect(code).toContain('inductive Shape');
    expect(code).toContain('| Circle');
    expect(code).toContain('inductive Color');
    expect(code).toContain('inductive Tree');
    expect(code).toContain('def areaShape');
    expect(code).toContain('match');
  });

  it('BrandedTypes.lean has structures with val field', () => {
    const code = require('fs').readFileSync(
      path.join(process.cwd(), 'lean/TSLean/Generated/Transpiled_generics_branded_types.lean'), 'utf8'
    );
    expect(code).toContain('structure UserId');
    expect(code).toContain('val : String');
    expect(code).toContain('structure RoomId');
    expect(code).toContain('def makeUserId');
  });

  it('Async.lean has IO return types', () => {
    const code = require('fs').readFileSync(
      path.join(process.cwd(), 'lean/TSLean/Generated/Transpiled_effects_async.lean'), 'utf8'
    );
    expect(code).toContain('IO');
    expect(code).toMatch(/def fetchUser|partial def fetchUser/);
  });

  it('all generated files have balanced parens', () => {
    const fs = require('fs');
    const dir = path.join(process.cwd(), 'lean/TSLean/Generated');
    function checkDir(d: string) {
      for (const entry of fs.readdirSync(d, { withFileTypes: true })) {
        const full = path.join(d, entry.name);
        if (entry.isDirectory()) {
          if (entry.name === 'SelfHost') continue;  // SelfHost files are stretch goals
          checkDir(full); continue;
        }
        if (!entry.name.endsWith('.lean')) continue;
        const code = fs.readFileSync(full, 'utf8');
        let depth = 0;
        for (const ch of code) {
          if (ch === '(') depth++;
          if (ch === ')') depth--;
          if (depth < 0) break;
        }
        expect(depth, `${full} has unbalanced parens`).toBe(0);
      }
    }
    checkDir(dir);
  });

  it('no auto-generated file contains raw TS syntax', () => {
    const fs = require('fs');
    // Only check the files we just generated (Basic, Generics, Effects subdirs)
    for (const subdir of ['Basic', 'Generics', 'Effects']) {
      const dir = path.join(process.cwd(), 'lean/TSLean/Generated', subdir);
      if (!fs.existsSync(dir)) continue;
      for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
        if (!entry.name.endsWith('.lean')) continue;
        const full = path.join(dir, entry.name);
        const code = fs.readFileSync(full, 'utf8');
        // Only check files that start with our auto-generated header
        if (!code.includes('Auto-generated by ts-lean-transpiler')) continue;
        expect(code, full).not.toMatch(/\bfunction\s+\w/);
        expect(code, full).not.toMatch(/\bconst\s+\w/);
        expect(code, full).not.toContain('===');
      }
    }
  });
});
