/**
 * Unit tests for LeanAST types and printer.
 *
 * Tests that the printer produces syntactically correct Lean 4 code
 * for every AST node type. Each test constructs a LeanAST node and
 * verifies the printed output matches expected Lean syntax.
 */

import { describe, it, expect } from 'vitest';
import { printFile, printDeclStr, printExprStr, printTyStr } from '../src/codegen/printer.js';
import type {
  LeanFile, LeanDecl, LeanExpr, LeanTy, LeanPat,
} from '../src/codegen/lean-ast.js';

// ─── Type printing ──────────────────────────────────────────────────────────────

describe('LeanAST type printing', () => {
  it('prints simple type names', () => {
    expect(printTyStr({ tag: 'TyName', name: 'String' })).toBe('String');
    expect(printTyStr({ tag: 'TyName', name: 'Nat' })).toBe('Nat');
    expect(printTyStr({ tag: 'TyName', name: 'Bool' })).toBe('Bool');
  });

  it('prints type application', () => {
    const t: LeanTy = {
      tag: 'TyApp',
      fn: { tag: 'TyName', name: 'Array' },
      args: [{ tag: 'TyName', name: 'String' }],
    };
    expect(printTyStr(t)).toBe('Array String');
  });

  it('prints nested type application with parens', () => {
    const t: LeanTy = {
      tag: 'TyApp',
      fn: { tag: 'TyName', name: 'Array' },
      args: [{
        tag: 'TyApp',
        fn: { tag: 'TyName', name: 'Option' },
        args: [{ tag: 'TyName', name: 'String' }],
      }],
    };
    expect(printTyStr(t)).toBe('Array (Option String)');
  });

  it('prints arrow types', () => {
    const t: LeanTy = {
      tag: 'TyArrow',
      params: [{ tag: 'TyName', name: 'String' }, { tag: 'TyName', name: 'Nat' }],
      ret: { tag: 'TyName', name: 'Bool' },
    };
    expect(printTyStr(t)).toBe('String → Nat → Bool');
  });

  it('prints tuple types', () => {
    const t: LeanTy = {
      tag: 'TyTuple',
      elems: [{ tag: 'TyName', name: 'String' }, { tag: 'TyName', name: 'Nat' }],
    };
    expect(printTyStr(t)).toBe('(String × Nat)');
  });

  it('prints empty tuple as Unit', () => {
    expect(printTyStr({ tag: 'TyTuple', elems: [] })).toBe('Unit');
  });

  it('prints parenthesized types', () => {
    const t: LeanTy = {
      tag: 'TyParen',
      inner: { tag: 'TyName', name: 'String' },
    };
    expect(printTyStr(t)).toBe('(String)');
  });

  it('parenthesizes arrow type args in application', () => {
    const t: LeanTy = {
      tag: 'TyApp',
      fn: { tag: 'TyName', name: 'IO' },
      args: [{
        tag: 'TyArrow',
        params: [{ tag: 'TyName', name: 'String' }],
        ret: { tag: 'TyName', name: 'Nat' },
      }],
    };
    expect(printTyStr(t)).toBe('IO (String → Nat)');
  });
});

// ─── Expression printing ────────────────────────────────────────────────────────

describe('LeanAST expression printing', () => {
  it('prints literals', () => {
    expect(printExprStr({ tag: 'Lit', value: '42' })).toBe('42');
    expect(printExprStr({ tag: 'Lit', value: '"hello"' })).toBe('"hello"');
    expect(printExprStr({ tag: 'Lit', value: 'true' })).toBe('true');
    expect(printExprStr({ tag: 'Lit', value: '()' })).toBe('()');
  });

  it('prints variables', () => {
    expect(printExprStr({ tag: 'Var', name: 'x' })).toBe('x');
    expect(printExprStr({ tag: 'Var', name: 'Array.push' })).toBe('Array.push');
  });

  it('sanitizes keyword identifiers', () => {
    expect(printExprStr({ tag: 'Var', name: 'from' })).toBe('«from»');
    expect(printExprStr({ tag: 'Var', name: 'match' })).toBe('«match»');
  });

  it('prints none and default', () => {
    expect(printExprStr({ tag: 'None' })).toBe('none');
    expect(printExprStr({ tag: 'Default' })).toBe('default');
    expect(printExprStr({ tag: 'Default', ty: { tag: 'TyName', name: 'Nat' } }))
      .toBe('(default : Nat)');
  });

  it('prints sorry with annotation', () => {
    expect(printExprStr({ tag: 'Sorry' })).toBe('sorry');
    expect(printExprStr({ tag: 'Sorry', ty: { tag: 'TyName', name: 'Bool' } }))
      .toBe('(sorry : Bool)');
    expect(printExprStr({ tag: 'Sorry', reason: 'TS API' }))
      .toBe('sorry /- TS API -/');
  });

  it('prints array literals', () => {
    expect(printExprStr({ tag: 'ArrayLit', elems: [] })).toBe('#[]');
    expect(printExprStr({
      tag: 'ArrayLit',
      elems: [{ tag: 'Lit', value: '1' }, { tag: 'Lit', value: '2' }],
    })).toBe('#[1, 2]');
  });

  it('prints function application', () => {
    const e: LeanExpr = {
      tag: 'App',
      fn: { tag: 'Var', name: 'greet' },
      args: [{ tag: 'Lit', value: '"World"' }],
    };
    expect(printExprStr(e)).toBe('greet "World"');
  });

  it('prints lambda', () => {
    const e: LeanExpr = {
      tag: 'Lam',
      params: ['x', 'y'],
      body: { tag: 'BinOp', op: '+', left: { tag: 'Var', name: 'x' }, right: { tag: 'Var', name: 'y' } },
    };
    expect(printExprStr(e)).toBe('fun x y => x + y');
  });

  it('prints let binding', () => {
    const e: LeanExpr = {
      tag: 'Let',
      name: 'x',
      value: { tag: 'Lit', value: '42' },
      body: { tag: 'Var', name: 'x' },
    };
    expect(printExprStr(e)).toBe('let x := 42\nx');
  });

  it('prints monadic bind', () => {
    const e: LeanExpr = {
      tag: 'Bind',
      name: 'result',
      value: { tag: 'App', fn: { tag: 'Var', name: 'fetchData' }, args: [] },
      body: { tag: 'App', fn: { tag: 'Var', name: 'pure' }, args: [{ tag: 'Var', name: 'result' }] },
    };
    expect(printExprStr(e)).toBe('let result ← fetchData\npure result');
  });

  it('prints if-then-else', () => {
    const e: LeanExpr = {
      tag: 'If',
      cond: { tag: 'Var', name: 'b' },
      then_: { tag: 'Lit', value: '1' },
      else_: { tag: 'Lit', value: '0' },
    };
    const result = printExprStr(e);
    expect(result).toContain('if b then');
    expect(result).toContain('1');
    expect(result).toContain('else');
    expect(result).toContain('0');
  });

  it('prints match expression', () => {
    const e: LeanExpr = {
      tag: 'Match',
      scrutinee: { tag: 'Var', name: 's' },
      arms: [
        { pat: { tag: 'PCtor', name: 'Circle', args: [{ tag: 'PVar', name: 'r' }] },
          body: { tag: 'Var', name: 'r' } },
        { pat: { tag: 'PWild' },
          body: { tag: 'Lit', value: '0' } },
      ],
    };
    const result = printExprStr(e);
    expect(result).toContain('match s with');
    expect(result).toContain('| .Circle r => r');
    expect(result).toContain('| _ => 0');
  });

  it('prints do notation', () => {
    const e: LeanExpr = {
      tag: 'Do',
      body: {
        tag: 'Seq',
        stmts: [
          { tag: 'Bind', name: 'x', value: { tag: 'Var', name: 'getLine' },
            body: { tag: 'Pure', value: { tag: 'Var', name: 'x' } } },
        ],
      },
    };
    const result = printExprStr(e);
    expect(result).toContain('do');
    expect(result).toContain('let x ← getLine');
    expect(result).toContain('pure x');
  });

  it('prints struct literal', () => {
    const e: LeanExpr = {
      tag: 'StructLit',
      fields: [
        { name: 'x', value: { tag: 'Lit', value: '1' } },
        { name: 'y', value: { tag: 'Lit', value: '2' } },
      ],
    };
    expect(printExprStr(e)).toBe('{ x := 1, y := 2 }');
  });

  it('prints struct update', () => {
    const e: LeanExpr = {
      tag: 'StructUpdate',
      base: { tag: 'Var', name: 's' },
      fields: [{ name: 'count', value: { tag: 'Lit', value: '0' } }],
    };
    expect(printExprStr(e)).toBe('{ s with count := 0 }');
  });

  it('prints string interpolation', () => {
    const e: LeanExpr = {
      tag: 'SInterp',
      parts: [
        { tag: 'Str', value: 'Hello, ' },
        { tag: 'Expr', expr: { tag: 'Var', name: 'name' } },
        { tag: 'Str', value: '!' },
      ],
    };
    expect(printExprStr(e)).toBe('s!"Hello, {name}!"');
  });

  it('prints modify', () => {
    const e: LeanExpr = {
      tag: 'Modify',
      fn: {
        tag: 'Lam',
        params: ['s'],
        body: { tag: 'StructUpdate', base: { tag: 'Var', name: 's' },
                fields: [{ name: 'count', value: { tag: 'Lit', value: '0' } }] },
      },
    };
    expect(printExprStr(e)).toBe('modify (fun s => { s with count := 0 })');
  });

  it('prints binary and unary operators', () => {
    const binop: LeanExpr = {
      tag: 'BinOp', op: '+',
      left: { tag: 'Var', name: 'a' },
      right: { tag: 'Var', name: 'b' },
    };
    expect(printExprStr(binop)).toBe('a + b');

    const unop: LeanExpr = { tag: 'UnOp', op: '!', operand: { tag: 'Var', name: 'x' } };
    expect(printExprStr(unop)).toBe('!x');
  });

  it('prints field access', () => {
    const e: LeanExpr = {
      tag: 'FieldAccess',
      obj: { tag: 'Var', name: 'self' },
      field: 'count',
    };
    expect(printExprStr(e)).toBe('self.count');
  });

  it('prints type annotation', () => {
    const e: LeanExpr = {
      tag: 'TypeAnnot',
      expr: { tag: 'Lit', value: '0' },
      ty: { tag: 'TyName', name: 'Float' },
    };
    expect(printExprStr(e)).toBe('(0 : Float)');
  });

  it('prints panic', () => {
    expect(printExprStr({ tag: 'Panic', msg: 'unreachable' })).toBe('panic! "unreachable"');
  });
});

// ─── Declaration printing ───────────────────────────────────────────────────────

describe('LeanAST declaration printing', () => {
  it('prints import', () => {
    expect(printDeclStr({ tag: 'Import', module: 'TSLean.Runtime.Basic' }))
      .toBe('import TSLean.Runtime.Basic');
  });

  it('prints open', () => {
    expect(printDeclStr({ tag: 'Open', namespaces: ['TSLean', 'TSLean.DO'] }))
      .toBe('open TSLean TSLean.DO');
  });

  it('prints simple def', () => {
    const d: LeanDecl = {
      tag: 'Def',
      partial: false,
      name: 'greet',
      tyParams: [],
      params: [{ name: 'name', ty: { tag: 'TyName', name: 'String' } }],
      retTy: { tag: 'TyName', name: 'String' },
      body: {
        tag: 'SInterp',
        parts: [
          { tag: 'Str', value: 'Hello, ' },
          { tag: 'Expr', expr: { tag: 'Var', name: 'name' } },
          { tag: 'Str', value: '!' },
        ],
      },
    };
    const result = printDeclStr(d);
    expect(result).toContain('def greet (name : String) : String :=');
    expect(result).toContain('s!"Hello, {name}!"');
  });

  it('prints partial def', () => {
    const d: LeanDecl = {
      tag: 'Def',
      partial: true,
      name: 'factorial',
      tyParams: [],
      params: [{ name: 'n', ty: { tag: 'TyName', name: 'Float' } }],
      retTy: { tag: 'TyName', name: 'Float' },
      body: {
        tag: 'If',
        cond: { tag: 'BinOp', op: '<=', left: { tag: 'Var', name: 'n' }, right: { tag: 'Lit', value: '0' } },
        then_: { tag: 'Lit', value: '1' },
        else_: { tag: 'BinOp', op: '*',
          left: { tag: 'Var', name: 'n' },
          right: { tag: 'App', fn: { tag: 'Var', name: 'factorial' },
                   args: [{ tag: 'Paren', inner: { tag: 'BinOp', op: '-',
                     left: { tag: 'Var', name: 'n' }, right: { tag: 'Lit', value: '1' } } }] } },
      },
    };
    const result = printDeclStr(d);
    expect(result).toContain('partial def factorial (n : Float) : Float :=');
    expect(result).toContain('if n <= 0 then');
  });

  it('prints def with type parameters', () => {
    const d: LeanDecl = {
      tag: 'Def',
      partial: false,
      name: 'mapEither',
      tyParams: [
        { name: 'L', explicit: false },
        { name: 'R', explicit: false },
        { name: 'S', explicit: false },
      ],
      params: [
        { name: 'e', ty: { tag: 'TyApp', fn: { tag: 'TyName', name: 'Either' },
                           args: [{ tag: 'TyName', name: 'L' }, { tag: 'TyName', name: 'R' }] } },
        { name: 'f', ty: { tag: 'TyArrow', params: [{ tag: 'TyName', name: 'R' }],
                           ret: { tag: 'TyName', name: 'S' } } },
      ],
      retTy: { tag: 'TyApp', fn: { tag: 'TyName', name: 'Either' },
               args: [{ tag: 'TyName', name: 'L' }, { tag: 'TyName', name: 'S' }] },
      body: { tag: 'Sorry' },
    };
    const result = printDeclStr(d);
    expect(result).toContain('{L : Type}');
    expect(result).toContain('{R : Type}');
    expect(result).toContain('{S : Type}');
    expect(result).toContain('(e : Either L R)');
    expect(result).toContain('(f : R → S)');
    expect(result).toContain(': Either L S :=');
  });

  it('prints structure', () => {
    const d: LeanDecl = {
      tag: 'Structure',
      name: 'Point',
      tyParams: [],
      fields: [
        { name: 'x', ty: { tag: 'TyName', name: 'Float' } },
        { name: 'y', ty: { tag: 'TyName', name: 'Float' } },
      ],
      deriving: ['Repr', 'BEq', 'Inhabited'],
    };
    const result = printDeclStr(d);
    expect(result).toContain('structure Point where');
    expect(result).toContain('mk ::');
    expect(result).toContain('x : Float');
    expect(result).toContain('y : Float');
    expect(result).toContain('deriving Repr, BEq, Inhabited');
  });

  it('prints generic structure', () => {
    const d: LeanDecl = {
      tag: 'Structure',
      name: 'Pair',
      tyParams: [
        { name: 'A', explicit: true },
        { name: 'B', explicit: true },
      ],
      fields: [
        { name: 'fst', ty: { tag: 'TyName', name: 'A' } },
        { name: 'snd', ty: { tag: 'TyName', name: 'B' } },
      ],
      deriving: ['Repr', 'BEq', 'Inhabited'],
    };
    const result = printDeclStr(d);
    expect(result).toContain('structure Pair (A : Type) (B : Type) where');
  });

  it('prints inductive', () => {
    const d: LeanDecl = {
      tag: 'Inductive',
      name: 'Shape',
      tyParams: [],
      ctors: [
        { name: 'Circle', fields: [{ name: 'radius', ty: { tag: 'TyName', name: 'Float' } }] },
        { name: 'Rectangle', fields: [
          { name: 'width', ty: { tag: 'TyName', name: 'Float' } },
          { name: 'height', ty: { tag: 'TyName', name: 'Float' } },
        ]},
        { name: 'Triangle', fields: [
          { name: 'base', ty: { tag: 'TyName', name: 'Float' } },
          { name: 'height', ty: { tag: 'TyName', name: 'Float' } },
        ]},
      ],
      deriving: ['Repr', 'BEq', 'Inhabited'],
    };
    const result = printDeclStr(d);
    expect(result).toContain('inductive Shape where');
    expect(result).toContain('| Circle (radius : Float)');
    expect(result).toContain('| Rectangle (width : Float) (height : Float)');
    expect(result).toContain('deriving Repr, BEq, Inhabited');
  });

  it('prints inductive with no-arg constructors', () => {
    const d: LeanDecl = {
      tag: 'Inductive',
      name: 'Color',
      tyParams: [],
      ctors: [
        { name: 'Red', fields: [] },
        { name: 'Green', fields: [] },
        { name: 'Blue', fields: [] },
      ],
      deriving: ['Repr', 'BEq', 'Inhabited'],
    };
    const result = printDeclStr(d);
    expect(result).toContain('| Red');
    expect(result).toContain('| Green');
    expect(result).toContain('| Blue');
  });

  it('prints abbrev', () => {
    const d: LeanDecl = {
      tag: 'Abbrev',
      name: 'UserId',
      tyParams: [],
      body: { tag: 'TyName', name: 'String' },
    };
    expect(printDeclStr(d)).toBe('abbrev UserId := String');
  });

  it('prints namespace', () => {
    const d: LeanDecl = {
      tag: 'Namespace',
      name: 'MyModule',
      decls: [
        { tag: 'Def', partial: false, name: 'x', tyParams: [], params: [],
          retTy: { tag: 'TyName', name: 'Nat' },
          body: { tag: 'Lit', value: '42' } },
      ],
    };
    const result = printDeclStr(d);
    expect(result).toContain('namespace MyModule');
    expect(result).toContain('def x : Nat :=');
    expect(result).toContain('end MyModule');
  });

  it('prints mutual block', () => {
    const d: LeanDecl = {
      tag: 'Mutual',
      decls: [
        { tag: 'Inductive', name: 'A', tyParams: [], ctors: [
          { name: 'mkA', fields: [{ name: 'b', ty: { tag: 'TyName', name: 'B' } }] },
        ], deriving: [] },
        { tag: 'Inductive', name: 'B', tyParams: [], ctors: [
          { name: 'mkB', fields: [{ name: 'a', ty: { tag: 'TyName', name: 'A' } }] },
        ], deriving: [] },
      ],
    };
    const result = printDeclStr(d);
    expect(result).toContain('mutual');
    expect(result).toContain('inductive A where');
    expect(result).toContain('inductive B where');
    expect(result).toContain('end');
  });

  it('prints doc comment', () => {
    const d: LeanDecl = {
      tag: 'Def',
      partial: false,
      name: 'greet',
      tyParams: [],
      params: [{ name: 'name', ty: { tag: 'TyName', name: 'String' } }],
      retTy: { tag: 'TyName', name: 'String' },
      body: { tag: 'Var', name: 'name' },
      docComment: 'Greet someone by name.',
    };
    const result = printDeclStr(d);
    expect(result).toContain('/-- Greet someone by name. -/');
  });

  it('prints def with type param constraints', () => {
    const d: LeanDecl = {
      tag: 'Def',
      partial: false,
      name: 'foo',
      tyParams: [{ name: 'T', explicit: false, constraints: ['Inhabited'] }],
      params: [{ name: 'x', ty: { tag: 'TyName', name: 'T' } }],
      retTy: { tag: 'TyName', name: 'T' },
      body: { tag: 'Default' },
    };
    const result = printDeclStr(d);
    expect(result).toContain('{T : Type} [Inhabited T]');
  });

  it('prints instance', () => {
    const d: LeanDecl = {
      tag: 'Instance',
      typeClass: 'ToString',
      args: [{ tag: 'TyName', name: 'MyType' }],
      methods: [{
        name: 'toString',
        params: [{ name: 'x', ty: { tag: 'TyName', name: 'MyType' } }],
        body: { tag: 'Lit', value: '"MyType"' },
      }],
    };
    const result = printDeclStr(d);
    expect(result).toContain('instance : ToString MyType where');
    expect(result).toContain('toString (x : MyType) := "MyType"');
  });

  it('prints theorem', () => {
    const d: LeanDecl = {
      tag: 'Theorem',
      name: 'foo_correct',
      statement: 'True',
      proof: 'trivial',
    };
    const result = printDeclStr(d);
    expect(result).toContain('theorem foo_correct : True := by');
    expect(result).toContain('trivial');
  });
});

// ─── File printing ──────────────────────────────────────────────────────────────

describe('LeanAST file printing', () => {
  it('prints a complete file', () => {
    const file: LeanFile = {
      banner: 'Auto-generated by ts-lean-transpiler',
      sourcePath: 'hello.ts',
      decls: [
        { tag: 'Import', module: 'TSLean.Runtime.Basic' },
        { tag: 'Import', module: 'TSLean.Runtime.Coercions' },
        { tag: 'Blank' },
        { tag: 'Open', namespaces: ['TSLean'] },
        { tag: 'Blank' },
        { tag: 'Namespace', name: 'TSLean.Generated.Hello', decls: [
          { tag: 'Def', partial: false, name: 'greet', tyParams: [],
            params: [{ name: 'name', ty: { tag: 'TyName', name: 'String' } }],
            retTy: { tag: 'TyName', name: 'String' },
            body: { tag: 'SInterp', parts: [
              { tag: 'Str', value: 'Hello, ' },
              { tag: 'Expr', expr: { tag: 'Var', name: 'name' } },
              { tag: 'Str', value: '!' },
            ]} },
        ]},
      ],
    };
    const result = printFile(file);
    expect(result).toContain('-- Auto-generated by ts-lean-transpiler');
    expect(result).toContain('-- Source: hello.ts');
    expect(result).toContain('import TSLean.Runtime.Basic');
    expect(result).toContain('open TSLean');
    expect(result).toContain('namespace TSLean.Generated.Hello');
    expect(result).toContain('def greet (name : String) : String :=');
    expect(result).toContain('s!"Hello, {name}!"');
    expect(result).toContain('end TSLean.Generated.Hello');
  });
});

// ─── Edge cases ─────────────────────────────────────────────────────────────────

describe('LeanAST edge cases', () => {
  it('prints def with where clause', () => {
    const d: LeanDecl = {
      tag: 'Def',
      partial: false,
      name: 'main',
      tyParams: [],
      params: [],
      retTy: { tag: 'TyName', name: 'Nat' },
      body: { tag: 'App', fn: { tag: 'Var', name: 'helper' }, args: [{ tag: 'Lit', value: '42' }] },
      where_: [
        { tag: 'Def', partial: false, name: 'helper', tyParams: [],
          params: [{ name: 'n', ty: { tag: 'TyName', name: 'Nat' } }],
          retTy: { tag: 'TyName', name: 'Nat' },
          body: { tag: 'Var', name: 'n' } },
      ],
    };
    const result = printDeclStr(d);
    expect(result).toContain('def main : Nat :=');
    expect(result).toContain('helper 42');
    expect(result).toContain('where');
    expect(result).toContain('def helper');
  });

  it('prints structure with extends', () => {
    const d: LeanDecl = {
      tag: 'Structure',
      name: 'ColorPoint',
      tyParams: [],
      extends_: 'Point',
      fields: [
        { name: 'color', ty: { tag: 'TyName', name: 'String' } },
      ],
      deriving: ['Repr', 'Inhabited'],
    };
    const result = printDeclStr(d);
    expect(result).toContain('structure ColorPoint extends Point where');
  });

  it('prints field with default value', () => {
    const d: LeanDecl = {
      tag: 'Structure',
      name: 'Config',
      tyParams: [],
      fields: [
        { name: 'debug', ty: { tag: 'TyName', name: 'Bool' }, default_: { tag: 'Lit', value: 'false' } },
        { name: 'name', ty: { tag: 'TyName', name: 'String' } },
      ],
      deriving: ['Repr', 'Inhabited'],
    };
    const result = printDeclStr(d);
    expect(result).toContain('debug : Bool := false');
    expect(result).toContain('name : String');
  });

  it('handles let rec', () => {
    const e: LeanExpr = {
      tag: 'Let',
      name: 'loop',
      rec: true,
      value: { tag: 'Lam', params: ['n'], body: { tag: 'Var', name: 'n' } },
      body: { tag: 'App', fn: { tag: 'Var', name: 'loop' }, args: [{ tag: 'Lit', value: '10' }] },
    };
    const result = printExprStr(e);
    expect(result).toContain('let rec loop := fun n => n');
  });

  it('prints sequence', () => {
    const e: LeanExpr = {
      tag: 'Seq',
      stmts: [
        { tag: 'Let', name: 'x', value: { tag: 'Lit', value: '1' }, body: { tag: 'Var', name: 'x' } },
      ],
    };
    const result = printExprStr(e);
    expect(result).toContain('let x := 1');
  });

  it('prints try-catch', () => {
    const e: LeanExpr = {
      tag: 'TryCatch',
      body: { tag: 'Var', name: 'riskyOp' },
      errName: 'err',
      handler: { tag: 'Default' },
    };
    expect(printExprStr(e)).toBe('tryCatch riskyOp (fun err => default)');
  });

  it('prints implicit parameter', () => {
    const d: LeanDecl = {
      tag: 'Def',
      partial: false,
      name: 'id',
      tyParams: [{ name: 'T', explicit: false }],
      params: [{ name: 'x', ty: { tag: 'TyName', name: 'T' }, implicit: true }],
      retTy: { tag: 'TyName', name: 'T' },
      body: { tag: 'Var', name: 'x' },
    };
    const result = printDeclStr(d);
    expect(result).toContain('{x : T}');
  });

  it('prints class', () => {
    const d: LeanDecl = {
      tag: 'Class',
      name: 'Describable',
      tyParams: [{ name: 'T', explicit: false }],
      methods: [
        { name: 'describe', ty: { tag: 'TyArrow', params: [{ tag: 'TyName', name: 'T' }],
                                   ret: { tag: 'TyName', name: 'String' } } },
      ],
    };
    const result = printDeclStr(d);
    expect(result).toContain('class Describable {T : Type} where');
    expect(result).toContain('describe : T → String');
  });

  it('prints standalone instance', () => {
    const d: LeanDecl = {
      tag: 'StandaloneInstance',
      code: 'instance : Inhabited Shape := ⟨sorry⟩',
    };
    expect(printDeclStr(d)).toBe('instance : Inhabited Shape := ⟨sorry⟩');
  });

  it('prints raw code', () => {
    const d: LeanDecl = { tag: 'Raw', code: '#check Nat' };
    expect(printDeclStr(d)).toBe('#check Nat');
  });
});
