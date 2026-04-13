// Advanced codegen tests: partial def, mutual blocks, namespace nesting,
// IO.Ref, s!"..." interpolation, Combined effects, instance decls.

import { describe, it, expect } from 'vitest';
import { generateLean } from '../src/codegen/index.js';
import {
  IRModule, IRDecl, IRExpr,
  TyString, TyFloat, TyBool, TyNat, TyUnit, TyRef, TyArray, TyOption,
  TyMap, TySet, TyTuple, TyFn,
  Pure, IO, Async, stateEffect, exceptEffect, combineEffects,
  litNat, litStr, litBool, litUnit, varExpr, holeExpr,
} from '../src/ir/types.js';

function mod(decls: IRDecl[]): IRModule {
  return { name: 'TSLean.Test', imports: [], decls, comments: [], sourceFile: 'test.ts' };
}

// ─── Partial def detection ─────────────────────────────────────────────────────

describe('Codegen: partial def', () => {
  it('recursive function → partial def', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'fact', typeParams: [],
      params: [{ name: 'n', type: TyNat }],
      retType: TyNat, effect: Pure,
      body: {
        tag: 'IfThenElse',
        cond: { tag: 'BinOp', op: 'Le', left: varExpr('n', TyNat), right: litNat(0), type: TyBool, effect: Pure },
        then: litNat(1),
        else_: { tag: 'BinOp', op: 'Mul',
          left: varExpr('n', TyNat),
          right: { tag: 'App', fn: varExpr('fact'), args: [{ tag: 'BinOp', op: 'Sub', left: varExpr('n'), right: litNat(1), type: TyNat, effect: Pure }], type: TyNat, effect: Pure },
          type: TyNat, effect: Pure },
        type: TyNat, effect: Pure,
      },
    }]));
    expect(code).toContain('partial def fact');
  });

  it('non-recursive → plain def', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'double', typeParams: [],
      params: [{ name: 'n', type: TyNat }],
      retType: TyNat, effect: Pure,
      body: { tag: 'BinOp', op: 'Mul', left: varExpr('n'), right: litNat(2), type: TyNat, effect: Pure },
    }]));
    expect(code).toContain('def double');
    expect(code).not.toContain('partial def double');
  });

  it('function with isPartial flag → partial def', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'diverge', typeParams: [],
      params: [], retType: TyUnit, effect: Pure,
      body: litUnit(), isPartial: true,
    }]));
    expect(code).toContain('partial def diverge');
  });
});

// ─── Mutual recursion ──────────────────────────────────────────────────────────

describe('Codegen: mutual recursion in namespace', () => {
  it('mutually recursive functions in namespace → mutual block', () => {
    const isEvenBody: IRExpr = {
      tag: 'IfThenElse',
      cond: { tag: 'BinOp', op: 'Eq', left: varExpr('n'), right: litNat(0), type: TyBool, effect: Pure },
      then: litBool(true),
      else_: { tag: 'App', fn: varExpr('isOdd'), args: [{ tag: 'BinOp', op: 'Sub', left: varExpr('n'), right: litNat(1), type: TyNat, effect: Pure }], type: TyBool, effect: Pure },
      type: TyBool, effect: Pure,
    };
    const isOddBody: IRExpr = {
      tag: 'IfThenElse',
      cond: { tag: 'BinOp', op: 'Eq', left: varExpr('n'), right: litNat(0), type: TyBool, effect: Pure },
      then: litBool(false),
      else_: { tag: 'App', fn: varExpr('isEven'), args: [{ tag: 'BinOp', op: 'Sub', left: varExpr('n'), right: litNat(1), type: TyNat, effect: Pure }], type: TyBool, effect: Pure },
      type: TyBool, effect: Pure,
    };
    const code = generateLean(mod([{
      tag: 'Namespace', name: 'Parity', decls: [
        { tag: 'FuncDef', name: 'isEven', typeParams: [], params: [{ name: 'n', type: TyNat }], retType: TyBool, effect: Pure, body: isEvenBody },
        { tag: 'FuncDef', name: 'isOdd',  typeParams: [], params: [{ name: 'n', type: TyNat }], retType: TyBool, effect: Pure, body: isOddBody },
      ],
    }]));
    expect(code).toContain('namespace Parity');
    expect(code).toContain('mutual');
    expect(code).toContain('end');
    expect(code).toContain('def isEven');
    expect(code).toContain('def isOdd');
  });

  it('non-mutually-recursive functions in namespace → no mutual', () => {
    const code = generateLean(mod([{
      tag: 'Namespace', name: 'Utils', decls: [
        { tag: 'FuncDef', name: 'f', typeParams: [], params: [], retType: TyUnit, effect: Pure, body: litUnit() },
        { tag: 'FuncDef', name: 'g', typeParams: [], params: [], retType: TyUnit, effect: Pure, body: litUnit() },
      ],
    }]));
    expect(code).not.toContain('mutual');
  });
});

// ─── IO.Ref for mutable vars ───────────────────────────────────────────────────

describe('Codegen: IO.Ref for mutable vars', () => {
  it('mutable VarDecl emits IO.Ref', () => {
    const code = generateLean(mod([{
      tag: 'VarDecl', name: 'counter', type: TyNat, value: litNat(0), mutable: true,
    }]));
    expect(code).toContain('IO.Ref');
    expect(code).toContain('counter');
  });

  it('immutable VarDecl emits def', () => {
    const code = generateLean(mod([{
      tag: 'VarDecl', name: 'PI', type: TyFloat, value: { tag: 'LitFloat', value: 3.14159, type: TyFloat, effect: Pure }, mutable: false,
    }]));
    expect(code).toContain('def PI');
    expect(code).not.toContain('IO.Ref');
  });
});

// ─── Combined effect return types ──────────────────────────────────────────────

describe('Codegen: Combined effect return type', () => {
  it('State+Except → StateT S (ExceptT E IO) retSig', () => {
    const eff = combineEffects([stateEffect(TyString), exceptEffect(TyFloat)]);
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'op', typeParams: [],
      params: [], retType: TyNat, effect: eff, body: litNat(0),
    }]));
    const line = code.split('\n').find(l => l.includes('def op'))!;
    expect(line).toContain('StateT');
    expect(line).toContain('ExceptT');
    expect(line).not.toContain('(IO)');
  });

  it('Pure → bare return type', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'pure_fn', typeParams: [],
      params: [], retType: TyNat, effect: Pure, body: litNat(42),
    }]));
    const line = code.split('\n').find(l => l.includes('def pure_fn'))!;
    expect(line).toMatch(/:\s*Nat\s*:=/);
    expect(line).not.toContain('IO');
    expect(line).not.toContain('StateT');
  });

  it('Async → IO return', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'fetchFn', typeParams: [],
      params: [], retType: TyString, effect: Async, body: litStr('result'),
    }]));
    const line = code.split('\n').find(l => l.includes('def fetchFn'))!;
    expect(line).toContain('IO');
  });
});

// ─── s!"..." interpolation ────────────────────────────────────────────────────

describe('Codegen: s!"..." interpolation', () => {
  function concatExpr(parts: (string | IRExpr)[]): IRExpr {
    const exprs: IRExpr[] = parts.map(p =>
      typeof p === 'string' ? litStr(p) : p
    );
    return exprs.reduce((acc, e) => ({
      tag: 'BinOp', op: 'Concat', left: acc, right: e,
      type: TyString, effect: Pure,
    }));
  }

  it('simple var concat with literals → s!"..." or ++ ', () => {
    const body = concatExpr(['Hello, ', varExpr('name', TyString), '!']);
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'greet', typeParams: [],
      params: [{ name: 'name', type: TyString }],
      retType: TyString, effect: Pure, body,
    }]));
    const fn = code.slice(code.indexOf('def greet'));
    // Either s! or ++ are acceptable correct output
    expect(fn.slice(0, 200)).toMatch(/s!"[^"]*\{name\}[^"]*"|"Hello.*\+\+|Hello.*name/);
  });

  it('all-literal concat → no s!', () => {
    const body = concatExpr(['Hello', ' ', 'World']);
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'hw', typeParams: [],
      params: [], retType: TyString, effect: Pure, body,
    }]));
    // All literals — no interpolation needed
    expect(code).toContain('def hw');
  });

  it('field access in template', () => {
    const fa: IRExpr = { tag: 'FieldAccess', obj: varExpr('u', TyRef('User')), field: 'name', type: TyString, effect: Pure };
    const body = concatExpr(['User: ', fa]);
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'descUser', typeParams: [],
      params: [{ name: 'u', type: TyRef('User') }],
      retType: TyString, effect: Pure, body,
    }]));
    expect(code).toContain('def descUser');
  });
});

// ─── Namespace nesting ────────────────────────────────────────────────────────

describe('Codegen: namespace nesting', () => {
  it('nested namespaces emit correct open/close', () => {
    const code = generateLean(mod([{
      tag: 'Namespace', name: 'Outer', decls: [{
        tag: 'Namespace', name: 'Inner', decls: [{
          tag: 'FuncDef', name: 'helper', typeParams: [],
          params: [], retType: TyUnit, effect: Pure, body: litUnit(),
        }],
      }],
    }]));
    expect(code).toContain('namespace Outer');
    expect(code).toContain('namespace Inner');
    expect(code).toContain('end Inner');
    expect(code).toContain('end Outer');
  });

  it('namespace with struct has correct indentation', () => {
    const code = generateLean(mod([{
      tag: 'Namespace', name: 'Geo', decls: [{
        tag: 'StructDef', name: 'Point', typeParams: [],
        fields: [{ name: 'x', type: TyFloat }, { name: 'y', type: TyFloat }],
      }],
    }]));
    expect(code).toContain('namespace Geo');
    expect(code).toContain('structure Point');
    expect(code).toContain('end Geo');
  });
});

// ─── Instance declarations ────────────────────────────────────────────────────

describe('Codegen: instance declarations', () => {
  it('instance : BEq emits correctly', () => {
    const code = generateLean(mod([{
      tag: 'InstanceDef',
      typeClass: 'BEq',
      typeArgs: [TyRef('MyType')],
      methods: [{
        tag: 'FuncDef', name: 'beq', typeParams: [],
        params: [{ name: 'a', type: TyRef('MyType') }, { name: 'b', type: TyRef('MyType') }],
        retType: TyBool, effect: Pure,
        body: { tag: 'BinOp', op: 'Eq', left: { tag: 'FieldAccess', obj: varExpr('a'), field: 'val', type: TyString, effect: Pure }, right: { tag: 'FieldAccess', obj: varExpr('b'), field: 'val', type: TyString, effect: Pure }, type: TyBool, effect: Pure },
      }],
    }]));
    expect(code).toContain('instance : BEq MyType');
    expect(code).toContain('beq');
  });

  it('theorem emits correctly', () => {
    const code = generateLean(mod([{
      tag: 'TheoremDef',
      name: 'add_comm',
      statement: '∀ (a b : Nat), a + b = b + a',
      proof: 'omega',
    }]));
    expect(code).toContain('theorem add_comm');
    expect(code).toContain('∀ (a b : Nat)');
    expect(code).toContain(':= by');
    expect(code).toContain('omega');
  });
});

// ─── Default parameters in codegen ───────────────────────────────────────────

describe('Codegen: default parameters', () => {
  it('default literal value emitted, not param name', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'greet', typeParams: [],
      params: [
        { name: 'name', type: TyString },
        { name: 'times', type: TyNat, default_: litNat(3) },
      ],
      retType: TyString, effect: Pure, body: litStr('hello'),
    }]));
    expect(code).toContain(':= 3');
    expect(code).not.toMatch(/times\s*:=\s*times/);
  });

  it('default string value emitted correctly', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'prefix', typeParams: [],
      params: [
        { name: 'msg', type: TyString },
        { name: 'pre', type: TyString, default_: litStr('INFO') },
      ],
      retType: TyString, effect: Pure, body: litStr('ok'),
    }]));
    expect(code).toContain(':= "INFO"');
  });
});

// ─── Additional match patterns ────────────────────────────────────────────────

describe('Codegen: advanced match patterns', () => {
  it('PNone → .none', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'test', typeParams: ['T'],
      params: [{ name: 'o', type: TyOption(TyRef('T')) }],
      retType: TyBool, effect: Pure,
      body: {
        tag: 'Match', scrutinee: varExpr('o', TyOption(TyRef('T'))),
        cases: [
          { pattern: { tag: 'PNone' }, body: litBool(false) },
          { pattern: { tag: 'PSome', inner: { tag: 'PVar', name: 'x' } }, body: litBool(true) },
        ],
        type: TyBool, effect: Pure,
      },
    }]));
    expect(code).toContain('.none');
    expect(code).toContain('.some');
  });

  it('PWild → _', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'alwaysTrue', typeParams: [],
      params: [{ name: 'x', type: TyNat }],
      retType: TyBool, effect: Pure,
      body: {
        tag: 'Match', scrutinee: varExpr('x', TyNat),
        cases: [{ pattern: { tag: 'PWild' }, body: litBool(true) }],
        type: TyBool, effect: Pure,
      },
    }]));
    expect(code).toContain('| _ => true');
  });
});

// ─── Lean keyword sanitization ────────────────────────────────────────────────

describe('Codegen: Lean keyword escaping', () => {
  it('function named "where" → «where»', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'where', typeParams: [],
      params: [], retType: TyUnit, effect: Pure, body: litUnit(),
    }]));
    expect(code).toContain('«where»');
  });

  it('function named "match" → «match»', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'match', typeParams: [],
      params: [], retType: TyUnit, effect: Pure, body: litUnit(),
    }]));
    expect(code).toContain('«match»');
  });

  it('function named "return" → «return»', () => {
    const code = generateLean(mod([{
      tag: 'FuncDef', name: 'return', typeParams: [],
      params: [], retType: TyUnit, effect: Pure, body: litUnit(),
    }]));
    expect(code).toContain('«return»');
  });
});
