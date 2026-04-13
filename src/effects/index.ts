// Effect inference: TypeScript AST → algebraic effects.
// Analyses function bodies to determine Pure / IO / Async / Except / State.

import * as ts from 'typescript';
import {
  Effect, IRType, Pure, IO, Async, stateEffect, exceptEffect, combineEffects,
  TyString, TyUnit,
} from '../ir/types.js';

// ─── Public API ──────────────────────────────────────────────────────────────

export function inferNodeEffect(node: ts.Node, checker: ts.TypeChecker): Effect {
  // When called on a function-like node, analyse its body directly so that
  // the "don't recurse into nested functions" guards don't block the top level.
  const target = getFunctionBody(node) ?? node;
  const effects: Effect[] = [];

  if (bodyContainsAwait(target))    effects.push(Async);
  if (bodyContainsThrow(target))    effects.push(exceptEffect(TyString));
  if (bodyContainsMutation(target)) effects.push(stateEffect(TyUnit));
  if (bodyContainsIO(target))       effects.push(IO);

  return combineEffects(effects);
}

export function monadString(effect: Effect, stateTypeName = 'σ'): string {
  switch (effect.tag) {
    case 'Pure':   return 'Id';
    case 'IO':     return 'IO';
    case 'Async':  return 'IO';
    case 'State':  return `StateT ${leanTypeName(effect.stateType)} IO`;
    case 'Except': return `ExceptT ${leanTypeName(effect.errorType)} IO`;
    case 'Combined': {
      const hasS = effect.effects.some(e => e.tag === 'State');
      const hasE = effect.effects.some(e => e.tag === 'Except');
      const se = effect.effects.find((e): e is { tag: 'State'; stateType: IRType } => e.tag === 'State');
      const ee = effect.effects.find((e): e is { tag: 'Except'; errorType: IRType } => e.tag === 'Except');
      const parts: string[] = [];
      if (hasS) parts.push(`StateT ${se ? leanTypeName(se.stateType) : stateTypeName}`);
      if (hasE) parts.push(`ExceptT ${ee ? leanTypeName(ee.errorType) : 'TSError'}`);
      parts.push('IO');
      // Build transformer stack: StateT S (ExceptT E IO)
      // The base monad (IO) must never be wrapped in parens — it would be invalid Lean.
      // We fold right-to-left: each wrapper takes the current inner stack as its last arg.
      // With ['StateT S', 'ExceptT E', 'IO']:
      //   'ExceptT E' + 'IO' → 'ExceptT E IO'
      //   'StateT S' + 'ExceptT E IO' → 'StateT S (ExceptT E IO)'
      if (parts.length === 1) return parts[0];
      return parts.reduceRight((inner, outer) => `${outer} ${inner.includes(' ') ? `(${inner})` : inner}`);
    }
  }
}

export function doMonadType(stateTypeName: string): string {
  return `DOMonad ${stateTypeName}`;
}

// Effect lattice
export function joinEffects(a: Effect, b: Effect): Effect {
  if (a.tag === 'Pure') return b;
  if (b.tag === 'Pure') return a;
  return combineEffects([a, b]);
}

export function effectSubsumes(a: Effect, b: Effect): boolean {
  if (b.tag === 'Pure') return true;
  if (a.tag === b.tag)  return true;
  if (a.tag === 'Combined') return a.effects.some(e => effectSubsumes(e, b));
  return false;
}

// ─── Internal helpers ─────────────────────────────────────────────────────────

function getFunctionBody(node: ts.Node): ts.Node | null {
  if (ts.isFunctionDeclaration(node) || ts.isFunctionExpression(node) ||
      ts.isMethodDeclaration(node))
    return (node as ts.FunctionDeclaration).body ?? null;
  if (ts.isArrowFunction(node)) return (node as ts.ArrowFunction).body;
  if (ts.isVariableStatement(node)) {
    const d = node.declarationList.declarations[0];
    if (d?.initializer && (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer)))
      return getFunctionBody(d.initializer);
  }
  return null;
}

function bodyContainsAwait(node: ts.Node): boolean {
  if (ts.isAwaitExpression(node)) return true;
  // Don't recurse into nested function scopes
  if (isNestedFnScope(node)) return false;
  return node.getChildren().some(bodyContainsAwait);
}

function bodyContainsThrow(node: ts.Node): boolean {
  if (ts.isThrowStatement(node)) return true;
  if (isNestedFnScope(node)) return false;
  return node.getChildren().some(bodyContainsThrow);
}

function bodyContainsMutation(node: ts.Node): boolean {
  if (ts.isBinaryExpression(node) && isAssignOp(node.operatorToken.kind)) return true;
  if (ts.isPrefixUnaryExpression(node)  && isIncrDecr(node.operator))  return true;
  if (ts.isPostfixUnaryExpression(node) && isIncrDecr(node.operator))  return true;
  if (isNestedFnScope(node)) return false;
  return node.getChildren().some(bodyContainsMutation);
}

function bodyContainsIO(node: ts.Node): boolean {
  if (ts.isCallExpression(node)) {
    const t = node.expression.getText();
    if (t.startsWith('console.') || t.startsWith('Date.') ||
        t.startsWith('Math.random') || t === 'fetch' || t.startsWith('crypto.'))
      return true;
  }
  if (isNestedFnScope(node)) return false;
  return node.getChildren().some(bodyContainsIO);
}

function isNestedFnScope(node: ts.Node): boolean {
  return ts.isFunctionDeclaration(node) || ts.isArrowFunction(node) ||
         ts.isFunctionExpression(node)  || ts.isMethodDeclaration(node);
}

function isAssignOp(kind: ts.SyntaxKind): boolean {
  return kind === ts.SyntaxKind.EqualsToken ||
    kind === ts.SyntaxKind.PlusEqualsToken  || kind === ts.SyntaxKind.MinusEqualsToken ||
    kind === ts.SyntaxKind.AsteriskEqualsToken || kind === ts.SyntaxKind.SlashEqualsToken ||
    kind === ts.SyntaxKind.PercentEqualsToken;
}

function isIncrDecr(kind: ts.SyntaxKind): boolean {
  return kind === ts.SyntaxKind.PlusPlusToken || kind === ts.SyntaxKind.MinusMinusToken;
}

function leanTypeName(t: IRType): string {
  switch (t.tag) {
    case 'String': return 'String';
    case 'Float':  return 'Float';
    case 'Nat':    return 'Nat';
    case 'Int':    return 'Int';
    case 'Bool':   return 'Bool';
    case 'Unit':   return 'Unit';
    case 'TypeRef': return t.args.length === 0 ? t.name : `(${t.name} ${t.args.map(leanTypeName).join(' ')})`;
    default:       return 'TSError';
  }
}
