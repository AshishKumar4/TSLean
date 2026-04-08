/**
 * @module effects
 *
 * Effect inference: analyses TypeScript AST nodes to determine which algebraic
 * effects a function body uses — Pure, IO, Async, Except (throw), or State
 * (mutation).  The codegen pass uses this to select the correct Lean 4 monad
 * transformer stack.
 *
 * Pipeline position:  TS AST → **Effect inference** → IR (effect-annotated)
 */

import * as ts from 'typescript';
import {
  Effect, IRType, Pure, IO, Async, stateEffect, exceptEffect, combineEffects,
  TyString, TyUnit,
} from '../ir/types.js';

// ─── Constants ──────────────────────────────────────────────────────────────────

/** TypeScript APIs that introduce IO effects when called. */
const IO_TRIGGERING_PREFIXES = [
  'console.',     // logging
  'Date.',        // current time
  'Math.random',  // randomness
  'crypto.',      // cryptographic RNG
] as const;

/** Full call expressions that introduce IO effects. */
const IO_TRIGGERING_CALLS = new Set(['fetch']);

/** The pure monad name in Lean 4 (identity monad). */
const PURE_MONAD = 'Id';

/** Fallback error type name when the type cannot be resolved. */
const FALLBACK_ERROR_TYPE = 'TSError';

// ─── Public API ─────────────────────────────────────────────────────────────────

/**
 * Infer the algebraic effect of a TypeScript AST node.
 *
 * For function-like nodes, analyses the body directly (skipping the outer
 * signature) so that nested-function guards don't suppress the top level.
 *
 * @param node    - Any TS AST node (typically a function declaration).
 * @param checker - The TypeScript type checker for the program.
 * @returns The combined effect — Pure if no side effects were detected.
 */
export function inferNodeEffect(node: ts.Node, checker: ts.TypeChecker): Effect {
  const target = getFunctionBody(node) ?? node;
  const effects: Effect[] = [];

  if (bodyContainsAwait(target))    effects.push(Async);
  if (bodyContainsThrow(target))    effects.push(exceptEffect(TyString));
  if (bodyContainsMutation(target)) effects.push(stateEffect(TyUnit));
  if (bodyContainsIO(target))       effects.push(IO);

  return combineEffects(effects);
}

/**
 * Convert an Effect to its Lean 4 monad string representation.
 *
 * The monad transformer stack is built right-to-left:
 * ```
 *   ['StateT S', 'ExceptT E', 'IO']
 *   → 'ExceptT E IO'             (fold step 1)
 *   → 'StateT S (ExceptT E IO)'  (fold step 2)
 * ```
 *
 * @param effect         - The effect to convert.
 * @param stateTypeName  - Fallback name for the state type variable (default `σ`).
 * @returns A valid Lean 4 type expression for the monad.
 */
export function monadString(effect: Effect, stateTypeName = 'σ'): string {
  switch (effect.tag) {
    case 'Pure':   return PURE_MONAD;
    case 'IO':     return 'IO';
    case 'Async':  return 'IO';
    case 'State':  return `StateT ${leanTypeName(effect.stateType)} IO`;
    case 'Except': return `ExceptT ${leanTypeName(effect.errorType)} IO`;
    case 'Combined': {
      const se = effect.effects.find((e): e is Extract<Effect, { tag: 'State' }> => e.tag === 'State');
      const ee = effect.effects.find((e): e is Extract<Effect, { tag: 'Except' }> => e.tag === 'Except');
      const parts: string[] = [];
      if (se) parts.push(`StateT ${leanTypeName(se.stateType)}`);
      else if (effect.effects.some(e => e.tag === 'State')) parts.push(`StateT ${stateTypeName}`);
      if (ee) parts.push(`ExceptT ${leanTypeName(ee.errorType)}`);
      else if (effect.effects.some(e => e.tag === 'Except')) parts.push(`ExceptT ${FALLBACK_ERROR_TYPE}`);
      parts.push('IO');
      // Right-fold: each wrapper takes the current inner stack as its last argument.
      if (parts.length === 1) return parts[0];
      return parts.reduceRight((inner, outer) =>
        `${outer} ${inner.includes(' ') ? `(${inner})` : inner}`
      );
    }
  }
}

/**
 * Generate the DOMonad type string for a Durable Object.
 * @param stateTypeName - The name of the DO state type parameter.
 */
export function doMonadType(stateTypeName: string): string {
  return `DOMonad ${stateTypeName}`;
}

/**
 * Compute the join (least upper bound) of two effects.
 * Pure is the identity element.
 */
export function joinEffects(a: Effect, b: Effect): Effect {
  if (a.tag === 'Pure') return b;
  if (b.tag === 'Pure') return a;
  return combineEffects([a, b]);
}

/**
 * Test whether effect `a` subsumes effect `b` — i.e., `a` can handle `b`.
 * Pure is subsumed by everything.  Combined effects check recursively.
 */
export function effectSubsumes(a: Effect, b: Effect): boolean {
  if (b.tag === 'Pure') return true;
  if (a.tag === b.tag)  return true;
  if (a.tag === 'Combined') return a.effects.some(e => effectSubsumes(e, b));
  return false;
}

// ─── Internal: AST scanning ─────────────────────────────────────────────────────
//
// Each `bodyContains*` function walks the AST looking for a specific pattern,
// but never recurses into nested function scopes (lambdas, arrow functions,
// method declarations) — those are separate effect boundaries.

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
    const text = node.expression.getText();
    if (IO_TRIGGERING_PREFIXES.some(p => text.startsWith(p)) || IO_TRIGGERING_CALLS.has(text))
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

/**
 * Map an IR type to its Lean 4 name for use in monad signatures.
 * Falls back to `TSError` for types that don't have a direct Lean primitive name.
 */
function leanTypeName(t: IRType): string {
  switch (t.tag) {
    case 'String':  return 'String';
    case 'Float':   return 'Float';
    case 'Nat':     return 'Nat';
    case 'Int':     return 'Int';
    case 'Bool':    return 'Bool';
    case 'Unit':    return 'Unit';
    case 'TypeRef': return t.args.length === 0 ? t.name : `(${t.name} ${t.args.map(leanTypeName).join(' ')})`;
    default:        return FALLBACK_ERROR_TYPE;
  }
}
