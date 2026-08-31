/**
 * @module roundtrip/profile
 *
 * The exact subset both compilers admit, defined on the TypeScript type and syntax
 * graph rather than on source text.
 *
 * A round trip only means something over constructs both directions carry with the same
 * declared semantics. That subset is stated here as a positive grammar: a type is in the
 * profile when this module can build a {@link ProfileType} for it, a declaration is in the
 * profile when its signature and its body are, and everything else is refused with the
 * reason it was refused. Nothing is admitted by pattern-matching names or comments.
 *
 * The grammar is deliberately finite. Every profile type has an enumerable value domain,
 * which is what lets the round trip compare the two sides by running them over the whole
 * domain instead of over samples.
 *
 * A generated module carries decoders for untrusted host data next to the declarations it
 * came from. Those decoders take the emitter's data union, which has no Lean carrier, so
 * the grammar refuses them and the projection drops them. The round trip then checks that
 * nothing the emitter recorded as a Lean declaration was dropped with them.
 */

import ts from 'typescript';
import {
  describeStringEnumeration,
  expectedStringEnumeration,
  TAGGED_OPTION,
  taggedOptionElement,
} from '../typemap/index.js';
import { isLeanIdentifier } from '../utils.js';

// ─── Types ──────────────────────────────────────────────────────────────────────

/** A field of a profile structure. Fields are ordered as declared. */
export interface ProfileField {
  readonly name: string;
  readonly type: ProfileType;
}

/** A type both compilers carry with the same declared semantics. */
export type ProfileType =
  | { readonly kind: 'boolean' }
  | { readonly kind: 'enumeration'; readonly name: string; readonly members: readonly string[] }
  | {
      readonly kind: 'structure';
      readonly name: string;
      readonly fields: readonly ProfileField[];
      /** How TypeScript introduces a value of it: `new Name(init)` or an object literal. */
      readonly introduced: 'class' | 'interface';
    }
  /**
   * An option, and which of the two TypeScript spellings a program uses for it. Both denote
   * the same Lean `Option`, so the encoding never enters a declaration's description; it
   * only says how to build and read a value at the JavaScript boundary.
   */
  | { readonly kind: 'option'; readonly inner: ProfileType; readonly encoding: 'undefined' | 'tagged' };

/** A declaration inside the profile, and the syntax the projection keeps for it. */
export interface ProfileDeclaration {
  /** The TypeScript name. A class member is named `Class.member`. */
  readonly name: string;
  /**
   * `encoding` is the generated option encoding's own alias. It declares no type of its
   * own — `Option A` is Lean's — but admitted declarations name it, so the projection has
   * to keep it for the projected module to compile.
   */
  readonly kind: 'enumeration' | 'structure' | 'function' | 'method' | 'encoding';
  /** Whether a consumer of the module can reach it. A method follows its class. */
  readonly exported: boolean;
  readonly node: ts.Declaration;
}

/** A declaration outside the profile, and why. */
export interface ProfileRefusal {
  readonly name: string;
  readonly reason: string;
}

/** What one module contributes to the profile, and what it does not. */
export interface ModuleProfile {
  readonly admitted: readonly ProfileDeclaration[];
  readonly refused: readonly ProfileRefusal[];
}

// ─── Type resolution ────────────────────────────────────────────────────────────

/**
 * The profile type a TypeScript type denotes, or `null` when the profile has no
 * carrier for it.
 *
 * `seen` carries the structures currently being resolved. A structure that reaches
 * itself has no finite value domain, so it leaves the profile rather than making the
 * comparison unbounded.
 */
export function resolveProfileType(
  type: ts.Type,
  checker: ts.TypeChecker,
  seen: ReadonlySet<string> = new Set(),
): ProfileType | null {
  if ((type.flags & ts.TypeFlags.Boolean) !== 0) return { kind: 'boolean' };

  const enumeration = describeStringEnumeration(type);
  if (enumeration !== null) {
    return { kind: 'enumeration', name: enumeration.name, members: enumeration.members };
  }

  if (type.isUnion()) {
    // Both spellings of an option denote the same Lean type, so both resolve to the same
    // profile type. The generated encoding tags its cases; the written one uses `undefined`.
    const tagged = taggedOptionElement(type, checker);
    if (tagged !== null) {
      const element = resolveProfileType(tagged, checker, seen);
      return element === null || element.kind === 'option'
        ? null
        : { kind: 'option', inner: element, encoding: 'tagged' };
    }
    // `T | undefined` flattens when `T` is itself a union, so the members no longer say
    // which alias was written. `getNonNullableType` rebuilds the written type, alias and
    // all, which is what names the Lean `Option` argument.
    if (!type.types.some((member) => (member.flags & ts.TypeFlags.Undefined) !== 0)) return null;
    const inner = resolveProfileType(checker.getNonNullableType(type), checker, seen);
    return inner === null || inner.kind === 'option'
      ? null
      : { kind: 'option', inner, encoding: 'undefined' };
  }

  return resolveStructure(type, checker, seen);
}

/**
 * The structure a nominal object type denotes.
 *
 * Only an interface or a class denotes one: an anonymous object type has no name for
 * the Lean structure to take. Every field must be readonly and required, because a Lean
 * structure field is neither optional nor assignable in place. A property declared as a
 * method is a member of the type rather than data, so it does not become a field; whether
 * that member is itself in the profile is decided where the class is classified.
 */
function resolveStructure(
  type: ts.Type,
  checker: ts.TypeChecker,
  seen: ReadonlySet<string>,
): ProfileType | null {
  const symbol = type.getSymbol();
  if (symbol === undefined) return null;
  // A generated structure name is also the name of its codec value, so the symbol carries
  // both declarations. Only the type-space one describes the structure.
  const declarations = (symbol.declarations ?? [])
    .filter((entry) => ts.isInterfaceDeclaration(entry) || ts.isClassDeclaration(entry));
  if (declarations.length !== 1) return null;
  const declaration = declarations[0];
  if ((declaration.typeParameters?.length ?? 0) > 0) return null;

  const name = declaration.name?.text;
  if (name === undefined || !isLeanIdentifier(name)) return null;
  if (seen.has(name)) return null;
  const nested = new Set([...seen, name]);

  const fields: ProfileField[] = [];
  for (const property of type.getProperties()) {
    const propertyDeclarations = property.declarations ?? [];
    if (propertyDeclarations.length !== 1) return null;
    const member = propertyDeclarations[0];
    if (ts.isMethodDeclaration(member) || ts.isMethodSignature(member)) continue;
    if (!ts.isPropertyDeclaration(member) && !ts.isPropertySignature(member)) return null;
    if ((property.flags & ts.SymbolFlags.Optional) !== 0) return null;
    if ((ts.getCombinedModifierFlags(member) & ts.ModifierFlags.Readonly) === 0) return null;
    if (!isLeanIdentifier(property.name)) return null;
    const fieldType = resolveProfileType(checker.getTypeOfSymbolAtLocation(property, member), checker, nested);
    if (fieldType === null) return null;
    fields.push({ name: property.name, type: fieldType });
  }
  if (fields.length === 0) return null;
  return {
    kind: 'structure',
    name,
    fields,
    introduced: ts.isClassDeclaration(declaration) ? 'class' : 'interface',
  };
}

// ─── Module classification ──────────────────────────────────────────────────────

/**
 * Classify every top-level declaration of a module, and every member of an admitted
 * class, as inside or outside the profile.
 */
export function profileModule(source: ts.SourceFile, checker: ts.TypeChecker): ModuleProfile {
  const admitted: ProfileDeclaration[] = [];
  const refused: ProfileRefusal[] = [];
  const context: TermContext = { checker };

  for (const statement of source.statements) {
    if (ts.isImportDeclaration(statement)) continue;
    classifyStatement(statement, context, admitted, refused);
  }
  return { admitted, refused };
}

/** What a term needs to be checked against. */
interface TermContext {
  readonly checker: ts.TypeChecker;
}

function classifyStatement(
  statement: ts.Statement,
  context: TermContext,
  admitted: ProfileDeclaration[],
  refused: ProfileRefusal[],
): void {
  if (ts.isTypeAliasDeclaration(statement)) {
    const name = statement.name.text;
    const declared = context.checker.getTypeAtLocation(statement.name);
    if (taggedOptionElement(declared, context.checker) !== null) {
      admitted.push({ name, kind: 'encoding', exported: isExported(statement), node: statement });
      return;
    }
    const enumeration = describeStringEnumeration(declared);
    if (enumeration === null || enumeration.name !== name) {
      refused.push({ name, reason: 'a type alias is in the profile only as an enumeration of string literals' });
      return;
    }
    admitted.push({ name, kind: 'enumeration', exported: isExported(statement), node: statement });
    return;
  }

  if (ts.isInterfaceDeclaration(statement)) {
    const name = statement.name.text;
    const shape = resolveProfileType(context.checker.getDeclaredTypeOfSymbol(symbolOf(statement.name, context)), context.checker);
    if (shape === null || shape.kind !== 'structure') {
      refused.push({ name, reason: 'an interface is in the profile only as a structure of profile fields' });
      return;
    }
    admitted.push({ name, kind: 'structure', exported: isExported(statement), node: statement });
    return;
  }

  if (ts.isClassDeclaration(statement)) {
    classifyClass(statement, context, admitted, refused);
    return;
  }

  if (ts.isFunctionDeclaration(statement)) {
    const name = statement.name?.text ?? '(anonymous)';
    const reason = refuseFunction(statement, context);
    if (reason !== null) {
      refused.push({ name, reason });
      return;
    }
    admitted.push({ name, kind: 'function', exported: isExported(statement), node: statement });
    return;
  }

  refused.push({
    name: statementName(statement),
    reason: `${ts.SyntaxKind[statement.kind]} is outside the profile`,
  });
}

/**
 * A class is in the profile when it denotes a structure and introduces that structure
 * the one canonical way. Its methods are classified one by one, so a decoder that takes
 * host data leaves the profile without taking the structure with it.
 */
function classifyClass(
  declaration: ts.ClassDeclaration,
  context: TermContext,
  admitted: ProfileDeclaration[],
  refused: ProfileRefusal[],
): void {
  const name = declaration.name?.text ?? '(anonymous)';
  const shape = declaration.name === undefined
    ? null
    : resolveProfileType(context.checker.getDeclaredTypeOfSymbol(symbolOf(declaration.name, context)), context.checker);
  if (shape === null || shape.kind !== 'structure') {
    refused.push({ name, reason: 'a class is in the profile only as a structure of profile fields' });
    return;
  }
  if ((declaration.heritageClauses?.length ?? 0) > 0) {
    refused.push({ name, reason: 'a class in the profile extends nothing' });
    return;
  }
  const constructors = declaration.members.filter(ts.isConstructorDeclaration);
  if (constructors.length !== 1 || !isCanonicalConstructor(constructors[0], shape, context)) {
    refused.push({
      name,
      reason: 'a class in the profile has one constructor that takes an initialiser and assigns every field from it',
    });
    return;
  }

  admitted.push({ name, kind: 'structure', exported: isExported(declaration), node: declaration });

  for (const member of declaration.members) {
    if (ts.isConstructorDeclaration(member) || ts.isPropertyDeclaration(member)) continue;
    const memberName = member.name === undefined ? '(unnamed)' : member.name.getText(declaration.getSourceFile());
    const qualified = `${name}.${memberName}`;
    if (!ts.isMethodDeclaration(member)) {
      refused.push({ name: qualified, reason: `${ts.SyntaxKind[member.kind]} is outside the profile` });
      continue;
    }
    if (member.modifiers?.some((modifier) => modifier.kind === ts.SyntaxKind.StaticKeyword) === true) {
      refused.push({ name: qualified, reason: 'a static member has no Lean counterpart in the profile' });
      continue;
    }
    const reason = refuseFunction(member, context);
    if (reason !== null) {
      refused.push({ name: qualified, reason });
      continue;
    }
    admitted.push({ name: qualified, kind: 'method', exported: isExported(declaration), node: member });
  }
}

/**
 * The one constructor shape the profile reads as a structure introduction: a single
 * initialiser parameter carrying exactly the structure's fields, a body that assigns
 * every field from it in declaration order, and a freeze that makes the value immutable
 * as the Lean structure already is.
 */
function isCanonicalConstructor(
  declaration: ts.ConstructorDeclaration,
  shape: Extract<ProfileType, { kind: 'structure' }>,
  context: TermContext,
): boolean {
  if (declaration.parameters.length !== 1) return false;
  const parameter = declaration.parameters[0];
  if (!ts.isIdentifier(parameter.name)) return false;
  const initialiser = resolveProfileType(context.checker.getTypeAtLocation(parameter), context.checker);
  if (initialiser === null || initialiser.kind !== 'structure') return false;
  if (!sameFields(initialiser.fields, shape.fields)) return false;

  const statements = declaration.body?.statements ?? [];
  if (statements.length !== shape.fields.length + 1) return false;
  for (const [index, field] of shape.fields.entries()) {
    const statement = statements[index];
    if (!ts.isExpressionStatement(statement) || !ts.isBinaryExpression(statement.expression)) return false;
    const assignment = statement.expression;
    if (assignment.operatorToken.kind !== ts.SyntaxKind.EqualsToken) return false;
    if (!isThisField(assignment.left, field.name)) return false;
    if (!ts.isPropertyAccessExpression(assignment.right)) return false;
    if (assignment.right.name.text !== field.name) return false;
    if (!ts.isIdentifier(assignment.right.expression)) return false;
    if (assignment.right.expression.text !== parameter.name.text) return false;
  }
  return isObjectFreezeOfThis(statements[shape.fields.length]);
}

function sameFields(left: readonly ProfileField[], right: readonly ProfileField[]): boolean {
  return left.length === right.length &&
    left.every((field, index) => field.name === right[index].name &&
      JSON.stringify(field.type) === JSON.stringify(right[index].type));
}

function isThisField(node: ts.Expression, field: string): boolean {
  return ts.isPropertyAccessExpression(node) &&
    node.expression.kind === ts.SyntaxKind.ThisKeyword &&
    node.name.text === field;
}

function isObjectFreezeOfThis(statement: ts.Statement | undefined): boolean {
  if (statement === undefined || !ts.isExpressionStatement(statement)) return false;
  const call = statement.expression;
  if (!ts.isCallExpression(call) || call.arguments.length !== 1) return false;
  if (call.arguments[0].kind !== ts.SyntaxKind.ThisKeyword) return false;
  const callee = call.expression;
  return ts.isPropertyAccessExpression(callee) &&
    ts.isIdentifier(callee.expression) &&
    callee.expression.text === 'Object' &&
    callee.name.text === 'freeze';
}

// ─── Functions and terms ────────────────────────────────────────────────────────

/** Why a function or method is outside the profile, or `null` when it is inside. */
function refuseFunction(
  declaration: ts.FunctionDeclaration | ts.MethodDeclaration,
  context: TermContext,
): string | null {
  if ((declaration.typeParameters?.length ?? 0) > 0) return 'a profile function takes no type parameters';
  if (declaration.asteriskToken !== undefined) return 'a generator has no profile counterpart';
  if (declaration.modifiers?.some((modifier) => modifier.kind === ts.SyntaxKind.AsyncKeyword) === true) {
    return 'an async function has no profile counterpart';
  }
  for (const parameter of declaration.parameters) {
    if (!ts.isIdentifier(parameter.name)) return 'a profile parameter is one named binding';
    if (parameter.dotDotDotToken !== undefined) return 'a rest parameter has no profile counterpart';
    if (parameter.questionToken !== undefined || parameter.initializer !== undefined) {
      return 'an optional parameter has no profile counterpart';
    }
    if (resolveProfileType(context.checker.getTypeAtLocation(parameter), context.checker) === null) {
      return `parameter ${parameter.name.text} has no profile type`;
    }
  }
  const signature = context.checker.getSignatureFromDeclaration(declaration);
  if (signature === undefined) return 'the signature does not resolve';
  if (resolveProfileType(signature.getReturnType(), context.checker) === null) {
    return 'the return type has no profile type';
  }
  const body = declaration.body;
  if (body === undefined) return 'a profile function has a body';
  return refuseBlock(body, context);
}

/**
 * A profile body binds constants, guards, and returns. Every path ends in a return, because
 * a Lean definition is an expression and has no fall-through.
 */
function refuseBlock(block: ts.Block, context: TermContext): string | null {
  if (block.statements.length === 0) return 'a profile body returns a value';
  for (const [index, statement] of block.statements.entries()) {
    const last = index === block.statements.length - 1;
    const reason = refuseStatement(statement, context, last);
    if (reason !== null) return reason;
  }
  const final = block.statements[block.statements.length - 1];
  return ts.isReturnStatement(final) || ts.isIfStatement(final)
    ? null
    : 'a profile body ends in a return';
}

function refuseStatement(statement: ts.Statement, context: TermContext, last: boolean): string | null {
  if (ts.isReturnStatement(statement)) {
    if (!last) return 'a profile body returns once, at the end';
    return statement.expression === undefined
      ? 'a profile return carries a value'
      : refuseTerm(statement.expression, context);
  }
  if (ts.isVariableStatement(statement)) {
    if ((statement.declarationList.flags & ts.NodeFlags.Const) === 0) {
      return 'a profile body binds constants';
    }
    for (const declaration of statement.declarationList.declarations) {
      if (!ts.isIdentifier(declaration.name)) return 'a profile binding is one named binding';
      if (declaration.initializer === undefined) return 'a profile binding has an initialiser';
      const reason = refuseTerm(declaration.initializer, context);
      if (reason !== null) return reason;
      if (resolveProfileType(context.checker.getTypeAtLocation(declaration.name), context.checker) === null) {
        return `binding ${declaration.name.text} has no profile type`;
      }
    }
    return null;
  }
  if (ts.isIfStatement(statement)) {
    const condition = refuseTerm(statement.expression, context);
    if (condition !== null) return condition;
    if (last) {
      if (statement.elseStatement === undefined) return 'a profile branch has both arms';
      return refuseBranch(statement.thenStatement, context) ?? refuseBranch(statement.elseStatement, context);
    }
    // An earlier branch is a guard: it takes its own exit and leaves the rest of the block as
    // the other arm. A guard carrying an `else` would make the statements after it dead, and
    // a guard that can fall through would leave a path with no value.
    if (statement.elseStatement !== undefined) return 'a profile guard leaves no unreachable statement';
    if (!alwaysReturns(statement.thenStatement)) return 'a profile guard returns';
    return refuseBranch(statement.thenStatement, context);
  }
  return `${ts.SyntaxKind[statement.kind]} is outside the profile`;
}

/** Whether every path through the statement returns, so nothing after it can be reached. */
function alwaysReturns(statement: ts.Statement): boolean {
  if (ts.isReturnStatement(statement)) return true;
  if (ts.isIfStatement(statement)) {
    return statement.elseStatement !== undefined
      && alwaysReturns(statement.thenStatement)
      && alwaysReturns(statement.elseStatement);
  }
  if (!ts.isBlock(statement)) return false;
  return statement.statements.some((entry) => alwaysReturns(entry));
}

function refuseBranch(statement: ts.Statement, context: TermContext): string | null {
  if (ts.isBlock(statement)) return refuseBlock(statement, context);
  return refuseStatement(statement, context, true);
}

/** Operators the profile carries, each with the same meaning on both sides. */
const PROFILE_BINARY_OPERATORS = new Set<ts.SyntaxKind>([
  ts.SyntaxKind.AmpersandAmpersandToken,
  ts.SyntaxKind.BarBarToken,
  ts.SyntaxKind.EqualsEqualsEqualsToken,
  ts.SyntaxKind.ExclamationEqualsEqualsToken,
]);

/** Why an expression is outside the profile, or `null` when it is inside. */
function refuseTerm(node: ts.Expression, context: TermContext): string | null {
  if (ts.isParenthesizedExpression(node)) return refuseTerm(node.expression, context);

  if (node.kind === ts.SyntaxKind.TrueKeyword || node.kind === ts.SyntaxKind.FalseKeyword) return null;
  if (node.kind === ts.SyntaxKind.ThisKeyword) return null;

  if (ts.isIdentifier(node)) {
    // `undefined` is the profile's `none`; its own type carries no other information.
    if (node.text === 'undefined') return null;
    return resolveProfileType(declaredTypeOf(node, context), context.checker) === null
      ? `${node.text} has no profile type`
      : null;
  }

  if (ts.isStringLiteral(node)) {
    return isEnumerationLiteral(node, context) ? null : 'a string literal in the profile names an enumeration case';
  }

  if (ts.isPrefixUnaryExpression(node)) {
    return node.operator === ts.SyntaxKind.ExclamationToken
      ? refuseTerm(node.operand, context)
      : 'the only profile prefix operator is negation';
  }

  if (ts.isBinaryExpression(node)) {
    if (!PROFILE_BINARY_OPERATORS.has(node.operatorToken.kind)) {
      return `${ts.tokenToString(node.operatorToken.kind) ?? '?'} is outside the profile`;
    }
    return refuseTerm(node.left, context) ?? refuseTerm(node.right, context);
  }

  if (ts.isConditionalExpression(node)) {
    return refuseTerm(node.condition, context) ??
      refuseTerm(node.whenTrue, context) ??
      refuseTerm(node.whenFalse, context);
  }

  if (ts.isPropertyAccessExpression(node)) {
    const reason = refuseTerm(node.expression, context);
    if (reason !== null) return reason;
    return resolveProfileType(declaredTypeOf(node, context), context.checker) === null
      ? `${node.name.text} has no profile type`
      : null;
  }

  if (ts.isCallExpression(node)) return refuseCall(node, context);
  if (ts.isNewExpression(node)) return refuseConstruction(node, context);
  if (ts.isObjectLiteralExpression(node)) return refuseObjectLiteral(node, context);

  return `${ts.SyntaxKind[node.kind]} is outside the profile`;
}

/** Whether a string literal stands where the profile expects an enumeration case. */
function isEnumerationLiteral(node: ts.StringLiteral, context: TermContext): boolean {
  const parent = node.parent;
  const expected = ts.isBinaryExpression(parent) && PROFILE_BINARY_OPERATORS.has(parent.operatorToken.kind)
    ? declaredTypeOf(parent.left === node ? parent.right : parent.left, context)
    : context.checker.getContextualType(node);
  if (expected === undefined) return false;
  const enumeration = expectedStringEnumeration(expected, context.checker);
  return enumeration !== null && enumeration.members.includes(node.text);
}

/** The type a name was declared with, which narrowing at a use site does not change. */
function declaredTypeOf(node: ts.Expression, context: TermContext): ts.Type {
  const symbol = context.checker.getSymbolAtLocation(node);
  const declaration = symbol?.valueDeclaration;
  return declaration !== undefined && symbol !== undefined
    ? context.checker.getTypeOfSymbolAtLocation(symbol, declaration)
    : context.checker.getTypeAtLocation(node);
}

/**
 * A call is in the profile when it names a declaration of this program that is itself in
 * the profile. A call into a library reaches semantics the round trip never checked.
 */
function refuseCall(node: ts.CallExpression, context: TermContext): string | null {
  const target = context.checker.getResolvedSignature(node)?.getDeclaration();
  if (target === undefined) return 'the call target does not resolve';
  if (!ts.isFunctionDeclaration(target) && !ts.isMethodDeclaration(target)) {
    return 'a profile call names a function or a method';
  }
  const reason = refuseFunction(target, context);
  if (reason !== null) return `call target is outside the profile: ${reason}`;
  if (node.arguments.length !== target.parameters.length) return 'a profile call passes every parameter';
  if (ts.isPropertyAccessExpression(node.expression)) {
    const receiver = refuseTerm(node.expression.expression, context);
    if (receiver !== null) return receiver;
  } else if (!ts.isIdentifier(node.expression)) {
    return 'a profile call names its target directly';
  }
  for (const argument of node.arguments) {
    const argumentReason = refuseTerm(argument, context);
    if (argumentReason !== null) return argumentReason;
  }
  return null;
}

/** `new S({ … })` introduces a profile structure, exactly as a Lean structure literal does. */
function refuseConstruction(node: ts.NewExpression, context: TermContext): string | null {
  const constructed = resolveProfileType(context.checker.getTypeAtLocation(node), context.checker);
  if (constructed === null || constructed.kind !== 'structure') return 'construction builds a profile structure';
  const argumentList = node.arguments ?? [];
  if (argumentList.length !== 1 || !ts.isObjectLiteralExpression(argumentList[0])) {
    return 'construction takes one initialiser literal';
  }
  return refuseObjectLiteral(argumentList[0], context);
}

/**
 * An object literal in the profile supplies every field of the structure it stands for, or
 * writes one case of the generated option encoding.
 */
function refuseObjectLiteral(node: ts.ObjectLiteralExpression, context: TermContext): string | null {
  const contextual = context.checker.getContextualType(node);
  const shape = contextual === undefined ? null : resolveProfileType(contextual, context.checker);
  if (shape !== null && shape.kind === 'option') return refuseOptionLiteral(node, context);
  if (shape === null || shape.kind !== 'structure') return 'an object literal stands for a profile structure';
  if (node.properties.length !== shape.fields.length) return `an initialiser of ${shape.name} supplies every field`;
  for (const [index, property] of node.properties.entries()) {
    if (!ts.isPropertyAssignment(property) || !ts.isIdentifier(property.name)) {
      return 'a profile initialiser names each field';
    }
    if (property.name.text !== shape.fields[index].name) {
      return `an initialiser of ${shape.name} lists its fields in declaration order`;
    }
    const reason = refuseTerm(property.initializer, context);
    if (reason !== null) return reason;
  }
  return null;
}

/**
 * One case of the generated option encoding: the absent case carries only its tag, and the
 * present case carries its tag and the value.
 */
function refuseOptionLiteral(node: ts.ObjectLiteralExpression, context: TermContext): string | null {
  const assignments = node.properties.filter(ts.isPropertyAssignment);
  if (assignments.length !== node.properties.length) return 'a profile option names each field';
  const field = (name: string): ts.Expression | undefined => assignments
    .find((entry) => ts.isIdentifier(entry.name) && entry.name.text === name)?.initializer;
  const tag = field(TAGGED_OPTION.tag);
  if (tag === undefined || !ts.isStringLiteralLike(tag)) return 'a profile option carries its tag';
  const value = field(TAGGED_OPTION.value);
  if (tag.text === TAGGED_OPTION.absent) {
    return assignments.length === 1 && value === undefined ? null : 'an absent option carries only its tag';
  }
  if (tag.text !== TAGGED_OPTION.present) return 'a profile option is absent or present';
  if (assignments.length !== 2 || value === undefined) return 'a present option carries its value';
  return refuseTerm(value, context);
}

// ─── Helpers ────────────────────────────────────────────────────────────────────

/** Whether a consumer of the module can reach the declaration by name. */
function isExported(declaration: ts.Declaration): boolean {
  return (ts.getCombinedModifierFlags(declaration) & ts.ModifierFlags.Export) !== 0;
}

function symbolOf(name: ts.Identifier, context: TermContext): ts.Symbol {
  const symbol = context.checker.getSymbolAtLocation(name);
  if (symbol === undefined) throw new TypeError(`${name.text} has no symbol`);
  return symbol;
}

function statementName(statement: ts.Statement): string {
  if (ts.isVariableStatement(statement)) {
    const first = statement.declarationList.declarations[0]?.name;
    if (first !== undefined && ts.isIdentifier(first)) return first.text;
  }
  const named = statement as { name?: ts.Node };
  return named.name !== undefined && ts.isIdentifier(named.name as ts.Node)
    ? (named.name as ts.Identifier).text
    : ts.SyntaxKind[statement.kind];
}
