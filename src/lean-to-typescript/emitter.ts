import ts from 'typescript';
import { createHash } from 'node:crypto';
import type {
  LeanToTypeScriptArtifact,
  LeanToTypeScriptEnvironmentAttestation,
  LeanToTypeScriptSemanticIdentity,
} from './artifact.js';
import type { LeanDeclaration, LeanEnumConstructor, LeanExpression, LeanSemanticProgram, LeanType } from './ir.js';
import {
  canonicalManifest,
  LEAN_TO_TYPESCRIPT_MANIFEST_SCHEMA_VERSION,
  provenanceHeader,
  verifyLeanToTypeScriptArtifact,
} from './manifest.js';
import { compareCodePoints } from './ordering.js';

export interface LeanToTypeScriptProvenance {
  readonly semantic: Omit<LeanToTypeScriptSemanticIdentity, 'generatedBodySha256'>;
  readonly environment: LeanToTypeScriptEnvironmentAttestation;
}

export function emitTypeScript(
  program: LeanSemanticProgram,
  provenance: LeanToTypeScriptProvenance,
): LeanToTypeScriptArtifact {
  const declarations = orderedDeclarations(program);
  const roots = new Set(program.roots);
  const declarationNames = new Map(
    program.declarations.map((declaration) => [declaration.name, localName(declaration.name)]),
  );
  const valueObjects = planValueObjects(program, declarationNames);
  const context: EmitContext = { roots, declarationNames, valueObjects, methods: methodIndex(valueObjects) };
  const statements = declarations.flatMap((declaration) => emitDeclaration(declaration, context));
  const file = ts.factory.updateSourceFile(
    ts.createSourceFile('generated.ts', '', ts.ScriptTarget.Latest, false, ts.ScriptKind.TS),
    statements,
  );
  // One blank line between top-level declarations: the printer emits none, and a formatter
  // preserves blank lines but never introduces them.
  const printer = ts.createPrinter({ newLine: ts.NewLineKind.LineFeed });
  const body = `${statements
    .map((statement) => printer.printNode(ts.EmitHint.Unspecified, statement, file))
    .join('\n\n')}\n`;
  const manifest = canonicalManifest({
    schemaVersion: LEAN_TO_TYPESCRIPT_MANIFEST_SCHEMA_VERSION,
    semantic: { ...provenance.semantic, generatedBodySha256: sha256(body) },
    environment: provenance.environment,
  });
  const artifact = { code: `${provenanceHeader(manifest)}${body}`, manifest };
  verifyLeanToTypeScriptArtifact(artifact);
  return artifact;
}

function sha256(value: string): string {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}

function orderedDeclarations(program: LeanSemanticProgram): readonly LeanDeclaration[] {
  const types = program.declarations
    .filter((declaration) => declaration.kind !== 'function')
    .sort((left, right) => {
      const kindOrder = Number(left.kind === 'record') - Number(right.kind === 'record');
      return kindOrder || compareCodePoints(left.name, right.name);
    });
  const functions = new Map(
    program.declarations
      .filter(
        (declaration): declaration is Extract<LeanDeclaration, { kind: 'function' }> => declaration.kind === 'function',
      )
      .map((declaration) => [declaration.name, declaration]),
  );
  const orderedFunctions: Extract<LeanDeclaration, { kind: 'function' }>[] = [];
  const visiting = new Set<string>();
  const visited = new Set<string>();
  const visit = (name: string): void => {
    if (visited.has(name)) return;
    if (visiting.has(name)) throw new TypeError(`recursive function cycle is outside the fragment: ${name}`);
    const declaration = functions.get(name);
    if (declaration === undefined) return;
    visiting.add(name);
    for (const dependency of calledFunctions(declaration.body)) visit(dependency);
    visiting.delete(name);
    visited.add(name);
    orderedFunctions.push(declaration);
  };
  for (const root of program.roots) visit(root);
  for (const name of [...functions.keys()].sort(compareCodePoints)) visit(name);
  return [...types, ...orderedFunctions];
}

function calledFunctions(expression: LeanExpression): readonly string[] {
  const names = new Set<string>();
  const visit = (node: LeanExpression): void => {
    switch (node.kind) {
      case 'call':
        names.add(node.function);
        node.arguments.forEach(visit);
        return;
      case 'let':
        visit(node.value);
        visit(node.body);
        return;
      case 'field':
        visit(node.target);
        return;
      case 'if':
        visit(node.condition);
        visit(node.consequent);
        visit(node.alternate);
        return;
      case 'equals':
      case 'and':
      case 'or':
        visit(node.left);
        visit(node.right);
        return;
      case 'not':
        visit(node.operand);
        return;
      case 'some':
        visit(node.value);
        return;
      case 'record':
        node.fields.forEach((field) => visit(field.value));
        return;
      case 'match':
        visit(node.scrutinee);
        node.cases.forEach((entry) => visit(entry.value));
        return;
      case 'variable':
      case 'boolean':
      case 'none':
      case 'variant':
        return;
    }
  };
  visit(expression);
  return [...names].sort(compareCodePoints);
}

type LeanFunction = Extract<LeanDeclaration, { readonly kind: 'function' }>;
type LeanEnum = Extract<LeanDeclaration, { readonly kind: 'enum' }>;

interface MethodPlan {
  readonly declaration: LeanFunction;
  readonly name: string;
  readonly dispatches: boolean;
}

interface CasePlan {
  readonly constructor: LeanEnumConstructor;
  readonly className: string;
  readonly singleton: string;
}

interface ValueObjectPlan {
  readonly declaration: LeanEnum;
  readonly className: string;
  readonly cases: readonly CasePlan[];
  readonly methods: readonly MethodPlan[];
}

interface EmitContext {
  readonly roots: ReadonlySet<string>;
  readonly declarationNames: ReadonlyMap<string, string>;
  readonly valueObjects: ReadonlyMap<string, ValueObjectPlan>;
  readonly methods: ReadonlyMap<string, MethodPlan>;
}

/**
 * A Lean inductive whose namespace carries dot-notation functions over it is a behavior
 * carrying value object; one with no such function is a tag. The distinction is structural,
 * so the same Lean source always lowers to the same TypeScript shape.
 */
function planValueObjects(
  program: LeanSemanticProgram,
  declarationNames: ReadonlyMap<string, string>,
): ReadonlyMap<string, ValueObjectPlan> {
  const allocator = new IdentifierAllocator([...declarationNames.values(), 'undefined', 'this']);
  const functions = program.declarations.filter(
    (declaration): declaration is LeanFunction => declaration.kind === 'function',
  );
  const enums = program.declarations
    .filter((declaration): declaration is LeanEnum => declaration.kind === 'enum')
    .sort((left, right) => compareCodePoints(left.name, right.name));
  const plans = new Map<string, ValueObjectPlan>();
  for (const declaration of enums) {
    const methods = functions
      .filter((candidate) => isDotNotationMethod(candidate, declaration.name))
      .map((candidate): MethodPlan => ({
        declaration: candidate,
        name: localName(candidate.name),
        dispatches: dispatchesOnReceiver(candidate, declaration.name),
      }));
    if (methods.length === 0) continue;
    const className = requiredDeclarationName(declarationNames, declaration.name);
    const cases = declaration.constructors.map((constructor): CasePlan => ({
      constructor,
      className: allocator.allocate(`${capitalize(constructor.name)}${className}`),
      singleton: allocator.allocate(`${constructor.name}${className}`),
    }));
    plans.set(declaration.name, { declaration, className, cases, methods });
  }
  return plans;
}

function methodIndex(valueObjects: ReadonlyMap<string, ValueObjectPlan>): ReadonlyMap<string, MethodPlan> {
  const methods = new Map<string, MethodPlan>();
  for (const plan of valueObjects.values()) {
    for (const method of plan.methods) methods.set(method.declaration.name, method);
  }
  return methods;
}

function isDotNotationMethod(declaration: LeanFunction, enumName: string): boolean {
  if (!declaration.name.startsWith(`${enumName}.`)) return false;
  if (declaration.name.slice(enumName.length + 1).includes('.')) return false;
  const receiver = declaration.parameters[0];
  return receiver !== undefined && receiver.type.kind === 'named' && receiver.type.name === enumName;
}

function dispatchesOnReceiver(declaration: LeanFunction, enumName: string): boolean {
  const body = declaration.body;
  return (
    body.kind === 'match' &&
    body.type === enumName &&
    body.scrutinee.kind === 'variable' &&
    body.scrutinee.index === declaration.parameters.length - 1
  );
}

function capitalize(value: string): string {
  return `${value.slice(0, 1).toUpperCase()}${value.slice(1)}`;
}

function emitDeclaration(declaration: LeanDeclaration, context: EmitContext): readonly ts.Statement[] {
  switch (declaration.kind) {
    case 'enum': {
      const plan = context.valueObjects.get(declaration.name);
      if (plan !== undefined) return emitValueObject(plan, context);
      return [
        documented(
          ts.factory.createTypeAliasDeclaration(
            [modifier(ts.SyntaxKind.ExportKeyword)],
            localName(declaration.name),
            undefined,
            ts.factory.createUnionTypeNode(
              declaration.constructors.map((constructor) => literalType(constructor.name)),
            ),
          ),
          declaration.doc,
        ),
      ];
    }
    case 'record':
      return [
        documented(
          ts.factory.createInterfaceDeclaration(
            [modifier(ts.SyntaxKind.ExportKeyword)],
            localName(declaration.name),
            undefined,
            undefined,
            declaration.fields.map((field) =>
              documented(
                ts.factory.createPropertySignature(
                  [ts.factory.createModifier(ts.SyntaxKind.ReadonlyKeyword)],
                  field.name === '__proto__'
                    ? ts.factory.createStringLiteral(field.name)
                    : ts.factory.createIdentifier(field.name),
                  undefined,
                  emitType(field.type, context.declarationNames),
                ),
                field.doc,
              ),
            ),
          ),
          declaration.doc,
        ),
      ];
    case 'function': {
      if (context.methods.has(declaration.name)) return [];
      const allocator = newAllocator(context);
      const parameters = declaration.parameters.map((parameter) => ({
        ...parameter,
        emittedName: allocator.allocate(parameter.name),
      }));
      const scope = parameters.map((parameter) => parameter.emittedName).reverse();
      return [
        documented(
          ts.factory.createFunctionDeclaration(
            context.roots.has(declaration.name) ? [modifier(ts.SyntaxKind.ExportKeyword)] : undefined,
            undefined,
            localName(declaration.name),
            undefined,
            parameters.map((parameter) =>
              ts.factory.createParameterDeclaration(
                undefined,
                undefined,
                parameter.emittedName,
                undefined,
                emitType(parameter.type, context.declarationNames),
              ),
            ),
            emitType(declaration.result, context.declarationNames),
            emitFunctionBody(declaration.body, scope, allocator, context),
          ),
          declaration.doc,
        ),
      ];
    }
  }
}

function newAllocator(context: EmitContext): IdentifierAllocator {
  const reserved = [...context.declarationNames.values(), 'undefined', 'this'];
  for (const plan of context.valueObjects.values()) {
    for (const entry of plan.cases) reserved.push(entry.className, entry.singleton);
  }
  return new IdentifierAllocator(reserved);
}

function emitValueObject(plan: ValueObjectPlan, context: EmitContext): readonly ts.Statement[] {
  const kindType = ts.factory.createUnionTypeNode(plan.cases.map((entry) => literalType(entry.constructor.name)));
  const base = ts.factory.createTypeReferenceNode(plan.className);
  const members: ts.ClassElement[] = plan.cases.map((entry) =>
    documented(
      ts.factory.createGetAccessorDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.StaticKeyword)],
        entry.constructor.name,
        [],
        base,
        ts.factory.createBlock([ts.factory.createReturnStatement(ts.factory.createIdentifier(entry.singleton))], true),
      ),
      entry.constructor.doc,
    ),
  );
  members.push(emitFromAccessor(plan, base));
  members.push(
    ts.factory.createPropertyDeclaration(
      [
        modifier(ts.SyntaxKind.PublicKeyword),
        modifier(ts.SyntaxKind.AbstractKeyword),
        modifier(ts.SyntaxKind.ReadonlyKeyword),
      ],
      'kind',
      undefined,
      kindType,
      undefined,
    ),
  );
  for (const method of plan.methods) members.push(emitBaseMethod(method, context));
  members.push(
    ts.factory.createMethodDeclaration(
      [modifier(ts.SyntaxKind.PublicKeyword)],
      undefined,
      'equals',
      undefined,
      undefined,
      [ts.factory.createParameterDeclaration(undefined, undefined, 'other', undefined, base)],
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
      ts.factory.createBlock(
        [
          ts.factory.createReturnStatement(
            ts.factory.createBinaryExpression(
              ts.factory.createThis(),
              ts.SyntaxKind.EqualsEqualsEqualsToken,
              ts.factory.createIdentifier('other'),
            ),
          ),
        ],
        true,
      ),
    ),
  );
  const declaration = documented(
    ts.factory.createClassDeclaration(
      [modifier(ts.SyntaxKind.ExportKeyword), modifier(ts.SyntaxKind.AbstractKeyword)],
      plan.className,
      undefined,
      undefined,
      members,
    ),
    plan.declaration.doc,
  );
  const subclasses = plan.cases.map((entry) => emitCaseClass(entry, plan, context));
  const singletons = plan.cases.map((entry) =>
    ts.factory.createVariableStatement(
      undefined,
      ts.factory.createVariableDeclarationList(
        [
          ts.factory.createVariableDeclaration(
            entry.singleton,
            undefined,
            undefined,
            ts.factory.createNewExpression(ts.factory.createIdentifier(entry.className), undefined, []),
          ),
        ],
        ts.NodeFlags.Const,
      ),
    ),
  );
  return [declaration, ...subclasses, ...singletons];
}

/** The representation codec for a Lean inductive: its `kind` tag back to its one value. */
function emitFromAccessor(plan: ValueObjectPlan, base: ts.TypeNode): ts.ClassElement {
  const parameterType = ts.factory.createIndexedAccessTypeNode(base, literalType('kind'));
  const clauses = plan.cases.map((entry) =>
    ts.factory.createCaseClause(ts.factory.createStringLiteral(entry.constructor.name), [
      ts.factory.createReturnStatement(
        ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier(plan.className), entry.constructor.name),
      ),
    ]),
  );
  return ts.factory.createMethodDeclaration(
    [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.StaticKeyword)],
    undefined,
    'from',
    undefined,
    undefined,
    [ts.factory.createParameterDeclaration(undefined, undefined, 'kind', undefined, parameterType)],
    base,
    ts.factory.createBlock(
      [ts.factory.createSwitchStatement(ts.factory.createIdentifier('kind'), ts.factory.createCaseBlock(clauses))],
      true,
    ),
  );
}

function emitBaseMethod(method: MethodPlan, context: EmitContext): ts.ClassElement {
  const allocator = newAllocator(context);
  const parameters = methodParameters(method, allocator, context);
  if (method.dispatches) {
    return documented(
      ts.factory.createMethodDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.AbstractKeyword)],
        undefined,
        method.name,
        undefined,
        undefined,
        parameters,
        emitType(method.declaration.result, context.declarationNames),
        undefined,
      ),
      method.declaration.doc,
    );
  }
  return documented(
    ts.factory.createMethodDeclaration(
      [modifier(ts.SyntaxKind.PublicKeyword)],
      undefined,
      method.name,
      undefined,
      undefined,
      parameters,
      emitType(method.declaration.result, context.declarationNames),
      emitFunctionBody(method.declaration.body, methodScope(parameters), allocator, context),
    ),
    method.declaration.doc,
  );
}

function emitCaseClass(entry: CasePlan, plan: ValueObjectPlan, context: EmitContext): ts.Statement {
  const members: ts.ClassElement[] = [
    ts.factory.createPropertyDeclaration(
      [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.ReadonlyKeyword)],
      'kind',
      undefined,
      undefined,
      ts.factory.createAsExpression(
        ts.factory.createStringLiteral(entry.constructor.name),
        ts.factory.createTypeReferenceNode('const'),
      ),
    ),
  ];
  for (const method of plan.methods) {
    if (!method.dispatches) continue;
    const body = method.declaration.body;
    if (body.kind !== 'match') throw new TypeError(`dispatching method ${method.declaration.name} lost its match`);
    const arm = body.cases.find((candidate) => candidate.constructor === entry.constructor.name);
    if (arm === undefined) {
      throw new TypeError(`method ${method.declaration.name} decides no ${entry.constructor.name} case`);
    }
    const allocator = newAllocator(context);
    const declared = methodParameters(method, allocator, context);
    const scope = methodScope(declared);
    const used = usedParameterCount(arm.value, scope);
    members.push(
      ts.factory.createMethodDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.OverrideKeyword)],
        undefined,
        method.name,
        undefined,
        undefined,
        declared.slice(0, used),
        emitType(method.declaration.result, context.declarationNames),
        emitFunctionBody(arm.value, scope, allocator, context),
      ),
    );
  }
  return ts.factory.createClassDeclaration(
    undefined,
    entry.className,
    undefined,
    [
      ts.factory.createHeritageClause(ts.SyntaxKind.ExtendsKeyword, [
        ts.factory.createExpressionWithTypeArguments(ts.factory.createIdentifier(plan.className), undefined),
      ]),
    ],
    members,
  );
}

function methodParameters(
  method: MethodPlan,
  allocator: IdentifierAllocator,
  context: EmitContext,
): readonly ts.ParameterDeclaration[] {
  return method.declaration.parameters
    .slice(1)
    .map((parameter) =>
      ts.factory.createParameterDeclaration(
        undefined,
        undefined,
        allocator.allocate(parameter.name),
        undefined,
        emitType(parameter.type, context.declarationNames),
      ),
    );
}

/** de Bruijn scope for a method body: the receiver is `this`, the rest are its parameters. */
function methodScope(parameters: readonly ts.ParameterDeclaration[]): readonly string[] {
  const names = parameters.map((parameter) => {
    if (!ts.isIdentifier(parameter.name)) throw new TypeError('emitted parameter is not an identifier');
    return parameter.name.text;
  });
  return [...names].reverse().concat('this');
}

/**
 * How many leading declared parameters an override has to keep: TypeScript admits an
 * override that ignores a trailing suffix, and the handwritten idiom drops it.
 */
function usedParameterCount(expression: LeanExpression, scope: readonly string[]): number {
  const receiverIndex = scope.length - 1;
  let highest = 0;
  const visit = (node: LeanExpression, depth: number): void => {
    switch (node.kind) {
      case 'variable': {
        const index = node.index - depth;
        if (index < 0 || index >= receiverIndex) return;
        highest = Math.max(highest, receiverIndex - index);
        return;
      }
      case 'let':
        visit(node.value, depth);
        visit(node.body, depth + 1);
        return;
      case 'field':
        visit(node.target, depth);
        return;
      case 'if':
        visit(node.condition, depth);
        visit(node.consequent, depth);
        visit(node.alternate, depth);
        return;
      case 'equals':
      case 'and':
      case 'or':
        visit(node.left, depth);
        visit(node.right, depth);
        return;
      case 'not':
        visit(node.operand, depth);
        return;
      case 'some':
        visit(node.value, depth);
        return;
      case 'record':
        node.fields.forEach((field) => visit(field.value, depth));
        return;
      case 'match':
        visit(node.scrutinee, depth);
        node.cases.forEach((entry) => visit(entry.value, depth));
        return;
      case 'call':
        node.arguments.forEach((argument) => visit(argument, depth));
        return;
      case 'boolean':
      case 'none':
      case 'variant':
        return;
    }
  };
  visit(expression, 0);
  return highest;
}

function documented<Node extends ts.Node>(node: Node, doc: string | undefined): Node {
  if (doc === undefined) return node;
  const lines = doc.replace(/\s+$/u, '').split('\n');
  const text = `*\n${lines.map((line) => (line.length === 0 ? ' *' : ` * ${line}`)).join('\n')}\n `;
  return ts.addSyntheticLeadingComment(node, ts.SyntaxKind.MultiLineCommentTrivia, text, true);
}

function modifier(kind: ts.ModifierSyntaxKind): ts.Modifier {
  return ts.factory.createModifier(kind);
}

function literalType(value: string): ts.TypeNode {
  return ts.factory.createLiteralTypeNode(ts.factory.createStringLiteral(value));
}

function emitType(type: LeanType, declarationNames: ReadonlyMap<string, string>): ts.TypeNode {
  switch (type.kind) {
    case 'boolean':
      return ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword);
    case 'named':
      return ts.factory.createTypeReferenceNode(requiredDeclarationName(declarationNames, type.name));
    case 'option':
      return ts.factory.createUnionTypeNode([
        emitType(type.inner, declarationNames),
        ts.factory.createKeywordTypeNode(ts.SyntaxKind.UndefinedKeyword),
      ]);
  }
}

function emitFunctionBody(
  expression: LeanExpression,
  scope: readonly string[],
  allocator: IdentifierAllocator,
  context: EmitContext,
): ts.Block {
  const statements: ts.Statement[] = [];
  let current = expression;
  let currentScope = scope;
  while (current.kind === 'let') {
    const emittedName = allocator.allocate(current.name);
    statements.push(
      ts.factory.createVariableStatement(
        undefined,
        ts.factory.createVariableDeclarationList(
          [
            ts.factory.createVariableDeclaration(
              emittedName,
              undefined,
              undefined,
              emitExpression(current.value, currentScope, context),
            ),
          ],
          ts.NodeFlags.Const,
        ),
      ),
    );
    currentScope = [emittedName, ...currentScope];
    current = current.body;
  }
  statements.push(ts.factory.createReturnStatement(emitExpression(current, currentScope, context)));
  return ts.factory.createBlock(statements, true);
}

function emitExpression(expression: LeanExpression, scope: readonly string[], context: EmitContext): ts.Expression {
  switch (expression.kind) {
    case 'variable': {
      const name = scope[expression.index];
      if (name === undefined) throw new TypeError(`unbound de Bruijn index ${expression.index}`);
      return name === 'this' ? ts.factory.createThis() : ts.factory.createIdentifier(name);
    }
    case 'boolean':
      return expression.value ? ts.factory.createTrue() : ts.factory.createFalse();
    case 'let':
      throw new TypeError('nested let expressions must be normalized before emission');
    case 'field':
      return expression.field === '__proto__'
        ? ts.factory.createElementAccessExpression(
            emitExpression(expression.target, scope, context),
            ts.factory.createStringLiteral(expression.field),
          )
        : ts.factory.createPropertyAccessExpression(
            emitExpression(expression.target, scope, context),
            expression.field,
          );
    case 'if':
      return ts.factory.createConditionalExpression(
        emitExpression(expression.condition, scope, context),
        undefined,
        emitExpression(expression.consequent, scope, context),
        undefined,
        emitExpression(expression.alternate, scope, context),
      );
    case 'equals':
      if (expression.right.kind === 'boolean' && expression.right.value) {
        return emitExpression(expression.left, scope, context);
      }
      if (expression.left.kind === 'boolean' && expression.left.value) {
        return emitExpression(expression.right, scope, context);
      }
      return ts.factory.createBinaryExpression(
        emitExpression(expression.left, scope, context),
        ts.SyntaxKind.EqualsEqualsEqualsToken,
        emitExpression(expression.right, scope, context),
      );
    case 'and':
    case 'or':
      return ts.factory.createBinaryExpression(
        emitExpression(expression.left, scope, context),
        expression.kind === 'and' ? ts.SyntaxKind.AmpersandAmpersandToken : ts.SyntaxKind.BarBarToken,
        emitExpression(expression.right, scope, context),
      );
    case 'not':
      return ts.factory.createPrefixUnaryExpression(
        ts.SyntaxKind.ExclamationToken,
        emitExpression(expression.operand, scope, context),
      );
    case 'some':
      return emitExpression(expression.value, scope, context);
    case 'none':
      return ts.factory.createIdentifier('undefined');
    case 'variant': {
      const plan = context.valueObjects.get(expression.type);
      if (plan === undefined) return ts.factory.createStringLiteral(expression.name);
      return ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier(plan.className), expression.name);
    }
    case 'match':
      throw new TypeError('a match outside dot-notation dispatch position is outside this fragment version');
    case 'record':
      return ts.factory.createObjectLiteralExpression(
        expression.fields.map((field) =>
          ts.factory.createPropertyAssignment(
            field.name === '__proto__'
              ? ts.factory.createComputedPropertyName(ts.factory.createStringLiteral(field.name))
              : ts.factory.createIdentifier(field.name),
            emitExpression(field.value, scope, context),
          ),
        ),
        true,
      );
    case 'call': {
      const method = context.methods.get(expression.function);
      if (method === undefined) {
        return ts.factory.createCallExpression(
          ts.factory.createIdentifier(requiredDeclarationName(context.declarationNames, expression.function)),
          undefined,
          expression.arguments.map((argument) => emitExpression(argument, scope, context)),
        );
      }
      const [receiver, ...rest] = expression.arguments;
      if (receiver === undefined) throw new TypeError(`method call ${expression.function} has no receiver`);
      return ts.factory.createCallExpression(
        ts.factory.createPropertyAccessExpression(emitExpression(receiver, scope, context), method.name),
        undefined,
        rest.map((argument) => emitExpression(argument, scope, context)),
      );
    }
  }
}

class IdentifierAllocator {
  readonly #used: Set<string>;

  public constructor(reserved: Iterable<string>) {
    this.#used = new Set(reserved);
  }

  public allocate(hint: string): string {
    const stem = safeIdentifierStem(hint);
    let candidate = stem;
    let suffix = 2;
    while (this.#used.has(candidate)) {
      candidate = `${stem}$${suffix}`;
      suffix += 1;
    }
    this.#used.add(candidate);
    return candidate;
  }
}

function safeIdentifierStem(hint: string): string {
  const sanitized = hint.replace(/[^$0-9A-Z_a-z]/gu, '_');
  const prefixed = /^[$A-Z_a-z]/u.test(sanitized) ? sanitized : `value_${sanitized}`;
  const candidate = prefixed.length === 0 ? 'value' : prefixed;
  const scanner = ts.createScanner(ts.ScriptTarget.Latest, false, ts.LanguageVariant.Standard, candidate);
  if (
    scanner.scan() !== ts.SyntaxKind.Identifier ||
    scanner.scan() !== ts.SyntaxKind.EndOfFileToken ||
    candidate === 'arguments' ||
    candidate === 'eval'
  ) {
    return `value_${candidate}`;
  }
  return candidate;
}

function requiredDeclarationName(names: ReadonlyMap<string, string>, name: string): string {
  const emitted = names.get(name);
  if (emitted === undefined) throw new TypeError(`missing emitted declaration name for ${name}`);
  return emitted;
}

function localName(name: string): string {
  const part = name.split('.').at(-1);
  if (part === undefined) throw new TypeError('empty Lean name');
  return part;
}
