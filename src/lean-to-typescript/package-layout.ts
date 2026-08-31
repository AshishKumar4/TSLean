import ts from 'typescript';
import { isLeanModuleName, type LeanDeclaration } from './ir.js';
import { compareCodePoints } from './ordering.js';

/**
 * The generated package root holds one shared runtime module. Its name is outside the Lean module
 * grammar, so no Lean module can ever claim that path.
 */
export const LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH = 'tslean-runtime.ts';

/**
 * Windows reserves these device names in every directory, with or without an extension, so a
 * module that spells one has no portable file to be written to.
 */
const RESERVED_PATH_COMPONENTS: ReadonlySet<string> = new Set([
  'con',
  'prn',
  'aux',
  'nul',
  ...Array.from({ length: 9 }, (_, index) => `com${index + 1}`),
  ...Array.from({ length: 9 }, (_, index) => `lpt${index + 1}`),
]);

/**
 * Lean admits `'`, `!` and `?` in a module name; a URL does not. `?` and `#` would turn the rest
 * of an ESM specifier into a query or a fragment, `%` would introduce percent-decoding, and a
 * separator or a traversal segment would leave the generated tree altogether. The emitted path
 * component is therefore restricted to a subset that is literal in a specifier and portable as a
 * filename, and a module outside it is refused by name rather than escaped into something else.
 */
function assertPathSafeComponent(component: string, leanModule: string): void {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/u.test(component)) {
    throw new TypeError(
      `Lean module ${leanModule} has a component outside the path-safe subset [A-Za-z_][A-Za-z0-9_]*: ${component}`,
    );
  }
  if (RESERVED_PATH_COMPONENTS.has(component.toLowerCase())) {
    throw new TypeError(`Lean module ${leanModule} names the reserved path component ${component}`);
  }
}

/** Where one Lean module's declarations are emitted: `A.B.C` becomes `A/B/C.ts`. */
export function generatedModulePath(leanModule: string): string {
  if (!isLeanModuleName(leanModule)) throw new TypeError(`invalid Lean module name: ${leanModule}`);
  const components = leanModule.split('.');
  for (const component of components) assertPathSafeComponent(component, leanModule);
  const path = `${components.join('/')}.ts`;
  if (path === LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH) {
    throw new TypeError(`Lean module ${leanModule} claims the generated runtime module path`);
  }
  return path;
}

/** The canonical order of generated modules: by path, by code point, independent of locale. */
export function compareGeneratedPaths(left: string, right: string): number {
  return compareCodePoints(left, right);
}

/**
 * Validates a generated module path before it becomes an ESM specifier. This is deliberately
 * stricter than `path.normalize`: normalization would silently turn an attacker-controlled `..`
 * or separator into a different module, while generation must either preserve the module identity
 * literally or reject it.
 */
function assertGeneratedModulePath(path: string): void {
  if (path === LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH) return;
  if (!path.endsWith('.ts') || path.includes('\\') || /[?#%]/u.test(path)) {
    throw new TypeError(`invalid generated module path: ${path}`);
  }
  const components = path.slice(0, -'.ts'.length).split('/');
  if (components.length === 0 || components.some((component) => !/^[A-Za-z_][A-Za-z0-9_]*$/u.test(component))) {
    throw new TypeError(`invalid generated module path: ${path}`);
  }
}

/** The ESM specifier one generated module uses to reach another. */
export function relativeModuleSpecifier(fromPath: string, toPath: string): string {
  assertGeneratedModulePath(fromPath);
  assertGeneratedModulePath(toPath);
  const fromDirectory = fromPath.split('/').slice(0, -1);
  const toSegments = toPath.split('/');
  const toDirectory = toSegments.slice(0, -1);
  const filename = toSegments[toSegments.length - 1];
  if (filename === undefined) throw new TypeError(`invalid generated module path: ${toPath}`);
  let shared = 0;
  while (
    shared < fromDirectory.length &&
    shared < toDirectory.length &&
    fromDirectory[shared] === toDirectory[shared]
  ) {
    shared += 1;
  }
  const ascent = Array.from({ length: fromDirectory.length - shared }, () => '..');
  const descent = toDirectory.slice(shared);
  const target = `${filename.replace(/\.ts$/u, '')}.js`;
  const specifier = [...ascent, ...descent, target].join('/');
  return ascent.length === 0 ? `./${specifier}` : specifier;
}

/** Which generated module owns each emitted top-level name. */
export type NameOwners = ReadonlyMap<string, string>;

/**
 * Every top-level name a printed statement binds. A generated module's own bindings are what it
 * can export, and what every other module has to import instead of redeclaring.
 */
export function declaredNames(statements: readonly ts.Statement[]): readonly string[] {
  const names: string[] = [];
  for (const statement of statements) {
    if (ts.isVariableStatement(statement)) {
      for (const declaration of statement.declarationList.declarations) {
        if (ts.isIdentifier(declaration.name)) names.push(declaration.name.text);
      }
      continue;
    }
    if (
      (ts.isFunctionDeclaration(statement) ||
        ts.isClassDeclaration(statement) ||
        ts.isInterfaceDeclaration(statement) ||
        ts.isTypeAliasDeclaration(statement)) &&
      statement.name !== undefined
    ) {
      names.push(statement.name.text);
    }
  }
  return names;
}

/** Whether a printed statement is exported, which decides if another module may import it. */
export function isExportedStatement(statement: ts.Statement): boolean {
  return (
    ts.canHaveModifiers(statement) &&
    (ts.getModifiers(statement) ?? []).some((modifier) => modifier.kind === ts.SyntaxKind.ExportKeyword)
  );
}

/**
 * Adds `export` to a declaration another generated module names. A helper stays module-private
 * until something imports it, so the emitted surface is exactly what the package's imports
 * require. Functions and type aliases are the two shapes the generated prelude places in a shared
 * module; every other statement already carries the export its own emitter decided.
 */
export function exportedDeclaration(statement: ts.Statement, required: ReadonlySet<string>): ts.Statement {
  if (isExportedStatement(statement)) return statement;
  if (ts.isFunctionDeclaration(statement) && statement.name !== undefined && required.has(statement.name.text)) {
    return ts.factory.updateFunctionDeclaration(
      statement,
      [ts.factory.createModifier(ts.SyntaxKind.ExportKeyword), ...(ts.getModifiers(statement) ?? [])],
      statement.asteriskToken,
      statement.name,
      statement.typeParameters,
      statement.parameters,
      statement.type,
      statement.body,
    );
  }
  if (ts.isTypeAliasDeclaration(statement) && required.has(statement.name.text)) {
    return ts.factory.updateTypeAliasDeclaration(
      statement,
      [ts.factory.createModifier(ts.SyntaxKind.ExportKeyword), ...(ts.getModifiers(statement) ?? [])],
      statement.name,
      statement.typeParameters,
      statement.type,
    );
  }
  return statement;
}

/** What one module refers to, split by whether the reference survives type erasure. */
export interface ModuleReferences {
  readonly all: ReadonlySet<string>;
  readonly values: ReadonlySet<string>;
}

/**
 * One lexical scope in generated TypeScript. Type and value names are separate namespaces: a type
 * parameter `A` must not hide a value import inside `typeof A`, and a value parameter `left` must
 * not hide an external type named `left` in a type annotation.
 */
interface LexicalScope {
  readonly parent: LexicalScope | undefined;
  readonly values: ReadonlySet<string>;
  readonly types: ReadonlySet<string>;
}

interface ScopeBindings {
  readonly values: readonly string[];
  readonly types: readonly string[];
}

/** The common syntax surface of a generated callable declaration or signature. */
interface CallableNode {
  readonly typeParameters?: readonly ts.TypeParameterDeclaration[];
  readonly parameters: readonly ts.ParameterDeclaration[];
  readonly type?: ts.TypeNode;
  readonly body?: ts.ConciseBody;
}

/**
 * Every name a statement uses, and which names survive type erasure. The traversal resolves the
 * lexical binders it sees before consulting the module owner map: a helper local such as `left`, a
 * type parameter such as `A`, or a loop local such as `codeUnit` is never an import merely because
 * another generated module happens to export the same spelling.
 */
export function referencedNames(statements: readonly ts.Statement[]): ModuleReferences {
  const all = new Set<string>();
  const values = new Set<string>();
  const root = scope(undefined, statementBindings(statements));

  const addReference = (name: string, inType: boolean, current: LexicalScope): void => {
    if (isBound(current, name, inType)) return;
    all.add(name);
    if (!inType) values.add(name);
  };

  const visitEntityName = (name: ts.EntityName, inType: boolean, current: LexicalScope): void => {
    if (ts.isIdentifier(name)) {
      addReference(name.text, inType, current);
      return;
    }
    // `A.B.C` imports only its root. `B` and `C` select members of that root; treating either as a
    // free name would synthesize an import when another module exports one by coincidence.
    visitEntityName(name.left, inType, current);
  };

  const visitPropertyName = (name: ts.PropertyName, current: LexicalScope): void => {
    if (ts.isComputedPropertyName(name)) visit(name.expression, false, current);
  };

  const visitTypeParameters = (
    parameters: readonly ts.TypeParameterDeclaration[] | undefined,
    current: LexicalScope,
  ): void => {
    for (const parameter of parameters ?? []) {
      if (parameter.constraint !== undefined) visit(parameter.constraint, true, current);
      if (parameter.default !== undefined) visit(parameter.default, true, current);
    }
  };

  const visitParameters = (parameters: readonly ts.ParameterDeclaration[], current: LexicalScope): void => {
    for (const parameter of parameters) {
      if (parameter.type !== undefined) visit(parameter.type, true, current);
      if (parameter.initializer !== undefined) visit(parameter.initializer, false, current);
    }
  };

  const visitCallable = (node: CallableNode, current: LexicalScope): void => {
    const typeNames = typeParameterBindings(node.typeParameters);
    const valueNames = parameterBindings(node.parameters);
    const callable = scope(current, { values: valueNames, types: typeNames });
    visitTypeParameters(node.typeParameters, callable);
    visitParameters(node.parameters, callable);
    if (node.type !== undefined) visit(node.type, true, callable);
    if (node.body !== undefined) visit(node.body, false, callable);
  };

  const visitClass = (node: ts.ClassDeclaration | ts.ClassExpression, current: LexicalScope): void => {
    const className = node.name === undefined ? [] : [node.name.text];
    const classScope = scope(current, {
      values: className,
      types: [...className, ...typeParameterBindings(node.typeParameters)],
    });
    visitTypeParameters(node.typeParameters, classScope);
    for (const clause of node.heritageClauses ?? []) visit(clause, false, classScope);
    for (const member of node.members) visit(member, false, classScope);
  };

  const visitInterface = (node: ts.InterfaceDeclaration, current: LexicalScope): void => {
    const interfaceScope = scope(current, { values: [], types: [node.name.text, ...typeParameterBindings(node.typeParameters)] });
    visitTypeParameters(node.typeParameters, interfaceScope);
    for (const clause of node.heritageClauses ?? []) visit(clause, false, interfaceScope);
    for (const member of node.members) visit(member, true, interfaceScope);
  };

  const visitVariableDeclaration = (node: ts.VariableDeclaration, current: LexicalScope): void => {
    if (ts.isObjectBindingPattern(node.name) || ts.isArrayBindingPattern(node.name)) {
      for (const element of node.name.elements) {
        if (ts.isBindingElement(element) && element.propertyName !== undefined) visitPropertyName(element.propertyName, current);
        if (ts.isBindingElement(element) && element.initializer !== undefined) visit(element.initializer, false, current);
      }
    }
    if (node.type !== undefined) visit(node.type, true, current);
    if (node.initializer !== undefined) visit(node.initializer, false, current);
  };

  const visitStatements = (entries: readonly ts.Statement[], current: LexicalScope): void => {
    const blockScope = scope(current, statementBindings(entries));
    for (const entry of entries) visit(entry, false, blockScope);
  };

  const visitFor = (node: ts.ForStatement, current: LexicalScope): void => {
    const loop = scope(current, variableBindings(node.initializer));
    if (node.initializer !== undefined) visit(node.initializer, false, loop);
    if (node.condition !== undefined) visit(node.condition, false, loop);
    if (node.incrementor !== undefined) visit(node.incrementor, false, loop);
    visit(node.statement, false, loop);
  };

  const visitForInOrOf = (node: ts.ForInOrOfStatement, current: LexicalScope): void => {
    const loop = scope(current, variableBindings(node.initializer));
    visit(node.initializer, false, loop);
    visit(node.expression, false, loop);
    visit(node.statement, false, loop);
  };

  const visit = (node: ts.Node, inType: boolean, current: LexicalScope): void => {
    if (ts.isIdentifier(node)) {
      addReference(node.text, inType, current);
      return;
    }
    if (ts.isQualifiedName(node)) {
      visitEntityName(node, inType, current);
      return;
    }
    if (ts.isPropertyAccessExpression(node)) {
      visit(node.expression, false, current);
      return;
    }
    if (ts.isPropertyAssignment(node)) {
      visitPropertyName(node.name, current);
      visit(node.initializer, false, current);
      return;
    }
    if (ts.isShorthandPropertyAssignment(node)) {
      addReference(node.name.text, false, current);
      if (node.objectAssignmentInitializer !== undefined) visit(node.objectAssignmentInitializer, false, current);
      return;
    }
    if (ts.isTypeReferenceNode(node)) {
      visitEntityName(node.typeName, true, current);
      for (const argument of node.typeArguments ?? []) visit(argument, true, current);
      return;
    }
    if (ts.isTypePredicateNode(node)) {
      // `value is T` sits inside a type annotation, but `value` resolves in the callable's value
      // scope; only the narrowed `T` resolves in type space.
      if (ts.isIdentifier(node.parameterName)) addReference(node.parameterName.text, false, current);
      if (node.type !== undefined) visit(node.type, true, current);
      return;
    }
    // `typeof x` and a heritage clause name a value from inside a type, so the reference returns
    // to value position rather than being erased with the type that encloses it.
    if (ts.isTypeQueryNode(node)) {
      visitEntityName(node.exprName, false, current);
      return;
    }
    if (ts.isExpressionWithTypeArguments(node)) {
      visit(node.expression, false, current);
      for (const argument of node.typeArguments ?? []) visit(argument, true, current);
      return;
    }
    if (ts.isFunctionDeclaration(node) || ts.isFunctionExpression(node) || ts.isArrowFunction(node)) {
      visitCallable(node, current);
      return;
    }
    if (ts.isMethodDeclaration(node) || ts.isMethodSignature(node) || ts.isGetAccessorDeclaration(node) ||
      ts.isSetAccessorDeclaration(node) || ts.isConstructorDeclaration(node) || ts.isFunctionTypeNode(node) ||
      ts.isConstructorTypeNode(node) || ts.isCallSignatureDeclaration(node) || ts.isConstructSignatureDeclaration(node) ||
      ts.isIndexSignatureDeclaration(node)) {
      visitCallable(node, current);
      return;
    }
    if (ts.isClassDeclaration(node) || ts.isClassExpression(node)) {
      visitClass(node, current);
      return;
    }
    if (ts.isInterfaceDeclaration(node)) {
      visitInterface(node, current);
      return;
    }
    if (ts.isTypeAliasDeclaration(node)) {
      const aliasScope = scope(current, { values: [], types: [node.name.text, ...typeParameterBindings(node.typeParameters)] });
      visitTypeParameters(node.typeParameters, aliasScope);
      visit(node.type, true, aliasScope);
      return;
    }
    if (ts.isVariableDeclaration(node)) {
      visitVariableDeclaration(node, current);
      return;
    }
    if (ts.isBlock(node)) {
      visitStatements(node.statements, current);
      return;
    }
    if (ts.isForStatement(node)) {
      visitFor(node, current);
      return;
    }
    if (ts.isForInStatement(node) || ts.isForOfStatement(node)) {
      visitForInOrOf(node, current);
      return;
    }
    if (ts.isCatchClause(node)) {
      const catchScope = scope(current, { values: node.variableDeclaration === undefined ? [] : bindingNames(node.variableDeclaration.name), types: [] });
      if (node.variableDeclaration !== undefined) visitVariableDeclaration(node.variableDeclaration, catchScope);
      visit(node.block, false, catchScope);
      return;
    }
    if (ts.isPropertyDeclaration(node)) {
      visitPropertyName(node.name, current);
      if (node.type !== undefined) visit(node.type, true, current);
      if (node.initializer !== undefined) visit(node.initializer, false, current);
      return;
    }
    if (ts.isPropertySignature(node)) {
      visitPropertyName(node.name, current);
      if (node.type !== undefined) visit(node.type, true, current);
      return;
    }
    if (ts.isLabeledStatement(node)) {
      visit(node.statement, inType, current);
      return;
    }
    if (ts.isBreakStatement(node) || ts.isContinueStatement(node)) return;
    ts.forEachChild(node, (child) => visit(child, inType || ts.isTypeNode(node), current));
  };

  for (const statement of statements) visit(statement, false, root);
  return { all, values };
}

function scope(parent: LexicalScope | undefined, bindings: ScopeBindings): LexicalScope {
  return { parent, values: new Set(bindings.values), types: new Set(bindings.types) };
}

function isBound(scope: LexicalScope, name: string, inType: boolean): boolean {
  for (let current: LexicalScope | undefined = scope; current !== undefined; current = current.parent) {
    if ((inType ? current.types : current.values).has(name)) return true;
  }
  return false;
}

function statementBindings(statements: readonly ts.Statement[]): ScopeBindings {
  const values: string[] = [];
  const types: string[] = [];
  for (const statement of statements) {
    if (ts.isVariableStatement(statement)) {
      for (const declaration of statement.declarationList.declarations) values.push(...bindingNames(declaration.name));
      continue;
    }
    if (ts.isFunctionDeclaration(statement) && statement.name !== undefined) {
      values.push(statement.name.text);
      continue;
    }
    if (ts.isClassDeclaration(statement) && statement.name !== undefined) {
      values.push(statement.name.text);
      types.push(statement.name.text);
      continue;
    }
    if (ts.isInterfaceDeclaration(statement) || ts.isTypeAliasDeclaration(statement)) {
      types.push(statement.name.text);
      continue;
    }
    if (ts.isEnumDeclaration(statement)) {
      values.push(statement.name.text);
      types.push(statement.name.text);
    }
  }
  return { values, types };
}

function variableBindings(initializer: ts.Node | undefined): ScopeBindings {
  if (initializer === undefined || !ts.isVariableDeclarationList(initializer)) return { values: [], types: [] };
  return { values: initializer.declarations.flatMap((declaration) => bindingNames(declaration.name)), types: [] };
}

function typeParameterBindings(parameters: readonly ts.TypeParameterDeclaration[] | undefined): readonly string[] {
  return (parameters ?? []).map((parameter) => parameter.name.text);
}

function parameterBindings(parameters: readonly ts.ParameterDeclaration[]): readonly string[] {
  return parameters.flatMap((parameter) => bindingNames(parameter.name));
}

function bindingNames(name: ts.BindingName): readonly string[] {
  if (ts.isIdentifier(name)) return [name.text];
  return name.elements.flatMap((element) => (ts.isBindingElement(element) ? bindingNames(element.name) : []));
}

export interface ModuleImport {
  readonly specifier: string;
  readonly names: readonly string[];
  /** Imported names this module only ever mentions in type position. */
  readonly typeOnly: ReadonlySet<string>;
}

/**
 * What one generated module imports, resolved against the package's owner map. Names are sorted
 * inside a specifier and specifiers are sorted against each other, so the emitted import block
 * is a function of the module graph alone.
 */
export function moduleImports(
  path: string,
  statements: readonly ts.Statement[],
  owners: NameOwners,
): readonly ModuleImport[] {
  const references = referencedNames(statements);
  const byOwner = new Map<string, string[]>();
  for (const name of references.all) {
    const owner = owners.get(name);
    if (owner === undefined || owner === path) continue;
    const existing = byOwner.get(owner);
    if (existing === undefined) byOwner.set(owner, [name]);
    else existing.push(name);
  }
  return [...byOwner]
    .sort(([left], [right]) => compareCodePoints(left, right))
    .map(([owner, names]) => ({
      specifier: relativeModuleSpecifier(path, owner),
      names: [...names].sort(compareCodePoints),
      typeOnly: new Set(names.filter((name) => !references.values.has(name))),
    }));
}

/**
 * One import declaration per source module. A name the importing module only mentions in type
 * position carries an inline `type` marker, so the emitted tree is correct under
 * `verbatimModuleSyntax` and a reader can see which names disappear at runtime.
 */
export function importStatement(entry: ModuleImport): ts.Statement {
  return ts.factory.createImportDeclaration(
    undefined,
    ts.factory.createImportClause(
      false,
      undefined,
      ts.factory.createNamedImports(
        entry.names.map((name) =>
          ts.factory.createImportSpecifier(entry.typeOnly.has(name), undefined, ts.factory.createIdentifier(name)),
        ),
      ),
    ),
    ts.factory.createStringLiteral(entry.specifier),
    undefined,
  );
}

/** Declarations grouped by the Lean module that declares them, in emission order. */
export function groupByLeanModule(
  ordered: readonly LeanDeclaration[],
): ReadonlyMap<string, readonly LeanDeclaration[]> {
  const groups = new Map<string, LeanDeclaration[]>();
  for (const leanModule of [...new Set(ordered.map((declaration) => declaration.module))].sort(compareCodePoints)) {
    groups.set(leanModule, []);
  }
  for (const declaration of ordered) {
    const group = groups.get(declaration.module);
    if (group === undefined) throw new TypeError(`declaration ${declaration.name} has no module group`);
    group.push(declaration);
  }
  return groups;
}
