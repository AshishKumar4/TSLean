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
 * Adds `export` to a function declaration. A helper stays module-private until another generated
 * module names it, so the emitted surface is exactly what the package's imports require.
 */
export function exportedFunction(statement: ts.FunctionDeclaration): ts.FunctionDeclaration {
  if (isExportedStatement(statement)) return statement;
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

/** What one module refers to, split by whether the reference survives type erasure. */
export interface ModuleReferences {
  readonly all: ReadonlySet<string>;
  readonly values: ReadonlySet<string>;
}

/**
 * Every name a statement uses, and which of them the module still needs once types are erased. A
 * name in declaration, member, or property position binds or selects rather than refers, so it is
 * skipped: the result is exactly the set of free names the module has to resolve, and a generated
 * local can never collide with one because the identifier allocator reserves every declaration
 * name first.
 */
export function referencedNames(statements: readonly ts.Statement[]): ModuleReferences {
  const all = new Set<string>();
  const values = new Set<string>();
  const visit = (node: ts.Node, inType: boolean): void => {
    if (ts.isIdentifier(node)) {
      all.add(node.text);
      if (!inType) values.add(node.text);
      return;
    }
    // `typeof x` and a heritage clause name a value from inside a type, so the reference returns
    // to value position rather than being erased with the type that encloses it.
    if (ts.isTypeQueryNode(node) || ts.isExpressionWithTypeArguments(node)) {
      visit(ts.isTypeQueryNode(node) ? node.exprName : node.expression, false);
      for (const argument of node.typeArguments ?? []) visit(argument, true);
      return;
    }
    const bound = boundName(node);
    ts.forEachChild(node, (child) => {
      if (child !== bound) visit(child, inType || ts.isTypeNode(child));
    });
  };
  for (const statement of statements) visit(statement, false);
  return { all, values };
}

function boundName(node: ts.Node): ts.Node | undefined {
  if (
    ts.isPropertyAccessExpression(node) ||
    ts.isPropertyAssignment(node) ||
    ts.isPropertySignature(node) ||
    ts.isPropertyDeclaration(node) ||
    ts.isMethodDeclaration(node) ||
    ts.isMethodSignature(node) ||
    ts.isGetAccessorDeclaration(node) ||
    ts.isSetAccessorDeclaration(node) ||
    ts.isFunctionDeclaration(node) ||
    ts.isClassDeclaration(node) ||
    ts.isInterfaceDeclaration(node) ||
    ts.isTypeAliasDeclaration(node) ||
    ts.isVariableDeclaration(node) ||
    ts.isParameter(node) ||
    ts.isBindingElement(node)
  ) {
    return node.name;
  }
  return undefined;
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
