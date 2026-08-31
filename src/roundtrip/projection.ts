/**
 * @module roundtrip/projection
 *
 * Cut a module down to its profile declarations.
 *
 * A generated module carries the declarations that came from Lean together with the
 * decoders that turn untrusted host data into them. The decoders take the emitter's data
 * union, which has no Lean carrier, so they are outside the profile and the round trip
 * cannot carry them back. The projection removes them and keeps everything else.
 *
 * The cut is made on the syntax tree, so no declaration is selected by matching its name
 * or its text. Whether the cut lost meaning is answered separately: the projected module
 * has to type-check on its own, and it has to still contain every declaration the emitter
 * recorded as the image of a Lean declaration.
 */

import ts from 'typescript';
import { profileModule, type ModuleProfile, type ProfileDeclaration } from './profile.js';

export interface ProjectedModule {
  /** The module path this projection came from. */
  readonly path: string;
  /** The projected TypeScript source. */
  readonly source: string;
  /** How the profile classified the original module. */
  readonly profile: ModuleProfile;
}

const PRINTER = ts.createPrinter({ newLine: ts.NewLineKind.LineFeed, removeComments: false });

/**
 * The profile projection of one module.
 *
 * Import specifiers survive only where the projected declarations still name them, so a
 * module that imported only for its decoders imports nothing afterwards.
 */
export function projectModule(
  source: ts.SourceFile,
  checker: ts.TypeChecker,
  path: string,
): ProjectedModule {
  const profile = profileModule(source, checker);
  const admittedNodes = new Set<ts.Node>(profile.admitted.map((entry) => entry.node));
  const kept: ts.Statement[] = [];

  for (const statement of source.statements) {
    if (ts.isImportDeclaration(statement)) continue;
    if (!admittedNodes.has(statement)) continue;
    kept.push(ts.isClassDeclaration(statement) ? keepProfileMembers(statement, profile) : statement);
  }

  const referenced = referencedNames(kept);
  const imports = source.statements
    .filter(ts.isImportDeclaration)
    .map((declaration) => narrowImport(declaration, referenced))
    .filter((declaration): declaration is ts.ImportDeclaration => declaration !== undefined);

  const projected = ts.factory.updateSourceFile(source, [...imports, ...kept]);
  return { path, source: PRINTER.printFile(projected), profile };
}

/** Drop the members of a class the profile refused, keeping its data and its constructor. */
function keepProfileMembers(
  declaration: ts.ClassDeclaration,
  profile: ModuleProfile,
): ts.ClassDeclaration {
  const admitted = new Set<ts.Node>(
    profile.admitted.filter((entry: ProfileDeclaration) => entry.kind === 'method').map((entry) => entry.node),
  );
  const members = declaration.members.filter(
    (member) =>
      ts.isPropertyDeclaration(member) || ts.isConstructorDeclaration(member) || admitted.has(member),
  );
  return ts.factory.updateClassDeclaration(
    declaration,
    declaration.modifiers,
    declaration.name,
    declaration.typeParameters,
    declaration.heritageClauses,
    members,
  );
}

/** Every identifier the projected statements mention, including in type positions. */
function referencedNames(statements: readonly ts.Statement[]): ReadonlySet<string> {
  const names = new Set<string>();
  const walk = (node: ts.Node): void => {
    if (ts.isIdentifier(node)) names.add(node.text);
    ts.forEachChild(node, walk);
  };
  for (const statement of statements) walk(statement);
  return names;
}

/** The same import with only the specifiers the projection still needs, or nothing. */
function narrowImport(
  declaration: ts.ImportDeclaration,
  referenced: ReadonlySet<string>,
): ts.ImportDeclaration | undefined {
  const clause = declaration.importClause;
  if (clause === undefined) return undefined;
  const bindings = clause.namedBindings;
  if (bindings === undefined || !ts.isNamedImports(bindings)) return undefined;
  const elements = bindings.elements.filter((element) => referenced.has(element.name.text));
  if (elements.length === 0) return undefined;
  return ts.factory.updateImportDeclaration(
    declaration,
    declaration.modifiers,
    ts.factory.updateImportClause(
      clause,
      clause.phaseModifier,
      clause.name,
      ts.factory.updateNamedImports(bindings, elements),
    ),
    declaration.moduleSpecifier,
    declaration.attributes,
  );
}
