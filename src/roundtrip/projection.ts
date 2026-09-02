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
 *
 * What is kept is *copied*, not printed. Printing a source file assembled from parsed
 * statements moves the comments of the statements that were left out: the module's own
 * header and every dropped declaration's documentation reappear at the end of the output,
 * which both resurrects the prose of a declaration the projection just removed and stops
 * the projection from being a fixed point. So each kept statement is reproduced from its
 * own source range — its full start through its end, which is the statement together with
 * the leading trivia its documentation comment sits in — and the ranges are joined. A range
 * the projection does not copy takes its comments with it, and a second projection copies
 * the same ranges again, so the result is stable.
 *
 * Two statement kinds are not copied whole. A class whose members the profile filtered is
 * copied member by member, so a kept member keeps the documentation it was written with. A
 * narrowed import is the one statement the projection rewrites rather than selects, so it
 * is built with the factory and printed; an import carries no documentation of its own, and
 * the trivia in front of it — where a generated module's header lives — is still copied.
 */

import { tmpdir } from 'node:os';
import { join } from 'node:path';
import * as ts from '../typescript-api/index.js';
import { forget, openProject, printNode, renderDiagnostic } from '../typescript-api/session.js';
import { profileModule, type ModuleProfile, type ProfileDeclaration } from './profile.js';

export interface ProjectedModule {
  /** The module path this projection came from. */
  readonly path: string;
  /** The projected TypeScript source. */
  readonly source: string;
  /** How the profile classified the original module. */
  readonly profile: ModuleProfile;
}

/** One statement the projection keeps: the text it contributes, and what it still mentions. */
interface KeptStatement {
  readonly text: string;
  /** The nodes actually kept, which is what the projection can still name. */
  readonly nodes: readonly ts.Node[];
}

/** Where the projection parses itself back. Nothing is written there; the text is virtual. */
const CHECK_ROOT = join(tmpdir(), 'tslean-projection-check');

/**
 * The profile projection of one module.
 *
 * Import specifiers survive only where the projected declarations still name them, so a
 * module that imported only for its decoders imports nothing afterwards.
 */
export function projectModule(source: ts.SourceFile, checker: ts.Checker, path: string): ProjectedModule {
  const profile = profileModule(source, checker);
  const admitted = new Set<ts.Node>(profile.admitted.map((entry) => entry.node));

  const kept = new Map<ts.Statement, KeptStatement>();
  for (const statement of source.statements) {
    if (ts.isImportDeclaration(statement) || !admitted.has(statement)) continue;
    kept.set(statement, keepStatement(source, statement, profile));
  }
  const referenced = referencedNames([...kept.values()].flatMap((entry) => entry.nodes));

  // Source order, so the trivia between two statements is copied exactly once and the
  // module's own header stays in front of whatever the module opened with.
  const segments: string[] = [];
  for (const statement of source.statements) {
    if (ts.isImportDeclaration(statement)) {
      const projected = projectImport(source, statement, referenced);
      if (projected !== undefined) segments.push(projected);
      continue;
    }
    const entry = kept.get(statement);
    if (entry !== undefined) segments.push(entry.text);
  }

  const projected = `${segments.join('')}\n`;
  requireTypeScript(projected, path);
  return { path, source: projected, profile };
}

/** What one kept statement contributes, copied from the module's own source. */
function keepStatement(
  source: ts.SourceFile,
  statement: ts.Statement,
  profile: ModuleProfile,
): KeptStatement {
  if (!ts.isClassDeclaration(statement)) {
    return {
      text: source.text.slice(statement.getFullStart(), statement.getEnd()),
      nodes: [statement],
    };
  }
  const members = profileMembers(statement, profile);
  // The class outside its member list is copied whole, each kept member is copied with its
  // leading trivia, and the range of a refused member is simply never copied.
  const text = [
    source.text.slice(statement.getFullStart(), statement.members.pos),
    ...members.map((member) => source.text.slice(member.getFullStart(), member.getEnd())),
    source.text.slice(statement.members.end, statement.getEnd()),
  ].join('');
  return { text, nodes: members };
}

/** The members of a class the profile admitted, keeping its data and its constructor. */
function profileMembers(
  declaration: ts.ClassDeclaration,
  profile: ModuleProfile,
): readonly ts.ClassElement[] {
  const admitted = new Set<ts.Node>(
    profile.admitted.filter((entry: ProfileDeclaration) => entry.kind === 'method').map((entry) => entry.node),
  );
  return declaration.members.filter(
    (member) =>
      ts.isPropertyDeclaration(member) || ts.isConstructorDeclaration(member) || admitted.has(member),
  );
}

/** Every identifier the projected nodes mention, including in type positions. */
function referencedNames(nodes: readonly ts.Node[]): ReadonlySet<string> {
  const names = new Set<string>();
  const walk = (node: ts.Node): void => {
    if (ts.isIdentifier(node)) names.add(node.text);
    node.forEachChild(walk);
  };
  for (const node of nodes) walk(node);
  return names;
}

/** What an import contributes to the projection, or nothing when none of it is needed. */
function projectImport(
  source: ts.SourceFile,
  declaration: ts.ImportDeclaration,
  referenced: ReadonlySet<string>,
): string | undefined {
  const narrowed = narrowImport(declaration, referenced);
  if (narrowed === undefined) return undefined;
  if (narrowed === declaration) {
    return source.text.slice(declaration.getFullStart(), declaration.getEnd());
  }
  // A narrowed import is rewritten rather than selected, so it is the one statement printed
  // instead of copied. The trivia in front of it is still copied, because a generated
  // module's header sits there when the module opens with an import.
  return source.text.slice(declaration.getFullStart(), declaration.getStart(source)) + printNode(narrowed);
}

/**
 * The same import with only the specifiers the projection still needs: the declaration
 * itself when every specifier survives, a rebuilt one when some did not, and nothing when
 * none did or when the import binds no named specifiers to narrow.
 */
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
  if (elements.length === bindings.elements.length) return declaration;
  return ts.factory.updateImportDeclaration(
    declaration,
    declaration.modifiers,
    ts.factory.updateImportClause(clause, clause.name, ts.factory.updateNamedImports(bindings, elements)),
    declaration.moduleSpecifier,
    declaration.attributes,
  );
}

/**
 * Parse the projection back and refuse it if the compiler reports a syntax error.
 *
 * The projection is assembled out of ranges rather than rendered, so the one thing that
 * could go wrong is arithmetic: a range that starts or ends in the wrong place produces
 * text no parser accepts. Reading the text back through the compiler turns that into a
 * failure here instead of a puzzling diagnostic several stages later. Diagnostics belong to
 * a project, so the text is handed to one as a virtual file under a path nothing else reads,
 * and the session's reading of that path is dropped again afterwards.
 */
function requireTypeScript(projected: string, path: string): void {
  const checkPath = join(CHECK_ROOT, path);
  const project = openProject({
    files: [checkPath],
    settings: { noLib: true, noResolve: true },
    virtual: new Map([[checkPath, projected]]),
  });
  try {
    const diagnostics = project.program.getSyntacticDiagnostics();
    if (diagnostics.length > 0) {
      throw new TypeError(
        `the projection of ${path} is not TypeScript: ${diagnostics
          .map((diagnostic) => renderDiagnostic(diagnostic, ' '))
          .join('; ')}`,
      );
    }
  } finally {
    project.close();
    forget([checkPath]);
  }
}
