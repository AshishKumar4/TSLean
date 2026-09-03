/**
 * @module typescript-api/session
 *
 * The compiler session every stage that reads TypeScript reads through.
 *
 * TypeScript 7 has no in-process compiler. `typescript/unstable/sync` is a client to a separate
 * native server, and a file becomes an AST — let alone a typed one — only inside a snapshot of
 * that server's view of the world. So the work every reader would otherwise repeat lives here
 * once: spawning the server, holding the current snapshot, giving the server text for paths that
 * have no file behind them, and turning a set of root files into a project with its own program,
 * checker and printer.
 *
 * Three facts about the server shape this module, and each one is a measured fact rather than a
 * reading of the documentation:
 *
 * - **Text can come from nowhere.** `FileChangeSummary` carries only paths, so there is no way to
 *   hand the server new content for a file. The content channel is the client's `fs` option: a
 *   virtual filesystem whose `readFile` answers from {@link overlay} and returns `undefined` to
 *   fall through to the real disk. That is what lets a caller parse a string, inject ambient
 *   declarations, and open a project whose configuration was never written down.
 *
 * - **A path is read once unless the server is told otherwise.** A second project over a path
 *   whose bytes changed still sees the first read — even though the project, the program and the
 *   snapshot are all new. Every request therefore carries a change notice for each path this
 *   session has already read, which is what {@link notice} computes.
 *
 * - **An open file's text is pinned when it is opened.** A change notice does not unpin it, and
 *   neither does closing the snapshot. Re-reading an open path takes a close carrying the change
 *   notice followed by a separate reopen; both in one update yields no project at all. That is
 *   what {@link release} is for.
 *
 * Projects stay readable after later snapshots, each holding the bytes it was built from, so a
 * caller may hold several at once — the round trip holds one program per lap. A caller that is
 * finished with a project says so through {@link ReadProject.close}, and nothing read through it
 * may be used afterwards.
 */

import { isAbsolute, dirname, sep } from 'node:path';
import {
  API,
  type Checker,
  type Diagnostic,
  type Program,
  type Project,
  type Snapshot,
} from 'typescript/unstable/sync';
import type { Node, SourceFile } from 'typescript/unstable/ast';

/**
 * Compiler options, spelled the way a `tsconfig.json` writes them rather than the way the
 * compiler resolves them: `target: 'es2022'`, `lib: ['es2022']`. The server parses the
 * configuration it is handed as configuration text, so a resolved spelling — `lib` as
 * `['lib.es2022.d.ts']`, `target` as a number — is refused with an option diagnostic.
 */
export interface CompilerSettings {
  readonly target?: string;
  readonly module?: string;
  readonly moduleResolution?: string;
  readonly lib?: readonly string[];
  readonly types?: readonly string[];
  readonly strict?: boolean;
  readonly skipLibCheck?: boolean;
  readonly noLib?: boolean;
  readonly noEmit?: boolean;
  readonly noResolve?: boolean;
  readonly noUnusedLocals?: boolean;
  readonly rootDir?: string;
  readonly baseUrl?: string;
  readonly paths?: Readonly<Record<string, readonly string[]>>;
}

/** A project to open: its root files, its options, and text for paths that have no file. */
export interface ProjectRequest {
  /** Absolute paths of the root files, in the order the program should hold them. */
  readonly files: readonly string[];
  readonly settings: CompilerSettings;
  /** Text for paths whose content does not come from disk, keyed by absolute path. */
  readonly virtual?: ReadonlyMap<string, string>;
}

/** An open project: the program and checker over its roots, and the compiler's own printer. */
export interface ReadProject {
  readonly program: Program;
  readonly checker: Checker;
  /** The AST of one path, or `undefined` when the program does not hold it. */
  sourceFile(path: string): SourceFile | undefined;
  /** The AST of one path, which the program must hold. */
  requireSourceFile(path: string): SourceFile;
  /** Every diagnostic the compiler reports for this project, before any emit. */
  diagnostics(): readonly Diagnostic[];
  /** One syntax node, printed the way the compiler writes it into a file. */
  print(node: Node): string;
  /** Releases the project. Nothing read through it may be used afterwards. */
  close(): void;
}

/** A `tsconfig.json` as the compiler reads it: what it resolved, selected, and objected to. */
export interface ParsedConfiguration {
  /**
   * The options the compiler resolved, keyed by option name, with values in the compiler's own
   * resolved spelling — `target` as a `ScriptTarget` number, `lib` as file names. It is a record
   * of unknowns because that is what the server answers with; a caller reads the options it needs
   * and checks each one, rather than being handed a shape nobody verified.
   */
  readonly options: Readonly<Record<string, unknown>>;
  readonly fileNames: readonly string[];
  /** What the compiler objected to in the configuration itself. Empty means it had no objection. */
  readonly diagnostics: readonly Diagnostic[];
}

/** Content for paths whose text does not come from disk. Absent means "read the disk". */
const overlay = new Map<string, string>();
/** Every path the server has read through this session, so a re-read carries a change notice. */
const seen = new Set<string>();
/** Paths open on the server. An open file's text is pinned at open time. */
const opened = new Set<string>();
/** The text each open path was last read with, so re-reading identical text is free. */
const openText = new Map<string, string>();

let client: API | undefined;
let snapshot: Snapshot | undefined;
let projectCount = 0;
let printing: ReadProject | undefined;

function server(): API {
  client ??= new API({
    cwd: process.cwd(),
    fs: {
      readFile: (path) => overlay.get(path),
      fileExists: (path) => (overlay.has(path) ? true : undefined),
    },
  });
  return client;
}

/**
 * One snapshot update. The wire request holds mutable arrays, so every path list is copied into
 * one; `changed` is the set of paths whose bytes the server must read again rather than answer
 * from what it read the first time.
 */
function update(params: {
  readonly openProjects?: readonly string[];
  readonly closeProjects?: readonly string[];
  readonly openFiles?: readonly string[];
  readonly closeFiles?: readonly string[];
  readonly changed?: readonly string[];
}): Snapshot {
  const { openProjects, closeProjects, openFiles, closeFiles, changed } = params;
  snapshot = server().updateSnapshot({
    ...(openProjects === undefined ? {} : { openProjects: [...openProjects] }),
    ...(closeProjects === undefined ? {} : { closeProjects: [...closeProjects] }),
    ...(openFiles === undefined ? {} : { openFiles: [...openFiles] }),
    ...(closeFiles === undefined ? {} : { closeFiles: [...closeFiles] }),
    ...(changed === undefined || changed.length === 0 ? {} : { fileChanges: { changed: [...changed] } }),
  });
  return snapshot;
}

function requireAbsolute(path: string): string {
  if (!isAbsolute(path)) {
    throw new TypeError(`the compiler session reads absolute paths only, and was given ${path}`);
  }
  return path;
}

/**
 * The components of the deepest directory that contains every root file, without a leading
 * separator. This is where a synthetic configuration is placed: option paths and root files are
 * absolute, so the only thing the configuration's own directory decides is where a package
 * lookup starts, and the roots' own tree is that answer. The separator is re-attached by the
 * caller, because an empty answer must join into one `/` that names the filesystem root — the
 * two-separator `//...` the server refuses, and a refusal is not recoverable, since the failed
 * name stays the one the snapshot holds.
 */
function commonDirectoryComponents(files: readonly string[]): readonly string[] {
  const [first] = files;
  if (first === undefined)
    return process
      .cwd()
      .split(sep)
      .filter((part) => part !== '');
  let common = dirname(first)
    .split(sep)
    .filter((part) => part !== '');
  for (const file of files.slice(1)) {
    const parts = dirname(file)
      .split(sep)
      .filter((part) => part !== '');
    let index = 0;
    while (index < common.length && index < parts.length && common[index] === parts[index]) index += 1;
    common = common.slice(0, index);
  }
  return common;
}

/**
 * A project over an exact set of root files. TypeScript 7 builds a program only from a
 * configuration file, so the configuration is written into the session's overlay: the server
 * reads it like any other file and nothing is left on disk.
 */
export function openProject(request: ProjectRequest): ReadProject {
  const files = request.files.map(requireAbsolute);
  for (const [path, text] of request.virtual ?? new Map<string, string>()) {
    const absolute = requireAbsolute(path);
    release([absolute]);
    overlay.set(absolute, text);
  }
  const configPath = [
    sep,
    ...commonDirectoryComponents(files),
    `tsconfig.tslean-session-${(projectCount += 1)}.json`,
  ].join('');
  overlay.set(configPath, JSON.stringify({ compilerOptions: request.settings, files, include: [] }));
  const loaded = update({
    openProjects: [configPath],
    changed: files.filter((file) => seen.has(file)),
  }).getProject(configPath);
  if (loaded === undefined) {
    throw new TypeError(`the compiler session could not open a project over ${String(files.length)} file(s)`);
  }
  for (const file of files) seen.add(file);
  return readProject(loaded, configPath);
}

function readProject(project: Project, configPath: string): ReadProject {
  const { program, checker } = project;
  return {
    program,
    checker,
    sourceFile: (path) => program.getSourceFile(requireAbsolute(path)),
    requireSourceFile: (path) => {
      const source = program.getSourceFile(requireAbsolute(path));
      if (source === undefined) throw new TypeError(`the project holds no source file at ${path}`);
      return source;
    },
    diagnostics: () => [
      ...program.getConfigFileParsingDiagnostics(),
      ...program.getProgramDiagnostics(),
      ...program.getSyntacticDiagnostics(),
      ...program.getGlobalDiagnostics(),
      ...program.getSemanticDiagnostics(),
    ],
    print: (node) => project.emitter.printNode(node),
    close: () => {
      overlay.delete(configPath);
      update({ closeProjects: [configPath] });
    },
  };
}

/**
 * The AST of `text` as if it were the file at `path`, without a checker. The text is held in the
 * session's overlay, so nothing is written to disk and a path with no file behind it is as valid
 * a source as one with. Parsing the same path with the same text again returns the same AST.
 */
export function parseSource(path: string, text: string): SourceFile {
  const absolute = requireAbsolute(path);
  if (openText.get(absolute) === text) {
    const cached = materialize(absolute);
    if (cached !== undefined) return cached;
  }
  release([absolute]);
  overlay.set(absolute, text);
  openText.set(absolute, text);
  return openSyntax(absolute, `the compiler session could not parse the source given for ${path}`);
}

/** The AST of a file on disk, without a checker, reading whatever is there now. */
export function readSourceFile(path: string): SourceFile {
  const absolute = requireAbsolute(path);
  release([absolute]);
  overlay.delete(absolute);
  openText.delete(absolute);
  return openSyntax(absolute, `the compiler session could not read a source file at ${path}`);
}

function openSyntax(path: string, failure: string): SourceFile {
  opened.add(path);
  update({ openFiles: [path], changed: seen.has(path) ? [path] : [] });
  seen.add(path);
  const source = materialize(path);
  if (source === undefined) throw new TypeError(failure);
  return source;
}

/** The AST the server now holds for a path: its default project's program is where it lands. */
function materialize(path: string): SourceFile | undefined {
  return (snapshot ?? update({})).getDefaultProjectForFile(path)?.program.getSourceFile(path);
}

/**
 * Drops the session's reading of these paths. An open file's text is pinned at open time and a
 * change notice alone does not unpin it, so releasing is a close carrying that notice; the
 * reopen that follows is what reads the text again.
 */
function release(paths: readonly string[]): void {
  const closing = paths.filter((path) => opened.has(path));
  if (closing.length === 0) return;
  for (const path of closing) {
    opened.delete(path);
    openText.delete(path);
  }
  update({ closeFiles: closing, changed: closing });
}

/**
 * Forgets what the session read for these paths, so the next read sees what is on disk now. A
 * stage that rewrites a file it has already read says so here; nothing else has to care that
 * reads are held.
 *
 * The path stays in {@link seen}, because that set is exactly what makes the next request carry a
 * change notice, and the notice is the only thing that makes the server re-read a path. Dropping
 * it here is what would leave a rewritten file graded against its old bytes.
 */
export function forget(paths: readonly string[]): void {
  const absolute = paths.map(requireAbsolute);
  release(absolute);
  for (const path of absolute) overlay.delete(path);
}

/**
 * One syntax node, printed the way the compiler writes it into a file. Printing is a server
 * operation, so it needs a project; a caller that has one prints through it, and everything else
 * prints through this one, which holds no files.
 */
export function printNode(node: Node): string {
  printing ??= openProject({ files: [], settings: { noLib: true } });
  return printing.print(node);
}

/**
 * A `tsconfig.json` on disk, as the compiler reads it.
 *
 * The options and file names come from `parseConfigFile`, which answers with what it resolved and
 * nothing about what went wrong: a truncated configuration, an unknown option and an unparsable
 * option value all come back as a success carrying defaults. The compiler does report all three,
 * but only through a project opened over the configuration itself, so that is where the
 * diagnostics are read from, and a caller that refuses a broken configuration has something to
 * refuse it with.
 */
export function configuration(path: string): ParsedConfiguration {
  const absolute = requireAbsolute(path);
  const parsed = server().parseConfigFile(absolute);
  const loaded = update({
    openProjects: [absolute],
    changed: seen.has(absolute) ? [absolute] : [],
  }).getProject(absolute);
  seen.add(absolute);
  if (loaded === undefined) {
    throw new TypeError(`the compiler session could not open the configuration at ${path}`);
  }
  const diagnostics = [...loaded.program.getConfigFileParsingDiagnostics()];
  update({ closeProjects: [absolute] });
  return { options: parsed.options, fileNames: parsed.fileNames, diagnostics };
}

/**
 * One diagnostic as a single message. A diagnostic carries its own text and, when the compiler
 * explained itself in steps, a chain of further diagnostics; each step is indented under the one
 * it explains, which is how the compiler's own renderer reads them.
 */
export function renderDiagnostic(diagnostic: Diagnostic, separator = '\n'): string {
  const render = (entry: Diagnostic, depth: number): readonly string[] => [
    `${'  '.repeat(depth)}${entry.text}`,
    ...(entry.messageChain ?? []).flatMap((next) => render(next, depth + 1)),
  ];
  return render(diagnostic, 0).join(separator);
}

/** Every diagnostic as one message, with the file each one belongs to when it names a file. */
export function renderDiagnostics(diagnostics: readonly Diagnostic[], separator = '\n'): string {
  return diagnostics
    .map((diagnostic) =>
      diagnostic.fileName === undefined
        ? renderDiagnostic(diagnostic, separator)
        : `${diagnostic.fileName}: ${renderDiagnostic(diagnostic, separator)}`,
    )
    .join(separator);
}
