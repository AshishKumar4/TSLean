import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';

export interface LeanLibraryFixture {
  readonly projectRoot: string;
  readonly sourceRoot: string;
  /** Each module's source path, keyed by Lean module name. */
  readonly sources: ReadonlyMap<string, string>;
  dispose(): void;
}

/**
 * A throwaway Lake project holding several Lean modules under one library root, so a compilation
 * can be checked against a module graph rather than a single file. The first module's first
 * component names the library, which is what Lake needs to resolve every module in the closure.
 */
export function createLeanLibraryFixture(modules: Readonly<Record<string, string>>): LeanLibraryFixture {
  const names = Object.keys(modules);
  const [first] = names;
  if (first === undefined) throw new TypeError('a Lean library fixture needs at least one module');
  const root = first.split('.')[0];
  if (root === undefined) throw new TypeError('a Lean module name has no first component');
  for (const name of names) {
    if (name.split('.')[0] !== root) {
      throw new TypeError(`module ${name} is outside the library root ${root}`);
    }
  }
  const projectRoot = mkdtempSync(join(tmpdir(), 'tslean-lean-library-'));
  const sourceRoot = join(projectRoot, 'sources');
  mkdirSync(sourceRoot);
  writeFileSync(join(projectRoot, 'lean-toolchain'), 'leanprover/lean4:v4.33.1\n');
  writeFileSync(join(projectRoot, 'lake-manifest.json'), '{"version":"1.1.0","name":"fixture","packages":[]}\n');
  writeFileSync(
    join(projectRoot, 'lakefile.toml'),
    [
      'name = "lean_to_typescript_library_fixture"',
      'version = "0.1.0"',
      '',
      '[[lean_lib]]',
      `name = "${root}"`,
      'srcDir = "sources"',
      `roots = ["${root}"]`,
      '',
    ].join('\n'),
  );
  const sources = new Map<string, string>();
  for (const [name, contents] of Object.entries(modules)) {
    const sourcePath = join(sourceRoot, `${name.split('.').join('/')}.lean`);
    mkdirSync(dirname(sourcePath), { recursive: true });
    writeFileSync(sourcePath, contents);
    sources.set(name, sourcePath);
  }
  return {
    projectRoot,
    sourceRoot,
    sources,
    dispose: () => rmSync(projectRoot, { force: true, recursive: true }),
  };
}
