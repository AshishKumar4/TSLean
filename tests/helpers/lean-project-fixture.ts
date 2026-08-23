import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';

export interface LeanProjectFixture {
  readonly projectRoot: string;
  readonly sourceRoot: string;
  readonly sourcePath: string;
  dispose(): void;
}

export function createLeanProjectFixture(source: string, moduleName = 'Fixture'): LeanProjectFixture {
  const projectRoot = mkdtempSync(join(tmpdir(), 'tslean-lean-project-'));
  const sourceRoot = join(projectRoot, 'sources');
  mkdirSync(sourceRoot);
  writeFileSync(join(projectRoot, 'lean-toolchain'), 'leanprover/lean4:v4.33.1\n');
  writeFileSync(join(projectRoot, 'lake-manifest.json'), '{"version":"1.1.0","name":"fixture","packages":[]}\n');
  writeFileSync(
    join(projectRoot, 'lakefile.toml'),
    [
      'name = "lean_to_typescript_fixture"',
      'version = "0.1.0"',
      '',
      '[[lean_lib]]',
      `name = "${moduleName.split('.')[0]}"`,
      'srcDir = "sources"',
      `roots = ["${moduleName}"]`,
      '',
    ].join('\n'),
  );
  const sourcePath = join(sourceRoot, `${moduleName.split('.').join('/')}.lean`);
  mkdirSync(dirname(sourcePath), { recursive: true });
  writeFileSync(sourcePath, source);
  return {
    projectRoot,
    sourceRoot,
    sourcePath,
    dispose: () => rmSync(projectRoot, { force: true, recursive: true }),
  };
}
