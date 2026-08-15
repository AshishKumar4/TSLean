import { execFileSync, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import {
  chmodSync,
  existsSync,
  linkSync,
  lstatSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, join, resolve } from 'node:path';
import { describe, expect, test } from 'vitest';
import { createLeanProjectFixture } from './helpers/lean-project-fixture.js';

const repositoryRoot = resolve(import.meta.dirname, '..');
const PACKED_COMPILER_TIMEOUT_MS = 60_000;

describe('published Lean to TypeScript API', () => {
  test('rejects aliased artifact destinations before compilation without modifying existing bytes', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-destinations-'));
    const destinationPath = join(temporaryRoot, 'artifact.ts');
    const original = Buffer.from('preserve this artifact\n');
    writeFileSync(destinationPath, original);
    try {
      const result = spawnSync(
        'bun',
        [
          join(repositoryRoot, 'src', 'lean-to-typescript', 'cli.ts'),
          '--project-root',
          join(temporaryRoot, 'missing-project'),
          '--module',
          'Missing',
          '--source',
          join(temporaryRoot, 'missing-project', 'Missing.lean'),
          '--declaration',
          'Missing.decide',
          '--output',
          './unused/../artifact.ts',
          '--manifest',
          destinationPath,
        ],
        { cwd: temporaryRoot, encoding: 'utf8' },
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr).toContain('--output and --manifest must identify distinct filesystem paths');
      expect(readFileSync(destinationPath)).toEqual(original);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test.each(['symlink-parent', 'hardlink', 'dangling-symlink'] as const)(
    'rejects %s aliases between artifact destinations before compilation',
    (aliasKind) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-destination-alias-'));
      const canonicalDirectory = join(temporaryRoot, 'canonical');
      mkdirSync(canonicalDirectory);
      const outputPath = join(canonicalDirectory, 'artifact.ts');
      let manifestPath: string;
      if (aliasKind === 'symlink-parent') {
        const aliasDirectory = join(temporaryRoot, 'alias');
        symlinkSync(canonicalDirectory, aliasDirectory, 'dir');
        manifestPath = join(aliasDirectory, 'artifact.ts');
      } else if (aliasKind === 'hardlink') {
        writeFileSync(outputPath, 'preserve hard-linked artifact\n');
        manifestPath = join(temporaryRoot, 'artifact.manifest.json');
        linkSync(outputPath, manifestPath);
      } else {
        manifestPath = join(temporaryRoot, 'artifact.manifest.json');
        symlinkSync(outputPath, manifestPath, 'file');
      }
      const original = existsSync(outputPath) ? readFileSync(outputPath) : undefined;
      try {
        const result = runSourceCompiler(
          temporaryRoot,
          join(temporaryRoot, 'missing-project'),
          join(temporaryRoot, 'missing-project', 'Missing.lean'),
          outputPath,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain('--output and --manifest must identify distinct filesystem paths');
        expect(existsSync(outputPath)).toBe(original !== undefined);
        if (original !== undefined) {
          expect(readFileSync(outputPath)).toEqual(original);
          expect(readFileSync(manifestPath)).toEqual(original);
        } else if (aliasKind === 'dangling-symlink') {
          expect(lstatSync(manifestPath).isSymbolicLink()).toBe(true);
        }
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test.each([
    ['--output', 'artifact', join('artifact', 'generated.manifest.json')],
    ['--manifest', join('artifact', 'generated.ts'), 'artifact'],
  ] as const)(
    'rejects a nonexisting %s destination that would contain the other artifact before compilation',
    (ancestor, outputRelativePath, manifestRelativePath) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-destination-containment-'));
      const preservedPath = join(temporaryRoot, 'preserved.txt');
      const original = Buffer.from('preserve unrelated bytes\n');
      writeFileSync(preservedPath, original);
      const outputPath = join(temporaryRoot, outputRelativePath);
      const manifestPath = join(temporaryRoot, manifestRelativePath);
      try {
        const result = runSourceCompiler(
          temporaryRoot,
          join(temporaryRoot, 'missing-project'),
          join(temporaryRoot, 'missing-project', 'Fixture.lean'),
          outputPath,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(`${ancestor} must not contain the other artifact destination`);
        expect(existsSync(outputPath)).toBe(false);
        expect(existsSync(manifestPath)).toBe(false);
        expect(readFileSync(preservedPath)).toEqual(original);
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test.each(['--output', '--manifest'] as const)(
    'rejects an existing directory as %s before compilation without modifying the companion artifact',
    (destination) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-directory-destination-'));
      const directoryPath = join(temporaryRoot, 'existing-directory');
      const preservedInDirectoryPath = join(directoryPath, 'preserved.txt');
      const companionPath = join(temporaryRoot, 'companion-artifact');
      const directoryOriginal = Buffer.from('preserve directory contents\n');
      const companionOriginal = Buffer.from('preserve companion artifact\n');
      mkdirSync(directoryPath);
      writeFileSync(preservedInDirectoryPath, directoryOriginal);
      writeFileSync(companionPath, companionOriginal);
      const outputPath = destination === '--output' ? directoryPath : companionPath;
      const manifestPath = destination === '--manifest' ? directoryPath : companionPath;
      try {
        const result = runSourceCompiler(
          temporaryRoot,
          join(temporaryRoot, 'missing-project'),
          join(temporaryRoot, 'missing-project', 'Fixture.lean'),
          outputPath,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(`${destination} must not identify an existing directory`);
        expect(readFileSync(preservedInDirectoryPath)).toEqual(directoryOriginal);
        expect(readFileSync(companionPath)).toEqual(companionOriginal);
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test.each(['--output', '--manifest'] as const)(
    'rejects %s beneath an existing non-directory before compilation',
    (destination) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-nondirectory-ancestor-'));
      const ancestorPath = join(temporaryRoot, 'existing-file');
      const companionPath = join(temporaryRoot, 'companion-artifact');
      const ancestorOriginal = Buffer.from('preserve ancestor bytes\n');
      const companionOriginal = Buffer.from('preserve companion artifact\n');
      writeFileSync(ancestorPath, ancestorOriginal);
      writeFileSync(companionPath, companionOriginal);
      const descendantPath = join(ancestorPath, 'generated-artifact');
      const outputPath = destination === '--output' ? descendantPath : companionPath;
      const manifestPath = destination === '--manifest' ? descendantPath : companionPath;
      try {
        const result = runSourceCompiler(
          temporaryRoot,
          join(temporaryRoot, 'missing-project'),
          join(temporaryRoot, 'missing-project', 'Fixture.lean'),
          outputPath,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(`${destination} has an existing non-directory ancestor`);
        expect(readFileSync(ancestorPath)).toEqual(ancestorOriginal);
        expect(readFileSync(companionPath)).toEqual(companionOriginal);
        expect(existsSync(descendantPath)).toBe(false);
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test.each([
    ['symlink-parent', '--output'],
    ['symlink-parent', '--manifest'],
    ['hardlink', '--output'],
    ['hardlink', '--manifest'],
  ] as const)('rejects a %s %s alias of the explicit Lean source before compilation', (aliasKind, destination) => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-source-alias-'));
    const projectRoot = join(temporaryRoot, 'project');
    mkdirSync(projectRoot);
    const sourcePath = join(projectRoot, 'Fixture.lean');
    const original = Buffer.from('def preserved : Bool := true\n');
    writeFileSync(sourcePath, original);
    let aliasedPath: string;
    if (aliasKind === 'symlink-parent') {
      const aliasRoot = join(temporaryRoot, 'alias-project');
      symlinkSync(projectRoot, aliasRoot, 'dir');
      aliasedPath = join(aliasRoot, 'Fixture.lean');
    } else {
      aliasedPath = join(temporaryRoot, 'source-alias');
      linkSync(sourcePath, aliasedPath);
    }
    const companionPath = join(temporaryRoot, 'companion-artifact');
    const companionOriginal = Buffer.from('preserve companion artifact\n');
    writeFileSync(companionPath, companionOriginal);
    const outputPath = destination === '--output' ? aliasedPath : companionPath;
    const manifestPath = destination === '--manifest' ? aliasedPath : companionPath;
    try {
      const result = runSourceCompiler(temporaryRoot, projectRoot, sourcePath, outputPath, manifestPath);

      expect(result.status).not.toBe(0);
      expect(result.stderr).toContain(`${destination} must not identify compiler input --source`);
      expect(readFileSync(sourcePath)).toEqual(original);
      expect(readFileSync(aliasedPath)).toEqual(original);
      expect(readFileSync(companionPath)).toEqual(companionOriginal);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test.each([
    ['direct', '--output'],
    ['direct', '--manifest'],
    ['hardlink', '--output'],
    ['hardlink', '--manifest'],
  ] as const)(
    'rejects a %s-path %s descendant of the explicit Lean source before compilation',
    (sourcePathKind, destination) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-source-descendant-'));
      const projectRoot = join(temporaryRoot, 'project');
      mkdirSync(projectRoot);
      const sourcePath = join(projectRoot, 'Fixture.lean');
      const sourceOriginal = Buffer.from('def preserved : Bool := true\n');
      writeFileSync(sourcePath, sourceOriginal);
      const destinationAncestor = sourcePathKind === 'direct' ? sourcePath : join(temporaryRoot, 'hard-linked-source');
      if (sourcePathKind === 'hardlink') linkSync(sourcePath, destinationAncestor);
      const descendantPath = join(destinationAncestor, 'generated-artifact');
      const companionPath = join(temporaryRoot, 'companion-artifact');
      const companionOriginal = Buffer.from('preserve companion artifact\n');
      writeFileSync(companionPath, companionOriginal);
      const outputPath = destination === '--output' ? descendantPath : companionPath;
      const manifestPath = destination === '--manifest' ? descendantPath : companionPath;
      try {
        const result = runSourceCompiler(temporaryRoot, projectRoot, sourcePath, outputPath, manifestPath);

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(
          `${destination} must not identify compiler input --source or an ancestor/descendant path`,
        );
        expect(readFileSync(sourcePath)).toEqual(sourceOriginal);
        expect(readFileSync(destinationAncestor)).toEqual(sourceOriginal);
        expect(readFileSync(companionPath)).toEqual(companionOriginal);
        expect(existsSync(descendantPath)).toBe(false);
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test.each(['--output', '--manifest'] as const)(
    'rejects %s when it aliases a captured compiler input without modifying either artifact',
    (destination) => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const toolchainPath = join(fixture.projectRoot, 'lean-toolchain');
      const original = readFileSync(toolchainPath);
      const companionPath = join(fixture.projectRoot, 'companion-artifact');
      const companionOriginal = Buffer.from('preserve companion artifact\n');
      writeFileSync(companionPath, companionOriginal);
      const outputPath = destination === '--output' ? toolchainPath : companionPath;
      const manifestPath = destination === '--manifest' ? toolchainPath : companionPath;
      try {
        const result = runSourceCompiler(
          fixture.projectRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputPath,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(
          `${destination} must not identify compiler input target-project:lean-toolchain`,
        );
        expect(readFileSync(toolchainPath)).toEqual(original);
        expect(readFileSync(companionPath)).toEqual(companionOriginal);
      } finally {
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test(
    'compiles a separate Lean package through the packed subpath export',
    () => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-packed-consumer-'));
      let installedPackageRoot = '';
      try {
        execFileSync('bun', ['run', 'build'], { cwd: repositoryRoot, stdio: 'pipe' });
        const packedPath = execFileSync(
          'bun',
          ['pm', 'pack', '--destination', temporaryRoot, '--ignore-scripts', '--quiet'],
          {
            cwd: repositoryRoot,
            encoding: 'utf8',
          },
        ).trim();
        const tarballName = basename(packedPath);
        if (!existsSync(join(temporaryRoot, tarballName))) {
          throw new TypeError('bun did not produce the package tarball');
        }
        const consumerRoot = join(temporaryRoot, 'consumer');
        const leanRoot = join(consumerRoot, 'lean-project');
        const sourceRoot = join(leanRoot, 'source');
        mkdirSync(sourceRoot, { recursive: true });
        writeFileSync(
          join(consumerRoot, 'package.json'),
          `${JSON.stringify({ type: 'module', dependencies: { tslean: `file:../${tarballName}` } }, null, 2)}\n`,
        );
        execFileSync('bun', ['install', '--offline', '--ignore-scripts'], { cwd: consumerRoot, stdio: 'pipe' });
        installedPackageRoot = join(consumerRoot, 'node_modules', 'tslean');
        const compilerExecutable = join(consumerRoot, 'node_modules', '.bin', 'lean-to-typescript');
        expect(
          execFileSync(compilerExecutable, ['--help'], {
            cwd: consumerRoot,
            encoding: 'utf8',
          }),
        ).toContain('Usage: lean-to-typescript');
        writeFileSync(join(leanRoot, 'lean-toolchain'), 'leanprover/lean4:v4.29.0\n');
        writeFileSync(join(leanRoot, 'lake-manifest.json'), '{"version":"1.1.0","name":"consumer","packages":[]}\n');
        writeFileSync(
          join(leanRoot, 'lakefile.toml'),
          [
            'name = "consumer"',
            'version = "0.1.0"',
            '',
            '[[lean_lib]]',
            'name = "Consumer"',
            'srcDir = "source"',
            'roots = ["Consumer"]',
            '',
          ].join('\n'),
        );
        const sourcePath = join(sourceRoot, 'Consumer.lean');
        writeFileSync(
          sourcePath,
          ['namespace Consumer', 'def decide (value : Bool) : Bool := !value', 'end Consumer', ''].join('\n'),
        );
        makeTreeReadOnly(installedPackageRoot);
        const generatedPath = join(consumerRoot, 'generated.ts');
        const manifestPath = join(consumerRoot, 'generated.manifest.json');
        const compilerArguments = [
          '--project-root',
          leanRoot,
          '--module',
          'Consumer',
          '--source',
          sourcePath,
          '--declaration',
          'Consumer.decide',
          '--output',
          generatedPath,
          '--manifest',
          manifestPath,
        ];
        execFileSync(compilerExecutable, compilerArguments, { cwd: consumerRoot, stdio: 'pipe' });
        const installedCode = readFileSync(generatedPath, 'utf8');
        const installedManifest: unknown = JSON.parse(readFileSync(manifestPath, 'utf8'));
        if (!isRecord(installedManifest) || !Array.isArray(installedManifest['inputs'])) {
          throw new TypeError('packed generator emitted a malformed manifest');
        }
        expect(installedCode).toContain('export function decide(value: boolean): boolean');
        expect(installedManifest['inputClosureSha256']).toBe(sha256(JSON.stringify(installedManifest['inputs'])));
        expect(installedCode).toContain(` * Manifest: ${sha256(JSON.stringify(installedManifest))}`);
        expect(spawnSync(compilerExecutable, [...compilerArguments, '--check']).status).toBe(0);
        writeFileSync(generatedPath, `${installedCode}\n`);
        const stale = spawnSync(compilerExecutable, [...compilerArguments, '--check'], { encoding: 'utf8' });
        expect(stale.status).not.toBe(0);
        expect(stale.stderr).toContain('generated artifact is stale');
        writeFileSync(
          join(consumerRoot, 'compile.mjs'),
          [
            "import { compileLeanToTypeScript, verifyLeanToTypeScriptArtifact } from 'tslean/lean-to-typescript';",
            "import { resolve } from 'node:path';",
            "const root = resolve('lean-project');",
            'const artifact = compileLeanToTypeScript({',
            '  projectRoot: root,',
            "  moduleName: 'Consumer',",
            "  sourcePath: resolve(root, 'source/Consumer.lean'),",
            "  declarations: ['Consumer.decide'],",
            '});',
            'verifyLeanToTypeScriptArtifact(artifact);',
            'process.stdout.write(JSON.stringify(artifact));',
            '',
          ].join('\n'),
        );
        const output = execFileSync(process.execPath, ['compile.mjs'], {
          cwd: consumerRoot,
          encoding: 'utf8',
          maxBuffer: 64 * 1024 * 1024,
        });
        const parsed: unknown = JSON.parse(output);
        if (!isRecord(parsed) || typeof parsed['code'] !== 'string' || !isRecord(parsed['manifest'])) {
          throw new TypeError('packed compiler emitted a malformed artifact');
        }
        expect(parsed['code']).toContain('export function decide(value: boolean): boolean');
        expect(parsed['manifest']['sourceModule']).toBe('Consumer');
        expect(
          readFileSync(
            join(consumerRoot, 'node_modules', 'tslean', 'lean', 'TSLean', 'LeanToTypeScript', 'Export.lean'),
          ),
        ).not.toHaveLength(0);
        expect(existsSync(join(sourceRoot, 'TSLean', 'LeanToTypeScript', 'Export.lean'))).toBe(false);
      } finally {
        if (installedPackageRoot && existsSync(installedPackageRoot)) makeTreeWritable(installedPackageRoot);
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );
});

function runSourceCompiler(
  cwd: string,
  projectRoot: string,
  sourcePath: string,
  outputPath: string,
  manifestPath: string,
): ReturnType<typeof spawnSync> {
  return spawnSync(
    'bun',
    [
      join(repositoryRoot, 'src', 'lean-to-typescript', 'cli.ts'),
      '--project-root',
      projectRoot,
      '--module',
      'Fixture',
      '--source',
      sourcePath,
      '--declaration',
      'Fixture.decide',
      '--output',
      outputPath,
      '--manifest',
      manifestPath,
    ],
    { cwd, encoding: 'utf8' },
  );
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function sha256(value: string): string {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}

function makeTreeReadOnly(path: string): void {
  const stats = lstatSync(path);
  if (stats.isSymbolicLink()) return;
  if (stats.isDirectory()) {
    for (const child of readdirSync(path)) makeTreeReadOnly(join(path, child));
  }
  chmodSync(path, stats.mode & ~0o222);
}

function makeTreeWritable(path: string): void {
  const stats = lstatSync(path);
  if (stats.isSymbolicLink()) return;
  chmodSync(path, stats.mode | 0o200);
  if (stats.isDirectory()) {
    for (const child of readdirSync(path)) makeTreeWritable(join(path, child));
  }
}
