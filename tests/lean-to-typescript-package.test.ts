import { execFileSync, spawn, spawnSync } from 'node:child_process';
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
  renameSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { describe, expect, test } from 'vitest';
import { choosePlacementFromUnknown } from '../examples/lean-to-typescript/placement.adapter.js';
import {
  nodeArtifactFileSystem,
  publishArtifactPairWithFileSystem,
  recoverArtifactPairWithFileSystem,
  type ArtifactDestination,
  type ArtifactFileSystem,
} from '../src/lean-to-typescript/artifact-transaction.js';
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

  test(
    'preserves both preexisting artifacts when the second destination cannot be staged',
    () => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const outputPath = join(fixture.projectRoot, 'generated.ts');
      const original = Buffer.from('preserve generated output\n');
      writeFileSync(outputPath, original);
      const manifestPath = `/sys/tslean-${process.pid}-manifest.json`;
      try {
        const result = runSourceCompiler(
          fixture.projectRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputPath,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(readFileSync(outputPath)).toEqual(original);
        expect(existsSync(manifestPath)).toBe(false);
      } finally {
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test(
    'rejects a destination-parent swap during compilation without publishing through the replacement path',
    async () => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const publicationRoot = join(fixture.projectRoot, 'publication');
      const movedRoot = join(fixture.projectRoot, 'publication-original');
      const wrapperRoot = join(fixture.projectRoot, 'wrapper');
      const markerPath = join(fixture.projectRoot, 'launcher-observed');
      mkdirSync(publicationRoot);
      mkdirSync(wrapperRoot);
      const outputPath = join(publicationRoot, 'generated.ts');
      const manifestPath = join(publicationRoot, 'generated.manifest.json');
      const outputOriginal = Buffer.from('preserve output\n');
      const manifestOriginal = Buffer.from('preserve manifest\n');
      writeFileSync(outputPath, outputOriginal);
      writeFileSync(manifestPath, manifestOriginal);
      const launcherPath = execFileSync('sh', ['-c', 'command -v lake'], { encoding: 'utf8' }).trim();
      const wrapperPath = join(wrapperRoot, 'lake');
      writeFileSync(
        wrapperPath,
        ['#!/bin/sh', `: > ${shellQuote(markerPath)}`, `exec ${shellQuote(launcherPath)} "$@"`, ''].join('\n'),
      );
      chmodSync(wrapperPath, 0o755);
      try {
        const child = spawn(
          'bun',
          compilerArguments(fixture.projectRoot, fixture.sourcePath, outputPath, manifestPath),
          {
            cwd: fixture.projectRoot,
            env: { ...process.env, PATH: `${wrapperRoot}:${process.env['PATH'] ?? ''}` },
            stdio: ['ignore', 'pipe', 'pipe'],
          },
        );
        await waitForPath(markerPath, child);
        renameSync(publicationRoot, movedRoot);
        mkdirSync(publicationRoot);
        const result = await collectChild(child);

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain('artifact destination changed during compilation');
        expect(readFileSync(join(movedRoot, 'generated.ts'))).toEqual(outputOriginal);
        expect(readFileSync(join(movedRoot, 'generated.manifest.json'))).toEqual(manifestOriginal);
        expect(existsSync(outputPath)).toBe(false);
        expect(existsSync(manifestPath)).toBe(false);
      } finally {
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test.each([
    ['write', 1, 'old'],
    ['write', 2, 'old'],
    ['write', 3, 'old'],
    ['write', 4, 'old'],
    ['rename', 1, 'old'],
    ['rename', 2, 'old'],
    ['rename', 3, 'old'],
    ['rename', 4, 'old'],
    ['fsync', 1, 'old'],
    ['fsync', 2, 'old'],
    ['fsync', 3, 'old'],
    ['fsync', 4, 'old'],
    ['fsync', 5, 'old'],
    ['fsync', 6, 'old'],
    ['fsync', 7, 'old'],
    ['fsync', 8, 'new'],
    ['fsync', 9, 'new'],
  ] as const)(
    'keeps a complete recoverable pair when %s operation %i fails',
    (operation, occurrence, expectedVersion) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-fault-'));
      const destinations = transactionDestinations(temporaryRoot);
      const oldContents = ['old output\n', 'old manifest\n'] as const;
      const newContents = ['new output\n', 'new manifest\n'] as const;
      writeFileSync(destinations[0].path, oldContents[0]);
      writeFileSync(destinations[1].path, oldContents[1]);
      try {
        let threw = false;
        try {
          publishArtifactPairWithFileSystem(
            destinations,
            newContents,
            faultingArtifactFileSystem(operation, occurrence),
          );
        } catch {
          threw = true;
        }

        expect(threw).toBe(expectedVersion === 'old');
        const expected = expectedVersion === 'old' ? oldContents : newContents;
        expect(readFileSync(destinations[0].path, 'utf8')).toBe(expected[0]);
        expect(readFileSync(destinations[1].path, 'utf8')).toBe(expected[1]);
        expect(transactionFiles(temporaryRoot)).toEqual([]);
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test.each([
    ['rename', 1, 'old'],
    ['rename', 2, 'old'],
    ['rename', 3, 'old'],
    ['rename', 4, 'old'],
    ['fsync', 3, 'old'],
    ['fsync', 4, 'old'],
    ['fsync', 5, 'old'],
    ['fsync', 6, 'new'],
    ['fsync', 7, 'new'],
    ['fsync', 8, 'new'],
    ['fsync', 9, 'new'],
  ] as const)(
    'recovers a complete pair after a process crash immediately after %s operation %i',
    (operation, occurrence, expectedVersion) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-crash-'));
      const destinations = transactionDestinations(temporaryRoot);
      const oldContents = ['old output\n', 'old manifest\n'] as const;
      const newContents = ['new output\n', 'new manifest\n'] as const;
      writeFileSync(destinations[0].path, oldContents[0]);
      writeFileSync(destinations[1].path, oldContents[1]);
      try {
        const crashed = crashArtifactTransaction(temporaryRoot, destinations, newContents, operation, occurrence);
        expect(crashed.signal).toBe('SIGKILL');

        recoverArtifactPairWithFileSystem(destinations, nodeArtifactFileSystem);

        const expected = expectedVersion === 'old' ? oldContents : newContents;
        expect(readFileSync(destinations[0].path, 'utf8')).toBe(expected[0]);
        expect(readFileSync(destinations[1].path, 'utf8')).toBe(expected[1]);
        expect(transactionFiles(temporaryRoot)).toEqual([]);
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test('fails closed on a corrupt recovery journal without touching either artifact', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-corrupt-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    const journalPath = join(temporaryRoot, transactionJournalFilename(destinations));
    writeFileSync(journalPath, '{not-json\n');
    try {
      expect(() => recoverArtifactPairWithFileSystem(destinations, nodeArtifactFileSystem)).toThrowError(
        /journal is corrupt/u,
      );
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
      expect(readFileSync(journalPath, 'utf8')).toBe('{not-json\n');
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('fails closed on a stale recovery journal before applying any recovery step', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-stale-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const newContents = ['new output\n', 'new manifest\n'] as const;
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    try {
      const crashed = crashArtifactTransaction(temporaryRoot, destinations, newContents, 'rename', 3);
      expect(crashed.signal).toBe('SIGKILL');
      const journalPath = join(temporaryRoot, transactionJournalFilename(destinations));
      const journal: unknown = JSON.parse(readFileSync(journalPath, 'utf8'));
      if (!isRecord(journal) || !Array.isArray(journal['artifacts']) || !isRecord(journal['artifacts'][1])) {
        throw new TypeError('crash probe did not produce the expected journal');
      }
      journal['artifacts'][1]['canonicalPath'] = join(temporaryRoot, 'stale.manifest.json');
      writeFileSync(journalPath, `${JSON.stringify(journal)}\n`);
      const beforeOutput = readFileSync(destinations[0].path);
      const beforeManifestExists = existsSync(destinations[1].path);
      const beforeManifest = beforeManifestExists ? readFileSync(destinations[1].path) : undefined;

      expect(() => recoverArtifactPairWithFileSystem(destinations, nodeArtifactFileSystem)).toThrowError(
        /names different destinations/u,
      );
      expect(readFileSync(destinations[0].path)).toEqual(beforeOutput);
      expect(existsSync(destinations[1].path)).toBe(beforeManifestExists);
      if (beforeManifest !== undefined) expect(readFileSync(destinations[1].path)).toEqual(beforeManifest);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test.each([
    ['write', 4, 'old'],
    ['fsync', 6, 'old'],
    ['rename', 4, 'old'],
    ['write', 6, 'new'],
    ['fsync', 11, 'new'],
    ['fsync', 12, 'new'],
  ] as const)(
    'keeps cross-directory publication recoverable when %s operation %i fails',
    (operation, occurrence, expectedVersion) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-cross-directory-'));
      const outputRoot = join(temporaryRoot, 'output');
      const manifestRoot = join(temporaryRoot, 'manifest');
      mkdirSync(outputRoot);
      mkdirSync(manifestRoot);
      const destinations = transactionDestinations(outputRoot, manifestRoot);
      const oldContents = ['old output\n', 'old manifest\n'] as const;
      const newContents = ['new output\n', 'new manifest\n'] as const;
      writeFileSync(destinations[0].path, oldContents[0]);
      writeFileSync(destinations[1].path, oldContents[1]);
      try {
        let threw = false;
        try {
          publishArtifactPairWithFileSystem(
            destinations,
            newContents,
            faultingArtifactFileSystem(operation, occurrence),
          );
        } catch {
          threw = true;
        }

        expect(threw).toBe(expectedVersion === 'old');
        const expected = expectedVersion === 'old' ? oldContents : newContents;
        expect(readFileSync(destinations[0].path, 'utf8')).toBe(expected[0]);
        expect(readFileSync(destinations[1].path, 'utf8')).toBe(expected[1]);
        expect([...transactionFiles(outputRoot), ...transactionFiles(manifestRoot)]).toEqual([]);
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test('rolls back through bound directory handles when the named publication directory is swapped', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-directory-swap-'));
    const publicationRoot = join(temporaryRoot, 'publication');
    const movedRoot = join(temporaryRoot, 'publication-original');
    mkdirSync(publicationRoot);
    const destinations = transactionDestinations(publicationRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const newContents = ['new output\n', 'new manifest\n'] as const;
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    let swapped = false;
    const swappingFileSystem: ArtifactFileSystem = {
      ...nodeArtifactFileSystem,
      rename: (from, to) => {
        if (!swapped) {
          swapped = true;
          renameSync(publicationRoot, movedRoot);
          mkdirSync(publicationRoot);
        }
        nodeArtifactFileSystem.rename(from, to);
      },
    };
    try {
      expect(() => publishArtifactPairWithFileSystem(destinations, newContents, swappingFileSystem)).toThrowError(
        /artifact destination changed during compilation/u,
      );
      expect(readFileSync(join(movedRoot, 'generated.ts'), 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(join(movedRoot, 'generated.manifest.json'), 'utf8')).toBe(oldContents[1]);
      expect(existsSync(destinations[0].path)).toBe(false);
      expect(existsSync(destinations[1].path)).toBe(false);
      expect(transactionFiles(movedRoot)).toEqual([]);
      expect(transactionFiles(publicationRoot)).toEqual([]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

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
        const installedEmitterPath = join(installedPackageRoot, 'dist', 'lean-to-typescript', 'emitter.js');
        writeFileSync(
          join(consumerRoot, 'mutate-after-import.mjs'),
          [
            "import { compileLeanToTypeScript } from 'tslean/lean-to-typescript';",
            "import { readFileSync, writeFileSync } from 'node:fs';",
            "import { resolve } from 'node:path';",
            `const emitterPath = ${JSON.stringify(installedEmitterPath)};`,
            "const original = readFileSync(emitterPath, 'utf8');",
            'writeFileSync(emitterPath, `${original}\\n// mutation after import\\n`);',
            'try {',
            "  const root = resolve('lean-project');",
            '  compileLeanToTypeScript({',
            '    projectRoot: root,',
            "    moduleName: 'Consumer',",
            "    sourcePath: resolve(root, 'source/Consumer.lean'),",
            "    declarations: ['Consumer.decide'],",
            '  });',
            '} finally {',
            '  writeFileSync(emitterPath, original);',
            '}',
            '',
          ].join('\n'),
        );
        const mutatedCompiler = spawnSync(process.execPath, ['mutate-after-import.mjs'], {
          cwd: consumerRoot,
          encoding: 'utf8',
        });
        expect(mutatedCompiler.status).not.toBe(0);
        expect(mutatedCompiler.stderr).toContain(
          'compiler runtime input changed after it was loaded: compiler:emitter',
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

  test('binds the executable model to one complete deterministic W-3 registry entry', () => {
    const registryPath = join(repositoryRoot, 'spec', 'lean-to-typescript', 'compiler-registry.json');
    const source = readFileSync(registryPath, 'utf8');
    const registry: unknown = JSON.parse(source);
    if (!isRecord(registry) || registry['schemaVersion'] !== 1 || !Array.isArray(registry['models'])) {
      throw new TypeError('compiler registry has an invalid root');
    }
    expect(source.endsWith('\n')).toBe(true);
    expect(source).not.toContain('\r');
    expect(registry['models']).toHaveLength(1);
    const model = registry['models'][0];
    if (!isRecord(model)) throw new TypeError('compiler registry model must be an object');
    expect(Object.keys(model).sort()).toEqual([
      'boundsArtifact',
      'entrypoint',
      'fragmentClosure',
      'generatedTarget',
      'id',
      'oracleOperation',
      'runtimeAdapter',
    ]);
    expect(model['id']).toBe('placement-v1');
    expect(model['entrypoint']).toEqual({
      projectRoot: 'lean',
      module: 'TSLean.Examples.Placement',
      source: 'lean/TSLean/Examples/Placement.lean',
      declarations: ['TSLean.Examples.Placement.choosePlacement'],
    });
    expect(model['fragmentClosure']).toEqual(['lean/TSLean/Examples/Placement.lean']);
    expect(model['generatedTarget']).toEqual({
      source: 'examples/lean-to-typescript/placement.generated.ts',
      manifest: 'examples/lean-to-typescript/placement.generated.manifest.json',
    });
    expect(model['runtimeAdapter']).toBe('examples/lean-to-typescript/placement.adapter.ts');
    expect(model['boundsArtifact']).toBe('spec/lean-to-typescript/placement.bounds.json');
    expect(model['oracleOperation']).toEqual({
      command: 'bunx vitest run tests/lean-to-typescript.test.ts',
      selector: 'generated decision agrees with Lean on the complete finite input domain',
      verdict: 'exactly-equal',
    });
    for (const path of registryPaths(model)) expect(statSync(join(repositoryRoot, path)).isFile()).toBe(true);

    const bounds: unknown = JSON.parse(readFileSync(join(repositoryRoot, String(model['boundsArtifact'])), 'utf8'));
    expect(bounds).toEqual({
      schemaVersion: 1,
      model: 'placement-v1',
      dimensions: [
        { name: 'manifest', cardinality: 8 },
        { name: 'policy', cardinality: 8 },
        { name: 'substrate', cardinality: 8 },
        { name: 'trust', cardinality: 8 },
      ],
      cases: 4096,
      coverage: 'exhaustive',
    });
    const dimensions = isRecord(bounds) && Array.isArray(bounds['dimensions']) ? bounds['dimensions'] : [];
    const cases = dimensions.reduce((product, dimension) => {
      if (!isRecord(dimension) || typeof dimension['cardinality'] !== 'number') {
        throw new TypeError('compiler bounds dimension is invalid');
      }
      return product * dimension['cardinality'];
    }, 1);
    expect(cases).toBe(isRecord(bounds) ? bounds['cases'] : undefined);
    expect(readFileSync(join(repositoryRoot, 'tests', 'lean-to-typescript.test.ts'), 'utf8')).toContain(
      String(isRecord(model['oracleOperation']) ? model['oracleOperation']['selector'] : ''),
    );
    expect(readFileSync(join(repositoryRoot, String(model['runtimeAdapter'])), 'utf8')).toContain(
      "from './placement.generated.js'",
    );
    const target = model['generatedTarget'];
    if (!isRecord(target)) throw new TypeError('compiler registry target is invalid');
    const manifest: unknown = JSON.parse(readFileSync(join(repositoryRoot, String(target['manifest'])), 'utf8'));
    if (!isRecord(manifest) || !Array.isArray(manifest['inputs'])) {
      throw new TypeError('registered generated manifest is invalid');
    }
    expect(manifest['sourceModule']).toBe('TSLean.Examples.Placement');
    expect(manifest['declarations']).toEqual(['TSLean.Examples.Placement.choosePlacement']);
    expect(
      manifest['inputs']
        .filter(isRecord)
        .map((input) => input['identity'])
        .filter((identity): identity is string => typeof identity === 'string'),
    ).toEqual(
      expect.arrayContaining(['compiler:bounds:placement-v1', 'compiler:registry', 'source:TSLean.Examples.Placement']),
    );
  });

  test('keeps the registered runtime adapter explicit and fail-closed', () => {
    const all = { bundled: true, dynamic: true, provider: true };
    const provider = { bundled: false, dynamic: false, provider: true };
    expect(choosePlacementFromUnknown(all, all, all, provider)).toBe('provider');
    expect(() => choosePlacementFromUnknown({ bundled: true }, all, all, all)).toThrowError(
      /manifest must be a plain PlacementSet/u,
    );
    expect(() => choosePlacementFromUnknown([], all, all, all)).toThrowError(/manifest must be a plain PlacementSet/u);
  });
});

function registryPaths(model: Record<string, unknown>): readonly string[] {
  const entrypoint = model['entrypoint'];
  const target = model['generatedTarget'];
  if (!isRecord(entrypoint) || !isRecord(target) || !Array.isArray(model['fragmentClosure'])) {
    throw new TypeError('compiler registry model paths are invalid');
  }
  return [
    String(entrypoint['source']),
    ...model['fragmentClosure'].map(String),
    String(target['source']),
    String(target['manifest']),
    String(model['runtimeAdapter']),
    String(model['boundsArtifact']),
  ];
}

type FaultOperation = 'fsync' | 'rename' | 'write';

function transactionDestinations(
  outputRoot: string,
  manifestRoot: string = outputRoot,
): readonly [ArtifactDestination, ArtifactDestination] {
  const outputPath = join(outputRoot, 'generated.ts');
  const manifestPath = join(manifestRoot, 'generated.manifest.json');
  return [
    { name: '--output', path: outputPath, canonicalPath: outputPath },
    { name: '--manifest', path: manifestPath, canonicalPath: manifestPath },
  ];
}

function faultingArtifactFileSystem(operation: FaultOperation, occurrence: number): ArtifactFileSystem {
  let writes = 0;
  let renames = 0;
  let synchronizations = 0;
  return {
    ...nodeArtifactFileSystem,
    write: (descriptor, contents) => {
      writes += 1;
      if (operation === 'write' && writes === occurrence) throw new TypeError('injected write failure');
      nodeArtifactFileSystem.write(descriptor, contents);
    },
    rename: (from, to) => {
      renames += 1;
      if (operation === 'rename' && renames === occurrence) throw new TypeError('injected rename failure');
      nodeArtifactFileSystem.rename(from, to);
    },
    fsync: (descriptor) => {
      synchronizations += 1;
      if (operation === 'fsync' && synchronizations === occurrence) throw new TypeError('injected fsync failure');
      nodeArtifactFileSystem.fsync(descriptor);
    },
  };
}

function crashArtifactTransaction(
  root: string,
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  contents: readonly [string, string],
  operation: FaultOperation,
  occurrence: number,
): ReturnType<typeof spawnSync> {
  const moduleUrl = pathToFileURL(join(repositoryRoot, 'src', 'lean-to-typescript', 'artifact-transaction.ts')).href;
  const scriptPath = join(root, 'crash-transaction.mjs');
  writeFileSync(
    scriptPath,
    [
      `import { nodeArtifactFileSystem, publishArtifactPairWithFileSystem } from ${JSON.stringify(moduleUrl)};`,
      `const destinations = ${JSON.stringify(destinations)};`,
      `const contents = ${JSON.stringify(contents)};`,
      `const operation = ${JSON.stringify(operation)};`,
      `const occurrence = ${occurrence};`,
      'let writes = 0;',
      'let renames = 0;',
      'let synchronizations = 0;',
      'const filesystem = {',
      '  ...nodeArtifactFileSystem,',
      '  write(descriptor, value) {',
      '    nodeArtifactFileSystem.write(descriptor, value);',
      "    if (operation === 'write' && ++writes === occurrence) process.kill(process.pid, 'SIGKILL');",
      '  },',
      '  rename(from, to) {',
      '    nodeArtifactFileSystem.rename(from, to);',
      "    if (operation === 'rename' && ++renames === occurrence) process.kill(process.pid, 'SIGKILL');",
      '  },',
      '  fsync(descriptor) {',
      '    nodeArtifactFileSystem.fsync(descriptor);',
      "    if (operation === 'fsync' && ++synchronizations === occurrence) process.kill(process.pid, 'SIGKILL');",
      '  },',
      '};',
      'publishArtifactPairWithFileSystem(destinations, contents, filesystem);',
      '',
    ].join('\n'),
  );
  return spawnSync('bun', [scriptPath], { cwd: root, encoding: 'utf8' });
}

function transactionJournalFilename(destinations: readonly [ArtifactDestination, ArtifactDestination]): string {
  const digest = createHash('sha256')
    .update(JSON.stringify(destinations.map((destination) => destination.canonicalPath)))
    .digest('hex');
  return `.tslean-transaction-${digest}.json`;
}

function transactionFiles(root: string): readonly string[] {
  return readdirSync(root).filter((name) => name.includes('.tslean-'));
}

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

function compilerArguments(
  projectRoot: string,
  sourcePath: string,
  outputPath: string,
  manifestPath: string,
): readonly string[] {
  return [
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
  ];
}

async function waitForPath(path: string, child: ReturnType<typeof spawn>): Promise<void> {
  const deadline = Date.now() + 10_000;
  while (!existsSync(path)) {
    if (child.exitCode !== null) throw new TypeError('compiler exited before invoking the Lake launcher');
    if (Date.now() >= deadline) throw new TypeError('compiler did not invoke the Lake launcher');
    await new Promise((resolvePromise) => setTimeout(resolvePromise, 10));
  }
}

async function collectChild(
  child: ReturnType<typeof spawn>,
): Promise<{ readonly status: number | null; readonly stderr: string }> {
  let stderr = '';
  child.stderr?.setEncoding('utf8');
  child.stderr?.on('data', (chunk: string) => {
    stderr += chunk;
  });
  const status = await new Promise<number | null>((resolvePromise, rejectPromise) => {
    child.once('error', rejectPromise);
    child.once('exit', resolvePromise);
  });
  return { status, stderr };
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function sha256(value: string): string {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}

function shellQuote(value: string): string {
  return `'${value.replaceAll("'", `'\\''`)}'`;
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
