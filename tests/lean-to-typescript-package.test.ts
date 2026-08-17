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
  unlinkSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { describe, expect, test } from 'vitest';
import { choosePlacementFromData } from '../examples/lean-to-typescript/placement.adapter.js';
import {
  nodeArtifactFileSystem,
  publishArtifactPairWithFileSystem,
  recoverArtifactPairWithFileSystem,
  type ArtifactDestination,
  type ArtifactFileSystem,
} from '../src/lean-to-typescript/artifact-transaction.js';
import { runLeanToTypeScriptCli } from '../src/lean-to-typescript/cli.js';
import { compileLeanToTypeScriptWithInputs } from '../src/lean-to-typescript/compiler.js';
import { compareCodePoints } from '../src/lean-to-typescript/ordering.js';
import { createLeanProjectFixture } from './helpers/lean-project-fixture.js';

const repositoryRoot = resolve(import.meta.dirname, '..');
const PACKED_COMPILER_TIMEOUT_MS = 60_000;

describe('published Lean to TypeScript API', () => {
  test('rejects unsupported platforms before compiler or publication mutation', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-unsupported-platform-'));
    const nonexistentProjectRoot = join(temporaryRoot, 'project');
    const outputRoot = join(temporaryRoot, 'output');
    const destinations = transactionDestinations(outputRoot);
    const unsupportedPlatform = { name: 'darwin' } as const;
    try {
      expect(() =>
        compileLeanToTypeScriptWithInputs(
          {
            projectRoot: nonexistentProjectRoot,
            moduleName: 'Fixture',
            sourcePath: join(nonexistentProjectRoot, 'Fixture.lean'),
            declarations: ['Fixture.decide'],
          },
          unsupportedPlatform,
        ),
      ).toThrowError(/Lean-to-TypeScript v1 requires Linux/u);
      expect(() =>
        publishArtifactPairWithFileSystem(
          destinations,
          ['generated output\n', 'generated manifest\n'],
          nodeArtifactFileSystem,
          unsupportedPlatform,
        ),
      ).toThrowError(/Lean-to-TypeScript v1 requires Linux/u);
      expect(() =>
        runLeanToTypeScriptCli(
          [
            '--project-root',
            nonexistentProjectRoot,
            '--module',
            'Fixture',
            '--source',
            join(nonexistentProjectRoot, 'Fixture.lean'),
            '--declaration',
            'Fixture.decide',
            '--output',
            destinations[0].path,
            '--manifest',
            destinations[1].path,
          ],
          unsupportedPlatform,
        ),
      ).toThrowError(/Lean-to-TypeScript v1 requires Linux/u);
      expect(existsSync(nonexistentProjectRoot)).toBe(false);
      expect(existsSync(outputRoot)).toBe(false);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

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

  test.each([1, 2, 3])('retries recovery after the recovery process crashes on rename %i', (occurrence) => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-recovery-crash-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    try {
      const publisher = crashArtifactTransaction(
        temporaryRoot,
        destinations,
        ['new output\n', 'new manifest\n'],
        'rename',
        3,
      );
      expect(publisher.signal).toBe('SIGKILL');
      const recovery = crashArtifactRecovery(temporaryRoot, destinations, 'rename', occurrence);
      expect(recovery.signal).toBe('SIGKILL');

      recoverArtifactPairWithFileSystem(destinations, nodeArtifactFileSystem);

      expect(readFileSync(destinations[0].path, 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
      expect(transactionFiles(temporaryRoot)).toEqual([]);
      expect(readdirSync(temporaryRoot).filter((name) => name.endsWith('.lock'))).toEqual([]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test.each([1, 2, 3, 4])('retries committed recovery after removal %i crashes', (occurrence) => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-committed-recovery-crash-'));
    const destinations = transactionDestinations(temporaryRoot);
    const newContents = ['new output\n', 'new manifest\n'] as const;
    writeFileSync(destinations[0].path, 'old output\n');
    writeFileSync(destinations[1].path, 'old manifest\n');
    try {
      const publisher = crashArtifactTransaction(temporaryRoot, destinations, newContents, 'fsync', 12);
      expect(publisher.signal).toBe('SIGKILL');
      const recovery = crashArtifactRecovery(temporaryRoot, destinations, 'remove', occurrence);
      expect(recovery.signal).toBe('SIGKILL');

      recoverArtifactPairWithFileSystem(destinations, nodeArtifactFileSystem);

      expect(readFileSync(destinations[0].path, 'utf8')).toBe(newContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(newContents[1]);
      expect(transactionFiles(temporaryRoot)).toEqual([]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

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

  test('never removes a replacement at a stage path after its own stage write fails', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-stage-write-replacement-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const replacementContents = 'foreign stage replacement\n';
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    let displacedStagePath: string | undefined;
    let replacementStagePath: string | undefined;
    const filesystem: ArtifactFileSystem = {
      ...nodeArtifactFileSystem,
      write(descriptor, contents) {
        nodeArtifactFileSystem.write(descriptor, contents);
        if (contents !== 'new output\n') return;
        const stagePath = nodeArtifactFileSystem.realpath(`/proc/self/fd/${descriptor}`);
        displacedStagePath = `${stagePath}.displaced`;
        replacementStagePath = stagePath;
        renameSync(stagePath, displacedStagePath);
        writeFileSync(stagePath, replacementContents);
        throw new TypeError('injected stage write failure');
      },
    };
    try {
      expect(() =>
        publishArtifactPairWithFileSystem(destinations, ['new output\n', 'new manifest\n'], filesystem),
      ).toThrowError(/artifact transaction file identity changed/u);
      expect(displacedStagePath).toBeDefined();
      expect(replacementStagePath).toBeDefined();
      if (displacedStagePath === undefined || replacementStagePath === undefined) {
        throw new TypeError('stage replacement was not injected');
      }
      expect(readFileSync(displacedStagePath, 'utf8')).toBe('new output\n');
      expect(readFileSync(replacementStagePath, 'utf8')).toBe(replacementContents);
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
      expect(readdirSync(temporaryRoot).filter((name) => name.endsWith('.lock'))).toHaveLength(1);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('rejects a stage path replaced before publication without accepting its contents', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-stage-prerename-replacement-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const foreignContents = 'foreign stage contents\n';
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    let renames = 0;
    let displacedStagePath: string | undefined;
    let replacementStagePath: string | undefined;
    const filesystem: ArtifactFileSystem = {
      ...nodeArtifactFileSystem,
      rename(from, to) {
        nodeArtifactFileSystem.rename(from, to);
        renames += 1;
        if (renames !== 2) return;
        const stageName = transactionFiles(temporaryRoot).find((name) =>
          name.startsWith('.generated.ts.tslean-stage-'),
        );
        if (stageName === undefined) throw new TypeError('output stage did not exist before publication');
        replacementStagePath = join(temporaryRoot, stageName);
        displacedStagePath = `${replacementStagePath}.displaced`;
        renameSync(replacementStagePath, displacedStagePath);
        writeFileSync(replacementStagePath, foreignContents);
      },
    };
    try {
      expect(() =>
        publishArtifactPairWithFileSystem(destinations, ['new output\n', 'new manifest\n'], filesystem),
      ).toThrowError(/artifact transaction file identity changed/u);
      expect(displacedStagePath).toBeDefined();
      expect(replacementStagePath).toBeDefined();
      if (displacedStagePath === undefined || replacementStagePath === undefined) {
        throw new TypeError('stage replacement was not injected');
      }
      expect(readFileSync(displacedStagePath, 'utf8')).toBe('new output\n');
      expect(readFileSync(replacementStagePath, 'utf8')).toBe(foreignContents);
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('never overwrites a replacement that appears after the original destination is moved', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-destination-replacement-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const foreignContents = 'foreign destination replacement\n';
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    let renames = 0;
    const filesystem: ArtifactFileSystem = {
      ...nodeArtifactFileSystem,
      rename(from, to) {
        nodeArtifactFileSystem.rename(from, to);
        renames += 1;
        if (renames === 2) writeFileSync(destinations[0].path, foreignContents);
      },
    };
    try {
      expect(() =>
        publishArtifactPairWithFileSystem(destinations, ['new output\n', 'new manifest\n'], filesystem),
      ).toThrowError(/artifact publication failed and rollback failed: artifact rollback destination changed/u);
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(foreignContents);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
      expect(transactionFiles(temporaryRoot)).toContain(transactionJournalFilename(destinations));
      expect(
        transactionFiles(temporaryRoot).some(
          (name) =>
            name.startsWith('.generated.ts.tslean-backup-') &&
            readFileSync(join(temporaryRoot, name), 'utf8') === oldContents[0],
        ),
      ).toBe(true);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('rejects a replacement moved to the destination during stage publication', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-stage-postrename-replacement-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const foreignContents = 'foreign published contents\n';
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    let renames = 0;
    let displacedStagePath: string | undefined;
    const filesystem: ArtifactFileSystem = {
      ...nodeArtifactFileSystem,
      rename(from, to) {
        renames += 1;
        if (renames === 3) {
          displacedStagePath = join(temporaryRoot, `${basename(from)}.displaced`);
          renameSync(from, displacedStagePath);
          writeFileSync(from, foreignContents);
        }
        nodeArtifactFileSystem.rename(from, to);
      },
    };
    try {
      expect(() =>
        publishArtifactPairWithFileSystem(destinations, ['new output\n', 'new manifest\n'], filesystem),
      ).toThrowError(/artifact publication failed and rollback failed: artifact transaction file identity changed/u);
      expect(displacedStagePath).toBeDefined();
      if (displacedStagePath === undefined) throw new TypeError('stage replacement was not injected');
      expect(readFileSync(displacedStagePath, 'utf8')).toBe('new output\n');
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(foreignContents);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
      expect(
        transactionFiles(temporaryRoot).some(
          (name) =>
            name.startsWith('.generated.ts.tslean-backup-') &&
            readFileSync(join(temporaryRoot, name), 'utf8') === oldContents[0],
        ),
      ).toBe(true);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('revalidates the complete published pair before recording its commit', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-pair-precommit-replacement-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const foreignContents = 'foreign output replacement\n';
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    let renames = 0;
    let displacedOutputPath: string | undefined;
    const filesystem: ArtifactFileSystem = {
      ...nodeArtifactFileSystem,
      rename(from, to) {
        nodeArtifactFileSystem.rename(from, to);
        renames += 1;
        if (renames !== 4) return;
        displacedOutputPath = `${destinations[0].path}.displaced`;
        renameSync(destinations[0].path, displacedOutputPath);
        writeFileSync(destinations[0].path, foreignContents);
      },
    };
    try {
      expect(() =>
        publishArtifactPairWithFileSystem(destinations, ['new output\n', 'new manifest\n'], filesystem),
      ).toThrowError(/artifact publication failed and rollback failed: artifact transaction file identity changed/u);
      expect(displacedOutputPath).toBeDefined();
      if (displacedOutputPath === undefined) throw new TypeError('output replacement was not injected');
      expect(readFileSync(displacedOutputPath, 'utf8')).toBe('new output\n');
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(foreignContents);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test.each([
    ['write', 1, 'old'],
    ['write', 2, 'old'],
    ['write', 3, 'old'],
    ['write', 4, 'old'],
    ['write', 5, 'old'],
    ['write', 6, 'old'],
    ['write', 7, 'old'],
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
    ['fsync', 8, 'old'],
    ['fsync', 9, 'old'],
    ['fsync', 10, 'old'],
    ['fsync', 11, 'old'],
    ['fsync', 12, 'old'],
    ['fsync', 13, 'old'],
    ['fsync', 14, 'new'],
    ['fsync', 15, 'new'],
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
    ['write', 1, 'old'],
    ['write', 2, 'old'],
    ['write', 3, 'old'],
    ['write', 4, 'old'],
    ['write', 5, 'old'],
    ['write', 6, 'old'],
    ['write', 7, 'new'],
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
    ['fsync', 8, 'old'],
    ['fsync', 9, 'old'],
    ['fsync', 10, 'old'],
    ['fsync', 11, 'old'],
    ['fsync', 12, 'new'],
    ['fsync', 13, 'new'],
    ['fsync', 14, 'new'],
    ['fsync', 15, 'new'],
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

  test('recovers an identity-bound stage left by a crash before the prepared journal', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-prejournal-crash-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const finalContents = ['final output\n', 'final manifest\n'] as const;
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    try {
      const crashed = crashArtifactTransaction(
        temporaryRoot,
        destinations,
        ['abandoned output\n', 'abandoned manifest\n'],
        'write',
        2,
      );
      expect(crashed.signal).toBe('SIGKILL');
      expect(transactionFiles(temporaryRoot).filter((name) => name.includes('.tslean-stage-'))).toHaveLength(1);

      publishArtifactPairWithFileSystem(destinations, finalContents, nodeArtifactFileSystem);

      expect(readFileSync(destinations[0].path, 'utf8')).toBe(finalContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(finalContents[1]);
      expect(transactionFiles(temporaryRoot)).toEqual([]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('preserves every recorded pre-journal stage when any identity was replaced', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-prejournal-replacement-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const foreignContents = 'foreign stage replacement\n';
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    try {
      const crashed = crashArtifactTransaction(
        temporaryRoot,
        destinations,
        ['abandoned output\n', 'abandoned manifest\n'],
        'write',
        5,
      );
      expect(crashed.signal).toBe('SIGKILL');
      const stageNames = transactionFiles(temporaryRoot).filter((name) => name.includes('.tslean-stage-'));
      expect(stageNames).toHaveLength(2);
      const outputStageName = stageNames.find((name) => name.startsWith('.generated.ts.tslean-stage-'));
      const manifestStageName = stageNames.find((name) => name.startsWith('.generated.manifest.json.tslean-stage-'));
      if (outputStageName === undefined || manifestStageName === undefined) {
        throw new TypeError('crashed publisher did not leave both stages');
      }
      const outputStagePath = join(temporaryRoot, outputStageName);
      const manifestStagePath = join(temporaryRoot, manifestStageName);
      const displacedManifestStagePath = `${manifestStagePath}.displaced`;
      renameSync(manifestStagePath, displacedManifestStagePath);
      writeFileSync(manifestStagePath, foreignContents);

      expect(() =>
        publishArtifactPairWithFileSystem(destinations, ['final output\n', 'final manifest\n'], nodeArtifactFileSystem),
      ).toThrowError(/artifact transaction file identity changed/u);

      expect(readFileSync(outputStagePath, 'utf8')).toBe('abandoned output\n');
      expect(readFileSync(manifestStagePath, 'utf8')).toBe(foreignContents);
      expect(readFileSync(displacedManifestStagePath, 'utf8')).toBe('abandoned manifest\n');
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('blocks a live contender, then recovers and publishes after the owner crashes', async () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-contender-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    const newContents = ['new output\n', 'new manifest\n'] as const;
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    const owner = startPausedCrashingArtifactTransaction(temporaryRoot, destinations, newContents);
    try {
      await waitForPath(owner.readyPath, owner.child);
      const contender = startObservedArtifactTransaction(temporaryRoot, destinations, [
        'contender output\n',
        'contender manifest\n',
      ]);
      await waitForPath(contender.attemptedPath, contender.child);
      await waitForProcessTurn();
      expect(existsSync(contender.acquiredPath)).toBe(false);
      expect(contender.child.exitCode).toBe(null);
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
      writeFileSync(owner.releasePath, 'continue\n');
      const crashed = await collectChild(owner.child);
      expect(crashed.signal).toBe('SIGKILL');
      const published = await collectChild(contender.child);
      expect(published.status).toBe(0);
      expect(readFileSync(contender.acquiredPath, 'utf8')).toBe('1\n');
      expect(readFileSync(destinations[0].path, 'utf8')).toBe('contender output\n');
      expect(readFileSync(destinations[1].path, 'utf8')).toBe('contender manifest\n');
      expect(transactionFiles(temporaryRoot)).toEqual([]);
    } finally {
      writeFileSync(owner.releasePath, 'cleanup\n');
      if (owner.child.exitCode === null && owner.child.signalCode === null) {
        owner.child.kill('SIGKILL');
        await collectChild(owner.child);
      }
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test.each([
    ['same-directory order', false],
    ['reversed cross-directory order', true],
  ] as const)(
    'rebinds a blocked contender after a successful owner removes the lock in %s',
    async (_name, crossDirectory) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-successful-handoff-'));
      const outputRoot = crossDirectory ? join(temporaryRoot, 'z-output') : temporaryRoot;
      const manifestRoot = crossDirectory ? join(temporaryRoot, 'a-manifest') : outputRoot;
      if (crossDirectory) {
        mkdirSync(outputRoot);
        mkdirSync(manifestRoot);
      }
      const destinations = transactionDestinations(outputRoot, manifestRoot);
      const contenderDestinations = crossDirectory ? ([destinations[1], destinations[0]] as const) : destinations;
      const contenderContents = crossDirectory
        ? (['contender manifest\n', 'contender output\n'] as const)
        : (['contender output\n', 'contender manifest\n'] as const);
      writeFileSync(destinations[0].path, 'old output\n');
      writeFileSync(destinations[1].path, 'old manifest\n');
      const owner = startPausedCrashingArtifactTransaction(
        temporaryRoot,
        destinations,
        ['owner output\n', 'owner manifest\n'],
        false,
      );
      try {
        await waitForPath(owner.readyPath, owner.child);
        const contender = startObservedArtifactTransaction(temporaryRoot, contenderDestinations, contenderContents);
        await waitForPath(contender.attemptedPath, contender.child);
        expect(readFileSync(contender.attemptedPath, 'utf8')).toBe('1\n');
        await waitForProcessTurn();
        expect(existsSync(contender.acquiredPath)).toBe(false);
        expect(contender.child.exitCode).toBe(null);

        writeFileSync(owner.releasePath, 'continue\n');
        const firstPublication = await collectChild(owner.child);
        expect(firstPublication.status).toBe(0);
        const secondPublication = await collectChild(contender.child);
        expect(secondPublication.status).toBe(0);
        expect(readFileSync(contender.acquiredPath, 'utf8')).toBe('2\n');
        expect(readFileSync(destinations[0].path, 'utf8')).toBe('contender output\n');
        expect(readFileSync(destinations[1].path, 'utf8')).toBe('contender manifest\n');
        expect([...transactionFiles(outputRoot), ...transactionFiles(manifestRoot)]).toEqual([]);
        expect(
          [outputRoot, manifestRoot].flatMap((root) => readdirSync(root).filter((name) => name.endsWith('.lock'))),
        ).toEqual([]);
      } finally {
        writeFileSync(owner.releasePath, 'cleanup\n');
        if (owner.child.exitCode === null && owner.child.signalCode === null) {
          owner.child.kill('SIGKILL');
          await collectChild(owner.child);
        }
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test('serializes a cross-directory pair independent of destination order', async () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-cross-directory-contender-'));
    const outputRoot = join(temporaryRoot, 'output');
    const manifestRoot = join(temporaryRoot, 'manifest');
    mkdirSync(outputRoot);
    mkdirSync(manifestRoot);
    const destinations = transactionDestinations(outputRoot, manifestRoot);
    const reversedDestinations = [destinations[1], destinations[0]] as const;
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    const owner = startPausedCrashingArtifactTransaction(temporaryRoot, destinations, [
      'new output\n',
      'new manifest\n',
    ]);
    try {
      await waitForPath(owner.readyPath, owner.child);

      const contender = startObservedArtifactTransaction(temporaryRoot, reversedDestinations, [
        'contender manifest\n',
        'contender output\n',
      ]);
      await waitForPath(contender.attemptedPath, contender.child);
      await waitForProcessTurn();
      expect(existsSync(contender.acquiredPath)).toBe(false);
      expect(contender.child.exitCode).toBe(null);
      writeFileSync(owner.releasePath, 'continue\n');
      const crashed = await collectChild(owner.child);
      expect(crashed.signal).toBe('SIGKILL');
      const published = await collectChild(contender.child);
      expect(published.status).toBe(0);
      expect(readFileSync(contender.acquiredPath, 'utf8')).toBe('1\n');
      expect(readFileSync(destinations[0].path, 'utf8')).toBe('contender output\n');
      expect(readFileSync(destinations[1].path, 'utf8')).toBe('contender manifest\n');
      expect([...transactionFiles(outputRoot), ...transactionFiles(manifestRoot)]).toEqual([]);
    } finally {
      writeFileSync(owner.releasePath, 'cleanup\n');
      if (owner.child.exitCode === null && owner.child.signalCode === null) {
        owner.child.kill('SIGKILL');
        await collectChild(owner.child);
      }
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('fails closed when a blocked contender wakes after a foreign process replaces the lock path', async () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-foreign-lock-handoff-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    const owner = startPausedCrashingArtifactTransaction(
      temporaryRoot,
      destinations,
      ['owner output\n', 'owner manifest\n'],
      false,
    );
    let replacement: ReturnType<typeof startForeignPublicationLockReplacement> | undefined;
    try {
      await waitForPath(owner.readyPath, owner.child);
      const contender = startObservedArtifactTransaction(temporaryRoot, destinations, [
        'contender output\n',
        'contender manifest\n',
      ]);
      await waitForPath(contender.attemptedPath, contender.child);
      expect(readFileSync(contender.attemptedPath, 'utf8')).toBe('1\n');
      await waitForProcessTurn();
      expect(existsSync(contender.acquiredPath)).toBe(false);

      const lockPath = join(temporaryRoot, `${transactionJournalFilename(destinations)}.lock`);
      replacement = startForeignPublicationLockReplacement(temporaryRoot, lockPath);
      await waitForPath(replacement.readyPath, replacement.child);
      const foreignLock = readFileSync(lockPath);
      const transactionState = transactionFiles(temporaryRoot).map(
        (name) => [name, readFileSync(join(temporaryRoot, name))] as const,
      );

      writeFileSync(owner.releasePath, 'continue\n');
      const displacedOwner = await collectChild(owner.child);
      expect(displacedOwner.status).not.toBe(0);
      expect(displacedOwner.stderr).toMatch(/artifact publication lock identity changed/u);
      await waitForFileContents(contender.attemptedPath, '2\n', contender.child);
      expect(readFileSync(contender.acquiredPath, 'utf8')).toBe('1\n');
      expect(contender.child.exitCode).toBe(null);

      writeFileSync(replacement.releasePath, 'continue\n');
      const foreignProcess = await collectChild(replacement.child);
      expect(foreignProcess.status).toBe(0);
      const rejectedContender = await collectChild(contender.child);
      expect(rejectedContender.status).not.toBe(0);
      expect(rejectedContender.stderr).toMatch(/journal owner does not match the publication lock/u);
      expect(readFileSync(contender.acquiredPath, 'utf8')).toBe('2\n');
      expect(readFileSync(lockPath)).toEqual(foreignLock);
      expect(
        transactionFiles(temporaryRoot).map((name) => [name, readFileSync(join(temporaryRoot, name))] as const),
      ).toEqual(transactionState);
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
    } finally {
      writeFileSync(owner.releasePath, 'cleanup\n');
      if (owner.child.exitCode === null && owner.child.signalCode === null) {
        owner.child.kill('SIGKILL');
        await collectChild(owner.child);
      }
      if (replacement !== undefined) {
        writeFileSync(replacement.releasePath, 'cleanup\n');
        if (replacement.child.exitCode === null && replacement.child.signalCode === null) {
          replacement.child.kill('SIGKILL');
          await collectChild(replacement.child);
        }
      }
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('fails closed when a live owner lock is deleted and recovers only after that owner exits', async () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-lock-deletion-'));
    const destinations = transactionDestinations(temporaryRoot);
    const oldContents = ['old output\n', 'old manifest\n'] as const;
    writeFileSync(destinations[0].path, oldContents[0]);
    writeFileSync(destinations[1].path, oldContents[1]);
    const owner = startPausedCrashingArtifactTransaction(temporaryRoot, destinations, [
      'new output\n',
      'new manifest\n',
    ]);
    try {
      await waitForPath(owner.readyPath, owner.child);
      const lockNames = readdirSync(temporaryRoot).filter((name) => name.endsWith('.lock'));
      expect(lockNames).toHaveLength(1);
      const lockName = lockNames[0];
      if (lockName === undefined) throw new TypeError('publication lock disappeared');
      unlinkSync(join(temporaryRoot, lockName));

      expect(() =>
        publishArtifactPairWithFileSystem(
          destinations,
          ['contender output\n', 'contender manifest\n'],
          nodeArtifactFileSystem,
        ),
      ).toThrowError(/journal belongs to a live foreign publisher/u);
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);

      writeFileSync(owner.releasePath, 'continue\n');
      const failedOwner = await collectChild(owner.child);
      expect(failedOwner.status).not.toBe(0);
      recoverArtifactPairWithFileSystem(destinations, nodeArtifactFileSystem);
      expect(readFileSync(destinations[0].path, 'utf8')).toBe(oldContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(oldContents[1]);
      expect(transactionFiles(temporaryRoot)).toEqual([]);
      expect(readdirSync(temporaryRoot).filter((name) => name.endsWith('.lock'))).toEqual([]);
    } finally {
      writeFileSync(owner.releasePath, 'cleanup\n');
      if (owner.child.exitCode === null && owner.child.signalCode === null) {
        owner.child.kill('SIGKILL');
        await collectChild(owner.child);
      }
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('preserves committed journals when the lock path is replaced during cleanup', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-committed-lock-replacement-'));
    const destinations = transactionDestinations(temporaryRoot);
    const lockPath = join(temporaryRoot, `${transactionJournalFilename(destinations)}.lock`);
    writeFileSync(destinations[0].path, 'old output\n');
    writeFileSync(destinations[1].path, 'old manifest\n');
    let backupRemovals = 0;
    let replaceOnNextSynchronization = false;
    let foreignLock: Buffer | undefined;
    const filesystem: ArtifactFileSystem = {
      ...nodeArtifactFileSystem,
      fsync(descriptor) {
        nodeArtifactFileSystem.fsync(descriptor);
        if (!replaceOnNextSynchronization) return;
        replaceOnNextSynchronization = false;
        const replacementPath = `${lockPath}.foreign`;
        writeFileSync(
          replacementPath,
          reassignPublicationLock(readFileSync(lockPath, 'utf8'), '00000000-0000-4000-8000-000000000000'),
        );
        renameSync(replacementPath, lockPath);
        foreignLock = readFileSync(lockPath);
      },
      remove(path) {
        nodeArtifactFileSystem.remove(path);
        if (path.includes('.tslean-backup-')) {
          backupRemovals += 1;
          replaceOnNextSynchronization = backupRemovals === 2;
        }
      },
    };
    try {
      expect(() =>
        publishArtifactPairWithFileSystem(destinations, ['new output\n', 'new manifest\n'], filesystem),
      ).toThrowError(/artifact publication lock identity changed/u);
      expect(foreignLock).toBeDefined();
      expect(readFileSync(lockPath)).toEqual(foreignLock);
      expect(transactionFiles(temporaryRoot)).toEqual([
        transactionJournalFilename(destinations),
        `${transactionJournalFilename(destinations)}.committed`,
      ]);
      expect(readFileSync(destinations[0].path, 'utf8')).toBe('new output\n');
      expect(readFileSync(destinations[1].path, 'utf8')).toBe('new manifest\n');
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('reuses and removes a stale publication lock left by a crashed owner', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-stale-lock-'));
    const destinations = transactionDestinations(temporaryRoot);
    writeFileSync(destinations[0].path, 'old output\n');
    writeFileSync(destinations[1].path, 'old manifest\n');
    try {
      const staleOwner = crashArtifactTransaction(
        temporaryRoot,
        destinations,
        ['abandoned output\n', 'abandoned manifest\n'],
        'fsync',
        3,
      );
      expect(staleOwner.signal).toBe('SIGKILL');
      const lockNames = readdirSync(temporaryRoot).filter((name) => name.endsWith('.lock'));
      expect(lockNames).toHaveLength(1);

      publishArtifactPairWithFileSystem(destinations, ['second output\n', 'second manifest\n'], nodeArtifactFileSystem);

      expect(readFileSync(destinations[0].path, 'utf8')).toBe('second output\n');
      expect(readFileSync(destinations[1].path, 'utf8')).toBe('second manifest\n');
      expect(readdirSync(temporaryRoot).filter((name) => name.endsWith('.lock'))).toEqual([]);
      expect(transactionFiles(temporaryRoot)).toEqual([]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('rejects a foreign lock owner without changing the crashed transaction', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-foreign-lock-'));
    const destinations = transactionDestinations(temporaryRoot);
    writeFileSync(destinations[0].path, 'old output\n');
    writeFileSync(destinations[1].path, 'old manifest\n');
    try {
      const crashed = crashArtifactTransaction(
        temporaryRoot,
        destinations,
        ['new output\n', 'new manifest\n'],
        'rename',
        3,
      );
      expect(crashed.signal).toBe('SIGKILL');
      const lockPath = join(temporaryRoot, `${transactionJournalFilename(destinations)}.lock`);
      writeFileSync(
        lockPath,
        reassignPublicationLock(readFileSync(lockPath, 'utf8'), '00000000-0000-4000-8000-000000000000'),
      );
      const beforeOutput = readFileSync(destinations[0].path);
      const beforeManifest = existsSync(destinations[1].path) ? readFileSync(destinations[1].path) : undefined;
      const beforeTransactionFiles = transactionFiles(temporaryRoot).map(
        (name) => [name, readFileSync(join(temporaryRoot, name))] as const,
      );

      expect(() => recoverArtifactPairWithFileSystem(destinations, nodeArtifactFileSystem)).toThrowError(
        /journal owner does not match the publication lock/u,
      );
      expect(readFileSync(destinations[0].path)).toEqual(beforeOutput);
      expect(existsSync(destinations[1].path)).toBe(beforeManifest !== undefined);
      if (beforeManifest !== undefined) expect(readFileSync(destinations[1].path)).toEqual(beforeManifest);
      expect(
        transactionFiles(temporaryRoot).map((name) => [name, readFileSync(join(temporaryRoot, name))] as const),
      ).toEqual(beforeTransactionFiles);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

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
    ['write', 5, 'old'],
    ['write', 6, 'old'],
    ['fsync', 10, 'old'],
    ['rename', 4, 'old'],
    ['write', 7, 'old'],
    ['write', 8, 'old'],
    ['write', 9, 'new'],
    ['fsync', 17, 'new'],
    ['fsync', 18, 'new'],
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
        if (!isRecord(installedManifest)) throw new TypeError('packed generator emitted a malformed manifest');
        const installedSemantic = installedManifest['semantic'];
        if (!isRecord(installedSemantic) || !Array.isArray(installedSemantic['inputs'])) {
          throw new TypeError('packed generator emitted a malformed semantic identity');
        }
        expect(installedCode).toContain('export function decide(value: boolean): boolean');
        expect(installedSemantic['inputClosureSha256']).toBe(sha256(JSON.stringify(installedSemantic['inputs'])));
        expect(installedCode).toContain(` * Semantic identity: ${sha256(JSON.stringify(installedSemantic))}`);
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
        const packedSemantic = parsed['manifest']['semantic'];
        if (!isRecord(packedSemantic)) throw new TypeError('packed compiler emitted a malformed semantic identity');
        expect(parsed['code']).toContain('export function decide(value: boolean): boolean');
        expect(packedSemantic['sourceModule']).toBe('Consumer');
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

  test('binds every executable model to one complete deterministic W-3 registry entry', () => {
    const registryPath = join(repositoryRoot, 'spec', 'lean-to-typescript', 'compiler-registry.json');
    const source = readFileSync(registryPath, 'utf8');
    const registry: unknown = JSON.parse(source);
    if (!isRecord(registry) || registry['schemaVersion'] !== 1 || !Array.isArray(registry['models'])) {
      throw new TypeError('compiler registry has an invalid root');
    }
    expect(source.endsWith('\n')).toBe(true);
    expect(source).not.toContain('\r');
    const models = registry['models'].filter(isRecord);
    expect(models).toHaveLength(registry['models'].length);
    expect(models.map((model) => model['id'])).toEqual(['placement-v1', 'enforcement-v1']);

    const oracleSuite = readFileSync(join(repositoryRoot, 'tests', 'lean-to-typescript.test.ts'), 'utf8');
    for (const model of models) {
      const identity = String(model['id']);
      // A model whose generated source carries its own decode boundary needs no adapter file, so
      // the adapter is optional; anything else about an entry is exact.
      expect(Object.keys(model).sort()).toEqual(
        [
          'boundsArtifact',
          'entrypoint',
          'fragmentClosure',
          'generatedTarget',
          'id',
          'oracleOperation',
          ...(Object.hasOwn(model, 'runtimeAdapter') ? ['runtimeAdapter'] : []),
        ].sort(),
      );
      const entrypoint = model['entrypoint'];
      const target = model['generatedTarget'];
      const oracle = model['oracleOperation'];
      if (!isRecord(entrypoint) || !isRecord(target) || !isRecord(oracle)) {
        throw new TypeError(`compiler registry model ${identity} is invalid`);
      }
      expect(Object.keys(entrypoint).sort()).toEqual(['declarations', 'module', 'projectRoot', 'source']);
      expect(Object.keys(target).sort()).toEqual(['manifest', 'source']);
      expect(oracle['command']).toBe('bunx vitest run tests/lean-to-typescript.test.ts');
      expect(oracle['verdict']).toBe('exactly-equal');
      expect(oracleSuite).toContain(String(oracle['selector']));
      for (const path of registryPaths(model)) expect(statSync(join(repositoryRoot, path)).isFile()).toBe(true);

      const generatedSource = readFileSync(join(repositoryRoot, String(target['source'])), 'utf8');
      const adapter = model['runtimeAdapter'];
      if (typeof adapter === 'string') {
        expect(readFileSync(join(repositoryRoot, adapter), 'utf8')).toContain(
          `from './${basename(String(target['source']), '.ts')}.js'`,
        );
      } else {
        // The codec's own boundary is a named union, never `unknown`: a consumer whose lint
        // forbids unparsed parameters has to be able to adopt the artifact unmodified.
        expect(generatedSource).toContain('public static fromData(value: GeneratedData)');
        expect(generatedSource).not.toMatch(/:\s*unknown\b/u);
      }

      const bounds: unknown = JSON.parse(readFileSync(join(repositoryRoot, String(model['boundsArtifact'])), 'utf8'));
      if (!isRecord(bounds) || !Array.isArray(bounds['operations'])) {
        throw new TypeError(`compiler bounds for ${identity} are invalid`);
      }
      expect(bounds['schemaVersion']).toBe(1);
      expect(bounds['model']).toBe(identity);
      expect(bounds['coverage']).toBe('exhaustive');
      let total = 0;
      for (const operation of bounds['operations']) {
        if (!isRecord(operation) || !Array.isArray(operation['dimensions'])) {
          throw new TypeError(`compiler bounds operation for ${identity} is invalid`);
        }
        const cases = operation['dimensions'].reduce((product, dimension) => {
          if (!isRecord(dimension) || typeof dimension['cardinality'] !== 'number') {
            throw new TypeError(`compiler bounds dimension for ${identity} is invalid`);
          }
          return product * dimension['cardinality'];
        }, 1);
        expect(cases).toBe(operation['cases']);
        total += cases;
      }
      expect(total).toBe(bounds['cases']);

      const manifest: unknown = JSON.parse(readFileSync(join(repositoryRoot, String(target['manifest'])), 'utf8'));
      if (!isRecord(manifest)) throw new TypeError(`registered manifest for ${identity} is invalid`);
      const semantic = manifest['semantic'];
      if (!isRecord(semantic) || !Array.isArray(semantic['inputs'])) {
        throw new TypeError(`registered semantic identity for ${identity} is invalid`);
      }
      expect(semantic['sourceModule']).toBe(entrypoint['module']);
      expect(semantic['declarations']).toEqual([...(entrypoint['declarations'] as readonly string[])].sort());
      expect(
        semantic['inputs']
          .filter(isRecord)
          .map((input) => input['identity'])
          .filter((value): value is string => typeof value === 'string'),
      ).toEqual(
        expect.arrayContaining([
          'compiler:spec:compiler-registry.json',
          `compiler:spec:${basename(String(model['boundsArtifact']))}`,
          `source:${String(entrypoint['module'])}`,
        ]),
      );
    }
  });

  test('keeps the registered runtime adapter explicit and fail-closed', () => {
    const all = { bundled: true, dynamic: true, provider: true };
    const provider = { bundled: false, dynamic: false, provider: true };
    expect(choosePlacementFromData(all, all, all, provider)).toBe('provider');
    expect(() => choosePlacementFromData({ bundled: true }, all, all, all)).toThrowError(
      /PlacementSet data fields must be exactly bundled, provider, dynamic/u,
    );
    expect(() => choosePlacementFromData([], all, all, all)).toThrowError(/PlacementSet data must be an object/u);
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
    ...(typeof model['runtimeAdapter'] === 'string' ? [model['runtimeAdapter']] : []),
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

function crashArtifactRecovery(
  root: string,
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  operation: 'remove' | 'rename',
  occurrence: number,
): ReturnType<typeof spawnSync> {
  const moduleUrl = pathToFileURL(join(repositoryRoot, 'src', 'lean-to-typescript', 'artifact-transaction.ts')).href;
  const scriptPath = join(root, 'crash-recovery.mjs');
  writeFileSync(
    scriptPath,
    [
      `import { nodeArtifactFileSystem, recoverArtifactPairWithFileSystem } from ${JSON.stringify(moduleUrl)};`,
      `const destinations = ${JSON.stringify(destinations)};`,
      `const operation = ${JSON.stringify(operation)};`,
      `const occurrence = ${occurrence};`,
      'let removals = 0;',
      'let renames = 0;',
      'const filesystem = {',
      '  ...nodeArtifactFileSystem,',
      '  rename(from, to) {',
      '    nodeArtifactFileSystem.rename(from, to);',
      "    if (operation === 'rename' && ++renames === occurrence) process.kill(process.pid, 'SIGKILL');",
      '  },',
      '  remove(path) {',
      '    nodeArtifactFileSystem.remove(path);',
      "    if (operation === 'remove' && ++removals === occurrence) process.kill(process.pid, 'SIGKILL');",
      '  },',
      '};',
      'recoverArtifactPairWithFileSystem(destinations, filesystem);',
      '',
    ].join('\n'),
  );
  return spawnSync('bun', [scriptPath], { cwd: root, encoding: 'utf8' });
}

function startPausedCrashingArtifactTransaction(
  root: string,
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  contents: readonly [string, string],
  crashAfterThirdRename = true,
): { readonly child: ReturnType<typeof spawn>; readonly readyPath: string; readonly releasePath: string } {
  const moduleUrl = pathToFileURL(join(repositoryRoot, 'src', 'lean-to-typescript', 'artifact-transaction.ts')).href;
  const scriptPath = join(root, 'paused-crash-transaction.mjs');
  const readyPath = join(root, 'owner-ready');
  const releasePath = join(root, 'owner-release');
  writeFileSync(
    scriptPath,
    [
      "import { existsSync, writeFileSync } from 'node:fs';",
      `import { nodeArtifactFileSystem, publishArtifactPairWithFileSystem } from ${JSON.stringify(moduleUrl)};`,
      `const destinations = ${JSON.stringify(destinations)};`,
      `const contents = ${JSON.stringify(contents)};`,
      `const crashAfterThirdRename = ${JSON.stringify(crashAfterThirdRename)};`,
      `const readyPath = ${JSON.stringify(readyPath)};`,
      `const releasePath = ${JSON.stringify(releasePath)};`,
      'let renames = 0;',
      'const filesystem = {',
      '  ...nodeArtifactFileSystem,',
      '  write(descriptor, value) {',
      '    nodeArtifactFileSystem.write(descriptor, value);',
      '    if (value.includes(\'"state":"prepared"\')) {',
      "      writeFileSync(readyPath, 'ready\\n');",
      '      while (!existsSync(releasePath)) Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 10);',
      '    }',
      '  },',
      '  rename(from, to) {',
      '    nodeArtifactFileSystem.rename(from, to);',
      '    renames += 1;',
      "    if (crashAfterThirdRename && renames === 3) process.kill(process.pid, 'SIGKILL');",
      '  },',
      '};',
      'publishArtifactPairWithFileSystem(destinations, contents, filesystem);',
      '',
    ].join('\n'),
  );
  return {
    child: spawn('bun', [scriptPath], { cwd: root, stdio: ['ignore', 'ignore', 'pipe'] }),
    readyPath,
    releasePath,
  };
}

function startObservedArtifactTransaction(
  root: string,
  destinations: readonly [ArtifactDestination, ArtifactDestination],
  contents: readonly [string, string],
): {
  readonly acquiredPath: string;
  readonly attemptedPath: string;
  readonly child: ReturnType<typeof spawn>;
} {
  const moduleUrl = pathToFileURL(join(repositoryRoot, 'src', 'lean-to-typescript', 'artifact-transaction.ts')).href;
  const scriptPath = join(root, 'observed-transaction.mjs');
  const attemptedPath = `${scriptPath}.attempted`;
  const acquiredPath = `${scriptPath}.acquired`;
  writeFileSync(
    scriptPath,
    [
      "import { writeFileSync } from 'node:fs';",
      `import { nodeArtifactFileSystem, publishArtifactPairWithFileSystem } from ${JSON.stringify(moduleUrl)};`,
      `const destinations = ${JSON.stringify(destinations)};`,
      `const contents = ${JSON.stringify(contents)};`,
      `const attemptedPath = ${JSON.stringify(attemptedPath)};`,
      `const acquiredPath = ${JSON.stringify(acquiredPath)};`,
      'let lockAttempts = 0;',
      'const filesystem = {',
      '  ...nodeArtifactFileSystem,',
      '  lock(descriptor) {',
      '    lockAttempts += 1;',
      "    writeFileSync(attemptedPath, String(lockAttempts) + '\\n');",
      '    nodeArtifactFileSystem.lock(descriptor);',
      "    writeFileSync(acquiredPath, String(lockAttempts) + '\\n');",
      '  },',
      '};',
      'publishArtifactPairWithFileSystem(destinations, contents, filesystem);',
      '',
    ].join('\n'),
  );
  return {
    acquiredPath,
    attemptedPath,
    child: spawn('bun', [scriptPath], { cwd: root, stdio: ['ignore', 'ignore', 'pipe'] }),
  };
}

function startForeignPublicationLockReplacement(
  root: string,
  lockPath: string,
): { readonly child: ReturnType<typeof spawn>; readonly readyPath: string; readonly releasePath: string } {
  const moduleUrl = pathToFileURL(join(repositoryRoot, 'src', 'lean-to-typescript', 'artifact-transaction.ts')).href;
  const scriptPath = join(root, 'foreign-lock-replacement.mjs');
  const readyPath = `${scriptPath}.ready`;
  const releasePath = `${scriptPath}.release`;
  writeFileSync(
    scriptPath,
    [
      "import { constants, existsSync, readFileSync, writeFileSync } from 'node:fs';",
      "import { randomUUID } from 'node:crypto';",
      `import { nodeArtifactFileSystem } from ${JSON.stringify(moduleUrl)};`,
      `const lockPath = ${JSON.stringify(lockPath)};`,
      `const readyPath = ${JSON.stringify(readyPath)};`,
      `const releasePath = ${JSON.stringify(releasePath)};`,
      "const processStat = readFileSync('/proc/' + process.pid + '/stat', 'utf8');",
      "const commandEnd = processStat.lastIndexOf(') ');",
      'const processStartTime = processStat.slice(commandEnd + 2).trim().split(/\\s+/u)[19];',
      "if (processStartTime === undefined) throw new TypeError('foreign process identity is unavailable');",
      "const replacementPath = lockPath + '.replacement-' + process.pid;",
      'const descriptor = nodeArtifactFileSystem.open(',
      '  replacementPath,',
      '  constants.O_RDWR | constants.O_CREAT | constants.O_EXCL,',
      '  0o600,',
      ');',
      'nodeArtifactFileSystem.lock(descriptor);',
      'nodeArtifactFileSystem.write(',
      '  descriptor,',
      "  JSON.stringify({ schemaVersion: 1, owner: { processId: process.pid, processStartTime, transactionId: randomUUID() } }) + '\\n',",
      ');',
      'nodeArtifactFileSystem.fsync(descriptor);',
      'nodeArtifactFileSystem.rename(replacementPath, lockPath);',
      "writeFileSync(readyPath, 'ready\\n');",
      'while (!existsSync(releasePath)) Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 10);',
      'nodeArtifactFileSystem.close(descriptor);',
      '',
    ].join('\n'),
  );
  return {
    child: spawn('bun', [scriptPath], { cwd: root, stdio: ['ignore', 'ignore', 'pipe'] }),
    readyPath,
    releasePath,
  };
}

function reassignPublicationLock(source: string, transactionId: string): string {
  if (!source.endsWith('\n')) throw new TypeError('publication lock is not newline terminated');
  const lines = source.slice(0, -1).split('\n');
  return `${lines
    .map((line) => {
      const record: unknown = JSON.parse(line);
      if (!isRecord(record) || !isRecord(record['owner'])) {
        throw new TypeError('publication lock record has no owner');
      }
      return JSON.stringify({
        ...record,
        owner: { ...record['owner'], transactionId },
      });
    })
    .join('\n')}\n`;
}

function transactionJournalFilename(destinations: readonly [ArtifactDestination, ArtifactDestination]): string {
  const digest = createHash('sha256')
    .update(JSON.stringify(destinations.map((destination) => destination.canonicalPath).sort(compareCodePoints)))
    .digest('hex');
  return `.tslean-transaction-${digest}.json`;
}

function transactionFiles(root: string): readonly string[] {
  return readdirSync(root)
    .filter((name) => name.includes('.tslean-') && !name.endsWith('.lock'))
    .sort(compareCodePoints);
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

async function waitForFileContents(path: string, expected: string, child: ReturnType<typeof spawn>): Promise<void> {
  const deadline = Date.now() + 10_000;
  while (!existsSync(path) || readFileSync(path, 'utf8') !== expected) {
    if (child.exitCode !== null) throw new TypeError('process exited before reaching the expected checkpoint');
    if (Date.now() >= deadline) throw new TypeError('process did not reach the expected checkpoint');
    await new Promise((resolvePromise) => setTimeout(resolvePromise, 10));
  }
}

async function waitForProcessTurn(): Promise<void> {
  await new Promise((resolvePromise) => setTimeout(resolvePromise, 50));
}

async function collectChild(
  child: ReturnType<typeof spawn>,
): Promise<{ readonly signal: NodeJS.Signals | null; readonly status: number | null; readonly stderr: string }> {
  let stderr = '';
  const stderrComplete = new Promise<void>((resolvePromise, rejectPromise) => {
    const stream = child.stderr;
    if (stream === null) {
      resolvePromise();
      return;
    }
    stream.setEncoding('utf8');
    stream.on('data', (chunk: string) => {
      stderr += chunk;
    });
    stream.once('error', rejectPromise);
    stream.once('end', resolvePromise);
    if (stream.readableEnded) resolvePromise();
  });
  const processComplete = new Promise<{ readonly signal: NodeJS.Signals | null; readonly status: number | null }>(
    (resolvePromise, rejectPromise) => {
      child.once('error', rejectPromise);
      child.once('exit', (status, signal) => resolvePromise({ signal, status }));
      if (child.exitCode !== null || child.signalCode !== null) {
        resolvePromise({ signal: child.signalCode, status: child.exitCode });
      }
    },
  );
  const [result] = await Promise.all([processComplete, stderrComplete]);
  return { ...result, stderr };
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
