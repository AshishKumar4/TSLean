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
import { basename, dirname, join, relative, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import ts from 'typescript';
import { describe, expect, test } from 'vitest';
import { choosePlacementFromData } from '../examples/lean-to-typescript/placement.adapter.js';
import {
  nodeArtifactFileSystem,
  publishArtifactsWithFileSystem,
  recoverArtifactsWithFileSystem,
  type ArtifactDestination,
  type ArtifactFileSystem,
  type ArtifactTransactionScope,
} from '../src/lean-to-typescript/artifact-transaction.js';
import { runLeanToTypeScriptCli } from '../src/lean-to-typescript/cli.js';
import { compileLeanToTypeScriptWithInputs } from '../src/lean-to-typescript/compiler.js';
import { compareCodePoints } from '../src/lean-to-typescript/ordering.js';
import { createLeanProjectFixture } from './helpers/lean-project-fixture.js';

const repositoryRoot = resolve(import.meta.dirname, '..');
const PACKED_COMPILER_TIMEOUT_MS = 60_000;
const PACKED_SUBPATH_EXPORT_TIMEOUT_MS = 90_000;

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
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
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
            '--out-dir',
            outputRoot,
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

  test.each([
    [['--out-dir', 'generated', '--output', 'generated.ts'], /unknown option --output/u],
    [[], /--out-dir is required/u],
    [['--out-dir', 'first', '--out-dir', 'second'], /--out-dir may be specified only once/u],
  ] as const)('rejects the retired output flag and a missing or repeated --out-dir', (extra, diagnostic) => {
    expect(() =>
      runLeanToTypeScriptCli([
        '--project-root',
        'lean',
        '--module',
        'Fixture',
        '--source',
        join('lean', 'Fixture.lean'),
        '--declaration',
        'Fixture.decide',
        '--manifest',
        'generated.manifest.json',
        ...extra,
      ]),
    ).toThrowError(diagnostic);
  });

  test(
    'rejects a manifest aliased to a generated module without modifying existing bytes',
    () => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const destinationRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-destinations-'));
      const outputDirectory = join(destinationRoot, 'generated');
      mkdirSync(outputDirectory);
      const destinationPath = join(outputDirectory, 'Fixture.ts');
      const original = Buffer.from('preserve this artifact\n');
      writeFileSync(destinationPath, original);
      try {
        const result = runSourceCompiler(
          destinationRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
          './unused/../generated/Fixture.ts',
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain('Fixture.ts and --manifest must identify distinct filesystem paths');
        expect(readFileSync(destinationPath)).toEqual(original);
      } finally {
        rmSync(destinationRoot, { force: true, recursive: true });
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test.each(['symlink-parent', 'hardlink', 'dangling-symlink'] as const)(
    'rejects %s aliases between generated artifact destinations',
    (aliasKind) => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const destinationRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-destination-alias-'));
      const outputDirectory = join(destinationRoot, 'generated');
      mkdirSync(outputDirectory);
      const modulePath = join(outputDirectory, 'Fixture.ts');
      let manifestPath: string;
      if (aliasKind === 'symlink-parent') {
        const aliasDirectory = join(outputDirectory, 'alias');
        symlinkSync(outputDirectory, aliasDirectory, 'dir');
        manifestPath = join(aliasDirectory, 'Fixture.ts');
      } else if (aliasKind === 'hardlink') {
        writeFileSync(modulePath, 'preserve hard-linked artifact\n');
        manifestPath = join(outputDirectory, 'tslean.manifest.json');
        linkSync(modulePath, manifestPath);
      } else {
        manifestPath = join(outputDirectory, 'tslean.manifest.json');
        symlinkSync(modulePath, manifestPath, 'file');
      }
      const original = existsSync(modulePath) ? readFileSync(modulePath) : undefined;
      try {
        const result = runSourceCompiler(
          destinationRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(
          aliasKind === 'hardlink'
            ? 'Fixture.ts and --manifest must identify distinct filesystem paths'
            : 'generated file path contains a symbolic link',
        );
        expect(existsSync(modulePath)).toBe(original !== undefined);
        if (original !== undefined) {
          expect(readFileSync(modulePath)).toEqual(original);
          expect(readFileSync(manifestPath)).toEqual(original);
        } else if (aliasKind === 'dangling-symlink') {
          expect(lstatSync(manifestPath).isSymbolicLink()).toBe(true);
        }
      } finally {
        rmSync(destinationRoot, { force: true, recursive: true });
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test.each([
    ['--manifest', 'generated', '--manifest must be a file inside --out-dir'],
    [
      'Fixture.ts',
      join('generated', 'Fixture.ts', 'generated.manifest.json'),
      'Fixture.ts must not contain the other artifact destination --manifest',
    ],
  ] as const)(
    'rejects a generated tree whose %s destination would contain the other artifact',
    (_ancestor, manifestRelativePath, diagnostic) => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const destinationRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-destination-containment-'));
      const preservedPath = join(destinationRoot, 'preserved.txt');
      const original = Buffer.from('preserve unrelated bytes\n');
      writeFileSync(preservedPath, original);
      const outputDirectory = join(destinationRoot, 'generated');
      const manifestPath = join(destinationRoot, manifestRelativePath);
      try {
        const result = runSourceCompiler(
          destinationRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(diagnostic);
        expect(existsSync(outputDirectory)).toBe(false);
        expect(existsSync(manifestPath)).toBe(false);
        expect(readFileSync(preservedPath)).toEqual(original);
      } finally {
        rmSync(destinationRoot, { force: true, recursive: true });
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test.each([
    [
      'a generated module path that already exists as a directory',
      'existing-directory',
      'Fixture.ts must not identify an existing directory',
    ],
    [
      'a generated tree beneath an existing non-directory',
      'non-directory-ancestor',
      '--out-dir has an existing non-directory ancestor',
    ],
    [
      'a generated tree inside a captured compiler input',
      'compiler-input',
      '--out-dir must not identify compiler input --project-root or an ancestor/descendant path',
    ],
  ] as const)(
    'rejects %s without publishing the generated tree',
    (_label, kind, diagnostic) => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const destinationRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-generated-tree-'));
      const preserved = Buffer.from('preserve unrelated bytes\n');
      const preservedPath = join(destinationRoot, 'preserved.txt');
      writeFileSync(preservedPath, preserved);
      const toolchainPath = join(fixture.projectRoot, 'lean-toolchain');
      const toolchain = readFileSync(toolchainPath);
      let outputDirectory: string;
      if (kind === 'existing-directory') {
        outputDirectory = join(destinationRoot, 'generated');
        mkdirSync(join(outputDirectory, 'Fixture.ts'), { recursive: true });
        writeFileSync(join(outputDirectory, 'Fixture.ts', 'preserved.txt'), preserved);
      } else if (kind === 'non-directory-ancestor') {
        const ancestorPath = join(destinationRoot, 'existing-file');
        writeFileSync(ancestorPath, preserved);
        outputDirectory = join(ancestorPath, 'generated');
      } else {
        outputDirectory = join(fixture.projectRoot, 'generated');
      }
      const manifestPath = join(outputDirectory, 'tslean.manifest.json');
      try {
        const result = runSourceCompiler(
          destinationRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(diagnostic);
        expect(existsSync(manifestPath)).toBe(false);
        expect(readFileSync(preservedPath)).toEqual(preserved);
        expect(readFileSync(toolchainPath)).toEqual(toolchain);
        if (kind === 'existing-directory') {
          expect(readFileSync(join(outputDirectory, 'Fixture.ts', 'preserved.txt'))).toEqual(preserved);
        }
      } finally {
        rmSync(destinationRoot, { force: true, recursive: true });
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test(
    'refuses an output root reached through a symbolic-link ancestor before compilation mutates it',
    () => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const destinationRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-output-root-symlink-'));
      const physical = join(destinationRoot, 'physical');
      const alias = join(destinationRoot, 'alias');
      mkdirSync(physical);
      symlinkSync(physical, alias, 'dir');
      const outputDirectory = join(alias, 'generated');
      const manifestPath = join(outputDirectory, 'tslean.manifest.json');
      try {
        const result = runSourceCompiler(
          destinationRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
          manifestPath,
        );
        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain('--out-dir must not be reached through a symbolic link');
        expect(existsSync(join(physical, 'generated'))).toBe(false);
        expect(existsSync(manifestPath)).toBe(false);
      } finally {
        rmSync(destinationRoot, { force: true, recursive: true });
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test(
    'refuses an unowned TypeScript sibling instead of deleting it during generation',
    () => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const destinationRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-unowned-file-'));
      const outputDirectory = join(destinationRoot, 'generated');
      const manifestPath = join(outputDirectory, 'tslean.manifest.json');
      const keepPath = join(outputDirectory, 'Keep.ts');
      mkdirSync(outputDirectory);
      writeFileSync(keepPath, 'export const keep = true;\n');
      try {
        const result = runSourceCompiler(
          destinationRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
          manifestPath,
        );
        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(`generated tree holds an unexpected file: ${keepPath}`);
        expect(readFileSync(keepPath, 'utf8')).toBe('export const keep = true;\n');
        expect(existsSync(manifestPath)).toBe(false);
      } finally {
        rmSync(destinationRoot, { force: true, recursive: true });
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test(
    'refuses a generated child path that resolves through a symbolic link outside the output root',
    () => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const destinationRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-child-symlink-'));
      const outputDirectory = join(destinationRoot, 'generated');
      const escapedPath = join(destinationRoot, 'outside.ts');
      const manifestPath = join(outputDirectory, 'tslean.manifest.json');
      mkdirSync(outputDirectory);
      writeFileSync(escapedPath, 'export const outside = true;\n');
      symlinkSync(escapedPath, join(outputDirectory, 'Fixture.ts'), 'file');
      try {
        const result = runSourceCompiler(
          destinationRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
          manifestPath,
        );
        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain('generated file escapes the output root through a symbolic link');
        expect(readFileSync(escapedPath, 'utf8')).toBe('export const outside = true;\n');
        expect(existsSync(manifestPath)).toBe(false);
      } finally {
        rmSync(destinationRoot, { force: true, recursive: true });
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
  );

  test(
    'refuses an in-root manifest symlink that targets an external file',
    () => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const destinationRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-manifest-symlink-'));
      const outputDirectory = join(destinationRoot, 'generated');
      const externalManifest = join(destinationRoot, 'external.manifest.json');
      const manifestPath = join(outputDirectory, 'tslean.manifest.json');
      mkdirSync(outputDirectory);
      writeFileSync(externalManifest, '{"external":true}\n');
      symlinkSync(externalManifest, manifestPath, 'file');
      try {
        const result = runSourceCompiler(
          destinationRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
          manifestPath,
        );
        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain('generated file path contains a symbolic link');
        expect(readFileSync(externalManifest, 'utf8')).toBe('{"external":true}\n');
      } finally {
        rmSync(destinationRoot, { force: true, recursive: true });
        fixture.dispose();
      }
    },
    PACKED_COMPILER_TIMEOUT_MS,
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

      recoverArtifactsWithFileSystem(transactionScope(destinations), destinations, nodeArtifactFileSystem);

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

      recoverArtifactsWithFileSystem(transactionScope(destinations), destinations, nodeArtifactFileSystem);

      expect(readFileSync(destinations[0].path, 'utf8')).toBe(newContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(newContents[1]);
      expect(transactionFiles(temporaryRoot)).toEqual([]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('rejects an existing directory as --manifest before compilation without creating generated files', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-directory-destination-'));
    const outputDirectory = join(temporaryRoot, 'generated');
    const directoryPath = join(outputDirectory, 'manifest');
    const preservedInDirectoryPath = join(directoryPath, 'preserved.txt');
    const directoryOriginal = Buffer.from('preserve directory contents\n');
    mkdirSync(directoryPath, { recursive: true });
    writeFileSync(preservedInDirectoryPath, directoryOriginal);
    try {
      const result = runSourceCompiler(
        temporaryRoot,
        join(temporaryRoot, 'missing-project'),
        join(temporaryRoot, 'missing-project', 'Fixture.lean'),
        outputDirectory,
        directoryPath,
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr).toContain('--manifest must not identify an existing directory');
      expect(readFileSync(preservedInDirectoryPath)).toEqual(directoryOriginal);
      expect(readdirSync(outputDirectory)).toEqual(['manifest']);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test(
    'preserves every preexisting artifact when one destination cannot be staged',
    () => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const outputDirectory = join(fixture.projectRoot, 'generated');
      mkdirSync(outputDirectory);
      const outputPath = join(outputDirectory, 'Fixture.ts');
      const original = Buffer.from('preserve generated output\n');
      writeFileSync(outputPath, original);
      const manifestPath = `/sys/tslean-${process.pid}-manifest.json`;
      try {
        const result = runSourceCompiler(
          fixture.projectRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
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
      const publicationContainer = mkdtempSync(join(tmpdir(), 'tslean-cli-root-swap-'));
      const publicationRoot = join(publicationContainer, 'publication');
      const movedRoot = join(publicationContainer, 'publication-original');
      const wrapperRoot = join(fixture.projectRoot, 'wrapper');
      const markerPath = join(fixture.projectRoot, 'launcher-observed');
      mkdirSync(publicationRoot);
      mkdirSync(wrapperRoot);
      const outputPath = join(publicationRoot, 'Fixture.ts');
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
          compilerArguments(fixture.projectRoot, fixture.sourcePath, publicationRoot, manifestPath),
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
        expect(readFileSync(join(movedRoot, 'Fixture.ts'))).toEqual(outputOriginal);
        expect(readFileSync(join(movedRoot, 'generated.manifest.json'))).toEqual(manifestOriginal);
        expect(existsSync(outputPath)).toBe(false);
        expect(existsSync(manifestPath)).toBe(false);
      } finally {
        rmSync(publicationContainer, { force: true, recursive: true });
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
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
          destinations,
          ['new output\n', 'new manifest\n'],
          filesystem,
        ),
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
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
          destinations,
          ['new output\n', 'new manifest\n'],
          filesystem,
        ),
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
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
          destinations,
          ['new output\n', 'new manifest\n'],
          filesystem,
        ),
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
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
          destinations,
          ['new output\n', 'new manifest\n'],
          filesystem,
        ),
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
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
          destinations,
          ['new output\n', 'new manifest\n'],
          filesystem,
        ),
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
          publishArtifactsWithFileSystem(
            transactionScope(destinations),
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

  test('publishes a three-destination generated tree all at once or not at all', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-three-destinations-'));
    const destinations = packageDestinations(temporaryRoot);
    const oldContents = ['old module\n', 'old source map\n', 'old manifest\n'] as const;
    const newContents = ['new module\n', 'new source map\n', 'new manifest\n'] as const;
    try {
      destinations.forEach((destination, index) => writeFileSync(destination.path, oldContents[index]));

      publishArtifactsWithFileSystem(transactionScope(destinations), destinations, newContents, nodeArtifactFileSystem);

      expect(destinations.map((destination) => readFileSync(destination.path, 'utf8'))).toEqual([...newContents]);
      expect(transactionFiles(temporaryRoot)).toEqual([]);
      // Every fault before the durable commit leaves the complete previous tree, never a mixture
      // of the two: staging, backup renames, and journal synchronization each roll all three back.
      for (const [operation, occurrence] of [
        ['write', 9],
        ['rename', 6],
        ['fsync', 15],
      ] as const) {
        expect(() =>
          publishArtifactsWithFileSystem(
            transactionScope(destinations),
            destinations,
            ['third module\n', 'third source map\n', 'third manifest\n'],
            faultingArtifactFileSystem(operation, occurrence),
          ),
        ).toThrowError(`injected ${operation} failure`);
        expect(destinations.map((destination) => readFileSync(destination.path, 'utf8'))).toEqual([...newContents]);
        expect(transactionFiles(temporaryRoot)).toEqual([]);
      }
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('shrinks a generated tree transactionally and restores removed files on rollback', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-shrink-'));
    const destinations = packageDestinations(temporaryRoot);
    const fullContents = ['full module\n', 'full source map\n', 'full manifest\n'] as const;
    const shrunkContents: readonly (string | undefined)[] = ['shrunk module\n', undefined, 'shrunk manifest\n'];
    try {
      destinations.forEach((destination, index) => writeFileSync(destination.path, fullContents[index]));

      // The second original moves to its backup before the third rename faults. Rollback must put
      // the source map back, not merely leave the module and manifest coherent without it.
      expect(() =>
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
          destinations,
          shrunkContents,
          faultingArtifactFileSystem('rename', 3),
        ),
      ).toThrowError('injected rename failure');
      expect(destinations.map((destination) => readFileSync(destination.path, 'utf8'))).toEqual([...fullContents]);
      expect(transactionFiles(temporaryRoot)).toEqual([]);

      publishArtifactsWithFileSystem(
        transactionScope(destinations),
        destinations,
        shrunkContents,
        nodeArtifactFileSystem,
      );
      expect(readFileSync(destinations[0].path, 'utf8')).toBe('shrunk module\n');
      expect(existsSync(destinations[1].path)).toBe(false);
      expect(readFileSync(destinations[2].path, 'utf8')).toBe('shrunk manifest\n');
      expect(transactionFiles(temporaryRoot)).toEqual([]);
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

        recoverArtifactsWithFileSystem(transactionScope(destinations), destinations, nodeArtifactFileSystem);

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

      publishArtifactsWithFileSystem(
        transactionScope(destinations),
        destinations,
        finalContents,
        nodeArtifactFileSystem,
      );

      expect(readFileSync(destinations[0].path, 'utf8')).toBe(finalContents[0]);
      expect(readFileSync(destinations[1].path, 'utf8')).toBe(finalContents[1]);
      expect(transactionFiles(temporaryRoot)).toEqual([]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('recovers pre-journal stages from an older larger tree before publishing a smaller tree', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-prejournal-shrink-'));
    const full = packageDestinations(temporaryRoot);
    const smaller = [full[0], full[2]] as const;
    const oldContents = ['old module\n', 'old source map\n', 'old manifest\n'] as const;
    full.forEach((destination, index) => writeFileSync(destination.path, oldContents[index]));
    try {
      // This kills after the second stage was written and lock-recorded, but before the prepared
      // journal. `Fixture.ts.map` is absent from the next publisher's destination set.
      const crashed = crashArtifactTransaction(
        temporaryRoot,
        full,
        ['abandoned module\n', 'abandoned source map\n', 'abandoned manifest\n'],
        'write',
        5,
      );
      expect(crashed.signal).toBe('SIGKILL');
      expect(transactionFiles(temporaryRoot).filter((name) => name.includes('.tslean-stage-'))).toHaveLength(2);

      publishArtifactsWithFileSystem(
        transactionScope(smaller),
        smaller,
        ['smaller module\n', 'smaller manifest\n'],
        nodeArtifactFileSystem,
      );

      expect(readFileSync(full[0].path, 'utf8')).toBe('smaller module\n');
      expect(readFileSync(full[1].path, 'utf8')).toBe('old source map\n');
      expect(readFileSync(full[2].path, 'utf8')).toBe('smaller manifest\n');
      expect(transactionFiles(temporaryRoot)).toEqual([]);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test('uses the root committed marker before a nested marker to recover a smaller tree after a crash', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-root-marker-'));
    const nestedRoot = join(temporaryRoot, 'nested');
    mkdirSync(nestedRoot);
    const modulePath = join(nestedRoot, 'Module.ts');
    const manifestPath = join(nestedRoot, 'tslean.manifest.json');
    const full = [
      { name: 'Module.ts', path: modulePath, canonicalPath: modulePath },
      { name: '--manifest', path: manifestPath, canonicalPath: manifestPath },
    ] as const;
    const scope: ArtifactTransactionScope = { identity: `test:${temporaryRoot}`, root: temporaryRoot };
    writeFileSync(modulePath, 'old module\n');
    writeFileSync(manifestPath, 'old manifest\n');
    const moduleUrl = pathToFileURL(join(repositoryRoot, 'src', 'lean-to-typescript', 'artifact-transaction.ts')).href;
    const crashPath = join(temporaryRoot, 'crash-after-first-committed-marker.mjs');
    writeFileSync(
      crashPath,
      [
        `import { nodeArtifactFileSystem, publishArtifactsWithFileSystem } from ${JSON.stringify(moduleUrl)};`,
        `const scope = ${JSON.stringify(scope)};`,
        `const destinations = ${JSON.stringify(full)};`,
        "const contents = ['new module\\n', 'new manifest\\n'];",
        'let committedWrites = 0;',
        'const filesystem = {',
        '  ...nodeArtifactFileSystem,',
        '  write(descriptor, value) {',
        '    nodeArtifactFileSystem.write(descriptor, value);',
        `    if (value.includes('"state":"committed"') && ++committedWrites === 1) process.kill(process.pid, 'SIGKILL');`,
        '  },',
        '};',
        'publishArtifactsWithFileSystem(scope, destinations, contents, filesystem);',
        '',
      ].join('\n'),
    );
    try {
      const crashed = spawnSync('bun', [crashPath], { cwd: temporaryRoot, encoding: 'utf8' });
      expect(crashed.signal).toBe('SIGKILL');

      // The next publisher has only the manifest in its current tree. Root-first ordering makes
      // the root committed marker discoverable, so journal-recorded nested paths finish as new.
      recoverArtifactsWithFileSystem(scope, [full[1]], nodeArtifactFileSystem);
      expect(readFileSync(modulePath, 'utf8')).toBe('new module\n');
      expect(readFileSync(manifestPath, 'utf8')).toBe('new manifest\n');
      expect(transactionFiles(temporaryRoot)).toEqual([]);
      expect(transactionFiles(nestedRoot)).toEqual([]);
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
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
          destinations,
          ['final output\n', 'final manifest\n'],
          nodeArtifactFileSystem,
        ),
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
  test('serializes overlapping trees with different manifests through the stable root lock', async () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-transaction-shape-contention-'));
    const smaller = transactionDestinations(temporaryRoot);
    const extraPath = join(temporaryRoot, 'Extra.ts');
    const growingManifest = join(temporaryRoot, 'growing.manifest.json');
    const growing = [
      smaller[0],
      { name: 'Extra.ts', path: extraPath, canonicalPath: extraPath },
      { name: '--manifest', path: growingManifest, canonicalPath: growingManifest },
    ] as const;
    writeFileSync(smaller[0].path, 'old module\n');
    writeFileSync(smaller[1].path, 'old smaller manifest\n');
    const owner = startPausedCrashingArtifactTransaction(temporaryRoot, growing, [
      'growing module\n',
      'growing extra module\n',
      'growing manifest\n',
    ]);
    try {
      await waitForPath(owner.readyPath, owner.child);
      // Same root and overlapping module path, but a genuinely different manifest and destination
      // set. Pair-derived or manifest-derived locks would race; the root lock keeps it blocked.
      const contender = startObservedArtifactTransaction(temporaryRoot, smaller, [
        'smaller module\n',
        'smaller manifest\n',
      ]);
      await waitForPath(contender.attemptedPath, contender.child);
      await waitForProcessTurn();
      expect(existsSync(contender.acquiredPath)).toBe(false);
      writeFileSync(owner.releasePath, 'continue\n');
      const crashed = await collectChild(owner.child);
      expect(crashed.signal).toBe('SIGKILL');
      const published = await collectChild(contender.child);
      expect(published.status).toBe(0);
      expect(readFileSync(smaller[0].path, 'utf8')).toBe('smaller module\n');
      expect(readFileSync(smaller[1].path, 'utf8')).toBe('smaller manifest\n');
      expect(existsSync(extraPath)).toBe(false);
      expect(existsSync(growingManifest)).toBe(false);
      expect(transactionFiles(temporaryRoot)).toEqual([]);
    } finally {
      writeFileSync(owner.releasePath, 'cleanup\n');
      if (owner.child.exitCode === null && owner.child.signalCode === null) owner.child.kill('SIGKILL');
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

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
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
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
      recoverArtifactsWithFileSystem(transactionScope(destinations), destinations, nodeArtifactFileSystem);
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
        publishArtifactsWithFileSystem(
          transactionScope(destinations),
          destinations,
          ['new output\n', 'new manifest\n'],
          filesystem,
        ),
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

      publishArtifactsWithFileSystem(
        transactionScope(destinations),
        destinations,
        ['second output\n', 'second manifest\n'],
        nodeArtifactFileSystem,
      );

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

      expect(() =>
        recoverArtifactsWithFileSystem(transactionScope(destinations), destinations, nodeArtifactFileSystem),
      ).toThrowError(/journal owner does not match the publication lock/u);
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
      expect(() =>
        recoverArtifactsWithFileSystem(transactionScope(destinations), destinations, nodeArtifactFileSystem),
      ).toThrowError(/journal is corrupt/u);
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
      expect(() =>
        recoverArtifactsWithFileSystem(transactionScope(destinations), destinations, nodeArtifactFileSystem),
      ).toThrowError(/journal entry names invalid transaction files/u);
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
    ['write', 9, 'old'],
    ['fsync', 17, 'old'],
    ['fsync', 18, 'old'],
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
          publishArtifactsWithFileSystem(
            transactionScope(destinations),
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
      expect(() =>
        publishArtifactsWithFileSystem(transactionScope(destinations), destinations, newContents, swappingFileSystem),
      ).toThrowError(/artifact destination changed during compilation/u);
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

  test('rejects --manifest beneath an existing non-directory before compilation', () => {
    const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-nondirectory-ancestor-'));
    const outputDirectory = join(temporaryRoot, 'generated');
    const ancestorPath = join(outputDirectory, 'existing-file');
    const ancestorOriginal = Buffer.from('preserve ancestor bytes\n');
    mkdirSync(outputDirectory);
    writeFileSync(ancestorPath, ancestorOriginal);
    const descendantPath = join(ancestorPath, 'generated-artifact');
    try {
      const result = runSourceCompiler(
        temporaryRoot,
        join(temporaryRoot, 'missing-project'),
        join(temporaryRoot, 'missing-project', 'Fixture.lean'),
        outputDirectory,
        descendantPath,
      );

      expect(result.status).not.toBe(0);
      expect(result.stderr).toContain('--manifest has an existing non-directory ancestor');
      expect(readFileSync(ancestorPath)).toEqual(ancestorOriginal);
      expect(existsSync(outputDirectory)).toBe(true);
      expect(existsSync(descendantPath)).toBe(false);
    } finally {
      rmSync(temporaryRoot, { force: true, recursive: true });
    }
  });

  test.each(['symlink-parent', 'hardlink'] as const)(
    'rejects a %s --manifest alias of the explicit Lean source before compilation',
    (aliasKind) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-source-alias-'));
      const projectRoot = join(temporaryRoot, 'project');
      mkdirSync(projectRoot);
      const sourcePath = join(projectRoot, 'Fixture.lean');
      const original = Buffer.from('def preserved : Bool := true\n');
      writeFileSync(sourcePath, original);
      const outputDirectory = join(temporaryRoot, 'generated');
      mkdirSync(outputDirectory);
      let aliasedPath: string;
      if (aliasKind === 'symlink-parent') {
        const aliasRoot = join(outputDirectory, 'alias-project');
        symlinkSync(projectRoot, aliasRoot, 'dir');
        aliasedPath = join(aliasRoot, 'Fixture.lean');
      } else {
        aliasedPath = join(outputDirectory, 'source-alias');
        linkSync(sourcePath, aliasedPath);
      }
      try {
        const result = runSourceCompiler(temporaryRoot, projectRoot, sourcePath, outputDirectory, aliasedPath);

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain(
          aliasKind === 'symlink-parent'
            ? 'generated file path contains a symbolic link'
            : '--manifest must not identify compiler input --source',
        );
        expect(readFileSync(sourcePath)).toEqual(original);
        expect(readFileSync(aliasedPath)).toEqual(original);
        expect(existsSync(outputDirectory)).toBe(true);
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test.each(['direct', 'hardlink'] as const)(
    'rejects a %s-path manifest outside the owned output root before compilation',
    (sourcePathKind) => {
      const temporaryRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-source-descendant-'));
      const projectRoot = join(temporaryRoot, 'project');
      mkdirSync(projectRoot);
      const sourcePath = join(projectRoot, 'Fixture.lean');
      const sourceOriginal = Buffer.from('def preserved : Bool := true\n');
      writeFileSync(sourcePath, sourceOriginal);
      const destinationAncestor = sourcePathKind === 'direct' ? sourcePath : join(temporaryRoot, 'hard-linked-source');
      if (sourcePathKind === 'hardlink') linkSync(sourcePath, destinationAncestor);
      const descendantPath = join(destinationAncestor, 'generated-artifact');
      const outputDirectory = join(temporaryRoot, 'generated');
      try {
        const result = runSourceCompiler(temporaryRoot, projectRoot, sourcePath, outputDirectory, descendantPath);

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain('--manifest must be a file inside --out-dir');
        expect(readFileSync(sourcePath)).toEqual(sourceOriginal);
        expect(readFileSync(destinationAncestor)).toEqual(sourceOriginal);
        expect(existsSync(descendantPath)).toBe(false);
      } finally {
        rmSync(temporaryRoot, { force: true, recursive: true });
      }
    },
  );

  test(
    'rejects --manifest when it aliases a captured compiler input without modifying either artifact',
    () => {
      const fixture = createLeanProjectFixture(
        ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
      );
      const destinationRoot = mkdtempSync(join(tmpdir(), 'tslean-cli-manifest-input-alias-'));
      const toolchainPath = join(fixture.projectRoot, 'lean-toolchain');
      const original = readFileSync(toolchainPath);
      const outputDirectory = join(destinationRoot, 'generated');
      const manifestPath = join(outputDirectory, 'manifest');
      mkdirSync(outputDirectory);
      linkSync(toolchainPath, manifestPath);
      try {
        const result = runSourceCompiler(
          destinationRoot,
          fixture.projectRoot,
          fixture.sourcePath,
          outputDirectory,
          manifestPath,
        );

        expect(result.status).not.toBe(0);
        expect(result.stderr).toContain('--manifest must not identify compiler input target-project:lean-toolchain');
        expect(readFileSync(toolchainPath)).toEqual(original);
        expect(existsSync(outputDirectory)).toBe(true);
      } finally {
        rmSync(destinationRoot, { force: true, recursive: true });
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
        const help = execFileSync(compilerExecutable, ['--help'], { cwd: consumerRoot, encoding: 'utf8' });
        expect(help).toContain('Usage: lean-to-typescript');
        expect(help).toContain('--out-dir <path>');
        expect(help).not.toContain('--output');
        writeFileSync(join(leanRoot, 'lean-toolchain'), 'leanprover/lean4:v4.33.1\n');
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
        const outputDirectory = join(consumerRoot, 'generated');
        const generatedPath = join(outputDirectory, 'Consumer.ts');
        const manifestPath = join(outputDirectory, 'tslean.manifest.json');
        const compilerArguments = [
          '--project-root',
          leanRoot,
          '--module',
          'Consumer',
          '--source',
          sourcePath,
          '--declaration',
          'Consumer.decide',
          '--out-dir',
          outputDirectory,
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
        const strayPath = join(outputDirectory, 'Stray.ts');
        writeFileSync(strayPath, 'export const stray = true;\n');
        const stray = spawnSync(compilerExecutable, [...compilerArguments, '--check'], { encoding: 'utf8' });
        expect(stray.status).not.toBe(0);
        expect(stray.stderr).toContain(`generated tree holds an unexpected file: ${strayPath}`);
        rmSync(strayPath);
        writeFileSync(generatedPath, `${installedCode}\n`);
        const stale = spawnSync(compilerExecutable, [...compilerArguments, '--check'], { encoding: 'utf8' });
        expect(stale.status).not.toBe(0);
        expect(stale.stderr).toContain('generated artifact is stale');
        writeFileSync(
          join(consumerRoot, 'compile.mjs'),
          [
            "import { compileLeanToTypeScript, verifyLeanToTypeScriptPackage } from 'tslean/lean-to-typescript';",
            "import { resolve } from 'node:path';",
            "const root = resolve('lean-project');",
            'const artifact = compileLeanToTypeScript({',
            '  projectRoot: root,',
            "  moduleName: 'Consumer',",
            "  sourcePath: resolve(root, 'source/Consumer.lean'),",
            "  declarations: ['Consumer.decide'],",
            '});',
            'verifyLeanToTypeScriptPackage(artifact);',
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
        if (!isRecord(parsed) || !Array.isArray(parsed['modules']) || !isRecord(parsed['manifest'])) {
          throw new TypeError('packed compiler emitted a malformed package');
        }
        const packedModule = parsed['modules'].filter(isRecord).find((module) => module['path'] === 'Consumer.ts');
        if (packedModule === undefined || typeof packedModule['code'] !== 'string') {
          throw new TypeError('packed compiler emitted no Consumer module');
        }
        const packedSemantic = parsed['manifest']['semantic'];
        if (!isRecord(packedSemantic)) throw new TypeError('packed compiler emitted a malformed semantic identity');
        expect(packedModule['code']).toContain('export function decide(value: boolean): boolean');
        expect(packedSemantic['entryModule']).toBe('Consumer');
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
    PACKED_SUBPATH_EXPORT_TIMEOUT_MS,
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

      const generatedPath = join(repositoryRoot, String(target['source']));
      const adapter = model['runtimeAdapter'];
      if (typeof adapter === 'string') {
        const specifier = relative(dirname(adapter), String(target['source'])).replace(/\.ts$/u, '.js');
        expect(readFileSync(join(repositoryRoot, adapter), 'utf8')).toContain(`from './${specifier}'`);
      }
      // Every input a registered declaration accepts is decoded by an exported boundary that reads
      // the named union, never `unknown`: a consumer whose lint forbids unparsed parameters has to
      // be able to adopt the artifact unmodified, and a model with no adapter has nowhere else to
      // put the boundary. The match is exact, so registering a model whose input is optional stops
      // here rather than passing on the boundary of the type the `Option` wraps: how the artifact
      // presents presence is a decision, and there is no such model yet to decide it against.
      expect(readFileSync(generatedPath, 'utf8')).not.toMatch(/:\s*unknown\b/u);
      expect(undecodedInputs(generatedPath, entrypoint['declarations'] as readonly string[])).toEqual([]);

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
      expect(semantic['entryModule']).toBe(entrypoint['module']);
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

/**
 * Which inputs of a generated module's registered declarations no exported boundary decodes. A
 * boundary is an exported call that reads the module's own data union and returns the input's
 * exact type: a validator, or `fromData` on an exported value. Whatever is left is an input a
 * consumer could only get past by asserting.
 */
function undecodedInputs(source: string, declarations: readonly string[]): readonly string[] {
  const program = ts.createProgram([source], {
    lib: ['lib.es2022.d.ts'],
    module: ts.ModuleKind.NodeNext,
    moduleResolution: ts.ModuleResolutionKind.NodeNext,
    noEmit: true,
    strict: true,
    target: ts.ScriptTarget.ES2022,
  });
  const checker = program.getTypeChecker();
  const file = program.getSourceFile(source);
  if (file === undefined) throw new TypeError(`generated module did not load: ${source}`);
  const moduleSymbol = checker.getSymbolAtLocation(file);
  if (moduleSymbol === undefined) throw new TypeError(`generated module exports nothing: ${source}`);
  const exported = checker.getExportsOfModule(moduleSymbol);
  const decoded = decodableTypes(checker, exported);
  const undecoded: string[] = [];
  for (const declaration of declarations) {
    const name = declaration.split('.').slice(-1).join('');
    const symbol = exported.find((candidate) => candidate.name === name);
    if (symbol === undefined) throw new TypeError(`generated module does not export ${name}`);
    const [signature] = symbolType(checker, symbol).getCallSignatures();
    if (signature === undefined) throw new TypeError(`registered declaration ${name} is not callable`);
    for (const parameter of signature.getParameters()) {
      const type = symbolType(checker, parameter);
      if (decoded.has(type)) continue;
      undecoded.push(`${name}(${parameter.name}: ${checker.typeToString(type)})`);
    }
  }
  return undecoded;
}

/** The exact types the module's exported boundary builds out of its own data union. */
function decodableTypes(checker: ts.TypeChecker, exported: readonly ts.Symbol[]): ReadonlySet<ts.Type> {
  const decoded = new Set<ts.Type>();
  for (const symbol of exported) {
    if (symbol.valueDeclaration === undefined) continue;
    const type = checker.getTypeOfSymbolAtLocation(symbol, symbol.valueDeclaration);
    const signatures = [...type.getCallSignatures()];
    const fromData = type.getProperty('fromData');
    const member = fromData?.declarations?.[0];
    if (fromData !== undefined && member !== undefined) {
      signatures.push(...checker.getTypeOfSymbolAtLocation(fromData, member).getCallSignatures());
    }
    for (const signature of signatures) {
      const [input] = signature.getParameters();
      if (input === undefined) continue;
      if (checker.typeToString(symbolType(checker, input)) !== 'GeneratedData') continue;
      decoded.add(signature.getReturnType());
    }
  }
  return decoded;
}

/** A symbol's type at its own declaration. A mapped-type member has declarations but no value one. */
function symbolType(checker: ts.TypeChecker, symbol: ts.Symbol): ts.Type {
  const declaration = symbol.valueDeclaration ?? symbol.declarations?.[0];
  if (declaration === undefined) throw new TypeError(`symbol ${symbol.name} has no declaration`);
  return checker.getTypeOfSymbolAtLocation(symbol, declaration);
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

/** Stable root scope for direct transaction tests, including the cross-directory cases. */
function transactionScope(destinations: readonly ArtifactDestination[]): ArtifactTransactionScope {
  const paths = destinations.map((destination) => destination.canonicalPath.split('/').slice(0, -1));
  const [first] = paths;
  if (first === undefined) throw new TypeError('transaction test destinations are empty');
  const common = first.filter((segment, index) => paths.every((path) => path[index] === segment));
  const root = common.join('/') || '/';
  return { identity: `test:${root}`, root };
}

function packageDestinations(root: string): readonly [ArtifactDestination, ArtifactDestination, ArtifactDestination] {
  const paths = ['Fixture.ts', 'Fixture.ts.map', 'generated.manifest.json'].map((name) => join(root, name));
  const [modulePath, sourceMapPath, manifestPath] = paths;
  if (modulePath === undefined || sourceMapPath === undefined || manifestPath === undefined) {
    throw new TypeError('package destinations are incomplete');
  }
  return [
    { name: 'Fixture.ts', path: modulePath, canonicalPath: modulePath },
    { name: 'Fixture.ts.map', path: sourceMapPath, canonicalPath: sourceMapPath },
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
  destinations: readonly ArtifactDestination[],
  contents: readonly (string | undefined)[],
  operation: FaultOperation,
  occurrence: number,
): ReturnType<typeof spawnSync> {
  const moduleUrl = pathToFileURL(join(repositoryRoot, 'src', 'lean-to-typescript', 'artifact-transaction.ts')).href;
  const scriptPath = join(root, 'crash-transaction.mjs');
  writeFileSync(
    scriptPath,
    [
      `import { nodeArtifactFileSystem, publishArtifactsWithFileSystem } from ${JSON.stringify(moduleUrl)};`,
      `const destinations = ${JSON.stringify(destinations)};`,
      `const scope = ${JSON.stringify(transactionScope(destinations))};`,
      `const contents = ${JSON.stringify(contents)}.map((value) => value === null ? undefined : value);`,
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
      'publishArtifactsWithFileSystem(scope, destinations, contents, filesystem);',
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
      `import { nodeArtifactFileSystem, recoverArtifactsWithFileSystem } from ${JSON.stringify(moduleUrl)};`,
      `const destinations = ${JSON.stringify(destinations)};`,
      `const scope = ${JSON.stringify(transactionScope(destinations))};`,
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
      'recoverArtifactsWithFileSystem(scope, destinations, filesystem);',
      '',
    ].join('\n'),
  );
  return spawnSync('bun', [scriptPath], { cwd: root, encoding: 'utf8' });
}

function startPausedCrashingArtifactTransaction(
  root: string,
  destinations: readonly ArtifactDestination[],
  contents: readonly (string | undefined)[],
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
      `import { nodeArtifactFileSystem, publishArtifactsWithFileSystem } from ${JSON.stringify(moduleUrl)};`,
      `const destinations = ${JSON.stringify(destinations)};`,
      `const scope = ${JSON.stringify(transactionScope(destinations))};`,
      `const contents = ${JSON.stringify(contents)}.map((value) => value === null ? undefined : value);`,
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
      'publishArtifactsWithFileSystem(scope, destinations, contents, filesystem);',
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
  destinations: readonly ArtifactDestination[],
  contents: readonly (string | undefined)[],
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
      `import { nodeArtifactFileSystem, publishArtifactsWithFileSystem } from ${JSON.stringify(moduleUrl)};`,
      `const destinations = ${JSON.stringify(destinations)};`,
      `const scope = ${JSON.stringify(transactionScope(destinations))};`,
      `const contents = ${JSON.stringify(contents)}.map((value) => value === null ? undefined : value);`,
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
      'publishArtifactsWithFileSystem(scope, destinations, contents, filesystem);',
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

function transactionJournalFilename(destinations: readonly ArtifactDestination[]): string {
  const scope = transactionScope(destinations);
  const digest = createHash('sha256')
    .update(JSON.stringify([scope.identity]))
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
  outputDirectory: string,
  manifestPath: string,
): ReturnType<typeof spawnSync> {
  return spawnSync('bun', compilerArguments(projectRoot, sourcePath, outputDirectory, manifestPath), {
    cwd,
    encoding: 'utf8',
  });
}

function compilerArguments(
  projectRoot: string,
  sourcePath: string,
  outputDirectory: string,
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
    '--out-dir',
    outputDirectory,
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
