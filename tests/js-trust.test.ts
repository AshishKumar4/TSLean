import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { beforeAll, describe, expect, it } from 'vitest';
import { ensureLeanBuildCurrent, leanFilesRecursively } from '../scripts/check-js-axioms.mjs';

const REQUIRED_LEAN_TARGETS = [
  'TSLean.JS.AxiomAuditMeta',
  'TSLean.JS.OrderedProps',
  'TSLean.Refinement',
  'TSLean.Refinement.AxiomAudit',
] as const;

beforeAll(() => ensureLeanBuildCurrent('lake', REQUIRED_LEAN_TARGETS), 120_000);

describe('JS elaborated-environment trust audit', () => {
  it('discovers proof forms and rejects malformed trust records', () => {
    const output = execFileSync('bun', ['scripts/check-js-axioms.mjs', '--self-test'], {
      cwd: resolve(import.meta.dirname, '..'),
      encoding: 'utf8',
    });
    expect(output.trim()).toBe('synthetic environment audit passed');
  }, 20_000);

  it('discovers ordered-property transition theorems', () => {
    const output = execFileSync('lake', ['env', 'lean', '../tests/lean-fixtures/ordered-props-transitions.lean'], {
      cwd: resolve(import.meta.dirname, '../lean'),
      encoding: 'utf8',
    });
    expect(output).toContain('TSLean.JS.OrderedProps.ownKeys_delete');
  });

  it('audits refinement proof declarations', () => {
    // A cold audit elaborates every refinement module and its #eval scale tests before emitting
    // records, and its cost grows with the record count (155 -> 191 across this slice). Measured
    // cold cost is ~16.5s, so 25s left barely 1.5x of headroom; 120s keeps the bound meaningful
    // while surviving a loaded machine and further growth.
    const output = execFileSync('lake', ['env', 'lean', 'TSLean/Refinement/AxiomAudit.lean'], {
      cwd: resolve(import.meta.dirname, '../lean'),
      encoding: 'utf8',
      timeout: 120_000,
    });
    expect(output).toContain('TSLean.Refinement.Heap.ExactExtension.trans');
    expect(output).toContain('TSLean.Refinement.EvidenceKind.join_assoc');
    expect(output).toContain('TSLean.Refinement.String.codec_roundtrip');
    expect(output).toContain('TSLean.Refinement.String.bmp_codeUnit_at');
  }, 150_000);

  it('rejects symlinks during recursive refinement discovery', (context) => {
    const directory = mkdtempSync(join(tmpdir(), 'tslean-refinement-symlink-'));
    try {
      const target = join(directory, 'Target.lean');
      const link = join(directory, 'Linked.lean');
      writeFileSync(target, 'def target := true\n');
      try {
        symlinkSync(target, link);
      } catch (error) {
        if (error instanceof Error && 'code' in error &&
            ['EACCES', 'ENOSYS', 'EPERM'].includes(String(error.code))) {
          context.skip();
          return;
        }
        throw error;
      }
      expect(() => leanFilesRecursively(directory)).toThrow('refinement source tree contains symlink');
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  });

  it('rejects orphaned compiled artifacts whose source module was deleted', () => {
    const repository = resolve(import.meta.dirname, '..');
    const artifact = 'lean/.lake/build/lib/lean/TSLean/Refinement/JsTrustOrphanFixture.olean';
    const runGate = () =>
      spawnSync('bun', ['scripts/check-js-axioms.mjs', '--self-test'], { cwd: repository, encoding: 'utf8' });
    writeFileSync(join(repository, artifact), '');
    try {
      const orphaned = runGate();
      expect(orphaned.status).not.toBe(0);
      expect(orphaned.stderr).toContain('orphaned Lean build artifacts have no source module');
      expect(orphaned.stderr).toContain(artifact);
    } finally {
      rmSync(join(repository, artifact), { force: true });
    }
    expect(runGate().stderr).not.toContain('orphaned Lean build artifacts');
  }, 180_000);

  it('refuses to audit when the Lean build cannot be brought up to date', () => {
    const directory = mkdtempSync(join(tmpdir(), 'tslean-lake-stub-'));
    try {
      const failing = join(directory, 'lake');
      writeFileSync(failing, '#!/bin/sh\necho "type mismatch in Broken.lean"\necho "build failed" >&2\nexit 3\n', {
        mode: 0o755,
      });
      expect(() => ensureLeanBuildCurrent(failing)).toThrow(
        /lake build exited with status 3[\s\S]*build failed[\s\S]*type mismatch in Broken\.lean/,
      );
      expect(() => ensureLeanBuildCurrent(join(directory, 'absent-lake'))).toThrow('cannot run lake build');
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  }, 20_000);

  it('keeps refinement authority constructors inaccessible', () => {
    const constructors = spawnSync(
      'lake',
      ['env', 'lean', '../tests/lean-fixtures/refinement-private-constructors.lean'],
      { cwd: resolve(import.meta.dirname, '../lean'), encoding: 'utf8' },
    );
    expect(constructors.status).not.toBe(0);
    const constructorOutput = `${constructors.stdout}\n${constructors.stderr}`;
    for (const constructor of [
      'Evidence.mk',
      'Assumption.mk',
      'ValidAssumptions.mk',
      'Guard.mk',
      'GuardReceipt.mk',
      'GuardMetadata.mk',
      'EvidenceMetadata.mk',
    ]) {
      expect(constructorOutput).toContain(`Unknown constant \`TSLean.Refinement.${constructor}\``);
    }

    const receipt = spawnSync(
      'lake',
      ['env', 'lean', '../tests/lean-fixtures/refinement-invalid-guard-receipt.lean'],
      { cwd: resolve(import.meta.dirname, '../lean'), encoding: 'utf8' },
    );
    expect(receipt.status).not.toBe(0);
    expect(`${receipt.stdout}\n${receipt.stderr}`).toContain(
      'Constructor for `TSLean.Refinement.GuardReceipt` is marked as private',
    );
  });
});
