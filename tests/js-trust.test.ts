import { execFileSync, spawnSync } from 'node:child_process';
import { mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { describe, expect, it } from 'vitest';
import { leanFilesRecursively } from '../scripts/check-js-axioms.mjs';

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
    const output = execFileSync('lake', ['env', 'lean', 'TSLean/Refinement/AxiomAudit.lean'], {
      cwd: resolve(import.meta.dirname, '../lean'),
      encoding: 'utf8',
      timeout: 25_000,
    });
    expect(output).toContain('TSLean.Refinement.Heap.ExactExtension.trans');
    expect(output).toContain('TSLean.Refinement.EvidenceKind.join_assoc');
  }, 30_000);

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
