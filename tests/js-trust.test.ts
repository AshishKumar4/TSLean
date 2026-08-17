import { execFileSync, spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { afterAll, beforeAll, describe, expect, it } from 'vitest';
import {
  checkModuleConstants,
  checkSources,
  emittedImportClosure,
  ensureLeanBuildCurrent,
  leanFilesRecursively,
} from '../scripts/check-js-axioms.mjs';
import { STATIC_LEAN_IMPORTS } from '../src/codegen/lower.js';
import { DO_LEAN_IMPORTS, WORKERS_LEAN_IMPORTS } from '../src/do-model/ambient.js';

const REPOSITORY = resolve(import.meta.dirname, '..');
const LEAN = join(REPOSITORY, 'lean');

/**
 * The files these tests plant inside `lean/` so the gate has something to reject.
 *
 * The gate refuses a source module with no artifact and an artifact with no source module, so one of
 * these left behind fails every later run of it — including runs that have nothing to do with this
 * file — and a Ctrl-C between the write and its `finally` is enough to leave one. Swept around the
 * suite so an interrupted run costs nothing but the interruption.
 */
const UNBUILT_SOURCE = 'lean/TSLean/Refinement/JsTrustUnbuiltFixture.lean';
const TOKEN_SOURCE = 'lean/TSLean/Refinement/JsTrustTokenFixture.lean';
const ORPHAN_ARTIFACT = 'lean/.lake/build/lib/lean/TSLean/Refinement/JsTrustOrphanFixture.olean';
/** Named so the sweep can delete the whole directory without ever meeting a real source module. */
const NESTED_DIRECTORY_NAME = 'JsTrustNested';
const NESTED_SOURCE = `lean/TSLean/JS/${NESTED_DIRECTORY_NAME}/Fixture.lean`;

function sweepPlantedFixtures(): void {
  for (const planted of [UNBUILT_SOURCE, TOKEN_SOURCE, ORPHAN_ARTIFACT]) {
    rmSync(join(REPOSITORY, planted), { force: true });
  }
  rmSync(dirname(join(REPOSITORY, NESTED_SOURCE)), { recursive: true, force: true });
}

/** The failure `checkSources` reports, or the empty string when it reports none. */
function sourceScanFailure(): string {
  try {
    checkSources();
    return '';
  } catch (error) {
    return error instanceof Error ? error.message : String(error);
  }
}

/**
 * Compile a standalone Lean module into `directory` so an audit can import it from there.
 *
 * The fabricated module never enters `lean/`: `checkModuleConstants` puts `directory` on the module
 * search path, so a test can hand the audit a taint of its own making and leave the repository
 * untouched.
 */
function compileModule(directory: string, module: string, source: string): void {
  const file = join(directory, `${module}.lean`);
  writeFileSync(file, source);
  execFileSync('lake', ['env', 'lean', '-R', directory, '-o', join(directory, `${module}.olean`), file], {
    cwd: LEAN,
    encoding: 'utf8',
    timeout: 120_000,
  });
}

describe('JS elaborated-environment trust audit', () => {
  beforeAll(sweepPlantedFixtures);
  afterAll(sweepPlantedFixtures);

  it('discovers proof forms and rejects malformed trust records', () => {
    // ~1s against a warm `.lake`, but every gate invocation begins by bringing the Lean build up to
    // date, and a cold or invalidated build is minutes of elaboration this bound must survive.
    const output = execFileSync('bun', ['scripts/check-js-axioms.mjs', '--self-test'], {
      cwd: resolve(import.meta.dirname, '..'),
      encoding: 'utf8',
      timeout: 600_000,
    });
    expect(output.trim()).toBe('synthetic environment audit passed');
  }, 620_000);

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
    const runGate = () =>
      spawnSync('bun', ['scripts/check-js-axioms.mjs', '--self-test'], { cwd: REPOSITORY, encoding: 'utf8' });
    writeFileSync(join(REPOSITORY, ORPHAN_ARTIFACT), '');
    try {
      const orphaned = runGate();
      expect(orphaned.status).not.toBe(0);
      expect(orphaned.stderr).toContain('orphaned Lean build artifacts have no source module');
      expect(orphaned.stderr).toContain(ORPHAN_ARTIFACT);
    } finally {
      rmSync(join(REPOSITORY, ORPHAN_ARTIFACT), { force: true });
    }
    expect(runGate().stderr).not.toContain('orphaned Lean build artifacts');
  }, 180_000);

  it('rejects a Lean source module that no build compiled', () => {
    // The converse of the orphan check, and the one that would have caught `Proofs/` and `V2/`:
    // nothing imports the fixture, so `lake build` never elaborates it and it has no artifact.
    const runGate = () =>
      spawnSync('bun', ['scripts/check-js-axioms.mjs', '--self-test'], { cwd: REPOSITORY, encoding: 'utf8' });
    writeFileSync(join(REPOSITORY, UNBUILT_SOURCE), 'theorem jsTrustUnbuiltFixture : True := trivial\n');
    try {
      const unbuilt = runGate();
      expect(unbuilt.status).not.toBe(0);
      expect(unbuilt.stderr).toContain('Lean source modules have no compiled artifact');
      expect(unbuilt.stderr).toContain('TSLean.Refinement.JsTrustUnbuiltFixture');
    } finally {
      rmSync(join(REPOSITORY, UNBUILT_SOURCE), { force: true });
    }
    expect(runGate().stderr).not.toContain('have no compiled artifact');
  }, 180_000);

  it('audits every emitted import the compiler declares, measured or not', () => {
    // Measurement alone audited whatever the fixture corpus happened to reach, which left the five
    // Workers modules — `axiom` groups and all — out of a base every Workers artifact imports. The
    // declared sets close that: the lowerer's scan is typed by `STATIC_LEAN_IMPORTS`, so a target it
    // can request is a target the audit covers.
    const declared = [...STATIC_LEAN_IMPORTS, ...DO_LEAN_IMPORTS, ...WORKERS_LEAN_IMPORTS];
    expect(emittedImportClosure()).toEqual(expect.arrayContaining(declared));
    const directory = mkdtempSync(join(tmpdir(), 'tslean-closure-fixture-'));
    try {
      writeFileSync(join(directory, 'pure.ts'), 'export function twice(x: number): number {\n  return x * 2;\n}\n');
      // A pure module emits the unconditional pair and nothing else, so a corpus of just this one
      // measures two modules — and the closure still audits every declared module, which is what
      // keeps a shrinking corpus from shrinking the audited base with it.
      expect(emittedImportClosure(directory)).toEqual([...new Set(declared)].sort());
      // `uuid` is mapped to `TSLean.Stdlib.Uuid`, which no source declares, so the emitted file
      // could never elaborate and the closure refuses to audit around it.
      writeFileSync(
        join(directory, 'ids.ts'),
        "import { v4 } from 'uuid';\n\nexport function id(): string {\n  return v4();\n}\n",
      );
      expect(() => emittedImportClosure(directory)).toThrow(
        'emitted imports name Lean modules with no source: TSLean.Stdlib.Uuid (ids.ts)',
      );
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  }, 120_000);

  it('audits declarations the proof audit cannot see', () => {
    const directory = mkdtempSync(join(tmpdir(), 'tslean-constant-fixture-'));
    try {
      // Not a `Prop`, so `#audit_proofs` skips it however it is proved.
      compileModule(
        directory,
        'JsTrustSorryFixture',
        'structure JsTrustSorryServer where\n  port : Nat\n\ninstance : Inhabited JsTrustSorryServer := ⟨sorry⟩\n',
      );
      expect(() => checkModuleConstants(['JsTrustSorryFixture'], 'JsTrustSorryFixture', directory)).toThrow(
        'instInhabitedJsTrustSorryServer depends on disallowed axiom sorryAx',
      );
      // Private, so `#audit_proofs` skips it however it is proved, and `native_decide` leaves the
      // compiler's evaluation behind as an axiom.
      compileModule(
        directory,
        'JsTrustPrivateFixture',
        'private theorem jsTrustPrivateFixture : (2 : Nat) + 2 = 4 := by native_decide\n',
      );
      expect(() => checkModuleConstants(['JsTrustPrivateFixture'], 'JsTrustPrivateFixture', directory)).toThrow(
        /_private\.JsTrustPrivateFixture\.0\.jsTrustPrivateFixture depends on disallowed axiom .*native_decide/,
      );
      compileModule(directory, 'JsTrustCleanFixture', 'theorem jsTrustCleanFixture : (2 : Nat) + 2 = 4 := rfl\n');
      expect(
        [...checkModuleConstants(['JsTrustCleanFixture'], 'JsTrustCleanFixture', directory).keys()],
      ).toContain('jsTrustCleanFixture');
    } finally {
      rmSync(directory, { recursive: true, force: true });
    }
  }, 180_000);

  it('rejects native_decide in the audited Lean trees', () => {
    // `native_decide` was absent from the forbidden-token scan, and `#audit_proofs` filters private
    // names, so a `private theorem ... := by native_decide` was invisible to both.
    const source = join(REPOSITORY, TOKEN_SOURCE);
    writeFileSync(source, 'theorem jsTrustTokenFixture : (2 : Nat) + 2 = 4 := by native_decide\n');
    try {
      expect(sourceScanFailure()).toContain(
        'JsTrustTokenFixture.lean contains forbidden declaration token: ' +
          'theorem jsTrustTokenFixture : (2 : Nat) + 2 = 4 := by native_decide',
      );
    } finally {
      rmSync(source, { force: true });
    }
    expect(sourceScanFailure()).not.toContain('JsTrustTokenFixture.lean');
  }, 20_000);

  it('scans the JS modules a subdirectory holds', () => {
    // The JS half read one directory level, so a module under `JS/<subdir>/` got no token scrutiny
    // while staying importable by every semantic module — and a `private axiom` there is invisible to
    // the other two checks as well: it is not a `Prop`, so the proof audit skips it, and no emitted
    // file imports it, so the emitted-base audit never loads it.
    const source = join(REPOSITORY, NESTED_SOURCE);
    const declaration = 'private axiom jsTrustNestedFixture : (2 : Nat) + 2 = 5';
    mkdirSync(dirname(source), { recursive: true });
    writeFileSync(source, `${declaration}\n`);
    try {
      expect(sourceScanFailure()).toContain(
        `${NESTED_DIRECTORY_NAME}/Fixture.lean contains forbidden declaration token: ${declaration}`,
      );
    } finally {
      sweepPlantedFixtures();
    }
    expect(sourceScanFailure()).not.toContain(NESTED_DIRECTORY_NAME);
  }, 20_000);

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
