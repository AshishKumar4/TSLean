// Build gate: the generated Lean must typecheck under the real toolchain.
//
// Every other test in this suite asserts on transpiler output as text, so a
// miscompilation that produces well-formed but ill-typed Lean passes them all.
// This gate transpiles a small representative fixture set and elaborates each
// result with `lake env lean`, against the runtime library in `lean/`.
//
// The set is deliberately small — one Lean elaboration costs ~0.5s, so the full
// fixture corpus would dominate the suite. Fixtures are elaborated one file at
// a time so a failure names the fixture that produced it.
//
// `advanced/anonymous-object.ts` is expected to be RED: anonymous object types
// lower to `AssocMap String TSAny` and the field arithmetic does not typecheck.
// It is listed here on purpose — a green gate that skips the known broken case
// would prove nothing.

import { spawnSync } from 'node:child_process';
import * as fs from 'node:fs';
import * as os from 'node:os';
import * as path from 'node:path';
import { afterAll, beforeAll, describe, expect, it } from 'vitest';
import { ensureLeanBuildCurrent } from '../scripts/check-js-axioms.mjs';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';

const ROOT = process.cwd();
const FIX = path.join(ROOT, 'tests/fixtures');
const LEAN = path.join(ROOT, 'lean');

/** Fixtures the gate elaborates, chosen to cover the core of the language. */
const FIXTURES: readonly string[] = [
  'basic/hello.ts', // functions, primitives, recursion, interpolation
  'basic/interfaces.ts', // structures, struct literals, field access
  'generics/discriminated-unions.ts', // inductives and match
  'generics/branded-types.ts', // type aliases and generics
  'effects/exceptions.ts', // throw / try-catch in a monadic context
  'projects/calculator/types.ts', // enums and unions
  // A carrier with no `Inhabited` instance one struct deep. Elaboration is the only check that
  // catches this class of defect: a wrongly emitted `deriving Inhabited` is well-formed Lean, and
  // the degradation scan reports nothing because the artifact carries no placeholder at all.
  'do-workers/nested-carrier.ts',
];

/**
 * Fixtures whose generated Lean is currently wrong, pinned to the exact
 * diagnostic they produce today.
 *
 * A permanently red gate gets ignored, and a skipped one records nothing, so
 * each defect asserts its own failure instead: the expectation breaks both if
 * the output regresses further and if it is fixed, and fixing it forces
 * promotion into `FIXTURES`. Anonymous object types map to
 * `AssocMap String TSAny` with `TSAny := String`, and no `Coe String Float`
 * exists, so arithmetic on a field cannot elaborate. The honest repair is not a
 * coercion: objects have no refinement or codec in `TSLean.Refinement`, so the
 * flow has to degrade visibly rather than claim a carrier it cannot justify.
 */
const KNOWN_BAD: ReadonlyArray<{ fixture: string; corpusId: string; diagnostic: RegExp }> = [
  {
    fixture: 'advanced/anonymous-object.ts',
    corpusId: 'objects-anonymous-shorthand-default',
    // Lean 4.33 includes "instance of type class" in this diagnostic. The missing HMul instance is
    // the same pinned miscompilation, so this still fails if it changes or becomes green.
    diagnostic: /failed to synthesize instance of type class HMul TSAny TSAny/u,
  },
];

let outDir = '';

function leanPath(fixture: string): string {
  return path.join(outDir, `${fixture.replace(/[/.]/g, '_')}.lean`);
}

/**
 * Elaborate one file and return its errors, each with its indented detail
 * lines folded in. Warnings (`unused variable`, `declaration uses sorry`) are
 * not errors: what a degraded artifact carries is `--strict`'s question.
 */
function elaborate(leanFile: string): string[] {
  const run = spawnSync('lake', ['env', 'lean', leanFile], {
    cwd: LEAN,
    encoding: 'utf8',
    timeout: 120_000,
  });
  if (run.error) throw run.error;

  const lines = `${run.stdout}${run.stderr}`.split('\n');
  const diagnostics: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    if (!/ error(?:\(|:)/.test(lines[i])) continue;
    const detail = [lines[i].replace(`${leanFile}:`, '')];
    while (i + 1 < lines.length && /^\s+\S/.test(lines[i + 1])) detail.push(lines[++i].trim());
    diagnostics.push(detail.join(' '));
  }
  if (run.status !== 0 && diagnostics.length === 0) {
    diagnostics.push(`lean exited with status ${String(run.status)}`);
  }
  return diagnostics;
}

describe('Lean build gate', () => {
  beforeAll(() => {
    // A stale .lake would let the gate elaborate against a library that no
    // longer exists in source.
    ensureLeanBuildCurrent();
    outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'tslean-build-gate-'));
    for (const fixture of [...FIXTURES, ...KNOWN_BAD.map((entry) => entry.fixture)]) {
      const code = generateLean(rewriteModule(parseFile({ fileName: path.join(FIX, fixture) })));
      fs.writeFileSync(leanPath(fixture), code, 'utf8');
    }
  });

  afterAll(() => {
    if (outDir) fs.rmSync(outDir, { recursive: true, force: true });
  });

  for (const fixture of FIXTURES) {
    it(`${fixture} generates Lean that typechecks`, () => {
      expect(elaborate(leanPath(fixture)), `${fixture}: generated Lean does not typecheck`).toEqual([]);
    });
  }

  for (const { fixture, corpusId, diagnostic } of KNOWN_BAD) {
    it(`${fixture} still miscompiles (${corpusId})`, () => {
      const diagnostics = elaborate(leanPath(fixture));
      expect(diagnostics, `${fixture}: expected the recorded defect, got a clean elaboration`).not.toEqual([]);
      expect(
        diagnostics.some((entry) => diagnostic.test(entry)),
        `${fixture}: recorded diagnostic no longer matches; if this is now fixed, move it into FIXTURES. Got: ${diagnostics.join(' | ')}`,
      ).toBe(true);
    });
  }
});
