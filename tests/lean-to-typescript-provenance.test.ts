import { execFileSync } from 'node:child_process';
import { existsSync, readdirSync, realpathSync } from 'node:fs';
import { join, resolve, sep } from 'node:path';
import { pathToFileURL } from 'node:url';
import { describe, expect, test } from 'vitest';
import { LEAN_TO_TYPESCRIPT_INPUT_PLANES } from '../src/lean-to-typescript/artifact.js';
import { runtimeInputSnapshots } from '../src/lean-to-typescript/runtime-provenance.js';

const repositoryRoot = realpathSync(resolve(import.meta.dirname, '..'));
const compilerSourceDirectory = join(repositoryRoot, 'src', 'lean-to-typescript');
const builtProvenanceModule = join(repositoryRoot, 'dist', 'lean-to-typescript', 'runtime-provenance.js');
const sourceExtension = '.ts';

/**
 * The semantic plane, read from the same table `compiler.ts` splits on rather than from a repeated
 * list of kinds. `semantic.inputClosureSha256` is the digest of exactly these entries, so these are
 * the ones that may not depend on how the compiler was launched. The environment plane is excluded
 * deliberately: it pins the runtime binary and the TypeScript install, so it cannot converge across
 * runtimes and is not a defect when it does not.
 */
const SEMANTIC_KINDS: Readonly<Record<string, true>> = Object.fromEntries(
  Object.entries(LEAN_TO_TYPESCRIPT_INPUT_PLANES)
    .filter(([, plane]) => plane === 'semantic')
    .map(([kind]) => [kind, true]),
);

interface SnapshotRow {
  readonly kind: string;
  readonly identity: string;
  readonly sha256: string;
  readonly path: string;
}

describe('compiler input provenance', () => {
  test('snapshots the same semantic closure loaded from source and loaded from dist', async () => {
    expect(semanticClosure(await builtSnapshots())).toEqual(semanticClosure(runtimeInputSnapshots));
  });

  test('names every reviewed compiler source file, and nothing else, under src/', async () => {
    const reviewed = readdirSync(compilerSourceDirectory, { withFileTypes: true })
      .filter((entry) => entry.isFile() && entry.name.endsWith(sourceExtension))
      .map((entry) => ({
        identity: `compiler:${entry.name.slice(0, -sourceExtension.length)}`,
        path: join(compilerSourceDirectory, entry.name),
      }))
      .sort((left, right) => (left.identity < right.identity ? -1 : 1));

    expect(reviewed.length).toBeGreaterThan(1);
    for (const snapshots of [runtimeInputSnapshots, await builtSnapshots()]) {
      expect(
        semanticClosure(snapshots)
          .filter((row) => row.path.startsWith(`${compilerSourceDirectory}${sep}`))
          .map((row) => ({ identity: row.identity, path: row.path })),
      ).toEqual(reviewed);
    }
  });
});

function semanticClosure(snapshots: readonly SnapshotRow[]): readonly SnapshotRow[] {
  return snapshots.filter((snapshot) => SEMANTIC_KINDS[snapshot.kind] === true);
}

/**
 * The provenance module as a published package runs it. Loading the built copy in the same process
 * as the source copy is what makes the comparison a test rather than a restatement of the code: the
 * two agree only because both resolve the compiler's source from the package root, and the earlier
 * module — which read its own directory with its own extension — disagreed on every entry.
 *
 * The specifier has to be dynamic. A static import would resolve `dist/**` at author time, so the
 * file would stop type-checking and stop loading on a clean checkout, where `dist/` does not exist
 * until `bun run build` and `verify` runs `lint` before it.
 */
async function builtSnapshots(): Promise<readonly SnapshotRow[]> {
  if (!existsSync(builtProvenanceModule)) {
    execFileSync('bun', ['run', 'build'], { cwd: repositoryRoot, stdio: 'pipe' });
  }
  const loaded: unknown = await import(pathToFileURL(builtProvenanceModule).href);
  if (typeof loaded !== 'object' || loaded === null || !('runtimeInputSnapshots' in loaded)) {
    throw new TypeError('built provenance module exports no runtimeInputSnapshots');
  }
  const snapshots = loaded.runtimeInputSnapshots;
  if (!Array.isArray(snapshots) || snapshots.length === 0 || !snapshots.every(isSnapshotRow)) {
    throw new TypeError('built provenance module exported an unrecognised input snapshot list');
  }
  return snapshots;
}

function isSnapshotRow(value: unknown): value is SnapshotRow {
  if (typeof value !== 'object' || value === null) return false;
  return (
    'kind' in value &&
    typeof value.kind === 'string' &&
    'identity' in value &&
    typeof value.identity === 'string' &&
    'sha256' in value &&
    typeof value.sha256 === 'string' &&
    'path' in value &&
    typeof value.path === 'string'
  );
}
