import { createHash } from 'node:crypto';
import { readdirSync, readFileSync, realpathSync } from 'node:fs';
import { createRequire } from 'node:module';
import { dirname, extname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import type { LeanToTypeScriptInput } from './artifact.js';

export interface RuntimeInputSnapshot extends LeanToTypeScriptInput {
  readonly path: string;
  readonly contents: Buffer;
}

const compilerDirectory = dirname(fileURLToPath(import.meta.url));
const packageRoot = realpathSync(resolve(compilerDirectory, '..', '..'));
const extension = extname(fileURLToPath(import.meta.url));
const typescriptPath = realpathSync(createRequire(import.meta.url).resolve('typescript'));
const specificationDirectory = realpathSync(join(packageRoot, 'spec', 'lean-to-typescript'));

export const runtimeInputSnapshots: readonly RuntimeInputSnapshot[] = capture([
  ...readdirSync(compilerDirectory, { withFileTypes: true })
    .filter((entry) => entry.isFile() && extname(entry.name) === extension)
    .map((entry) => ({
      kind: 'compiler-source' as const,
      identity: `compiler:${entry.name.slice(0, -extension.length)}`,
      path: realpathSync(join(compilerDirectory, entry.name)),
    })),
  { kind: 'compiler-source', identity: 'compiler:package', path: realpathSync(join(packageRoot, 'package.json')) },
  // Every registered model's specification, so adding one cannot silently escape provenance.
  ...readdirSync(specificationDirectory, { withFileTypes: true })
    .filter((entry) => entry.isFile() && extname(entry.name) === '.json')
    .map((entry) => ({
      kind: 'compiler-source' as const,
      identity: `compiler:spec:${entry.name}`,
      path: realpathSync(join(specificationDirectory, entry.name)),
    })),
  { kind: 'compiler-runtime', identity: 'compiler:runtime', path: realpathSync(process.execPath) },
  { kind: 'compiler-runtime', identity: 'typescript:compiler', path: typescriptPath },
  {
    kind: 'compiler-runtime',
    identity: 'typescript:package',
    path: realpathSync(join(dirname(typescriptPath), '..', 'package.json')),
  },
  // Every ambient library the generated program could be checked against, so the surface it is
  // allowed to assume is pinned rather than sampled.
  ...readdirSync(dirname(typescriptPath), { withFileTypes: true })
    .filter((entry) => entry.isFile() && entry.name.startsWith('lib.') && entry.name.endsWith('.d.ts'))
    .map((entry) => ({
      kind: 'compiler-runtime' as const,
      identity: `typescript:library:${entry.name}`,
      path: realpathSync(join(dirname(typescriptPath), entry.name)),
    })),
]);

export function assertRuntimeInputsUnchanged(): void {
  for (const snapshot of runtimeInputSnapshots) {
    if (!snapshot.contents.equals(readFileSync(snapshot.path))) {
      throw new TypeError(`compiler runtime input changed after it was loaded: ${snapshot.identity}`);
    }
  }
}

function capture(
  inputs: readonly {
    readonly kind: LeanToTypeScriptInput['kind'];
    readonly identity: string;
    readonly path: string;
  }[],
): readonly RuntimeInputSnapshot[] {
  return inputs
    .map((input) => {
      const contents = readFileSync(input.path);
      return { ...input, contents, sha256: sha256(contents) };
    })
    .sort((left, right) => compareCodePoints(left.identity, right.identity));
}

function compareCodePoints(left: string, right: string): number {
  return left < right ? -1 : left > right ? 1 : 0;
}

function sha256(value: Buffer): string {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}
