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

export const runtimeInputSnapshots: readonly RuntimeInputSnapshot[] = capture([
  ...readdirSync(compilerDirectory, { withFileTypes: true })
    .filter((entry) => entry.isFile() && extname(entry.name) === extension)
    .map((entry) => ({
      kind: 'compiler' as const,
      identity: `compiler:${entry.name.slice(0, -extension.length)}`,
      path: realpathSync(join(compilerDirectory, entry.name)),
    })),
  { kind: 'compiler', identity: 'compiler:package', path: realpathSync(join(packageRoot, 'package.json')) },
  { kind: 'compiler', identity: 'compiler:registry', path: registryPath('compiler-registry.json') },
  { kind: 'compiler', identity: 'compiler:bounds:placement-v1', path: registryPath('placement.bounds.json') },
  { kind: 'compiler', identity: 'compiler:runtime', path: realpathSync(process.execPath) },
  { kind: 'typescript', identity: 'typescript:compiler', path: typescriptPath },
  {
    kind: 'typescript',
    identity: 'typescript:package',
    path: realpathSync(join(dirname(typescriptPath), '..', 'package.json')),
  },
  ...['lib.decorators.d.ts', 'lib.decorators.legacy.d.ts', 'lib.es5.d.ts'].map((name) => ({
    kind: 'typescript' as const,
    identity: `typescript:library:${name}`,
    path: realpathSync(join(dirname(typescriptPath), name)),
  })),
]);

export function assertRuntimeInputsUnchanged(): void {
  for (const snapshot of runtimeInputSnapshots) {
    if (!snapshot.contents.equals(readFileSync(snapshot.path))) {
      throw new TypeError(`compiler runtime input changed after it was loaded: ${snapshot.identity}`);
    }
  }
}

function registryPath(name: string): string {
  return realpathSync(join(packageRoot, 'spec', 'lean-to-typescript', name));
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
