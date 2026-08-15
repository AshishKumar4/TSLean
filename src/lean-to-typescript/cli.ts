#!/usr/bin/env node

import {
  existsSync,
  lstatSync,
  mkdirSync,
  readFileSync,
  readlinkSync,
  realpathSync,
  statSync,
  writeFileSync,
} from 'node:fs';
import { basename, dirname, isAbsolute, relative, resolve, sep } from 'node:path';
import { compileLeanToTypeScriptWithInputs } from './compiler.js';

interface CompilerArguments {
  readonly projectRoot: string;
  readonly moduleName: string;
  readonly sourcePath: string;
  readonly declarations: readonly string[];
  readonly outputPath: string;
  readonly manifestPath: string;
  readonly check: boolean;
}

interface NamedPath {
  readonly name: string;
  readonly path: string;
}

interface FilesystemIdentity extends NamedPath {
  readonly canonicalPath: string;
  readonly canonicalAncestorInode: string;
  readonly unresolvedSegments: readonly string[];
  readonly existingDirectory: boolean;
  readonly nonDirectoryAncestor: boolean;
}

type FilesystemRelationship = 'same' | 'ancestor' | 'descendant' | 'disjoint';

function main(arguments_: readonly string[]): void {
  if (arguments_.includes('--help')) {
    process.stdout.write(`${usage()}\n`);
    return;
  }

  const options = parseArguments(arguments_);
  const projectRoot = resolve(options.projectRoot);
  const sourcePath = resolve(options.sourcePath);
  const outputPath = resolve(options.outputPath);
  const manifestPath = resolve(options.manifestPath);
  const destinations = [
    { name: '--output', path: outputPath },
    { name: '--manifest', path: manifestPath },
  ] as const;
  assertArtifactPathsAreIsolated(destinations, [{ name: '--source', path: sourcePath }]);
  const compilation = compileLeanToTypeScriptWithInputs({
    projectRoot,
    moduleName: options.moduleName,
    sourcePath,
    declarations: options.declarations,
  });
  assertArtifactPathsAreIsolated(
    destinations,
    compilation.inputs.map(({ identity, path }) => ({ name: identity, path })),
  );
  const { artifact } = compilation;
  const manifest = `${JSON.stringify(artifact.manifest, null, 2)}\n`;
  if (options.check) {
    assertCurrent(outputPath, artifact.code);
    assertCurrent(manifestPath, manifest);
  } else {
    write(outputPath, artifact.code);
    write(manifestPath, manifest);
  }
}

function assertArtifactPathsAreIsolated(
  destinations: readonly [NamedPath, NamedPath],
  compilerInputs: readonly NamedPath[],
): void {
  const output = filesystemIdentity(destinations[0]);
  const manifest = filesystemIdentity(destinations[1]);
  for (const destination of [output, manifest]) {
    if (destination.existingDirectory) {
      throw new TypeError(`${destination.name} must not identify an existing directory`);
    }
  }
  const destinationRelationship = filesystemRelationship(output, manifest);
  if (destinationRelationship === 'same') {
    throw new TypeError('--output and --manifest must identify distinct filesystem paths');
  }
  if (destinationRelationship === 'ancestor') {
    throw new TypeError('--output must not contain the other artifact destination');
  }
  if (destinationRelationship === 'descendant') {
    throw new TypeError('--manifest must not contain the other artifact destination');
  }
  const inputs = compilerInputs.map(filesystemIdentity);
  for (const destination of [output, manifest]) {
    const aliasedInput = inputs.find((input) => filesystemRelationship(destination, input) !== 'disjoint');
    if (aliasedInput !== undefined) {
      throw new TypeError(
        `${destination.name} must not identify compiler input ${aliasedInput.name} or an ancestor/descendant path`,
      );
    }
    if (destination.nonDirectoryAncestor) {
      throw new TypeError(`${destination.name} has an existing non-directory ancestor`);
    }
  }
}

function filesystemIdentity(namedPath: NamedPath): FilesystemIdentity {
  return { ...namedPath, ...canonicalPath(namedPath.path) };
}

function canonicalPath(
  path: string,
  visitedSymlinks: ReadonlySet<string> = new Set(),
): Pick<
  FilesystemIdentity,
  'canonicalPath' | 'canonicalAncestorInode' | 'unresolvedSegments' | 'existingDirectory' | 'nonDirectoryAncestor'
> {
  let candidate = resolve(path);
  const suffix: string[] = [];
  while (true) {
    let canonicalAncestor: string | undefined;
    try {
      canonicalAncestor = realpathSync(candidate);
    } catch (error: unknown) {
      if (!hasErrorCode(error, 'ENOENT', 'ENOTDIR', 'ELOOP')) throw error;
    }
    if (canonicalAncestor !== undefined) {
      const metadata = statSync(candidate, { bigint: true });
      return {
        canonicalPath: resolve(canonicalAncestor, ...suffix),
        canonicalAncestorInode: `${metadata.dev}:${metadata.ino}`,
        unresolvedSegments: suffix,
        existingDirectory: suffix.length === 0 && metadata.isDirectory(),
        nonDirectoryAncestor: suffix.length > 0 && !metadata.isDirectory(),
      };
    }
    const metadata = lstatIfPresent(candidate);
    if (metadata?.isSymbolicLink()) {
      if (visitedSymlinks.has(candidate)) throw new TypeError(`filesystem path contains a symlink cycle: ${path}`);
      const visited = new Set(visitedSymlinks).add(candidate);
      const target = resolve(dirname(candidate), readlinkSync(candidate), ...suffix);
      return canonicalPath(target, visited);
    }
    const parent = dirname(candidate);
    if (parent === candidate) throw new TypeError(`filesystem path cannot be canonicalized: ${path}`);
    suffix.unshift(basename(candidate));
    candidate = parent;
  }
}

function lstatIfPresent(path: string): ReturnType<typeof lstatSync> | undefined {
  try {
    return lstatSync(path);
  } catch (error: unknown) {
    if (hasErrorCode(error, 'ENOENT', 'ENOTDIR', 'ELOOP')) return undefined;
    throw error;
  }
}

function hasErrorCode(error: unknown, ...codes: readonly string[]): boolean {
  return error instanceof Error && 'code' in error && typeof error.code === 'string' && codes.includes(error.code);
}

function filesystemRelationship(left: FilesystemIdentity, right: FilesystemIdentity): FilesystemRelationship {
  const canonicalRelationship = absolutePathRelationship(left.canonicalPath, right.canonicalPath);
  if (canonicalRelationship !== 'disjoint') return canonicalRelationship;
  if (left.canonicalAncestorInode !== right.canonicalAncestorInode) return 'disjoint';
  return segmentRelationship(left.unresolvedSegments, right.unresolvedSegments);
}

function absolutePathRelationship(left: string, right: string): FilesystemRelationship {
  if (left === right) return 'same';
  if (isStrictDescendant(left, right)) return 'ancestor';
  if (isStrictDescendant(right, left)) return 'descendant';
  return 'disjoint';
}

function isStrictDescendant(ancestor: string, candidate: string): boolean {
  const descendant = relative(ancestor, candidate);
  return descendant.length > 0 && descendant !== '..' && !descendant.startsWith(`..${sep}`) && !isAbsolute(descendant);
}

function segmentRelationship(left: readonly string[], right: readonly string[]): FilesystemRelationship {
  if (left.length === right.length && left.every((segment, index) => segment === right[index])) return 'same';
  if (left.length < right.length && left.every((segment, index) => segment === right[index])) return 'ancestor';
  if (right.length < left.length && right.every((segment, index) => segment === left[index])) return 'descendant';
  return 'disjoint';
}

function parseArguments(arguments_: readonly string[]): CompilerArguments {
  let projectRoot: string | undefined;
  let moduleName: string | undefined;
  let sourcePath: string | undefined;
  let outputPath: string | undefined;
  let manifestPath: string | undefined;
  let check = false;
  const declarations: string[] = [];

  for (let index = 0; index < arguments_.length;) {
    const option = arguments_[index];
    if (option === '--check') {
      if (check) throw new TypeError('--check may be specified only once');
      check = true;
      index += 1;
      continue;
    }
    const value = arguments_[index + 1];
    if (option === undefined || value === undefined) throw new TypeError(`missing value for ${option ?? 'argument'}`);
    switch (option) {
      case '--project-root':
        projectRoot = uniqueValue(projectRoot, value, option);
        break;
      case '--module':
        moduleName = uniqueValue(moduleName, value, option);
        break;
      case '--source':
        sourcePath = uniqueValue(sourcePath, value, option);
        break;
      case '--declaration':
        declarations.push(value);
        break;
      case '--output':
        outputPath = uniqueValue(outputPath, value, option);
        break;
      case '--manifest':
        manifestPath = uniqueValue(manifestPath, value, option);
        break;
      default:
        throw new TypeError(`unknown option ${option}`);
    }
    index += 2;
  }

  if (declarations.length === 0) throw new TypeError('at least one --declaration is required');
  return {
    projectRoot: requiredValue(projectRoot, '--project-root'),
    moduleName: requiredValue(moduleName, '--module'),
    sourcePath: requiredValue(sourcePath, '--source'),
    declarations,
    outputPath: requiredValue(outputPath, '--output'),
    manifestPath: requiredValue(manifestPath, '--manifest'),
    check,
  };
}

function uniqueValue(previous: string | undefined, value: string, option: string): string {
  if (previous !== undefined) throw new TypeError(`${option} may be specified only once`);
  return value;
}

function requiredValue(value: string | undefined, option: string): string {
  if (value === undefined) throw new TypeError(`${option} is required`);
  return value;
}

function write(absolutePath: string, contents: string): void {
  mkdirSync(dirname(absolutePath), { recursive: true });
  writeFileSync(absolutePath, contents, 'utf8');
}

function assertCurrent(absolutePath: string, expected: string): void {
  if (!existsSync(absolutePath) || readFileSync(absolutePath, 'utf8') !== expected) {
    throw new TypeError(`generated artifact is stale: ${absolutePath}`);
  }
}

function usage(): string {
  return [
    'Usage: lean-to-typescript --project-root <path> --module <name> --source <path>',
    '  --declaration <name> [--declaration <name> ...] --output <path> --manifest <path> [--check]',
  ].join('\n');
}

try {
  main(process.argv.slice(2));
} catch (error: unknown) {
  process.stderr.write(`${error instanceof Error ? error.message : String(error)}\n`);
  process.exitCode = 1;
}
