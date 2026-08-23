import { createHash } from 'node:crypto';
import { chmodSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, extname, join, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import ts from 'typescript';
import { beforeAll, describe, expect, test } from 'vitest';
import {
  compileLeanToTypeScript,
  environmentAttestationDrift,
  generatedModulePath,
  semanticIdentityDigest,
  UnsupportedLeanFragmentError,
  verifyLeanToTypeScriptPackage,
  type LeanToTypeScriptModuleArtifact,
  type LeanToTypeScriptPackage,
  type LeanToTypeScriptRequest,
} from '../src/lean-to-typescript/index.js';
import { generatedPackageDigest } from '../src/lean-to-typescript/manifest.js';
import { createLeanProjectFixture } from './helpers/lean-project-fixture.js';

const repositoryRoot = resolve(import.meta.dirname, '..');
const leanRoot = join(repositoryRoot, 'lean');
const sourcePath = join(leanRoot, 'TSLean', 'Examples', 'Placement.lean');
const generatedRoot = join(repositoryRoot, 'examples', 'lean-to-typescript', 'generated');
const manifestPath = join(repositoryRoot, 'examples', 'lean-to-typescript', 'generated', 'tslean.manifest.json');
const request = {
  projectRoot: leanRoot,
  moduleName: 'TSLean.Examples.Placement',
  sourcePath,
  declarations: ['TSLean.Examples.Placement.choosePlacement'],
} satisfies LeanToTypeScriptRequest;
const enforcementGeneratedRoot = join(repositoryRoot, 'examples', 'agent-core', 'facets', 'generated');
const enforcementManifestPath = join(
  repositoryRoot,
  'examples',
  'agent-core',
  'facets',
  'generated',
  'tslean.manifest.json',
);
const enforcementRequest = {
  projectRoot: leanRoot,
  moduleName: 'AgentCore.Facets.Enforcement',
  sourcePath: join(leanRoot, 'AgentCore', 'Facets', 'Enforcement.lean'),
  declarations: ['AgentCore.Facets.enforcementFloor', 'AgentCore.Facets.claimHonorsEnforcementFloor'],
} satisfies LeanToTypeScriptRequest;
const IMPACT_KINDS = ['observe', 'mutate', 'externalSend', 'execute', 'delegate', 'administer'] as const;
const adversarialSource = [
  'namespace Fixture',
  'inductive Choice where',
  '  | first',
  '  | second',
  'partial def unsupportedPartial (value : Nat) : Nat := unsupportedPartial value',
  'unsafe def unsupportedUnsafe (value : Bool) : Bool := value',
  'opaque unsupportedOpaque (value : Bool) : Bool := value',
  'axiom unsupportedAxiom (value : Bool) : Bool',
  'def unsupportedHigherOrder (predicate : Bool → Bool) (value : Bool) : Bool := predicate value',
  'def unsupportedOptionEquality (left right : Option Bool) : Bool :=',
  '  if left = right then true else false',
  'def hygienicEquationBinder : Choice → Bool',
  '  | .first => true',
  '  | .second => false',
  'def unsupportedNestedOption (value : Option (Option Bool)) : Option (Option Bool) := value',
  'unsafe def implementedByReplacement (value : Bool) : Bool := !value',
  '@[implemented_by implementedByReplacement]',
  'def implementedByDependency (value : Bool) : Bool := value',
  'def throughImplementedBy (value : Bool) : Bool := implementedByDependency value',
  'noncomputable def unsupportedNoncomputable (value : Bool) : Bool := value',
  '@[extern "tslean_test_external"]',
  'def unsupportedExtern (value : Bool) : Bool := value',
  'def csimpSource (value : Bool) : Bool := value',
  'def csimpTarget (value : Bool) : Bool := value',
  'theorem csimpProof : @csimpSource = @csimpTarget := rfl',
  'attribute [csimp] csimpProof',
  'def throughCsimp (value : Bool) : Bool := csimpSource value',
  'structure ProjectionRecord where',
  '  value : Bool',
  'def projectionTarget (record : ProjectionRecord) : Bool := record.value',
  'theorem projectionCsimpProof : @ProjectionRecord.value = @projectionTarget := rfl',
  'attribute [csimp] projectionCsimpProof',
  'def throughProjectionCsimp (record : ProjectionRecord) : Bool := record.value',
  'def externalCsimpTarget (value : Bool) : Bool := value',
  'axiom externalCsimpProof : @Bool.not = @externalCsimpTarget',
  'attribute [csimp] externalCsimpProof',
  'def throughExternalCsimp (value : Bool) : Bool := !value',
  'def unsupportedNestedLet (condition : Bool) : Bool :=',
  '  if condition then (let value := false; value) else true',
  'end Fixture',
  '',
].join('\n');

beforeAll(() => {
  const result = spawnSync('lake', ['build', 'TSLean.Examples.Placement'], {
    cwd: leanRoot,
    encoding: 'utf8',
  });
  if (result.status !== 0) {
    throw new TypeError(`Lean placement oracle prerequisite failed: ${spawnFailure(result)}`);
  }
});

describe('Lean to TypeScript checked-fragment compiler', () => {
  test('emits deterministic ergonomic TypeScript with content-bound provenance', () => {
    const first = compileLeanToTypeScript(request);
    const second = compileLeanToTypeScript(request);
    const code = entryCode(first);

    expect(second).toEqual(first);
    expect(code).toContain('export type Placement = "bundled" | "provider" | "dynamic";');
    expect(code).toContain('export class PlacementSet {');
    expect(code).toContain('export function choosePlacement(');
    expect(first.manifest.schemaVersion).toBe(3);
    expect(first.manifest.semantic.entryModule).toBe('TSLean.Examples.Placement');
    expect(first.manifest.semantic.modules.map((module) => module.path)).toEqual(['TSLean/Examples/Placement.ts']);
    expect(first.manifest.semantic.leanToolchain.identity).toBe('leanprover/lean4:v4.16.0');
    expect(first.manifest.semantic.leanToolchain.leanVersion).toContain('Lean (version 4.16.0');
    expect(first.manifest.semantic.leanToolchain.lakeVersion).toContain('Lake version 5.0.0');
    expect(first.manifest.semantic.semanticIrSha256).toMatch(/^sha256:[0-9a-f]{64}$/u);
    expect(first.manifest.semantic.inputClosureSha256).toMatch(/^sha256:[0-9a-f]{64}$/u);
    expect(first.manifest.semantic.modules.map((module) => module.bodySha256)).toEqual(
      first.modules.map((module) => sha256(generatedBody(module.code))),
    );
    expect(first.manifest.semantic.generatedBodySha256).toBe(
      generatedPackageDigest(
        first.modules.map((module) => ({ path: module.path, bodySha256: sha256(generatedBody(module.code)) })),
      ),
    );
    expect(first.manifest.environment.typescriptVersion).toBe(ts.version);
    expect(first.manifest.environment.runtime).toMatch(/^(?:bun|node):/u);
    expect(first.manifest.environment.platform).toBe(`${process.platform}-${process.arch}`);
    expect(first.manifest.semantic.inputs).toEqual(
      expect.arrayContaining([
        {
          kind: 'lean-source',
          identity: 'source:TSLean.Examples.Placement',
          sha256: sha256(readFileSync(sourcePath)),
        },
        expect.objectContaining({ kind: 'compiler-source', identity: 'compiler:lean-exporter' }),
        expect.objectContaining({ kind: 'lean-project', identity: 'target-project:lean-toolchain' }),
      ]),
    );
    expect(first.manifest.environment.inputs).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ kind: 'lean-module', identity: 'module:TSLean.Examples.Placement' }),
        expect.objectContaining({ kind: 'compiler-runtime', identity: 'typescript:compiler' }),
        expect.objectContaining({ kind: 'lean-toolchain', identity: 'target-toolchain:lean-executable' }),
      ]),
    );
    for (const inputs of [first.manifest.semantic.inputs, first.manifest.environment.inputs]) {
      const identities = inputs.map((input) => input.identity);
      expect(
        identities.every((identity, index) => {
          const previous = identities[index - 1];
          return previous === undefined || previous < identity;
        }),
      ).toBe(true);
      expect(new Set(identities).size).toBe(identities.length);
    }
    expect(() => verifyLeanToTypeScriptPackage(first)).not.toThrow();
    const compilerModules = readdirSync(join(repositoryRoot, 'src', 'lean-to-typescript'), { withFileTypes: true })
      .filter((entry) => entry.isFile() && extname(entry.name) === '.ts')
      .map((entry) => `compiler:${basename(entry.name, '.ts')}`)
      .sort();
    const semanticIdentities = first.manifest.semantic.inputs.map((input) => input.identity);
    expect(semanticIdentities.filter((identity) => compilerModules.includes(identity))).toEqual(compilerModules);
  });

  test('keeps the generating environment out of the artifact bytes', () => {
    const emitted = compileLeanToTypeScript(request);
    const code = entryCode(emitted);
    const header = code.slice(0, code.indexOf(' */'));
    expect(header).not.toContain(emitted.manifest.environment.runtime);
    expect(header).not.toContain(emitted.manifest.environment.typescriptVersion);
    expect(header).not.toContain(emitted.manifest.environment.inputClosureSha256);
    expect(header).toContain(` * Semantic identity: ${semanticIdentityDigest(emitted.manifest.semantic)}`);
    // Re-attesting a different environment leaves the code and the semantic identity intact.
    const reattestedEnvironment = { ...emitted.manifest.environment, runtime: 'node:v0.0.0-attestation-probe' };
    const reattested = {
      modules: emitted.modules,
      manifest: { ...emitted.manifest, environment: reattestedEnvironment },
    };
    expect(() => verifyLeanToTypeScriptPackage(reattested)).not.toThrow();
    expect(environmentAttestationDrift(emitted.manifest.environment, reattestedEnvironment)).toEqual([
      `runtime ${emitted.manifest.environment.runtime} -> node:v0.0.0-attestation-probe`,
    ]);
  });

  test('rejects a manifest whose input is filed under the other identity plane', () => {
    const emitted = compileLeanToTypeScript(request);
    const [semanticInput] = emitted.manifest.semantic.inputs;
    if (semanticInput === undefined) throw new TypeError('semantic input closure is empty');
    const misfiled = {
      modules: emitted.modules,
      manifest: {
        ...emitted.manifest,
        environment: {
          ...emitted.manifest.environment,
          inputs: [semanticInput, ...emitted.manifest.environment.inputs],
        },
      },
    };
    expect(() => verifyLeanToTypeScriptPackage(misfiled)).toThrowError(/input .* belongs to the other identity plane/u);
  });

  test('generates byte-identical artifacts under a different generating runtime', () => {
    const node = compileInChild('C');
    const bun = compileInChild('C', 'bun');
    const nodeArtifact: unknown = JSON.parse(node);
    const bunArtifact: unknown = JSON.parse(bun);
    verifyLeanToTypeScriptPackage(nodeArtifact);
    verifyLeanToTypeScriptPackage(bunArtifact);
    expect(bunArtifact.modules).toEqual(nodeArtifact.modules);
    expect(semanticIdentityDigest(bunArtifact.manifest.semantic)).toBe(
      semanticIdentityDigest(nodeArtifact.manifest.semantic),
    );
    expect(bunArtifact.manifest.environment.runtime).not.toBe(nodeArtifact.manifest.environment.runtime);
    expect(environmentAttestationDrift(nodeArtifact.manifest.environment, bunArtifact.manifest.environment)).toContain(
      `runtime ${nodeArtifact.manifest.environment.runtime} -> ${bunArtifact.manifest.environment.runtime}`,
    );
  });

  test('binds provenance to the imported module source', () => {
    expect(() =>
      compileLeanToTypeScript({
        ...request,
        sourcePath: join(leanRoot, 'TSLean', 'LeanToTypeScript', 'Export.lean'),
      }),
    ).toThrowError(/Lean source path does not define module TSLean\.Examples\.Placement/u);
  });

  test("emits a root declared by an imported module into that module's own generated file", () => {
    const fixture = createLeanProjectFixture('import Policy.Extra\n', 'Policy');
    const dependencyDirectory = join(fixture.sourceRoot, 'Policy');
    mkdirSync(dependencyDirectory, { recursive: true });
    writeFileSync(
      join(dependencyDirectory, 'Extra.lean'),
      ['namespace Policy', 'def fromExtra (value : Bool) : Bool := value', 'end Policy', ''].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Policy',
        sourcePath: fixture.sourcePath,
        declarations: ['Policy.fromExtra'],
      });
      expect(emitted.manifest.semantic.entryModule).toBe('Policy');
      expect(emitted.manifest.semantic.modules.map((module) => [module.path, module.leanModule])).toEqual([
        ['Policy/Extra.ts', 'Policy.Extra'],
      ]);
      expect(moduleCode(emitted, 'Policy/Extra.ts')).toContain('export function fromExtra(value: boolean): boolean');
    } finally {
      fixture.dispose();
    }
  });

  test('rejects a root declared outside the frozen target module closure', () => {
    const fixture = createLeanProjectFixture('import Policy.Extra\n', 'Policy');
    const dependencyDirectory = join(fixture.sourceRoot, 'Policy');
    mkdirSync(dependencyDirectory, { recursive: true });
    writeFileSync(
      join(dependencyDirectory, 'Extra.lean'),
      ['namespace Policy', 'def fromExtra (value : Bool) : Bool := value', 'end Policy', ''].join('\n'),
    );
    try {
      for (const declaration of ['Bool.not', 'Policy.missing']) {
        expect(() =>
          compileLeanToTypeScript({
            projectRoot: fixture.projectRoot,
            moduleName: 'Policy',
            sourcePath: fixture.sourcePath,
            declarations: [declaration],
          }),
        ).toThrowError(
          new RegExp(
            `exported declaration ${declaration.replace('.', '\\.')} is outside the frozen target module closure`,
            'u',
          ),
        );
      }
    } finally {
      fixture.dispose();
    }
  });

  test('allows declaration namespaces to differ from their defining module', () => {
    const fixture = createLeanProjectFixture(
      ['namespace Domain', 'def decide (value : Bool) : Bool := value', 'end Domain', ''].join('\n'),
      'Policy',
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Policy',
        sourcePath: fixture.sourcePath,
        declarations: ['Domain.decide'],
      });
      const code = entryCode(emitted);
      expect(code).toContain('export function decide(value: boolean): boolean');
    } finally {
      fixture.dispose();
    }
  });

  test('accepts lowercase ASCII Lean module names supported by Lake', () => {
    const fixture = createLeanProjectFixture(
      ['namespace policy', 'def decide (value : Bool) : Bool := value', 'end policy', ''].join('\n'),
      'policy',
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'policy',
        sourcePath: fixture.sourcePath,
        declarations: ['policy.decide'],
      });
      const code = entryCode(emitted);
      expect(code).toContain('export function decide(value: boolean): boolean');
    } finally {
      fixture.dispose();
    }
  });

  test('never substitutes a compiler-package module for the same-named target module', () => {
    const moduleName = 'TSLean.Examples.Placement';
    const fixture = createLeanProjectFixture(
      [
        'namespace TSLean.Examples.Placement',
        'def choosePlacement (value : Bool) : Bool := value',
        'end TSLean.Examples.Placement',
        '',
      ].join('\n'),
      moduleName,
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName,
        sourcePath: fixture.sourcePath,
        declarations: ['TSLean.Examples.Placement.choosePlacement'],
      });
      const code = entryCode(emitted);
      expect(code).toContain('export function choosePlacement(value: boolean): boolean');
      const choosePlacement = evaluateGeneratedModuleExports(code)['choosePlacement'];
      expect(typeof choosePlacement).toBe('function');
      if (typeof choosePlacement !== 'function') throw new TypeError('generated choosePlacement is not callable');
      expect(choosePlacement(false)).toBe(false);
      expect(choosePlacement(true)).toBe(true);
      expect(emitted.manifest.semantic.inputs).toContainEqual({
        kind: 'lean-source',
        identity: `source:${moduleName}`,
        sha256: sha256(readFileSync(fixture.sourcePath)),
      });
    } finally {
      fixture.dispose();
    }
  });

  test('rejects a target closure that shadows the semantic exporter', () => {
    const fixture = createLeanProjectFixture(
      [
        'import TSLean.LeanToTypeScript.Export',
        'namespace Fixture',
        'def decide (value : Bool) : Bool := value',
        'end Fixture',
        '',
      ].join('\n'),
    );
    const exporterDirectory = join(fixture.sourceRoot, 'TSLean', 'LeanToTypeScript');
    mkdirSync(exporterDirectory, { recursive: true });
    writeFileSync(
      join(exporterDirectory, 'Export.lean'),
      ['namespace TSLean.LeanToTypeScript', 'def impostor : Bool := true', 'end TSLean.LeanToTypeScript', ''].join(
        '\n',
      ),
    );
    writeFileSync(
      join(fixture.projectRoot, 'lakefile.toml'),
      [
        'name = "lean_to_typescript_fixture"',
        'version = "0.1.0"',
        '',
        '[[lean_lib]]',
        'name = "Fixture"',
        'srcDir = "sources"',
        'roots = ["Fixture", "TSLean.LeanToTypeScript.Export"]',
        '',
      ].join('\n'),
    );
    try {
      expect(() =>
        compileLeanToTypeScript({
          projectRoot: fixture.projectRoot,
          moduleName: 'Fixture',
          sourcePath: fixture.sourcePath,
          declarations: ['Fixture.decide'],
        }),
      ).toThrowError(/Lean module TSLean\.LeanToTypeScript\.Export resolves to multiple artifacts/u);
    } finally {
      fixture.dispose();
    }
  });

  test('generated decision agrees with Lean on the complete finite input domain', () => {
    const emitted = compileLeanToTypeScript(request);
    const code = entryCode(emitted);
    const generated = evaluateGeneratedModule(code);
    const lean = evaluateLeanPlacement();

    expect(generated).toEqual(lean);
    expect(generated).toHaveLength(4_096);
  });

  test('canonicalizes requested declaration order', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'def A (value : Bool) : Bool := value',
        'def a (value : Bool) : Bool := !value',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const base = {
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
      } satisfies Omit<LeanToTypeScriptRequest, 'declarations'>;
      const first = compileLeanToTypeScript({ ...base, declarations: ['Fixture.a', 'Fixture.A'] });
      const second = compileLeanToTypeScript({ ...base, declarations: ['Fixture.A', 'Fixture.a'] });
      expect(first).toEqual(second);
      expect(first.manifest.semantic.declarations).toEqual(['Fixture.A', 'Fixture.a']);
    } finally {
      fixture.dispose();
    }
  });

  test('collects admitted named types nested in structure fields', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'inductive Choice where',
        '  | first',
        '  | second',
        'structure Wrapper where',
        '  choice : Option Choice',
        'def identity (value : Wrapper) : Wrapper := value',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.identity'],
      });
      const code = entryCode(emitted);
      expect(code).toContain('export type Choice = "first" | "second";');
      expect(code).toContain('readonly choice: Choice | undefined;');
      const identity = evaluateGeneratedModuleExports(code)['identity'];
      if (typeof identity !== 'function') throw new TypeError('generated identity is not callable');
      expect(identity({ choice: 'first' })).toEqual({ choice: 'first' });
    } finally {
      fixture.dispose();
    }
  });

  test('hashes the transitive imported source and compiled-module closure', () => {
    const fixture = createLeanProjectFixture(
      [
        'import Fixture.Dependency',
        'namespace Fixture',
        'def root (value : Bool) : Bool := dependency value',
        'end Fixture',
        '',
      ].join('\n'),
    );
    const dependencyDirectory = join(fixture.sourceRoot, 'Fixture');
    mkdirSync(dependencyDirectory);
    const dependencyPath = join(dependencyDirectory, 'Dependency.lean');
    writeFileSync(
      dependencyPath,
      ['namespace Fixture', 'def dependency (value : Bool) : Bool := !value', 'end Fixture', ''].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.root'],
      });
      expect(emitted.manifest.semantic.inputs).toContainEqual({
        kind: 'lean-source',
        identity: 'source:Fixture.Dependency',
        sha256: sha256(readFileSync(dependencyPath)),
      });
      expect(emitted.manifest.environment.inputs).toContainEqual(
        expect.objectContaining({ kind: 'lean-module', identity: 'module:Fixture.Dependency' }),
      );
    } finally {
      fixture.dispose();
    }
  });

  test('executes the captured toolchain instead of a later PATH build wrapper', () => {
    const fixture = createLeanProjectFixture(
      ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
    );
    const wrapperRoot = mkdtempSync(join(tmpdir(), 'tslean-lake-wrapper-'));
    const wrapperPath = join(wrapperRoot, 'lake');
    const invocationLogPath = join(wrapperRoot, 'invocations.log');
    const launcherPath = spawnSync('sh', ['-c', 'command -v lake'], { encoding: 'utf8' }).stdout.trim();
    const originalPath = process.env['PATH'];
    writeFileSync(
      wrapperPath,
      [
        '#!/bin/sh',
        `printf '%s\n' "$*" >> ${shellQuote(invocationLogPath)}`,
        `if [ "$PWD" = ${shellQuote(fixture.projectRoot)} ] && [ "$1" = "-H" ] && [ "$2" = "build" ]; then`,
        `  cp ${shellQuote(fixture.sourcePath)} ${shellQuote(`${fixture.sourcePath}.saved`)}`,
        `  printf '%s\\n' 'namespace Fixture' 'def decide (value : Bool) : Bool := !value' 'end Fixture' > ${shellQuote(fixture.sourcePath)}`,
        `  ${shellQuote(launcherPath)} "$@"`,
        '  status=$?',
        `  mv ${shellQuote(`${fixture.sourcePath}.saved`)} ${shellQuote(fixture.sourcePath)}`,
        '  exit "$status"',
        'fi',
        `exec ${shellQuote(launcherPath)} "$@"`,
        '',
      ].join('\n'),
    );
    chmodSync(wrapperPath, 0o755);
    try {
      process.env['PATH'] = `${wrapperRoot}:${originalPath ?? ''}`;
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.decide'],
      });
      const code = entryCode(emitted);
      const decide = evaluateGeneratedModuleExports(code)['decide'];
      if (typeof decide !== 'function') throw new TypeError('generated decide is not callable');
      expect(decide(false)).toBe(false);
      expect(decide(true)).toBe(true);
      expect(emitted.manifest.environment.inputs).toContainEqual(
        expect.objectContaining({
          kind: 'lean-toolchain',
          identity: 'toolchain-launcher:lake',
          sha256: sha256(readFileSync(wrapperPath)),
        }),
      );
      expect(emitted.manifest.environment.inputs.some((input) => input.identity.startsWith('toolchain-runtime:'))).toBe(
        true,
      );
      const canonicalLake = spawnSync(launcherPath, ['env', 'which', 'lake'], {
        cwd: fixture.projectRoot,
        encoding: 'utf8',
      }).stdout.trim();
      expect(emitted.manifest.environment.inputs).toContainEqual({
        kind: 'lean-toolchain',
        identity: 'target-toolchain:lake-executable',
        sha256: sha256(readFileSync(canonicalLake)),
      });
      expect(emitted.manifest.semantic.inputs).toContainEqual({
        kind: 'lean-source',
        identity: 'source:Fixture',
        sha256: sha256(readFileSync(fixture.sourcePath)),
      });
      expect(readFileSync(invocationLogPath, 'utf8').trim().split('\n')).toEqual(['env which lake', 'env which lake']);
    } finally {
      process.env['PATH'] = originalPath;
      fixture.dispose();
      rmSync(wrapperRoot, { force: true, recursive: true });
    }
  });

  test('rejects a source changed and restored while the immutable staged source is compiled', () => {
    const fixture = createLeanProjectFixture(
      ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
    );
    const wrapperRoot = mkdtempSync(join(tmpdir(), 'tslean-source-mutation-wrapper-'));
    const wrapperPath = join(wrapperRoot, 'lake');
    const launcherPath = spawnSync('sh', ['-c', 'command -v lake'], { encoding: 'utf8' }).stdout.trim();
    const originalPath = process.env['PATH'];
    writeFileSync(
      wrapperPath,
      [
        '#!/bin/sh',
        'if [ "$1" = "env" ] && [ "$2" = "which" ] && [ "$3" = "lake" ]; then',
        '  printf \'%s\\n\' "$0"',
        '  exit 0',
        'fi',
        'case "$PWD:$1:$2" in',
        '  */target:-H:build)',
        `    cp ${shellQuote(fixture.sourcePath)} ${shellQuote(`${fixture.sourcePath}.saved`)}`,
        `    printf '%s\\n' 'namespace Fixture' 'def decide (value : Bool) : Bool := !value' 'end Fixture' > ${shellQuote(fixture.sourcePath)}`,
        `    ${shellQuote(launcherPath)} "$@"`,
        '    status=$?',
        `    mv ${shellQuote(`${fixture.sourcePath}.saved`)} ${shellQuote(fixture.sourcePath)}`,
        '    exit "$status"',
        '    ;;',
        'esac',
        `exec ${shellQuote(launcherPath)} "$@"`,
        '',
      ].join('\n'),
    );
    chmodSync(wrapperPath, 0o755);
    try {
      process.env['PATH'] = `${wrapperRoot}:${originalPath ?? ''}`;
      expect(() =>
        compileLeanToTypeScript({
          projectRoot: fixture.projectRoot,
          moduleName: 'Fixture',
          sourcePath: fixture.sourcePath,
          declarations: ['Fixture.decide'],
        }),
      ).toThrowError(
        /compiler input changed during Lean to TypeScript compilation: target-stage-source:.*Fixture\.lean/u,
      );
      expect(readFileSync(fixture.sourcePath, 'utf8')).toContain(':= value');
    } finally {
      process.env['PATH'] = originalPath;
      fixture.dispose();
      rmSync(wrapperRoot, { force: true, recursive: true });
    }
  });

  test('ignores ambient toolchain overrides when resolving the pinned project toolchain', () => {
    const fixture = createLeanProjectFixture(
      ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
    );
    const originalToolchain = process.env['ELAN_TOOLCHAIN'];
    try {
      process.env['ELAN_TOOLCHAIN'] = 'tslean-deliberately-unavailable-toolchain';
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.decide'],
      });
      expect(emitted.manifest.semantic.leanToolchain.identity).toBe('leanprover/lean4:v4.16.0');
      expect(emitted.manifest.semantic.leanToolchain.leanVersion).toContain('Lean (version 4.16.0');
    } finally {
      if (originalToolchain === undefined) {
        delete process.env['ELAN_TOOLCHAIN'];
      } else {
        process.env['ELAN_TOOLCHAIN'] = originalToolchain;
      }
      fixture.dispose();
    }
  });

  test('compiles a Lean 4.16 Lake DSL project with a transitive source closure', () => {
    const projectRoot = mkdtempSync(join(tmpdir(), 'tslean-lake-dsl-project-'));
    const dependencyDirectory = join(projectRoot, 'Fixture');
    const fixtureSourcePath = join(projectRoot, 'Fixture.lean');
    try {
      mkdirSync(dependencyDirectory);
      writeFileSync(join(projectRoot, 'lean-toolchain'), 'leanprover/lean4:v4.16.0\n');
      writeFileSync(join(projectRoot, 'lake-manifest.json'), '{"version":"1.1.0","name":"fixture","packages":[]}\n');
      writeFileSync(
        join(projectRoot, 'lakefile.lean'),
        [
          'import Lake',
          'open Lake DSL',
          '',
          'package fixture where',
          '',
          'lean_lib Fixture where',
          '  roots := #[`Fixture]',
          '',
        ].join('\n'),
      );
      writeFileSync(
        join(dependencyDirectory, 'Dependency.lean'),
        [
          'namespace Fixture.Dependency',
          'def invert (value : Bool) : Bool := !value',
          'end Fixture.Dependency',
          '',
        ].join('\n'),
      );
      writeFileSync(
        fixtureSourcePath,
        [
          'import Fixture.Dependency',
          'namespace Fixture',
          'def decide (value : Bool) : Bool := Fixture.Dependency.invert value',
          'end Fixture',
          '',
        ].join('\n'),
      );

      const emitted = compileLeanToTypeScript({
        projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixtureSourcePath,
        declarations: ['Fixture.decide'],
      });

      expect(emitted.manifest.semantic.leanToolchain.identity).toBe('leanprover/lean4:v4.16.0');
      expect(emitted.manifest.semantic.modules.map((module) => module.path)).toEqual([
        'Fixture.ts',
        'Fixture/Dependency.ts',
      ]);
      expect(entryCode(emitted)).toContain('export function decide(');
    } finally {
      rmSync(projectRoot, { force: true, recursive: true });
    }
  });

  test('refuses a target that is pinned to a different exact Lean toolchain', () => {
    const fixture = createLeanProjectFixture(
      ['namespace Fixture', 'def decide (value : Bool) : Bool := value', 'end Fixture', ''].join('\n'),
    );
    try {
      writeFileSync(join(fixture.projectRoot, 'lean-toolchain'), 'leanprover/lean4:v4.29.0\n');
      expect(() =>
        compileLeanToTypeScript({
          projectRoot: fixture.projectRoot,
          moduleName: 'Fixture',
          sourcePath: fixture.sourcePath,
          declarations: ['Fixture.decide'],
        }),
      ).toThrow('target and compiler Lean toolchains do not match exactly');
    } finally {
      fixture.dispose();
    }
  });

  test('generates byte-identical artifacts in independent locale-varied processes', () => {
    expect(compileInChild('C')).toBe(compileInChild('tr_TR.UTF-8'));
  });

  test('the exhaustive oracle detects a generated-code semantic mutation', () => {
    const emitted = compileLeanToTypeScript(request);
    const code = entryCode(emitted);
    const mutation = mutateFirstConjunction(code);
    expect(evaluateGeneratedModule(mutation)).not.toEqual(evaluateLeanPlacement());
  });

  test('rejects generated-body, manifest, and provenance-header substitution', () => {
    const emitted = compileLeanToTypeScript(request);
    const code = entryCode(emitted);
    const bodyMutation = code.replace('this.bundled && right.bundled', 'this.bundled || right.bundled');
    if (bodyMutation === code) throw new TypeError('generated body mutation did not apply');
    expect(() => verifyLeanToTypeScriptPackage(withEntryCode(emitted, bodyMutation))).toThrowError(
      /generated module body does not match its manifest: TSLean\/Examples\/Placement\.ts/u,
    );

    const manifestSubstitution = {
      ...emitted.manifest,
      semantic: { ...emitted.manifest.semantic, entryModule: 'Substituted.Module' },
    };
    expect(() =>
      verifyLeanToTypeScriptPackage({ modules: emitted.modules, manifest: manifestSubstitution }),
    ).toThrowError(/generated provenance header does not match its manifest: TSLean\/Examples\/Placement\.ts/u);

    const headerSubstitution = code.replace(
      / \* Semantic identity: sha256:[0-9a-f]{64}/u,
      ` * Semantic identity: ${'sha256:'.padEnd(71, '0')}`,
    );
    if (headerSubstitution === code) throw new TypeError('provenance header mutation did not apply');
    expect(() => verifyLeanToTypeScriptPackage(withEntryCode(emitted, headerSubstitution))).toThrowError(
      /generated provenance header does not match its manifest: TSLean\/Examples\/Placement\.ts/u,
    );
  });

  test('the source compiler and checked-in release artifact have identical semantic output', () => {
    const emitted = compileLeanToTypeScript(request);
    const committed = committedPackage(generatedRoot, manifestPath, emitted);
    expect(() => verifyLeanToTypeScriptPackage(committed)).not.toThrow();
    expect(committed.manifest.semantic.semanticIrSha256).toBe(emitted.manifest.semantic.semanticIrSha256);
    expect(committed.modules.map((module) => generatedBody(module.code))).toEqual(
      emitted.modules.map((module) => generatedBody(module.code)),
    );
  });

  test.each([
    ['Fixture.unsupportedPartial', 'Fixture.unsupportedPartial'],
    ['Fixture.unsupportedUnsafe', 'Fixture.unsupportedUnsafe'],
    ['Fixture.unsupportedOpaque', 'Fixture.unsupportedOpaque'],
    ['Fixture.unsupportedAxiom', 'Fixture.unsupportedAxiom'],
    ['Fixture.unsupportedHigherOrder', 'Fixture.unsupportedHigherOrder'],
    ['Fixture.unsupportedOptionEquality', 'Fixture.unsupportedOptionEquality'],
    ['Fixture.hygienicEquationBinder', 'Fixture.hygienicEquationBinder'],
    ['Fixture.unsupportedNestedOption', 'Fixture.unsupportedNestedOption'],
    ['Fixture.throughImplementedBy', 'Fixture.implementedByDependency'],
    ['Fixture.unsupportedNoncomputable', 'Fixture.unsupportedNoncomputable'],
    ['Fixture.unsupportedExtern', 'Fixture.unsupportedExtern'],
    ['Fixture.throughCsimp', 'Fixture.csimpSource'],
    ['Fixture.throughProjectionCsimp', 'Fixture.ProjectionRecord.value'],
    ['Fixture.throughExternalCsimp', 'Bool.not'],
    ['Fixture.unsupportedNestedLet', 'Fixture.unsupportedNestedLet'],
  ])('rejects unsupported declaration %s with stable attribution', (root, declaration) => {
    expect(unsupportedFixtureError(root)).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
      declaration,
    });
  });

  test.each([
    ['Nat', 'def rejected (value : Nat) : Nat := value', 'Fixture.rejected'],
    // `String`'s own closure carries an `extern` implementation, so the metadata audit refuses it
    // before the type rule is reached; both refusals are fail-closed and attributable.
    ['String', 'def rejected (value : String) : String := value', 'String.mk'],
  ])('rejects unsupported built-in data type %s in the Lean exporter', (_type, declarationSource, declaration) => {
    expect(unsupportedSourceError(declarationSource, 'Fixture.rejected')).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
      declaration,
    });
  });

  test('rejects an empty inductive in the Lean exporter', () => {
    const source = ['inductive Empty where', 'def rejected (_value : Empty) : Bool := true'].join('\n');
    expect(unsupportedSourceError(source, 'Fixture.rejected')).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
      declaration: 'Fixture.Empty',
    });
  });

  test(
    'rejects a enum declared in Prop',
    () => {
      const source = [
        'inductive EnumProp : Prop where',
        '  | value',
        'def rejected (_value : EnumProp) : Bool := true',
      ].join('\n');
      expect(unsupportedSourceError(source, 'Fixture.rejected')).toMatchObject({
        code: 'UNSUPPORTED_LEAN_FRAGMENT',
        declaration: 'Fixture.EnumProp',
      });
    },
    30_000,
  );

  test.each([
    ['structure', 'Prop', ['structure StructProp : Prop where'], 'StructProp'],
    ['enum', 'Type 1', ['inductive EnumType1 : Type 1 where', '  | value'], 'EnumType1'],
    ['structure', 'Type 1', ['structure StructType1 : Type 1 where'], 'StructType1'],
    ['enum', 'Type 2', ['inductive EnumType2 : Type 2 where', '  | value'], 'EnumType2'],
    ['structure', 'Type 2', ['structure StructType2 : Type 2 where'], 'StructType2'],
  ])(
    'rejects a %s declared in %s',
    (_kind, _sort, declarationLines, typeName) => {
      const source = [...declarationLines, `def rejected (_value : ${typeName}) : Bool := true`].join('\n');
      expect(unsupportedSourceError(source, 'Fixture.rejected')).toMatchObject({
        code: 'UNSUPPORTED_LEAN_FRAGMENT',
        declaration: `Fixture.${typeName}`,
      });
    },
    15_000,
  );

  test.each([
    ['reserved declaration', 'def «default» (value : Bool) : Bool := value', 'Fixture.default', 'Fixture.default'],
    [
      'Unicode declaration dependency',
      ['def «café» (value : Bool) : Bool := value', 'def rejected (value : Bool) : Bool := «café» value'].join('\n'),
      'Fixture.rejected',
      'Fixture.«café»',
    ],
    [
      'Unicode structure field',
      [
        'structure UnicodeField where',
        '  «café» : Bool',
        'def rejected (value : UnicodeField) : Bool := value.«café»',
      ].join('\n'),
      'Fixture.rejected',
      'Fixture.UnicodeField',
    ],
    ['Unicode parameter', 'def rejected («café» : Bool) : Bool := «café»', 'Fixture.rejected', 'Fixture.rejected'],
    [
      'Unicode let binder',
      'def rejected (value : Bool) : Bool := let «café» := value; «café»',
      'Fixture.rejected',
      'Fixture.rejected',
    ],
  ])('rejects a TypeScript-unsafe %s in the Lean exporter', (_case, source, root, declaration) => {
    expect(unsupportedSourceError(source, root)).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
      declaration,
    });
  });

  test('rejects colliding TypeScript declaration bindings in the Lean exporter', () => {
    const source = [
      'namespace Left',
      'structure Pair where',
      '  value : Bool',
      'end Left',
      'namespace Right',
      'structure Pair where',
      '  value : Bool',
      'end Right',
      'structure Wrapper where',
      '  left : Left.Pair',
      '  right : Right.Pair',
      'def rejected (value : Wrapper) : Wrapper := value',
    ].join('\n');
    expect(unsupportedSourceError(source, 'Fixture.rejected')).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
      declaration: 'Fixture.Right.Pair',
    });
  });

  test('lowers a behaviour-carrying inductive with payloads to a class hierarchy', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'inductive Lease where',
        '  | unheld',
        '  | held (exclusive : Bool) (expired : Bool)',
        'def Lease.admitsWrite (lease : Lease) (durable : Bool) : Bool :=',
        '  match lease with',
        '  | .unheld => false',
        '  | .held exclusive expired => exclusive && !expired && durable',
        'def decide (lease : Lease) (durable : Bool) : Bool := lease.admitsWrite durable',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.decide'],
      });
      const code = entryCode(emitted);
      expect(code).toContain('export abstract class Lease');
      expect(code).toContain('public static get unheld(): Lease');
      expect(code).toContain('public static held(exclusive: boolean, expired: boolean): Lease');
      expect(code).toContain('public abstract admitsWrite(durable: boolean): boolean;');
      expect(code).toContain('return this.exclusive && !this.expired && durable;');
      // A payload constructor has more than one inhabitant, so reference equality is not Lean
      // equality and `from` cannot be total on the tag; neither is emitted.
      expect(code).not.toContain('public static from(');
      expect(code).toContain('public abstract equals(other: Lease): boolean;');

      const generated = evaluateGeneratedModuleExports(code);
      const lease = requireConstructor(generated, 'Lease');
      const held = requireStatic(lease, 'held');
      const unheld = requireProperty(lease, 'unheld');
      const decide = requireFunction(generated, 'decide');
      expect(decide(unheld, true)).toBe(false);
      expect(decide(held(true, false), true)).toBe(true);
      expect(decide(held(true, true), true)).toBe(false);
      expect(decide(held(true, false), false)).toBe(false);

      const value = held(true, false);
      expect(Object.isFrozen(value)).toBe(true);
      expect(requireMethod(value, 'equals')(held(true, false))).toBe(true);
      expect(requireMethod(value, 'equals')(held(false, false))).toBe(false);
      expect(requireMethod(value, 'equals')(unheld)).toBe(false);
      expect(requireMethod(value, 'toData')()).toEqual({ kind: 'held', exclusive: true, expired: false });
      expect(requireMethod(unheld, 'toData')()).toEqual({ kind: 'unheld' });

      const fromData = requireStatic(lease, 'fromData');
      expect(requireMethod(fromData({ kind: 'held', exclusive: true, expired: false }), 'equals')(value)).toBe(true);
      expect(fromData({ kind: 'unheld' })).toBe(unheld);
      expect(() => fromData({ kind: 'held', exclusive: true })).toThrowError(
        /Lease\.held data fields must be exactly kind, exclusive, expired/u,
      );
      expect(() => fromData({ kind: 'held', exclusive: 'yes', expired: false })).toThrowError(
        /Lease\.held exclusive must be a boolean/u,
      );
      expect(() => fromData({ kind: 'released' })).toThrowError(/Lease data must name a constructor/u);
      expect(() => fromData(null)).toThrowError(/Lease data must be an object/u);
    } finally {
      fixture.dispose();
    }
  });

  test('lowers structural recursion to dispatch on a strictly smaller value', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'inductive Path where',
        '  | leaf',
        '  | step (rest : Path)',
        'def Path.evenDepth (path : Path) : Bool :=',
        '  match path with',
        '  | .leaf => true',
        '  | .step rest => !rest.evenDepth',
        'def decide (path : Path) : Bool := path.evenDepth',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.decide'],
      });
      const code = entryCode(emitted);
      expect(code).toContain('return !this.rest.evenDepth();');
      const generated = evaluateGeneratedModuleExports(code);
      const path = requireConstructor(generated, 'Path');
      const step = requireStatic(path, 'step');
      const decide = requireFunction(generated, 'decide');
      let value: unknown = requireProperty(path, 'leaf');
      for (const expected of [true, false, true, false, true]) {
        expect(decide(value)).toBe(expected);
        value = step(value);
      }
      // The representation of a recursive inductive is recursive too, and its codec round-trips.
      const nested = step(step(requireProperty(path, 'leaf')));
      expect(requireMethod(nested, 'toData')()).toEqual({
        kind: 'step',
        rest: { kind: 'step', rest: { kind: 'leaf' } },
      });
      expect(requireMethod(requireStatic(path, 'fromData')(requireMethod(nested, 'toData')()), 'equals')(nested)).toBe(
        true,
      );
    } finally {
      fixture.dispose();
    }
  });

  test.each([
    [
      'recursion Lean settles by well-founded descent',
      [
        'inductive Path where',
        '  | leaf',
        '  | step (rest : Path)',
        'def Path.size (path : Path) : Bool :=',
        '  match path with',
        '  | .leaf => true',
        '  | .step rest => Path.size rest',
        'termination_by path',
        'def rejected (path : Path) : Bool := path.size',
      ],
    ],
    [
      'mutual recursion',
      [
        'inductive Path where',
        '  | leaf',
        '  | step (rest : Path)',
        'mutual',
        'def Path.even (path : Path) : Bool :=',
        '  match path with',
        '  | .leaf => true',
        '  | .step rest => Path.odd rest',
        'def Path.odd (path : Path) : Bool :=',
        '  match path with',
        '  | .leaf => false',
        '  | .step rest => Path.even rest',
        'end',
        'def rejected (path : Path) : Bool := path.even',
      ],
    ],
  ])('rejects %s', (_case, declarationLines) => {
    expect(unsupportedSourceError(declarationLines.join('\n'), 'Fixture.rejected')).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
    });
  });

  test('lowers a payload inductive with no behaviour to a discriminated union', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'inductive Origin where',
        '  | host',
        '  | callee (trusted : Bool)',
        'def calleeOrigin (trusted : Bool) : Origin := .callee trusted',
        'def hostOrigin : Origin := .host',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.calleeOrigin', 'Fixture.hostOrigin'],
      });
      const code = entryCode(emitted);
      expect(code).toContain('readonly kind: "callee";');
      expect(code).toContain('readonly trusted: boolean;');
      expect(code).not.toContain('class Origin');
      const generated = evaluateGeneratedModuleExports(code);
      expect(requireFunction(generated, 'calleeOrigin')(true)).toEqual({ kind: 'callee', trusted: true });
      expect(requireFunction(generated, 'hostOrigin')()).toEqual({ kind: 'host' });
    } finally {
      fixture.dispose();
    }
  });

  test('lowers a behaviour-carrying record to an immutable class with transition helpers', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'inductive Tier where',
        '  | direct',
        '  | mediated',
        'structure Seam where',
        '  turnOwned : Bool',
        '  ownFilesystem : Bool',
        'def Seam.tier (seam : Seam) : Tier :=',
        '  if seam.turnOwned && seam.ownFilesystem then .direct else .mediated',
        'def Seam.withTurnOwned (seam : Seam) (turnOwned : Bool) : Seam :=',
        '  { seam with turnOwned := turnOwned }',
        'def decide (seam : Seam) : Tier := (seam.withTurnOwned true).tier',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.decide'],
      });
      const code = entryCode(emitted);
      expect(code).toContain('export interface SeamInit');
      expect(code).toContain('export class Seam');
      expect(code).toContain('public constructor(init: SeamInit)');
      expect(code).toContain('Object.freeze(this);');
      expect(code).toContain('public withTurnOwned(turnOwned: boolean): Seam');
      expect(code).toContain('return new Seam({');
      // No behaviour lives on `Tier`, so it stays the string union agent-core codecs read.
      expect(code).toContain('export type Tier = "direct" | "mediated";');

      const generated = evaluateGeneratedModuleExports(code);
      const seam = requireConstructor(generated, 'Seam');
      const original = new seam({ turnOwned: false, ownFilesystem: true });
      expect(Object.isFrozen(original)).toBe(true);
      expect(requireFunction(generated, 'decide')(original)).toBe('direct');
      const moved = requireMethod(original, 'withTurnOwned')(true);
      expect(moved).not.toBe(original);
      expect(requireProperty(original, 'turnOwned')).toBe(false);
      expect(requireProperty(moved, 'turnOwned')).toBe(true);
      expect(requireMethod(moved, 'equals')(new seam({ turnOwned: true, ownFilesystem: true }))).toBe(true);
      expect(requireMethod(moved, 'toData')()).toEqual({ turnOwned: true, ownFilesystem: true });
      const decoded = requireStatic(seam, 'fromData')({ turnOwned: true, ownFilesystem: true });
      expect(requireMethod(decoded, 'equals')(moved)).toBe(true);
      expect(() => requireStatic(seam, 'fromData')({ turnOwned: true })).toThrowError(
        /Seam data fields must be exactly turnOwned, ownFilesystem/u,
      );
    } finally {
      fixture.dispose();
    }
  });

  test.each([
    [
      'a nested constructor pattern',
      [
        'inductive Lease where',
        '  | unheld',
        '  | held (exclusive : Bool)',
        'def Lease.rejected (lease : Lease) : Bool :=',
        '  match lease with',
        '  | .unheld => false',
        '  | .held true => true',
        '  | .held false => false',
        'def rejected (lease : Lease) : Bool := lease.rejected',
      ],
      'Fixture.rejected',
    ],
    [
      'a wildcard alternative',
      [
        'inductive Lease where',
        '  | unheld',
        '  | held (exclusive : Bool)',
        'def Lease.rejected (lease : Lease) : Bool :=',
        '  match lease with',
        '  | .held exclusive => exclusive',
        '  | _ => false',
        'def rejected (lease : Lease) : Bool := lease.rejected',
      ],
      'Fixture.rejected',
    ],
    [
      'a match on two discriminants',
      [
        'inductive Lease where',
        '  | unheld',
        '  | held (exclusive : Bool)',
        'def rejected (left right : Lease) : Bool :=',
        '  match left, right with',
        '  | .unheld, .unheld => true',
        '  | _, _ => false',
      ],
      'Fixture.rejected',
    ],
    [
      'a match binding a discriminant equation',
      [
        'inductive Lease where',
        '  | unheld',
        '  | held (exclusive : Bool)',
        'def Lease.rejected (lease : Lease) : Bool :=',
        '  match h : lease with',
        '  | .unheld => true',
        '  | .held exclusive => exclusive',
        'def rejected (lease : Lease) : Bool := lease.rejected',
      ],
      'Fixture.rejected',
    ],
    [
      'a constructor field that depends on an earlier field',
      [
        'inductive Guard where',
        '  | always',
        '  | proof (flag : Bool) (evidence : flag = true)',
        'def rejected (guard : Guard) : Bool := match guard with | .always => true | .proof flag _ => flag',
      ],
      'Fixture.rejected',
    ],
  ])('rejects %s', (_case, declarationLines, root) => {
    expect(unsupportedSourceError(declarationLines.join('\n'), root)).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
    });
  });

  test('rejects a compiler replacement two hops behind an admitted external constant', () => {
    // `if value = true` decides through `instDecidableEqBool`, whose own definition uses
    // `Bool.decEq`: a replacement there changes what executable Lean runs without appearing as a
    // direct dependency of anything this compiler emits.
    const source = [
      'def boolDecEqTarget (left right : Bool) : Decidable (left = right) := Bool.decEq left right',
      'axiom transitiveExternalCsimpProof : @Bool.decEq = @boolDecEqTarget',
      'attribute [csimp] transitiveExternalCsimpProof',
      'def rejected (value : Bool) : Bool := if value = true then true else false',
    ].join('\n');
    expect(unsupportedSourceError(source, 'Fixture.rejected')).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
      declaration: 'Bool.decEq',
    });
  });

  test('refuses a structural record that carries a value object into data position', () => {
    const source = [
      'structure Seam where',
      '  turnOwned : Bool',
      'def Seam.direct (seam : Seam) : Bool := seam.turnOwned',
      'structure Wrapper where',
      '  seam : Seam',
      'structure Outer where',
      '  wrapper : Wrapper',
      'def Outer.reads (outer : Outer) : Bool := outer.wrapper.seam.direct',
      'def rejected (outer : Outer) : Bool := outer.reads',
    ].join('\n');
    expect(unsupportedSourceError(source, 'Fixture.rejected')).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
      declaration: 'Fixture.Outer',
      diagnostic: expect.stringContaining('carries the value object Fixture.Seam'),
    });
  });

  test('refuses a match on a computed scrutinee outside dot-notation dispatch', () => {
    // A tag union is decided by comparing the scrutinee against each tag, so a scrutinee that
    // computes would be re-evaluated per alternative. It has to be named by a `let` first.
    const source = [
      'inductive Choice where',
      '  | first',
      '  | second',
      'def flip (choice : Choice) : Choice :=',
      '  match choice with',
      '  | .first => .second',
      '  | .second => .first',
      'def rejected (choice : Choice) : Bool :=',
      '  match Fixture.flip choice with',
      '  | .first => true',
      '  | .second => false',
    ].join('\n');
    expect(unsupportedSourceError(source, 'Fixture.rejected')).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
      declaration: 'Fixture.rejected',
      diagnostic: expect.stringContaining('bind the scrutinee with let first'),
    });
  });

  test('generated enforcement floor agrees with Lean on the complete finite input domain', () => {
    const emitted = compileLeanToTypeScript(enforcementRequest);
    const code = entryCode(emitted);
    const generated = evaluateGeneratedModuleExports(code);
    const floor = requireFunction(generated, 'enforcementFloor');
    const honors = requireFunction(generated, 'claimHonorsEnforcementFloor');
    const rows: string[] = [];
    for (const impact of IMPACT_KINDS) {
      for (const turnOwnedSession of [true, false]) {
        for (const sessionFilesystemTarget of [true, false]) {
          rows.push(String(floor(impact, turnOwnedSession, sessionFilesystemTarget)));
        }
      }
    }
    for (const claimed of IMPACT_KINDS) {
      for (const derived of IMPACT_KINDS) {
        for (const sessionFilesystemTarget of [true, false]) {
          rows.push(String(honors(claimed, derived, sessionFilesystemTarget)));
        }
      }
    }
    expect(rows).toHaveLength(96);
    expect(rows).toEqual(evaluateLeanEnforcement());
    // The whole surface is substitutable for the handwritten module: a closed tag vocabulary and
    // free functions over it, so no value object stands between a consumer and the decision.
    expect(code).toContain(
      'export type Impact = "observe" | "mutate" | "externalSend" | "execute" | "delegate" | "administer";',
    );
    expect(code).toContain('export type EnforcementTier = "direct" | "mediated";');
    expect(code).toContain(
      'export function enforcementFloor(impact: Impact, turnOwnedSession: boolean, sessionFilesystemTarget: boolean): EnforcementTier {',
    );
    expect(code).not.toContain('class');
  });

  test('exports one validating decode boundary for every enforcement input', () => {
    const emitted = compileLeanToTypeScript(enforcementRequest);
    const code = entryCode(emitted);
    const generated = evaluateGeneratedModuleExports(code);
    const fromData = requireMethod(generated['Impact'], 'fromData');
    const requireBoolean = requireFunction(generated, 'requireBoolean');
    const floor = requireFunction(generated, 'enforcementFloor');
    // The boundary admits exactly what Lean declares and refuses every other value a JSON
    // document can deliver in an impact's place, including one shaped like a tagged constructor.
    for (const impact of IMPACT_KINDS) expect(fromData(impact)).toBe(impact);
    for (const refused of ['sudo', '', 'Observe', 7, 0, true, null, undefined, {}, ['observe']]) {
      expect(() => fromData(refused)).toThrowError(/^Impact must name a Impact$/u);
    }
    expect(() => fromData({ kind: 'observe' })).toThrowError(/^Impact must name a Impact$/u);
    // A primitive input is validated too, by value rather than by `typeof`, so neither the string
    // `"true"` nor a truthy number reaches a decision.
    for (const admitted of [true, false]) expect(requireBoolean(admitted, 'turnOwnedSession')).toBe(admitted);
    for (const refused of ['true', 'false', 1, 0, '', null, undefined, {}]) {
      expect(() => requireBoolean(refused, 'turnOwnedSession')).toThrowError(/^turnOwnedSession must be a boolean$/u);
    }
    // End to end from undecoded data: nothing between the caller and the decision is asserted.
    expect(floor(fromData('mutate'), requireBoolean(true, 'owned'), requireBoolean(false, 'own'))).toBe('mediated');
    expect(floor(fromData('observe'), requireBoolean(false, 'owned'), requireBoolean(false, 'own'))).toBe('direct');
    // One decoder and one boundary for the one type, and no value object invented to carry them.
    expect([...code.matchAll(/function requireImpact\(/gu)]).toHaveLength(1);
    expect([...code.matchAll(/export const Impact = Object\.freeze\(\{/gu)]).toHaveLength(1);
    expect(code).toContain('export function requireBoolean(value: GeneratedData, name: string): boolean {');
    expect(code).not.toContain('class');
    expect(code).not.toMatch(/:\s*unknown\b/u);
  });

  test('lowers a behaviour-carrying nullary inductive to singletons with a total tag codec', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'inductive Tier where',
        '  | direct',
        '  | mediated',
        'def Tier.escalates (tier : Tier) : Bool :=',
        '  match tier with',
        '  | .direct => true',
        '  | .mediated => false',
        'def decide (tier : Tier) : Bool := tier.escalates',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.decide'],
      });
      const code = entryCode(emitted);
      // A nullary constructor has exactly one inhabitant, so `from` is total on the tag and
      // reference equality is Lean equality; the codec reads its boundary union, never `unknown`.
      expect(code).toContain('public static from(kind: Tier["kind"]): Tier');
      expect(code).toContain('public static fromData(value: GeneratedData): Tier');
      expect(code).not.toMatch(/:\s*unknown\b/u);
      expect(code).not.toContain('typeof');

      const generated = evaluateGeneratedModuleExports(code);
      const tier = requireConstructor(generated, 'Tier');
      const from = requireStatic(tier, 'from');
      const fromData = requireStatic(tier, 'fromData');
      for (const kind of ['direct', 'mediated'] as const) {
        expect(requireProperty(from(kind), 'kind')).toBe(kind);
        expect(requireMethod(fromData(kind), 'toData')()).toBe(kind);
        expect(requireMethod(from(kind), 'equals')(fromData(kind))).toBe(true);
        expect(fromData(kind)).toBe(from(kind));
      }
      expect(requireFunction(generated, 'decide')(from('direct'))).toBe(true);
      expect(requireFunction(generated, 'decide')(from('mediated'))).toBe(false);
      // Every non-tag arrival is refused by the same default, so the decoder stays total without
      // a `typeof` pre-check.
      expect(() => fromData('sudo')).toThrowError(/Tier data must name a constructor/u);
      expect(() => fromData(7)).toThrowError(/Tier data must name a constructor/u);
      expect(() => fromData(null)).toThrowError(/Tier data must name a constructor/u);
    } finally {
      fixture.dispose();
    }
  });

  test('lowers a match on a tag union outside dispatch position to equality conditionals', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'inductive Seam where',
        '  | inSession',
        '  | crossSession',
        '  | external',
        'def admits (seam : Seam) (trusted : Bool) : Bool :=',
        '  match seam with',
        '  | .inSession => true',
        '  | .crossSession => trusted',
        '  | .external => false',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.admits'],
      });
      const code = entryCode(emitted);
      expect(code).toContain('export type Seam = "inSession" | "crossSession" | "external";');
      expect(code).toContain('return seam === "inSession" ? true : seam === "crossSession" ? trusted : false;');
      expect(code).not.toContain('class');
      const admits = requireFunction(evaluateGeneratedModuleExports(code), 'admits');
      expect([
        admits('inSession', false),
        admits('crossSession', true),
        admits('crossSession', false),
        admits('external', true),
      ]).toEqual([true, true, false, false]);
    } finally {
      fixture.dispose();
    }
  });

  test('refuses a match on a payload-carrying union outside dispatch position', () => {
    const source = [
      'inductive Lease where',
      '  | unheld',
      '  | held (exclusive : Bool)',
      'def rejected (lease : Lease) : Bool :=',
      '  match lease with',
      '  | .unheld => false',
      '  | .held exclusive => exclusive',
    ].join('\n');
    expect(unsupportedSourceError(source, 'Fixture.rejected')).toMatchObject({
      code: 'UNSUPPORTED_LEAN_FRAGMENT',
      declaration: 'Fixture.rejected',
      diagnostic: expect.stringContaining('payload-carrying union'),
    });
  });

  test('the checked-in enforcement artifact matches the source compiler', () => {
    const emitted = compileLeanToTypeScript(enforcementRequest);
    const committed = committedPackage(enforcementGeneratedRoot, enforcementManifestPath, emitted);
    expect(() => verifyLeanToTypeScriptPackage(committed)).not.toThrow();
    expect(committed.modules.map((module) => generatedBody(module.code))).toEqual(
      emitted.modules.map((module) => generatedBody(module.code)),
    );
  });

  test('compiles an isolated Lean project without a local TSLean exporter', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'structure PrototypeField where',
        '  __proto__ : Bool',
        'def invert (value : Bool) : Bool := !value',
        'def compileMe (invert : Bool) : PrototypeField :=',
        '  let invert := Fixture.invert invert',
        '  { __proto__ := Fixture.invert invert }',
        'def optional (undefined : Bool) : Option Bool :=',
        '  if undefined then none else some true',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const emitted = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.optional', 'Fixture.compileMe'],
      });
      const code = entryCode(emitted);
      const generated = evaluateGeneratedModuleExports(code);
      const compileMe = generated['compileMe'];
      expect(typeof compileMe).toBe('function');
      if (typeof compileMe !== 'function') throw new TypeError('generated compileMe is not callable');
      const output: unknown = compileMe(true);
      if (typeof output !== 'object' || output === null) throw new TypeError('generated output is not an object');
      expect(Reflect.get(output, '__proto__')).toBe(true);
      expect(Object.hasOwn(output, '__proto__')).toBe(true);
      expect(Object.getPrototypeOf(output)).toBe(Object.prototype);
      const optional = generated['optional'];
      expect(typeof optional).toBe('function');
      if (typeof optional !== 'function') throw new TypeError('generated optional is not callable');
      expect(optional(true)).toBeUndefined();
      expect(optional(false)).toBe(true);
    } finally {
      fixture.dispose();
    }
  });
});

type Callable = (...args: readonly unknown[]) => unknown;

function requireFunction(exports: Record<string, unknown>, name: string): Callable {
  const value = exports[name];
  if (typeof value !== 'function') throw new TypeError(`generated module did not export ${name}`);
  return value as Callable;
}

function requireConstructor(exports: Record<string, unknown>, name: string): new (init: unknown) => object {
  const value = exports[name];
  if (typeof value !== 'function') throw new TypeError(`generated module did not export class ${name}`);
  return value as new (init: unknown) => object;
}

function requireStatic(owner: object, name: string): Callable {
  const value = Reflect.get(owner, name);
  if (typeof value !== 'function') throw new TypeError(`generated class has no static ${name}`);
  return value.bind(owner) as Callable;
}

function requireMethod(owner: unknown, name: string): Callable {
  if (typeof owner !== 'object' || owner === null) throw new TypeError('generated value is not an object');
  const value = Reflect.get(owner, name);
  if (typeof value !== 'function') throw new TypeError(`generated value has no method ${name}`);
  return value.bind(owner) as Callable;
}

function requireProperty(owner: unknown, name: string): unknown {
  if ((typeof owner !== 'object' && typeof owner !== 'function') || owner === null) {
    throw new TypeError('generated value is not an object');
  }
  return Reflect.get(owner, name);
}

function sha256(value: string | Buffer): string {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}

function shellQuote(value: string): string {
  return `'${value.replaceAll("'", `'\\''`)}'`;
}

function unsupportedFixtureError(declaration: string): UnsupportedLeanFragmentError {
  const fixture = createLeanProjectFixture(adversarialSource);
  try {
    compileLeanToTypeScript({
      projectRoot: fixture.projectRoot,
      moduleName: 'Fixture',
      sourcePath: fixture.sourcePath,
      declarations: [declaration],
    });
  } catch (error) {
    if (error instanceof UnsupportedLeanFragmentError) return error;
    throw error;
  } finally {
    fixture.dispose();
  }
  throw new TypeError('unsupported Lean fixture compiled successfully');
}

function unsupportedSourceError(source: string, declaration: string): UnsupportedLeanFragmentError {
  const fixture = createLeanProjectFixture(['namespace Fixture', source, 'end Fixture', ''].join('\n'));
  try {
    compileLeanToTypeScript({
      projectRoot: fixture.projectRoot,
      moduleName: 'Fixture',
      sourcePath: fixture.sourcePath,
      declarations: [declaration],
    });
  } catch (error) {
    if (error instanceof UnsupportedLeanFragmentError) return error;
    throw error;
  } finally {
    fixture.dispose();
  }
  throw new TypeError('unsupported Lean source compiled successfully');
}

function evaluateGeneratedModule(code: string): readonly string[] {
  const generated = evaluateGeneratedModuleExports(code);
  const choosePlacement = generated['choosePlacement'];
  if (typeof choosePlacement !== 'function') {
    throw new TypeError('generated module did not export choosePlacement');
  }
  const decode = generated['PlacementSet'];
  if (typeof decode !== 'function' || !('fromData' in decode) || typeof decode.fromData !== 'function') {
    throw new TypeError('generated module did not export the PlacementSet value object');
  }
  const sets = placementSets().map((set) => decode.fromData(set));
  const outputs: string[] = [];
  for (const manifest of sets) {
    for (const policy of sets) {
      for (const substrate of sets) {
        for (const trust of sets) {
          outputs.push(String(choosePlacement(manifest, policy, substrate, trust)));
        }
      }
    }
  }
  return outputs;
}

function evaluateGeneratedModuleExports(code: string): Record<string, unknown> {
  const javascript = ts.transpileModule(code, {
    compilerOptions: {
      module: ts.ModuleKind.CommonJS,
      target: ts.ScriptTarget.ES2022,
    },
  }).outputText;
  const exports: Record<string, unknown> = {};
  new Function('exports', javascript)(exports);
  return exports;
}

function mutateFirstConjunction(code: string): string {
  const source = ts.createSourceFile('generated.ts', code, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS);
  let mutated = false;
  const transform: ts.TransformerFactory<ts.SourceFile> = (context) => (root) => {
    const visit = (node: ts.Node): ts.VisitResult<ts.Node> => {
      if (
        !mutated &&
        ts.isBinaryExpression(node) &&
        node.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken
      ) {
        mutated = true;
        return ts.factory.updateBinaryExpression(
          node,
          node.left,
          ts.factory.createToken(ts.SyntaxKind.BarBarToken),
          node.right,
        );
      }
      return ts.visitEachChild(node, visit, context);
    };
    const result = ts.visitNode(root, visit);
    if (!ts.isSourceFile(result)) throw new TypeError('mutation transformer did not return a source file');
    return result;
  };
  const transformed = ts.transform(source, [transform]);
  try {
    const result = transformed.transformed[0];
    if (!mutated || result === undefined || !ts.isSourceFile(result)) {
      throw new TypeError('generated module contains no conjunction to mutate');
    }
    return ts.createPrinter({ newLine: ts.NewLineKind.LineFeed }).printFile(result);
  } finally {
    transformed.dispose();
  }
}

function generatedBody(code: string): string {
  const marker = ' */\n';
  const boundary = code.indexOf(marker);
  if (boundary < 0) throw new TypeError('generated module has no provenance header');
  return code.slice(boundary + marker.length);
}

function moduleCode(emitted: LeanToTypeScriptPackage, path: string): string {
  const module = emitted.modules.find((candidate) => candidate.path === path);
  if (module === undefined) throw new TypeError(`generated package has no module ${path}`);
  return module.code;
}

/** The generated module that carries the requested entry Lean module's own declarations. */
function entryCode(emitted: LeanToTypeScriptPackage): string {
  return moduleCode(emitted, generatedModulePath(emitted.manifest.semantic.entryModule));
}

function withEntryCode(emitted: LeanToTypeScriptPackage, code: string): LeanToTypeScriptPackage {
  const path = generatedModulePath(emitted.manifest.semantic.entryModule);
  return {
    ...emitted,
    modules: emitted.modules.map((module) => (module.path === path ? { ...module, code } : module)),
  };
}

/**
 * The committed generated tree, read back from disk under the paths the fresh compilation names.
 * The manifest stays undecoded so verification is what decodes it.
 */
function committedPackage(
  root: string,
  committedManifestPath: string,
  emitted: LeanToTypeScriptPackage,
): { readonly modules: readonly LeanToTypeScriptModuleArtifact[]; readonly manifest: unknown } {
  const manifest: unknown = JSON.parse(readFileSync(committedManifestPath, 'utf8'));
  return {
    modules: emitted.modules.map((module) => ({
      path: module.path,
      code: readFileSync(join(root, module.path), 'utf8'),
      sourceMap:
        module.sourceMap === undefined
          ? undefined
          : { path: module.sourceMap.path, contents: readFileSync(join(root, module.sourceMap.path), 'utf8') },
    })),
    manifest,
  };
}

function placementSets(): readonly {
  readonly bundled: boolean;
  readonly provider: boolean;
  readonly dynamic: boolean;
}[] {
  const sets = [];
  for (let bits = 0; bits < 8; bits += 1) {
    sets.push({
      bundled: (bits & 1) !== 0,
      provider: (bits & 2) !== 0,
      dynamic: (bits & 4) !== 0,
    });
  }
  return sets;
}

function evaluateLeanPlacement(): readonly string[] {
  return leanOracleRows([
    'import TSLean.Examples.Placement',
    'import Lean.Data.Json',
    'open TSLean.Examples.Placement',
    'def sets : List PlacementSet := (List.range 8).map fun bits =>',
    '  { bundled := bits % 2 = 1, provider := bits / 2 % 2 = 1, dynamic := bits / 4 % 2 = 1 }',
    'def outputName : Option Placement → String',
    '  | some .bundled => "bundled"',
    '  | some .provider => "provider"',
    '  | some .dynamic => "dynamic"',
    '  | none => "undefined"',
    'def outputs : List String := sets.flatMap fun manifest =>',
    '  sets.flatMap fun policy => sets.flatMap fun substrate => sets.map fun trust =>',
    '    outputName (choosePlacement manifest policy substrate trust)',
    '#eval IO.println (Lean.Json.arr (outputs.map Lean.Json.str).toArray).compress',
    '',
  ]);
}

/** Runs one `#eval` driver against the real toolchain and reads the row list it prints. */
function leanOracleRows(driverLines: readonly string[]): readonly string[] {
  const directory = mkdtempSync(join(tmpdir(), 'tslean-lean-oracle-'));
  const driver = join(directory, 'Oracle.lean');
  try {
    writeFileSync(driver, driverLines.join('\n'));
    const result = spawnSync('lake', ['env', 'lean', driver], {
      cwd: leanRoot,
      encoding: 'utf8',
      maxBuffer: 4 * 1024 * 1024,
    });
    if (result.status !== 0) throw new TypeError(`Lean oracle failed: ${spawnFailure(result)}`);
    const line = result.stdout.split(/\r?\n/u).find((candidate) => candidate.startsWith('["'));
    if (line === undefined) throw new TypeError('Lean oracle emitted no result');
    const parsed: unknown = JSON.parse(line);
    if (!Array.isArray(parsed) || !parsed.every((value) => typeof value === 'string')) {
      throw new TypeError('Lean oracle emitted a malformed result');
    }
    return parsed;
  } finally {
    rmSync(directory, { force: true, recursive: true });
  }
}

function evaluateLeanEnforcement(): readonly string[] {
  return leanOracleRows([
    'import AgentCore.Facets.Enforcement',
    'import Lean.Data.Json',
    'open AgentCore.Facets',
    'def impacts : List Impact := [.observe, .mutate, .externalSend, .execute, .delegate, .administer]',
    'def tierName : EnforcementTier → String',
    '  | .direct => "direct"',
    '  | .mediated => "mediated"',
    'def floorRows : List String := impacts.flatMap fun impact =>',
    '  [true, false].flatMap fun owned => [true, false].map fun own =>',
    '    tierName (enforcementFloor impact owned own)',
    'def claimRows : List String := impacts.flatMap fun claimed =>',
    '  impacts.flatMap fun derived => [true, false].map fun own =>',
    '    toString (claimHonorsEnforcementFloor claimed derived own)',
    '#eval IO.println (Lean.Json.arr ((floorRows ++ claimRows).map Lean.Json.str).toArray).compress',
    '',
  ]);
}

function spawnFailure(result: ReturnType<typeof spawnSync>): string {
  const details: string[] = [];
  if (result.error !== undefined) details.push(result.error.message);
  if (result.signal !== null) details.push(`signal ${result.signal}`);
  if (typeof result.stdout === 'string' && result.stdout.trim().length > 0) details.push(result.stdout.trim());
  if (typeof result.stderr === 'string' && result.stderr.trim().length > 0) details.push(result.stderr.trim());
  return details.join('\n') || `exit status ${result.status ?? 'unknown'}`;
}

function compileInChild(locale: string, runtime: 'bun' | 'node' = 'node'): string {
  const script = [
    "import { compileLeanToTypeScript } from './src/lean-to-typescript/index.ts';",
    "import { resolve } from 'node:path';",
    'const repository = process.cwd();',
    'const artifact = compileLeanToTypeScript({',
    "  projectRoot: resolve(repository, 'lean'),",
    "  moduleName: 'TSLean.Examples.Placement',",
    "  sourcePath: resolve(repository, 'lean/TSLean/Examples/Placement.lean'),",
    "  declarations: ['TSLean.Examples.Placement.choosePlacement'],",
    '});',
    'process.stdout.write(JSON.stringify(artifact));',
  ].join('\n');
  const invocation =
    runtime === 'bun'
      ? { executable: 'bun', arguments_: ['--eval', script] }
      : { executable: process.execPath, arguments_: ['--import', 'tsx', '--input-type=module', '--eval', script] };
  const result = spawnSync(invocation.executable, invocation.arguments_, {
    cwd: repositoryRoot,
    encoding: 'utf8',
    env: { ...process.env, LC_ALL: locale, LANG: locale },
    maxBuffer: 64 * 1024 * 1024,
  });
  if (result.status !== 0) {
    throw new TypeError(`child compiler failed: ${result.stderr}`);
  }
  return result.stdout;
}
