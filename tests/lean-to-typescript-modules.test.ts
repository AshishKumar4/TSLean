import { spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, relative, resolve, sep } from 'node:path';
import ts from 'typescript';
import { describe, expect, test } from 'vitest';
import {
  compileLeanToTypeScript,
  generatedModulePath,
  LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH,
  UnsupportedLeanFragmentError,
  verifyLeanToTypeScriptPackage,
  type LeanToTypeScriptPackage,
  type LeanToTypeScriptRequest,
} from '../src/lean-to-typescript/index.js';
import { compareGeneratedPaths, relativeModuleSpecifier } from '../src/lean-to-typescript/package-layout.js';
import {
  decideAccess,
  grantedCapability,
} from '../examples/lean-to-typescript/package/generated/TSLean/Examples/Package/Decision.js';
import {
  Capability,
  Grant,
} from '../examples/lean-to-typescript/package/generated/TSLean/Examples/Package/Capability.js';
import { Policy } from '../examples/lean-to-typescript/package/generated/TSLean/Examples/Package/Policy.js';

const repositoryRoot = resolve(import.meta.dirname, '..');
const leanRoot = join(repositoryRoot, 'lean');
const generatedRoot = join(repositoryRoot, 'examples', 'lean-to-typescript', 'package', 'generated');
const manifestPath = join(repositoryRoot, 'examples', 'lean-to-typescript', 'package', 'generated.manifest.json');

const packageRequest = {
  projectRoot: leanRoot,
  moduleName: 'TSLean.Examples.Package.Decision',
  sourcePath: join(leanRoot, 'TSLean', 'Examples', 'Package', 'Decision.lean'),
  declarations: [
    'TSLean.Examples.Package.decideAccess',
    'TSLean.Examples.Package.grantedCapability',
    'TSLean.Examples.Package.Policy.effective',
  ],
  outputDirectory: generatedRoot,
} satisfies LeanToTypeScriptRequest;

const COMPILATION_TIMEOUT_MS = 600_000;

const capabilities = ['read', 'write', 'administer'] as const satisfies readonly Capability[];

describe('Lean package to TypeScript module tree', () => {
  test('maps each Lean module name to one generated file path', () => {
    expect(generatedModulePath('TSLean.Examples.Package.Decision')).toBe('TSLean/Examples/Package/Decision.ts');
    expect(generatedModulePath('Fixture')).toBe('Fixture.ts');
    expect(() => generatedModulePath('Not A Module')).toThrowError(/invalid Lean module name/u);
    expect(() => generatedModulePath('lean/../escape')).toThrowError(/invalid Lean module name/u);
  });

  test('resolves a relative ESM specifier between two generated modules', () => {
    expect(relativeModuleSpecifier('TSLean/Examples/Package/Policy.ts', 'TSLean/Examples/Package/Capability.ts')).toBe(
      './Capability.js',
    );
    expect(relativeModuleSpecifier('TSLean/Examples/Package/Policy.ts', 'tslean-runtime.ts')).toBe(
      '../../../tslean-runtime.js',
    );
    expect(relativeModuleSpecifier('A/B.ts', 'A/C/D.ts')).toBe('./C/D.js');
    expect(relativeModuleSpecifier('A/B/C.ts', 'A/D.ts')).toBe('../D.js');
    expect(relativeModuleSpecifier('A.ts', 'B.ts')).toBe('./B.js');
  });

  test('emits the committed package as one file per Lean module plus one shared runtime', () => {
    expect(generatedFiles()).toEqual([
      'TSLean/Examples/Package/Capability.ts',
      'TSLean/Examples/Package/Capability.ts.map',
      'TSLean/Examples/Package/Decision.ts',
      'TSLean/Examples/Package/Decision.ts.map',
      'TSLean/Examples/Package/Policy.ts',
      'TSLean/Examples/Package/Policy.ts.map',
      'tslean-runtime.ts',
    ]);
    const manifest = committedManifest();
    expect(manifest.semantic.modules.map((module) => [module.path, module.leanModule])).toEqual([
      ['TSLean/Examples/Package/Capability.ts', 'TSLean.Examples.Package.Capability'],
      ['TSLean/Examples/Package/Decision.ts', 'TSLean.Examples.Package.Decision'],
      ['TSLean/Examples/Package/Policy.ts', 'TSLean.Examples.Package.Policy'],
      [LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH, ''],
    ]);
    expect(manifest.semantic.entryModule).toBe('TSLean.Examples.Package.Decision');
  });

  test('states the module graph as deterministic relative imports', () => {
    expect(importBlock('TSLean/Examples/Package/Capability.ts')).toEqual([
      'import { type GeneratedData, dataFields, requireBoolean } from "../../../tslean-runtime.js";',
    ]);
    expect(importBlock('TSLean/Examples/Package/Policy.ts')).toEqual([
      'import { type Capability, Grant, type GrantData, requireCapability } from "./Capability.js";',
      'import { type GeneratedData, dataFields, requireBoolean } from "../../../tslean-runtime.js";',
    ]);
    expect(importBlock('TSLean/Examples/Package/Decision.ts')).toEqual([
      'import { type Capability } from "./Capability.js";',
      'import { type Policy } from "./Policy.js";',
    ]);
    expect(importBlock(LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH)).toEqual([]);
  });

  test('records the import graph in the manifest and keeps it acyclic', () => {
    const manifest = committedManifest();
    const imports = new Map(manifest.semantic.modules.map((module) => [module.path, module.imports]));
    expect(imports.get('TSLean/Examples/Package/Capability.ts')).toEqual(['tslean-runtime.ts']);
    expect(imports.get('TSLean/Examples/Package/Policy.ts')).toEqual([
      'TSLean/Examples/Package/Capability.ts',
      'tslean-runtime.ts',
    ]);
    expect(imports.get('TSLean/Examples/Package/Decision.ts')).toEqual([
      'TSLean/Examples/Package/Capability.ts',
      'TSLean/Examples/Package/Policy.ts',
    ]);
    expect(imports.get(LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH)).toEqual([]);
    // Every recorded import names a module the package actually emits, and nothing imports itself.
    for (const [path, entries] of imports) {
      for (const entry of entries) {
        expect(imports.has(entry)).toBe(true);
        expect(entry).not.toBe(path);
      }
    }
    expect(topologicalOrder(imports)).toHaveLength(imports.size);
  });

  test('binds every generated module to its own Lean module in the provenance header', () => {
    const manifest = committedManifest();
    for (const module of manifest.semantic.modules) {
      const header = readGenerated(module.path).split('\n').slice(0, 17);
      expect(header).toContain(` * Generated module: ${module.path}`);
      expect(header).toContain(` * Package entry module: ${manifest.semantic.entryModule}`);
      expect(header).toContain(` * Generated module body: ${module.bodySha256}`);
      expect(header).toContain(` * Generated package body: ${manifest.semantic.generatedBodySha256}`);
      expect(header).toContain(
        ` * Lean module: ${module.leanModule === '' ? '(generated package runtime)' : module.leanModule}`,
      );
    }
    // One package digest, shared by every module: no file can be refreshed on its own.
    const digests = new Set(
      manifest.semantic.modules.map((module) => {
        const line = readGenerated(module.path)
          .split('\n')
          .find((candidate) => candidate.startsWith(' * Generated package body: '));
        return line;
      }),
    );
    expect(digests.size).toBe(1);
  });

  test('points every generated declaration at the Lean text that declares it', () => {
    const manifest = committedManifest();
    const generated = manifest.semantic.modules.filter((module) => module.leanModule !== '');
    expect(generated.flatMap((module) => module.declarations).length).toBeGreaterThanOrEqual(7);
    for (const module of generated) {
      for (const declaration of module.declarations) {
        const source = readFileSync(join(leanRoot, declaration.span.source), 'utf8').split('\n');
        expect(declaration.span.source).toBe(`${module.leanModule.split('.').join('/')}.lean`);
        expect(declaration.span.endLine).toBeGreaterThanOrEqual(declaration.span.startLine);
        expect(declaration.span.endLine).toBeLessThanOrEqual(source.length);
        const component = declaration.declaration.split('.').slice(-1)[0] ?? '';
        const text = source.slice(declaration.span.startLine - 1, declaration.span.endLine).join('\n');
        expect(text).toContain(component);
        // The recorded line starts the statement that carries the declaration. A dot-notation
        // method is carried by its receiver's class, so its name appears inside that statement
        // rather than on its first line.
        const carried = readGenerated(module.path)
          .split('\n')
          .slice(declaration.line - 1);
        expect(carried.some((line) => line.includes(declaration.emitted))).toBe(true);
      }
    }
  });

  test('decodes every source map back to the span its manifest records', () => {
    const manifest = committedManifest();
    for (const module of manifest.semantic.modules) {
      if (module.leanModule === '') {
        expect(module.sourceMapSha256).toBe('');
        continue;
      }
      const map: unknown = JSON.parse(readGenerated(`${module.path}.map`));
      if (typeof map !== 'object' || map === null) throw new TypeError('source map is not an object');
      const decoded = map as { version: number; sources: string[]; mappings: string; file: string };
      expect(decoded.version).toBe(3);
      expect(resolve(dirname(join(generatedRoot, `${module.path}.map`)), decoded.sources[0] ?? '')).toBe(
        join(leanRoot, `${module.leanModule.split('.').join('/')}.lean`),
      );
      expect(decoded.file).toBe(module.path.split('/').slice(-1)[0]);
      const segments = decodeMappings(decoded.mappings);
      expect(segments.length).toBeGreaterThan(0);
      for (const segment of segments) {
        const declaration = module.declarations.find((candidate) => candidate.line === segment.generatedLine);
        if (declaration === undefined)
          throw new TypeError(`source map names an unmapped line ${segment.generatedLine}`);
        expect(segment.sourceIndex).toBe(0);
        expect(segment.sourceLine + 1).toBe(declaration.span.startLine);
        expect(segment.sourceColumn).toBe(declaration.span.startColumn);
      }
    }
  });

  test('accounts for the whole reachable Lean closure', () => {
    const manifest = committedManifest();
    const closure = manifest.semantic.closure;
    expect(closure.length).toBeGreaterThan(20);
    for (const entry of closure) {
      expect(['emitted', 'erased', 'runtime-boundary']).toContain(entry.role);
      expect(entry.reason === '').toBe(entry.role === 'emitted');
    }
    const emitted = closure.filter((entry) => entry.role === 'emitted').map((entry) => entry.declaration);
    const recorded = manifest.semantic.modules
      .flatMap((module) => module.declarations)
      .map((declaration) => declaration.declaration);
    expect([...emitted].sort()).toEqual([...recorded].sort());
    // Every requested root is emitted, and every emitted declaration is attributed to a module.
    for (const root of manifest.semantic.declarations) expect(emitted).toContain(root);
    for (const entry of closure.filter((candidate) => candidate.role === 'emitted')) {
      expect(entry.module).not.toBe('');
    }
    // Both erasure and the runtime boundary are exercised, so neither role is vacuous here.
    expect(closure.some((entry) => entry.role === 'erased')).toBe(true);
    expect(closure.some((entry) => entry.role === 'runtime-boundary')).toBe(true);
  });

  test('type-checks the committed tree under a stricter configuration than it was emitted with', () => {
    const paths = generatedFiles()
      .filter((path) => path.endsWith('.ts'))
      .map((path) => join(generatedRoot, path));
    const program = ts.createProgram(paths, {
      exactOptionalPropertyTypes: true,
      lib: ['lib.es2022.d.ts'],
      module: ts.ModuleKind.NodeNext,
      moduleResolution: ts.ModuleResolutionKind.NodeNext,
      noEmit: true,
      noImplicitOverride: true,
      noUncheckedIndexedAccess: true,
      noUnusedLocals: true,
      noUnusedParameters: true,
      strict: true,
      target: ts.ScriptTarget.ES2022,
    });
    expect(
      ts
        .getPreEmitDiagnostics(program)
        .map((diagnostic) => ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n')),
    ).toEqual([]);
  });

  /**
   * The compiler records its own loaded files as semantic inputs, so a run from `src/*.ts` and the
   * release run from `dist/*.js` legitimately differ in the semantic-identity and input-closure
   * digests. Everything the Lean sources decide has to match exactly: the module bodies, the
   * source maps, the semantic IR, the module layout, the spans and the closure. Byte equality of
   * the whole file including its header is what `bun run lean-to-typescript:package:check` proves,
   * against the same compiler build that wrote it.
   */
  test(
    'reproduces every committed generated byte the Lean sources decide',
    () => {
      const emitted = compileLeanToTypeScript(packageRequest);
      verifyLeanToTypeScriptPackage(emitted);
      const committed = committedManifest();
      for (const module of emitted.modules) {
        expect(bodyOf(module.code)).toBe(bodyOf(readGenerated(module.path)));
        expect(module.sourceMap?.contents ?? '').toBe(
          module.sourceMap === undefined ? '' : readGenerated(module.sourceMap.path),
        );
      }
      expect(emitted.manifest.semantic.entryModule).toBe(committed.semantic.entryModule);
      expect(emitted.manifest.semantic.declarations).toEqual(committed.semantic.declarations);
      expect(emitted.manifest.semantic.generatedBodySha256).toBe(committed.semantic.generatedBodySha256);
      expect(emitted.manifest.semantic.semanticIrSha256).toBe(committed.semantic.semanticIrSha256);
      expect(emitted.manifest.semantic.closure).toEqual(committed.semantic.closure);
      expect(emitted.manifest.semantic.modules).toEqual(committed.semantic.modules);
    },
    COMPILATION_TIMEOUT_MS,
  );

  test(
    'reaches the same bytes on a second independent compilation',
    () => {
      const first = compileLeanToTypeScript(packageRequest);
      const second = compileLeanToTypeScript(packageRequest);
      expect(moduleBytes(second)).toEqual(moduleBytes(first));
      expect(second.manifest.semantic).toEqual(first.manifest.semantic);
    },
    COMPILATION_TIMEOUT_MS,
  );

  test(
    'agrees with Lean on the complete finite access-decision domain',
    () => {
      const rows = grants().flatMap((granted) =>
        capabilities.flatMap((ceiling) =>
          [true, false].flatMap((frozen) =>
            capabilities.map((requested) => {
              const policy = new Policy({ granted, ceiling, frozen });
              const admitted = grantedCapability(policy, requested);
              return `${decideAccess(policy, requested)}/${admitted ?? 'undefined'}`;
            }),
          ),
        ),
      );
      expect(rows).toHaveLength(144);
      expect(rows).toEqual(evaluateLeanAccess());
    },
    COMPILATION_TIMEOUT_MS,
  );

  test(
    'refuses a dot-notation method whose receiver is declared by another module',
    () => {
      const fixture = createLeanPackageFixture([
        {
          name: 'Fixture.Data',
          source: ['namespace Fixture', '', 'structure Box where', '  flag : Bool', '', 'end Fixture', ''].join('\n'),
        },
        {
          name: 'Fixture.Entry',
          source: [
            'import Fixture.Data',
            '',
            'namespace Fixture',
            '',
            'def Box.flip (box : Box) : Bool := !box.flag',
            '',
            'def read (box : Box) : Bool := box.flip',
            '',
            'end Fixture',
            '',
          ].join('\n'),
        },
      ]);
      try {
        expect(() =>
          compileLeanToTypeScript({
            projectRoot: fixture.projectRoot,
            moduleName: 'Fixture.Entry',
            sourcePath: join(fixture.sourceRoot, 'Fixture', 'Entry.lean'),
            declarations: ['Fixture.read'],
            outputDirectory: join(fixture.projectRoot, 'out'),
          }),
        ).toThrowError(UnsupportedLeanFragmentError);
      } finally {
        fixture.dispose();
      }
    },
    COMPILATION_TIMEOUT_MS,
  );

  test('refuses a module name that cannot become a safe path component', () => {
    // Lean admits these; a URL or a Windows filename does not.
    for (const name of ["Fix'ture", 'Fixture!', 'Fixture?', "A.b'c", 'A.CON', 'A.nul', 'A.com1', 'A.LPT9']) {
      expect(() => generatedModulePath(name)).toThrowError(/path-safe subset|reserved path component/u);
    }
    for (const name of ['../escape', 'A/B', 'A\\B', 'A#b', 'A%2Fb', 'A?b', '.hidden', 'A..B', '']) {
      expect(() => generatedModulePath(name)).toThrowError(/invalid Lean module name|path-safe subset/u);
    }
    // No Lean module may claim the generated runtime path.
    expect(() => generatedModulePath('tslean-runtime')).toThrowError(/invalid Lean module name/u);
    // And the accepted ones stay literal in a specifier: no query, hash, escape or separator.
    for (const name of ['A', 'A.B_1', 'Zoo.aardvark']) {
      const path = generatedModulePath(name);
      expect(path).toMatch(/^[A-Za-z_][A-Za-z0-9_]*(?:\/[A-Za-z_][A-Za-z0-9_]*)*\.ts$/u);
      expect(relativeModuleSpecifier('X/Y.ts', path)).not.toMatch(/[?#%\\]/u);
    }
  });

  test('orders the runtime module by the same path comparator as every other module', () => {
    // 't' > 'T' by code point, so a lowercase Lean module can sort after the runtime module. The
    // comparator has to be locale-independent, or the manifest order would depend on the machine.
    const paths = ['tslean-runtime.ts', 'TSLean/A.ts', 'zoo/b.ts', 'Zoo/b.ts'];
    const sorted = [...paths].sort(compareGeneratedPaths);
    expect(sorted).toEqual(['TSLean/A.ts', 'Zoo/b.ts', 'tslean-runtime.ts', 'zoo/b.ts']);
    for (const locale of ['en-US', 'de-DE', 'tr-TR', 'sv-SE']) {
      expect([...paths].sort((left, right) => compareGeneratedPaths(left, right))).toEqual(sorted);
      expect(locale).toBeTruthy();
    }
    // The committed manifest is in exactly that order, runtime module included.
    const recorded = committedManifest().semantic.modules.map((module) => module.path);
    expect(recorded).toEqual([...recorded].sort(compareGeneratedPaths));
  });

  test('records a source map source that resolves from the map to the real Lean file', () => {
    const manifest = committedManifest();
    for (const module of manifest.semantic.modules) {
      if (module.leanModule === '') continue;
      const map: { sources: string[] } = JSON.parse(readGenerated(`${module.path}.map`));
      const mapDirectory = dirname(join(generatedRoot, `${module.path}.map`));
      const resolved = resolve(mapDirectory, map.sources[0] ?? '');
      expect(existsSync(resolved)).toBe(true);
      expect(resolved).toBe(join(leanRoot, `${module.leanModule.split('.').join('/')}.lean`));
    }
    expect(manifest.semantic.leanProjectPath).toBe(relative(generatedRoot, leanRoot).split(sep).join('/'));
  });

  test(
    'refuses two Lean modules that would emit the same TypeScript name',
    () => {
      const shared = (namespaceName: string) =>
        [
          `namespace ${namespaceName}`,
          '',
          'structure Config where',
          '  flag : Bool',
          '',
          `end ${namespaceName}`,
          '',
        ].join('\n');
      const fixture = createLeanPackageFixture([
        { name: 'Fixture.Left', source: shared('Fixture.Left') },
        { name: 'Fixture.Right', source: shared('Fixture.Right') },
        {
          name: 'Fixture.Entry',
          source: [
            'import Fixture.Left',
            'import Fixture.Right',
            '',
            'namespace Fixture',
            '',
            'def read (left : Fixture.Left.Config) (right : Fixture.Right.Config) : Bool :=',
            '  left.flag && right.flag',
            '',
            'end Fixture',
            '',
          ].join('\n'),
        },
      ]);
      try {
        expect(() =>
          compileLeanToTypeScript({
            projectRoot: fixture.projectRoot,
            moduleName: 'Fixture.Entry',
            sourcePath: join(fixture.sourceRoot, 'Fixture', 'Entry.lean'),
            declarations: ['Fixture.read'],
            outputDirectory: join(fixture.projectRoot, 'out'),
          }),
        ).toThrowError(/Fixture\.Left\.Config.*Fixture\.Right\.Config.*both emit Config/u);
      } finally {
        fixture.dispose();
      }
    },
    COMPILATION_TIMEOUT_MS,
  );

  test(
    'emits a two-module package whose entry module imports the other',
    () => {
      const fixture = createLeanPackageFixture([
        {
          name: 'Fixture.Data',
          source: [
            'namespace Fixture',
            '',
            'inductive Colour where',
            '  | red',
            '  | blue',
            '  deriving DecidableEq, Repr',
            '',
            'end Fixture',
            '',
          ].join('\n'),
        },
        {
          name: 'Fixture.Entry',
          source: [
            'import Fixture.Data',
            '',
            'namespace Fixture',
            '',
            'def isRed (colour : Colour) : Bool :=',
            '  match colour with',
            '  | .red => true',
            '  | .blue => false',
            '',
            'end Fixture',
            '',
          ].join('\n'),
        },
      ]);
      try {
        const emitted = compileLeanToTypeScript({
          projectRoot: fixture.projectRoot,
          moduleName: 'Fixture.Entry',
          sourcePath: join(fixture.sourceRoot, 'Fixture', 'Entry.lean'),
          declarations: ['Fixture.isRed'],
          outputDirectory: join(fixture.projectRoot, 'out'),
        });
        verifyLeanToTypeScriptPackage(emitted);
        expect(emitted.modules.map((module) => module.path)).toEqual([
          'Fixture/Data.ts',
          'Fixture/Entry.ts',
          LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH,
        ]);
        const entry = emitted.modules.find((module) => module.path === 'Fixture/Entry.ts');
        expect(entry?.code).toContain('import { type Colour } from "./Data.js";');
        expect(entry?.code).toContain('export function isRed(colour: Colour): boolean');
        const data = emitted.modules.find((module) => module.path === 'Fixture/Data.ts');
        expect(data?.code).toContain('import { type GeneratedData } from "../tslean-runtime.js";');
        expect(data?.code).toContain('export type Colour = "red" | "blue";');
        expect(data?.code).toContain('export const Colour = Object.freeze({');
        // A root parameter is an external input even when no record field reaches it, so the
        // type's module carries its boundary and the package gets the shared data union runtime.
        expect(emitted.modules.some((module) => module.path === LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH)).toBe(true);
      } finally {
        fixture.dispose();
      }
    },
    COMPILATION_TIMEOUT_MS,
  );

  test('decodes an external input through the exported boundary of the module that declares it', () => {
    // `Capability` lowers to a union and `Policy` to a value object, and both are decoded the same
    // way, so a caller never has to know which lowering the Lean source implied.
    for (const capability of capabilities) expect(Capability.fromData(capability)).toBe(capability);
    for (const refused of ['root', '', 'Read', 7, true, null, undefined, {}]) {
      expect(() => Capability.fromData(refused)).toThrowError(/^Capability must name a Capability$/u);
    }
    const granted = { read: true, write: false, administer: false };
    const policy = Policy.fromData({ granted, ceiling: 'read', frozen: false });
    expect(decideAccess(policy, Capability.fromData('read'))).toBe('allow');
    expect(grantedCapability(policy, Capability.fromData('write'))).toBeUndefined();
    // A field decode reaches the same decoder across the module edge and reports the field it read
    // rather than the type, so one type has one decoder and still two diagnostics.
    expect(() => Policy.fromData({ granted, ceiling: 'root', frozen: false })).toThrowError(
      /^Policy ceiling must name a Capability$/u,
    );
    expect(importBlock('TSLean/Examples/Package/Policy.ts')).toContain(
      'import { type Capability, Grant, type GrantData, requireCapability } from "./Capability.js";',
    );
    expect(
      generatedFiles().filter(
        (path) => path.endsWith('.ts') && readGenerated(path).includes('function requireCapability('),
      ),
    ).toEqual(['TSLean/Examples/Package/Capability.ts']);
  });

  test(
    'exports one decode boundary per root input, in the module that declares its type',
    () => {
      const fixture = createLeanPackageFixture([
        {
          name: 'Fixture.Tag',
          source: [
            'namespace Fixture',
            '',
            'inductive Tag where',
            '  | first',
            '  | second',
            '',
            'end Fixture',
            '',
          ].join('\n'),
        },
        {
          name: 'Fixture.Box',
          source: [
            'import Fixture.Tag',
            '',
            'namespace Fixture',
            '',
            'structure Box where',
            '  tag : Tag',
            '  flag : Bool',
            '',
            'end Fixture',
            '',
          ].join('\n'),
        },
        {
          name: 'Fixture.Entry',
          source: [
            'import Fixture.Box',
            '',
            'namespace Fixture',
            '',
            'def reads (tag : Tag) (box : Box) (flag : Bool) : Bool :=',
            '  match tag with',
            '  | .first => box.flag && flag',
            '  | .second => flag',
            '',
            'def passes (tag : Option Tag) : Option Tag := tag',
            '',
            'end Fixture',
            '',
          ].join('\n'),
        },
      ]);
      try {
        const request = {
          projectRoot: fixture.projectRoot,
          moduleName: 'Fixture.Entry',
          sourcePath: join(fixture.sourceRoot, 'Fixture', 'Entry.lean'),
          declarations: ['Fixture.passes', 'Fixture.reads'],
        } satisfies LeanToTypeScriptRequest;
        const emitted = compileLeanToTypeScript(request);
        verifyLeanToTypeScriptPackage(emitted);
        const code = new Map(emitted.modules.map((module) => [module.path, module.code]));
        const occurrences = (needle: string): number =>
          emitted.modules.reduce((total, module) => total + module.code.split(needle).length - 1, 0);
        // Every input `reads` takes is decoded by an export of the module that declares its type:
        // the two data types through `fromData`, the primitive through the shared validator.
        expect(code.get('Fixture/Tag.ts')).toContain('export const Tag = Object.freeze({');
        expect(code.get('Fixture/Box.ts')).toContain('export const Box = Object.freeze({');
        expect(code.get(LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH)).toContain(
          'export function requireBoolean(value: GeneratedData, name: string): boolean {',
        );
        // The declaring module owns the decoder and the nested one imports it, so neither the
        // decoder nor the boundary is emitted twice anywhere in the package.
        expect(code.get('Fixture/Box.ts')).toContain('import { type Tag, requireTag } from "./Tag.js";');
        expect(code.get('Fixture/Box.ts')).toContain('requireTag(data["tag"], "Box tag")');
        expect(occurrences('function requireTag(')).toBe(1);
        expect(occurrences('function requireBox(')).toBe(1);
        expect(occurrences('Object.freeze({')).toBe(2);
        expect(occurrences('fromData(value: GeneratedData)')).toBe(2);
        // The entry module states the decision over decoded values and imports nothing to run.
        expect(code.get('Fixture/Entry.ts')).toContain(
          'export function reads(tag: Tag, box: Box, flag: boolean): boolean {',
        );
        expect(code.get('Fixture/Entry.ts')).toContain('import { type Box } from "./Box.js";');
        // An optional input names the same boundary: presence is the caller's to resolve, and the
        // type it wraps gets no second decoder for being reached through an `Option`.
        expect(code.get('Fixture/Entry.ts')).toContain(
          'export function passes(tag: Tag | undefined): Tag | undefined {',
        );
        expect(occurrences(': unknown')).toBe(0);
        expect(moduleBytes(compileLeanToTypeScript(request))).toEqual(moduleBytes(emitted));
      } finally {
        fixture.dispose();
      }
    },
    COMPILATION_TIMEOUT_MS,
  );
});

function generatedFiles(): readonly string[] {
  const files: string[] = [];
  const walk = (directory: string, prefix: string): void => {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      if (entry.isDirectory()) walk(join(directory, entry.name), `${prefix}${entry.name}/`);
      else files.push(`${prefix}${entry.name}`);
    }
  };
  walk(generatedRoot, '');
  return files.sort();
}

/** A generated module without its provenance header: exactly what the Lean sources decide. */
function bodyOf(code: string): string {
  return code.split('\n').slice(17).join('\n');
}

function readGenerated(path: string): string {
  return readFileSync(join(generatedRoot, path), 'utf8');
}

function committedManifest(): {
  readonly semantic: {
    readonly entryModule: string;
    readonly declarations: readonly string[];
    readonly generatedBodySha256: string;
    readonly modules: readonly {
      readonly path: string;
      readonly leanModule: string;
      readonly imports: readonly string[];
      readonly bodySha256: string;
      readonly sourceMapSha256: string;
      readonly declarations: readonly {
        readonly declaration: string;
        readonly emitted: string;
        readonly line: number;
        readonly span: {
          readonly source: string;
          readonly startLine: number;
          readonly startColumn: number;
          readonly endLine: number;
          readonly endColumn: number;
        };
      }[];
    }[];
    readonly closure: readonly {
      readonly declaration: string;
      readonly module: string;
      readonly role: string;
      readonly reason: string;
    }[];
  };
} {
  return JSON.parse(readFileSync(manifestPath, 'utf8'));
}

/** The import statements a generated module opens with, before its first declaration. */
function importBlock(path: string): readonly string[] {
  return readGenerated(path)
    .split('\n')
    .slice(17)
    .filter((line) => line.startsWith('import '));
}

function moduleBytes(emitted: LeanToTypeScriptPackage): readonly (readonly string[])[] {
  return emitted.modules.map((module) => [module.path, module.code, module.sourceMap?.contents ?? '']);
}

/** Kahn's algorithm: a shorter result than the module count means the import graph has a cycle. */
function topologicalOrder(imports: ReadonlyMap<string, readonly string[]>): readonly string[] {
  const ordered: string[] = [];
  const remaining = new Map([...imports].map(([path, entries]) => [path, new Set(entries)]));
  while (remaining.size > 0) {
    const ready = [...remaining].filter(([, entries]) => entries.size === 0).map(([path]) => path);
    if (ready.length === 0) return ordered;
    for (const path of ready.sort()) {
      ordered.push(path);
      remaining.delete(path);
    }
    for (const entries of remaining.values()) for (const path of ready) entries.delete(path);
  }
  return ordered;
}

interface MappingSegment {
  readonly generatedLine: number;
  readonly generatedColumn: number;
  readonly sourceIndex: number;
  readonly sourceLine: number;
  readonly sourceColumn: number;
}

const BASE64_DIGITS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';

/** Decodes a version 3 `mappings` string into absolute positions. */
function decodeMappings(mappings: string): readonly MappingSegment[] {
  const segments: MappingSegment[] = [];
  let sourceIndex = 0;
  let sourceLine = 0;
  let sourceColumn = 0;
  for (const [line, group] of mappings.split(';').entries()) {
    if (group === '') continue;
    let generatedColumn = 0;
    for (const segment of group.split(',')) {
      const values = decodeVariableLengthQuantities(segment);
      if (values.length !== 4) throw new TypeError('source map segment is not a four-field mapping');
      generatedColumn += values[0] ?? 0;
      sourceIndex += values[1] ?? 0;
      sourceLine += values[2] ?? 0;
      sourceColumn += values[3] ?? 0;
      segments.push({ generatedLine: line + 1, generatedColumn, sourceIndex, sourceLine, sourceColumn });
    }
  }
  return segments;
}

function decodeVariableLengthQuantities(segment: string): readonly number[] {
  const values: number[] = [];
  let shift = 0;
  let accumulated = 0;
  for (const character of segment) {
    const digit = BASE64_DIGITS.indexOf(character);
    if (digit < 0) throw new TypeError(`source map digit is invalid: ${character}`);
    accumulated += (digit & 0b11111) << shift;
    if ((digit & 0b100000) !== 0) {
      shift += 5;
      continue;
    }
    values.push((accumulated & 1) === 1 ? -(accumulated >>> 1) : accumulated >>> 1);
    shift = 0;
    accumulated = 0;
  }
  return values;
}

function grants(): readonly Grant[] {
  return [...Array(8).keys()].map(
    (bits) =>
      new Grant({
        read: bits % 2 === 1,
        write: Math.floor(bits / 2) % 2 === 1,
        administer: Math.floor(bits / 4) % 2 === 1,
      }),
  );
}

/** The same 144 rows, computed by Lean itself against the real toolchain. */
function evaluateLeanAccess(): readonly string[] {
  const directory = mkdtempSync(join(tmpdir(), 'tslean-package-oracle-'));
  const driver = join(directory, 'Oracle.lean');
  try {
    writeFileSync(
      driver,
      [
        'import TSLean.Examples.Package.Decision',
        'import Lean.Data.Json',
        'open TSLean.Examples.Package',
        'def grants : List Grant := (List.range 8).map fun bits =>',
        '  { read := bits % 2 = 1, write := bits / 2 % 2 = 1, administer := bits / 4 % 2 = 1 }',
        'def capabilities : List Capability := [.read, .write, .administer]',
        'def capabilityName : Capability → String',
        '  | .read => "read"',
        '  | .write => "write"',
        '  | .administer => "administer"',
        'def decisionName : Decision → String',
        '  | .allow => "allow"',
        '  | .deny => "deny"',
        'def admittedName : Option Capability → String',
        '  | some capability => capabilityName capability',
        '  | none => "undefined"',
        'def rows : List String := grants.flatMap fun granted =>',
        '  capabilities.flatMap fun ceiling => [true, false].flatMap fun frozen =>',
        '    capabilities.map fun requested =>',
        '      let policy : Policy := { granted := granted, ceiling := ceiling, frozen := frozen }',
        '      decisionName (decideAccess policy requested) ++ "/" ++ admittedName (grantedCapability policy requested)',
        '#eval IO.println (Lean.Json.arr (rows.map Lean.Json.str).toArray).compress',
        '',
      ].join('\n'),
    );
    const result = spawnSync('lake', ['env', 'lean', driver], {
      cwd: leanRoot,
      encoding: 'utf8',
      maxBuffer: 4 * 1024 * 1024,
    });
    if (result.status !== 0) {
      throw new TypeError(`Lean oracle failed: ${result.stderr}${result.stdout}`);
    }
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

interface LeanPackageFixture {
  readonly projectRoot: string;
  readonly sourceRoot: string;
  dispose(): void;
}

/** A throwaway Lake project holding several modules, so import edges can be compiled for real. */
function createLeanPackageFixture(
  modules: readonly { readonly name: string; readonly source: string }[],
): LeanPackageFixture {
  const projectRoot = mkdtempSync(join(tmpdir(), 'tslean-lean-package-'));
  const sourceRoot = join(projectRoot, 'sources');
  mkdirSync(sourceRoot);
  writeFileSync(join(projectRoot, 'lean-toolchain'), 'leanprover/lean4:v4.29.0\n');
  writeFileSync(join(projectRoot, 'lake-manifest.json'), '{"version":"1.1.0","name":"fixture","packages":[]}\n');
  const library = modules[0]?.name.split('.')[0];
  if (library === undefined) throw new TypeError('a Lean package fixture needs at least one module');
  writeFileSync(
    join(projectRoot, 'lakefile.toml'),
    [
      'name = "lean_to_typescript_package_fixture"',
      'version = "0.1.0"',
      '',
      '[[lean_lib]]',
      `name = "${library}"`,
      'srcDir = "sources"',
      `roots = [${modules.map((module) => `"${module.name}"`).join(', ')}]`,
      '',
    ].join('\n'),
  );
  for (const module of modules) {
    const path = join(sourceRoot, `${module.name.split('.').join('/')}.lean`);
    mkdirSync(dirname(path), { recursive: true });
    writeFileSync(path, module.source);
  }
  return { projectRoot, sourceRoot, dispose: () => rmSync(projectRoot, { force: true, recursive: true }) };
}
