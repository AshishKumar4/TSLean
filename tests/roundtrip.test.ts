// The round-trip profile, the projection, and what strict acceptance now means.
//
// These tests are strict on purpose: each one names a construct the two compilers have to
// carry the same way, and fails when the recovered Lean stops naming the same cases, stops
// type-checking, or stops being the same bytes on a second lap.
//
// The cases that elaborate Lean are grouped at the end so a failure in the cheap structural
// checks reports before the expensive ones run.

import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { homedir as home, tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import ts from 'typescript';
import { leanAccepts, leanRun } from '../src/lean-check.js';
import { generateLean } from '../src/codegen/index.js';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import {
  profileModule,
  projectModule,
  resolveProfileType,
  verifyLeanToTypeScriptRoundtrip,
  verifyTypeScriptToLeanRoundtrip,
} from '../src/roundtrip/index.js';
import { domainSize, enumerateTuples, enumerateValues, renderValue, valueAt } from '../src/roundtrip/values.js';
import { transpileProject } from '../src/project/index.js';
import { decodeManifest } from '../src/lean-to-typescript/manifest.js';

const OPTIONS: ts.CompilerOptions = {
  target: ts.ScriptTarget.ES2022,
  module: ts.ModuleKind.NodeNext,
  moduleResolution: ts.ModuleResolutionKind.NodeNext,
  strict: true,
  skipLibCheck: true,
  lib: ['lib.es2022.d.ts'],
};

/** Open one in-memory module so a test states its input as source rather than as a fixture path. */
function open(source: string, fileName = '/roundtrip.ts'): { file: ts.SourceFile; checker: ts.TypeChecker } {
  const host = ts.createCompilerHost(OPTIONS);
  const original = host.getSourceFile.bind(host);
  host.getSourceFile = (name, version, onError, shouldCreate) =>
    name === fileName
      ? ts.createSourceFile(name, source, version, true, ts.ScriptKind.TS)
      : original(name, version, onError, shouldCreate);
  host.fileExists = (name) => (name === fileName ? true : ts.sys.fileExists(name));
  host.readFile = (name) => (name === fileName ? source : ts.sys.readFile(name));
  const program = ts.createProgram([fileName], OPTIONS, host);
  const file = program.getSourceFile(fileName);
  if (file === undefined) throw new Error(`no source file at ${fileName}`);
  return { file, checker: program.getTypeChecker() };
}

/** The Lean the TypeScript-to-Lean compiler emits for one in-memory module. */
function toLean(source: string): string {
  return generateLean(rewriteModule(parseFile({ fileName: '/roundtrip.ts', sourceText: source })));
}

function admitted(source: string): readonly string[] {
  const { file, checker } = open(source);
  return profileModule(file, checker).admitted.map((entry) => `${entry.name}:${entry.kind}`);
}

function refusal(source: string, name: string): string {
  const { file, checker } = open(source);
  const entry = profileModule(file, checker).refused.find((candidate) => candidate.name === name);
  return entry?.reason ?? '(admitted)';
}

describe('enumeration constructors', () => {
  it('names each Lean constructor with the literal it came from', () => {
    const lean = toLean('export type Impact = "observe" | "externalSend";\n');
    expect(lean).toContain('inductive Impact where');
    expect(lean).toContain('| observe');
    expect(lean).toContain('| externalSend');
    expect(lean).not.toContain('| Observe');
  });

  it('lowers a literal compared against an enumeration to that constructor', () => {
    const lean = toLean(
      'export type Impact = "observe" | "mutate";\n' +
        'export function isObserve(impact: Impact): boolean { return impact === "observe"; }\n',
    );
    // Lean's derived equality on an inductive reaches `Nat.decEq`, which the
    // Lean-to-TypeScript fragment refuses, so the comparison decides every constructor.
    expect(lean).toContain('match impact with');
    expect(lean).toContain('| .observe => true');
    expect(lean).toContain('| .mutate => false');
    expect(lean).not.toContain('impact == "observe"');
    expect(lean).not.toContain('impact == Impact.observe');
  });

  it('lowers a literal returned where an enumeration is expected to that constructor', () => {
    const lean = toLean(
      'export type Tier = "direct" | "mediated";\n' +
        'export function floorOf(direct: boolean): Tier { return direct ? "direct" : "mediated"; }\n',
    );
    expect(lean).toContain('Tier.direct');
    expect(lean).toContain('Tier.mediated');
  });

  it('folds a chain of tests of one enumeration into a single match', () => {
    const lean = toLean(
      'export type Impact = "observe" | "mutate" | "administer";\n' +
        'export function admits(impact: Impact, owned: boolean): boolean {\n' +
        '  return impact === "observe" ? true : impact === "mutate" ? owned : false;\n' +
        '}\n',
    );
    // A chain and a match are the same decision written two ways, and the two compilers
    // write it the two ways, so the chain has to fold or the term grows on every lap.
    expect(lean).toContain('match impact with');
    expect(lean).toContain('| .observe => true');
    expect(lean).toContain('| .mutate => owned');
    expect(lean).toContain('| .administer => false');
    expect(lean).not.toContain('==');
  });

  it('leaves a union whose literals cannot name Lean constructors as strings', () => {
    const lean = toLean('export type Kebab = "a-b" | "c-d";\n');
    expect(lean).not.toContain('inductive Kebab');
    expect(refusal('export type Kebab = "a-b" | "c-d";\n', 'Kebab')).toContain('enumeration');
  });
});

describe('booleans, options and structures', () => {
  it('resolves `T | undefined` to an option over the alias it was written with', () => {
    const source =
      'export type Placement = "bundled" | "dynamic";\n' +
      'export function pick(bundled: boolean): Placement | undefined {\n' +
      '  return bundled ? "bundled" : undefined;\n' +
      '}\n';
    const { file, checker } = open(source);
    const declaration = file.statements.filter(ts.isFunctionDeclaration)[0];
    const signature = checker.getSignatureFromDeclaration(declaration);
    expect(signature).toBeDefined();
    const result = resolveProfileType(signature!.getReturnType(), checker);
    expect(result).toEqual({
      kind: 'option',
      inner: { kind: 'enumeration', name: 'Placement', members: ['bundled', 'dynamic'] },
      encoding: 'undefined',
    });
  });

  it('resolves the generated tagged encoding to the same option as `T | undefined`', () => {
    const source =
      'export type Placement = "bundled" | "dynamic";\n' +
      'export type Option<A> = { readonly kind: "none" } | { readonly kind: "some"; readonly value: A };\n' +
      'export function pick(bundled: boolean): Option<Placement> {\n' +
      '  if (bundled) { return { kind: "some", value: "bundled" }; }\n' +
      '  return { kind: "none" };\n' +
      '}\n';
    const { file, checker } = open(source);
    const declaration = file.statements.filter(ts.isFunctionDeclaration)[0];
    const signature = checker.getSignatureFromDeclaration(declaration);
    expect(signature).toBeDefined();
    // The two spellings denote one Lean `Option`, so they resolve to one profile type and
    // differ only in how a value crosses the JavaScript boundary.
    expect(resolveProfileType(signature!.getReturnType(), checker)).toEqual({
      kind: 'option',
      inner: { kind: 'enumeration', name: 'Placement', members: ['bundled', 'dynamic'] },
      encoding: 'tagged',
    });
  });

  it('emits `Option` rather than a string for a nullable enumeration return', () => {
    const lean = toLean(
      'export type Placement = "bundled" | "dynamic";\n' +
        'export function pick(bundled: boolean): Placement | undefined {\n' +
        '  return bundled ? "bundled" : undefined;\n' +
        '}\n',
    );
    expect(lean).toContain(': Option Placement');
  });

  it('lowers an immutable class to a structure under its own name', () => {
    const lean = toLean(
      'export interface PairInit { readonly left: boolean; readonly right: boolean; }\n' +
        'export class Pair {\n' +
        '  public readonly left: boolean;\n' +
        '  public readonly right: boolean;\n' +
        '  public constructor(init: PairInit) { this.left = init.left; this.right = init.right; Object.freeze(this); }\n' +
        '  public both(): boolean { return this.left && this.right; }\n' +
        '}\n',
    );
    expect(lean).toContain('structure Pair where');
    expect(lean).toContain('def Pair.both (self : Pair) : Bool');
    expect(lean).not.toContain('PairState');
  });

  it('lowers a method call on a structure to the definition that carries it', () => {
    const lean = toLean(
      'export interface PairInit { readonly left: boolean; readonly right: boolean; }\n' +
        'export class Pair {\n' +
        '  public readonly left: boolean;\n' +
        '  public readonly right: boolean;\n' +
        '  public constructor(init: PairInit) { this.left = init.left; this.right = init.right; Object.freeze(this); }\n' +
        '  public both(): boolean { return this.left && this.right; }\n' +
        '}\n' +
        'export function ask(pair: Pair): boolean { return pair.both(); }\n',
    );
    expect(lean).toContain('Pair.both pair');
    expect(lean).not.toMatch(/def ask[^\n]*default/u);
  });

  it('refuses a class that mutates its own state', () => {
    const source =
      'export class Counter {\n' +
      '  public value: boolean;\n' +
      '  public constructor(value: boolean) { this.value = value; }\n' +
      '  public toggle(): boolean { this.value = !this.value; return this.value; }\n' +
      '}\n';
    expect(refusal(source, 'Counter')).toContain('structure of profile fields');
  });
});

describe('generated decoders', () => {
  const GENERATED =
    'export type Mode = "strict" | "lenient";\n' +
    'export function pick(mode: Mode): boolean { return mode === "strict"; }\n' +
    'export type GeneratedData = boolean | string | readonly GeneratedData[] | {\n' +
    '    readonly [key: string]: GeneratedData;\n' +
    '};\n' +
    'export function requireMode(value: GeneratedData, name: string): Mode {\n' +
    '    if (value === "strict" || value === "lenient") { return value; }\n' +
    '    throw new TypeError(`${name} must name a Mode`);\n' +
    '}\n';

  it('refuses the data union and every decoder over it', () => {
    expect(admitted(GENERATED)).toEqual(['Mode:enumeration', 'pick:function']);
    expect(refusal(GENERATED, 'GeneratedData')).toContain('enumeration');
    expect(refusal(GENERATED, 'requireMode')).toContain('no profile type');
  });

  it('projects the module down to its declarations and leaves it compiling', () => {
    const { file, checker } = open(GENERATED);
    const projected = projectModule(file, checker, 'Generated.ts').source;
    expect(projected).toContain('export type Mode');
    expect(projected).toContain('export function pick');
    expect(projected).not.toContain('GeneratedData');
    expect(projected).not.toContain('requireMode');
    expect(open(projected).file.statements).toHaveLength(2);
  });
});

describe('value domains', () => {
  it('enumerates a structure in odometer order with the last field varying fastest', () => {
    const type = {
      kind: 'structure' as const,
      name: 'Pair',
      introduced: 'interface' as const,
      fields: [
        { name: 'left', type: { kind: 'boolean' as const } },
        { name: 'right', type: { kind: 'boolean' as const } },
      ],
    };
    expect(domainSize(type)).toBe(4);
    expect(enumerateValues(type).map(renderValue)).toEqual([
      '{false,false}',
      '{false,true}',
      '{true,false}',
      '{true,true}',
    ]);
  });

  it('counts an option as its payload domain plus the empty case', () => {
    const type = {
      kind: 'option' as const,
      inner: { kind: 'enumeration' as const, name: 'Tier', members: ['direct', 'mediated'] },
    };
    expect(enumerateValues(type).map(renderValue)).toEqual(['none', 'some(direct)', 'some(mediated)']);
  });

  it('truncates a tuple domain to the limit without changing the order', () => {
    const boolean = { kind: 'boolean' as const };
    const full = enumerateTuples([boolean, boolean, boolean], 8).map((row) => row.map(renderValue).join(''));
    expect(full).toEqual([
      'falsefalsefalse',
      'falsefalsetrue',
      'falsetruefalse',
      'falsetruetrue',
      'truefalsefalse',
      'truefalsetrue',
      'truetruefalse',
      'truetruetrue',
    ]);
    expect(enumerateTuples([boolean, boolean, boolean], 3).map((row) => row.map(renderValue).join(''))).toEqual(
      full.slice(0, 3),
    );
  });
});

describe('fixed point', () => {
  it('produces the same Lean on a second compilation', () => {
    const source =
      'export type Tier = "direct" | "mediated";\n' +
      'export function floorOf(direct: boolean): Tier { return direct ? "direct" : "mediated"; }\n';
    expect(toLean(source)).toBe(toLean(source));
  });

  it('produces the same projection on a second projection', () => {
    const source =
      'export type Mode = "strict" | "lenient";\n' +
      'export function pick(mode: Mode): boolean { return mode === "strict"; }\n';
    const first = projectModule(open(source).file, open(source).checker, 'Mode.ts').source;
    const second = projectModule(open(first).file, open(first).checker, 'Mode.ts').source;
    expect(second).toBe(first);
  });
});

describe('modules and effects', () => {
  it('opens a sibling module so an imported type resolves rather than binding implicitly', () => {
    const shared = '/shared.ts';
    const lean = generateLean(
      rewriteModule(
        parseFile({
          fileName: '/consumer.ts',
          sourceText:
            'import { type Level } from "./shared.js";\n' +
            'export function loud(level: Level): boolean { return level === "high"; }\n',
          extraFiles: new Map([[shared, 'export type Level = "low" | "high";\n']]),
        }),
      ),
    );
    expect(lean).toContain('import TSLean.Generated.Shared');
    expect(lean).toMatch(/^open .*TSLean\.Generated\.Shared/mu);
  });

  it('keeps an effectful function outside the profile', () => {
    const source = 'export async function later(flag: boolean): Promise<boolean> { return flag; }\n';
    expect(refusal(source, 'later')).toContain('async');
  });
});

describe('Lean acceptance', () => {
  it('accepts the Lean recovered from an enumeration, an option and a structure', () => {
    const lean = toLean(
      'export type Tier = "direct" | "mediated";\n' +
        'export interface SessionInit { readonly owned: boolean; }\n' +
        'export class Session {\n' +
        '  public readonly owned: boolean;\n' +
        '  public constructor(init: SessionInit) { this.owned = init.owned; Object.freeze(this); }\n' +
        '  public tier(): Tier { return this.owned ? "direct" : "mediated"; }\n' +
        '}\n' +
        'export function served(session: Session): Tier | undefined {\n' +
        '  return session.tier() === "direct" ? "direct" : undefined;\n' +
        '}\n',
    );
    const acceptance = leanAccepts([{ module: 'TSLeanRoundtrip.AcceptanceCase', code: lean, imports: [] }]);
    expect(acceptance.diagnostics.filter((entry) => entry.severity === 'error')).toEqual([]);
    expect(acceptance.accepted).toBe(true);
  });

  it('reports the Lean errors an ill-typed lowering produces rather than passing', () => {
    const acceptance = leanAccepts([
      {
        module: 'TSLeanRoundtrip.RejectionCase',
        code: 'inductive Tier where\n  | direct\n  | mediated\n\ndef broken : Tier := "direct"\n',
        imports: [],
      },
    ]);
    expect(acceptance.accepted).toBe(false);
    expect(acceptance.diagnostics.some((entry) => entry.message.includes('Tier'))).toBe(true);
  });
});

describe('names that must not be substituted', () => {
  it('keeps a renamed import bound to the module it came from', () => {
    const lean = generateLean(
      rewriteModule(
        parseFile({
          fileName: '/consumer.ts',
          sourceText:
            'import { type Level as Loudness } from "./shared.js";\n' +
            'export function loud(level: Loudness): boolean { return level === "high"; }\n',
          extraFiles: new Map([['/shared.ts', 'export type Level = "low" | "high";\n']]),
        }),
      ),
    );
    // The alias is a local name for the same type, so the constructors stay the declared ones.
    expect(lean).toContain('| .high => true');
    expect(lean).not.toContain('Loudness');
  });

  it('does not read a same-named field of another type as a JavaScript API', () => {
    const lean = toLean(
      'export interface StreamInit { readonly read: boolean; readonly write: boolean; }\n' +
        'export class Stream {\n' +
        '  public readonly read: boolean;\n' +
        '  public readonly write: boolean;\n' +
        '  public constructor(init: StreamInit) { this.read = init.read; this.write = init.write; Object.freeze(this); }\n' +
        '  public both(): boolean { return this.read && this.write; }\n' +
        '}\n',
    );
    expect(lean).toContain('self.read && self.write');
    expect(lean).not.toMatch(/def Stream\.both[^\n]*default/u);
  });

  it('reads a cross-file field name from the file that declares it', () => {
    const lean = generateLean(
      rewriteModule(
        parseFile({
          fileName: '/user.ts',
          sourceText:
            'import { Grant, type GrantInit } from "./grant.js";\n' +
            'export function frozen(grant: Grant): Grant { return new Grant({ read: grant.read, write: false }); }\n',
          extraFiles: new Map([
            [
              '/grant.ts',
              'export interface GrantInit { readonly read: boolean; readonly write: boolean; }\n' +
                'export class Grant {\n' +
                '  public readonly read: boolean;\n' +
                '  public readonly write: boolean;\n' +
                '  public constructor(init: GrantInit) { this.read = init.read; this.write = init.write; Object.freeze(this); }\n' +
                '}\n',
            ],
          ]),
        }),
      ),
    );
    expect(lean).toContain('{ read := grant.read, write := false }');
  });

  it('refuses an enumeration whose literal collides with a Lean keyword', () => {
    expect(refusal('export type Branch = "if" | "else";\n', 'Branch')).toContain('enumeration');
  });
});

describe('what the round trip must refuse or bound', () => {
  it('decides an equality between two enumeration values without a derived equality', () => {
    const lean = toLean(
      'export type Impact = "observe" | "mutate" | "administer";\n' +
        'export function same(left: Impact, right: Impact): boolean { return left === right; }\n',
    );
    // A derived equality on an inductive reaches `Nat.decEq`, which the Lean-to-TypeScript
    // fragment refuses, so a variable-to-variable comparison decides both sides.
    expect(lean).toContain('match left with');
    expect(lean).toContain('match right with');
    expect(lean).not.toContain('left == right');
    expect(lean).not.toContain('==');
  });

  it('brackets a nested match so the next arm does not attach to the inner one', () => {
    const lean = toLean(
      'export type Capability = "read" | "write" | "administer";\n' +
        'export function agree(left: Capability, right: Capability, also: boolean): boolean {\n' +
        '  return left === right && also;\n' +
        '}\n',
    );
    // Written on one line, an unbracketed inner match swallows the outer match's next arm and
    // Lean reports the outer match as non-exhaustive. An unparenthesized outer match is worse:
    // `&& also` then attaches only to its final arm. These exercise the first and second arms,
    // not only the last one Lean's parser happens to accept.
    expect(lean).toContain('=> (match right with');
    expect(lean).toContain('(match left with');
    const run = leanRun([{ module: 'TSLeanRoundtrip.NestedMatchCase', code: lean, imports: [] }], {
      module: 'TSLeanRoundtrip.NestedMatchDriver',
      imports: ['TSLeanRoundtrip.NestedMatchCase'],
      code: [
        'import TSLeanRoundtrip.NestedMatchCase',
        'def main : IO Unit := do',
        '  IO.println (if TSLean.Generated.Roundtrip.agree .read .read false then "true" else "false")',
        '  IO.println (if TSLean.Generated.Roundtrip.agree .write .write true then "true" else "false")',
        '',
      ].join('\n'),
    });
    expect(run.accepted).toBe(true);
    expect(run.output.trim().split('\n')).toEqual(['false', 'true']);
  });
  it('leaves a scrutinee that reads a local where the local is in scope', () => {
    const lean = toLean(
      'export type Tier = "direct" | "mediated";\n' +
        'export function pick(flag: boolean): boolean {\n' +
        '  const chosen: Tier = flag ? "direct" : "mediated";\n' +
        '  const tier: Tier = chosen;\n' +
        '  return tier === "direct";\n' +
        '}\n',
    );
    // Hoisting a scrutinee above the binding it reads would move it out of scope.
    const hoist = lean.indexOf('let decided0');
    const local = lean.indexOf('let tier');
    expect(hoist === -1 || hoist > local).toBe(true);
  });

  it('does not shadow a binding already named like a hoisted scrutinee', () => {
    const lean = toLean(
      'export type Tier = "direct" | "mediated";\n' +
        'export function floorOf(flag: boolean): Tier { return flag ? "direct" : "mediated"; }\n' +
        'export function pick(flag: boolean): boolean {\n' +
        '  const decided0 = flag;\n' +
        '  return floorOf(flag) === "direct" && decided0;\n' +
        '}\n',
    );
    // The scrutinee reads only a parameter, so it hoists; the name it takes has to step past
    // the binding the source already made.
    expect(lean).toContain('let decided1 :=');
    expect(lean).not.toContain('let decided0 := floorOf');
  });

  it('does not hoist through a local that shadows a module declaration', () => {
    const lean = toLean(
      'export type Tier = "direct" | "mediated";\n' +
        'export function chosen(flag: boolean): Tier { return flag ? "direct" : "mediated"; }\n' +
        'export function identity(tier: Tier): Tier { return tier; }\n' +
        'export function pick(flag: boolean): boolean {\n' +
        '  const chosen: Tier = flag ? "direct" : "mediated";\n' +
        '  return identity(chosen) === "direct";\n' +
        '}\n',
    );
    // The local `chosen` shadows the module function of the same name. A name-only check
    // used to decide that it was module-visible and emitted `identity chosen` before the
    // local binding. The match must stay after that binding.
    const local = lean.indexOf('let chosen');
    // The scrutinee's own bracketing is the printer's business; the ordering is the invariant.
    const match = lean.search(/match \(?identity chosen\)? with/u);
    expect(match).toBeGreaterThan(local);
    expect(lean.slice(0, local)).not.toContain('identity chosen');
  });

  it('refuses two sources whose base names collide instead of losing one', async () => {
    const root = mkdtempSync(join(tmpdir(), 'tslean-collision-'));
    try {
      const body =
        'export type Mode = "on" | "off";\nexport function on(mode: Mode): boolean { return mode === "on"; }\n';
      mkdirSync(join(root, 'nested'), { recursive: true });
      writeFileSync(join(root, 'Mode.ts'), body, 'utf8');
      writeFileSync(join(root, 'nested', 'Mode.ts'), body, 'utf8');
      // A module name comes from a file's base name, so these two would silently become one
      // module and one of them would be lost.
      await expect(
        verifyTypeScriptToLeanRoundtrip([join(root, 'Mode.ts'), join(root, 'nested', 'Mode.ts')]),
      ).rejects.toThrow(/both compile to/u);
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });

  it('names members by their owner, so two classes cannot stand in for each other', () => {
    const source =
      'export interface PairInit { readonly left: boolean; readonly right: boolean; }\n' +
      'export class First {\n' +
      '  public readonly left: boolean;\n' +
      '  public readonly right: boolean;\n' +
      '  public constructor(init: PairInit) { this.left = init.left; this.right = init.right; Object.freeze(this); }\n' +
      '  public both(): boolean { return this.left && this.right; }\n' +
      '}\n' +
      'export class Second {\n' +
      '  public readonly left: boolean;\n' +
      '  public readonly right: boolean;\n' +
      '  public constructor(init: PairInit) { this.left = init.left; this.right = init.right; Object.freeze(this); }\n' +
      '  public both(): boolean { return this.left || this.right; }\n' +
      '}\n';
    expect(admitted(source)).toContain('First.both:method');
    expect(admitted(source)).toContain('Second.both:method');
    expect(admitted(source)).not.toContain('both:method');
  });

  it('keys a project module graph by its Lean module name', () => {
    const root = mkdtempSync(join(tmpdir(), 'tslean-graph-'));
    try {
      writeFileSync(join(root, 'shared.ts'), 'export type Level = "low" | "high";\n', 'utf8');
      writeFileSync(
        join(root, 'consumer.ts'),
        'import { type Level } from "./shared.js";\n' +
          'export function loud(level: Level): boolean { return level === "high"; }\n',
        'utf8',
      );
      const result = transpileProject({ projectDir: root, outputDir: join(root, 'out'), generateLakefile: false });
      for (const file of result.files) {
        // A lookup by source path answers nothing, which is how an import list went missing.
        expect(result.graph.nodes.get(file.module)).toBeDefined();
        expect(result.graph.nodes.get(file.tsFile)).toBeUndefined();
      }
      const consumer = result.files.find((file) => file.module.endsWith('Consumer'));
      expect(result.graph.nodes.get(consumer?.module ?? '')?.imports ?? []).toHaveLength(1);
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
  });

  it('builds only the tuples asked for, however large the domain is', () => {
    const wide = {
      kind: 'structure' as const,
      name: 'Wide',
      introduced: 'interface' as const,
      fields: Array.from({ length: 20 }, (_, index) => ({
        name: `field${String(index)}`,
        type: { kind: 'boolean' as const },
      })),
    };

    expect(domainSize(wide)).toBe(2 ** 20);
    const rows = enumerateTuples([wide, wide], 4);
    expect(rows).toHaveLength(4);
    // Indexing reaches a value without materialising the product it sits in.
    expect(renderValue(valueAt(wide, 2 ** 20 - 1))).toBe(`{${Array(20).fill('true').join(',')}}`);
  });

  it('refuses a domain too large to index rather than sampling a wrapped index', () => {
    const huge = {
      kind: 'structure' as const,
      name: 'Huge',
      introduced: 'interface' as const,
      fields: Array.from({ length: 60 }, (_, index) => ({
        name: `field${String(index)}`,
        type: { kind: 'boolean' as const },
      })),
    };
    expect(() => enumerateTuples([huge, huge], 4)).toThrow(/too large to enumerate/u);
  });
});

describe('source identity boundaries', () => {
  it('fails the source triangle when an explicit original Lean root is unavailable', async () => {
    const report = await verifyLeanToTypeScriptRoundtrip(
      join(process.cwd(), 'examples/lean-to-typescript/roundtrip/Parity/generated/tslean.manifest.json'),
      { sourceRoot: join(process.cwd(), 'does-not-exist') },
    );
    const check = report.checks.find(
      (entry) => entry.name === 'the generated typescript computes what its Lean source does',
    );
    expect(check?.holds).toBe(false);
    expect(check?.detail).toContain('not run');
    expect(report.counterexamples.some((entry) => entry.subject === '(original Lean source root)')).toBe(true);
  });

  it('compares only manifest-backed source callables, not generated class helpers', async () => {
    const report = await verifyLeanToTypeScriptRoundtrip(
      join(process.cwd(), 'examples/lean-to-typescript/roundtrip/Window/generated/tslean.manifest.json'),
      { leanProjectRoot: join(process.cwd(), 'lean') },
    );
    // Window exports generated `toData` and `equals`, but its Lean manifest names only
    // fullyOpen and flip. Those two, not the generated helpers, are source observations.
    expect(report.sourceBehaviour?.coverage.map((entry) => entry.function)).toHaveLength(2);
    expect(
      report.checks.find((entry) => entry.name === 'the generated typescript computes what its Lean source does')
        ?.detail,
    ).toContain('2/2 manifest callable(s) observed');
  });
  it('verifies a certificate-bearing manifest end to end', async () => {
    // The observation driver needs the module's compiled olean, which the project's default
    // targets do not build; a cached build is a no-op when the tree is warm.
    const lake = resolve(home(), '.elan', 'bin', 'lake');
    const build = spawnSync(lake, ['build', 'TSLean.Examples.Placement'], {
      cwd: join(process.cwd(), 'lean'),
      encoding: 'utf8',
    });
    if (build.status !== 0) throw new TypeError(`Placement olean build failed: ${build.stdout}${build.stderr}`);
    const manifestPath = join(process.cwd(), 'examples/lean-to-typescript/generated/tslean.manifest.json');
    const report = await verifyLeanToTypeScriptRoundtrip(manifestPath, {
      leanProjectRoot: join(process.cwd(), 'lean'),
    });
    const manifest = JSON.parse(readFileSync(manifestPath, 'utf8')) as { semantic?: { certificates?: unknown } };
    const certificates = manifest.semantic?.certificates;
    expect(Array.isArray(certificates) && certificates.length > 0).toBe(true);
    expect(report.checks.every((entry) => entry.holds)).toBe(true);
  });

  it('reads a manifest one minor revision ahead within the same major', () => {
    const manifestPath = join(process.cwd(), 'examples/lean-to-typescript/generated/tslean.manifest.json');
    const parsed = JSON.parse(readFileSync(manifestPath, 'utf8')) as Record<string, unknown>;
    const tolerated = { ...parsed, schemaVersion: 4002 };
    expect(() => decodeManifest(tolerated)).not.toThrow();
    const refused = { ...parsed, schemaVersion: 5001 };
    expect(() => decodeManifest(refused)).toThrowError('unsupported Lean to TypeScript manifest schema');
  });

  it('rejects same-named types from different modules before renderer or constructor maps choose one', async () => {
    const root = mkdtempSync(join(tmpdir(), 'tslean-type-collision-'));
    try {
      // `open` is a Lean keyword, so a literal spelled that way would be refused before the
      // type identity is ever resolved and the collision would go unexercised.
      const source = (name: string) =>
        `export type State = "raised" | "lowered";\n` +
        `export function ${name}(state: State): boolean { return state === "raised"; }\n`;
      writeFileSync(join(root, 'alpha.ts'), source('alpha'), 'utf8');
      writeFileSync(join(root, 'beta.ts'), source('beta'), 'utf8');
      const report = await verifyTypeScriptToLeanRoundtrip([join(root, 'alpha.ts'), join(root, 'beta.ts')]);
      expect(report.holds).toBe(false);
      expect(report.counterexamples.some((entry) => entry.actual.includes('qualify the type identity'))).toBe(true);
    } finally {
      rmSync(root, { recursive: true, force: true });
    }
    // Two modules, and a further lap over each, so this runs Lake four times.
  }, 180_000);
});

describe('what a report has to contain', () => {
  it('compares the generated TypeScript with both the recovered and the original Lean', async () => {
    const report = await verifyLeanToTypeScriptRoundtrip(
      join(process.cwd(), 'examples/lean-to-typescript/roundtrip/Parity/generated/tslean.manifest.json'),
      { leanProjectRoot: join(process.cwd(), 'lean') },
    );
    const names = report.checks.map((check) => check.name);
    // Both compilers could share a bug and agree with themselves, so the generated
    // TypeScript is also compared against the Lean it was generated from.
    expect(names).toContain('both sides compute the same function');
    expect(names).toContain('the generated typescript computes what its Lean source does');
    expect(report.holds).toBe(true);
    expect(report.behaviour?.coverage.every((entry) => entry.exhaustive)).toBe(true);
  });

  it('executes both sides in the TypeScript-to-Lean direction too', async () => {
    const report = await verifyTypeScriptToLeanRoundtrip([join(process.cwd(), 'examples/roundtrip/tier.ts')], {
      leanProjectRoot: join(process.cwd(), 'lean'),
    });
    const compute = report.checks.find((check) => check.name === 'both sides compute the same function');
    expect(compute).toBeDefined();
    expect(compute?.holds).toBe(true);
    expect(compute?.detail).toContain('every domain exhausted');
    expect(report.holds).toBe(true);
    // Executes Lake for the Lean side, so it carries the same budget as the lap test above.
  }, 180_000);
});
