import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { afterAll, beforeAll, describe, expect, test } from 'vitest';
import ts from 'typescript';
import {
  compileLeanToTypeScript,
  UnsupportedLeanFragmentError,
  type LeanToTypeScriptPackage,
} from '../src/lean-to-typescript/index.js';
import { createLeanLibraryFixture, type LeanLibraryFixture } from './helpers/lean-library-fixture.js';
import { createLeanProjectFixture, type LeanProjectFixture } from './helpers/lean-project-fixture.js';

/**
 * A representative multi-module Lean library. Between the three modules it uses every admitted
 * family: a finite inductive with behaviour, a structure with behaviour, a generic structure, a
 * polymorphic function, higher-order values, structural recursion over both a user inductive and a
 * `List`, pattern matching over a tag union, a payload union, a `List` and an `Option`, `Except`,
 * `Nat`, `String`, and the admitted collection operations.
 */
const LIBRARY: Readonly<Record<string, string>> = {
  'Library.Core': [
    'namespace Library.Core',
    '',
    '/-- A severity a diagnostic can carry. -/',
    'inductive Severity where',
    '  | info',
    '  | warning',
    '  | failure',
    '',
    '/-- How strongly a severity blocks publication. -/',
    'def Severity.weight (severity : Severity) : Nat :=',
    '  match severity with',
    '  | .info => 0',
    '  | .warning => 1',
    '  | .failure => 2',
    '',
    'def Severity.blocks (severity : Severity) : Bool := 1 < severity.weight',
    '',
    '/-- A pair, generic in both components. -/',
    'structure Pair (first : Type) (second : Type) where',
    '  left : first',
    '  right : second',
    '',
    'def Pair.swap {a b : Type} (pair : Pair a b) : Pair b a :=',
    '  { left := pair.right, right := pair.left }',
    '',
    'def Pair.mapLeft {a b c : Type} (pair : Pair a b) (step : a → c) : Pair c b :=',
    '  { left := step pair.left, right := pair.right }',
    '',
    'end Library.Core',
    '',
  ].join('\n'),
  'Library.Diagnostics': [
    'import Library.Core',
    '',
    'namespace Library.Diagnostics',
    '',
    'open Library.Core',
    '',
    '/-- One diagnostic a check produced. -/',
    'structure Diagnostic where',
    '  code : String',
    '  severity : Severity',
    '',
    'def Diagnostic.escalate (diagnostic : Diagnostic) : Diagnostic :=',
    '  { diagnostic with severity := .failure }',
    '',
    'def escalated (diagnostics : List Diagnostic) : List Diagnostic :=',
    '  diagnostics.map (fun diagnostic => diagnostic.escalate)',
    '',
    'def blocking (diagnostics : List Diagnostic) : List Diagnostic :=',
    '  diagnostics.filter (fun diagnostic => diagnostic.severity.blocks)',
    '',
    'def codes (diagnostics : List Diagnostic) : List String :=',
    '  diagnostics.map (fun diagnostic => diagnostic.code)',
    '',
    '/-- The worst severity in a list, folded left to right. -/',
    'def worst (diagnostics : List Diagnostic) : Severity :=',
    '  diagnostics.foldl',
    '    (fun accumulator diagnostic =>',
    '      if accumulator.weight < diagnostic.severity.weight then diagnostic.severity else accumulator)',
    '    Severity.info',
    '',
    'def joined (values : List String) : String :=',
    '  match values with',
    '  | [] => ""',
    '  | head :: tail => head ++ joined tail',
    '',
    'end Library.Diagnostics',
    '',
  ].join('\n'),
  'Library.Report': [
    'import Library.Diagnostics',
    '',
    'namespace Library.Report',
    '',
    'open Library.Core',
    'open Library.Diagnostics',
    '',
    '/-- A tree of checks, so the report walks a recursive structure. -/',
    'inductive Check where',
    '  | leaf (diagnostic : Diagnostic)',
    '  | both (left : Check) (right : Check)',
    '',
    'def Check.collect (check : Check) : List Diagnostic :=',
    '  match check with',
    '  | .leaf diagnostic => [diagnostic]',
    '  | .both left right => left.collect ++ right.collect',
    '',
    'def Check.count (check : Check) : Nat := check.collect.length',
    '',
    '/-- The monomorphic shape a caller receives. -/',
    'structure Summary where',
    '  total : Nat',
    '  codes : String',
    '',
    'def counted (check : Check) : Pair Nat String :=',
    '  { left := check.count, right := joined (codes check.collect) }',
    '',
    'def summary (check : Check) : Summary :=',
    '  let pair := (counted check).swap',
    '  { total := pair.right, codes := pair.left }',
    '',
    '/-- The report a caller receives, or the first blocking code that stopped it. -/',
    'def publish (check : Check) : Except String Severity :=',
    '  let diagnostics := check.collect',
    '  let blockers := blocking diagnostics',
    '  match blockers.head? with',
    '  | none => .ok (worst diagnostics)',
    '  | some blocker => .error blocker.code',
    '',
    'def allInfo (check : Check) : Bool :=',
    '  check.collect.all (fun diagnostic => !diagnostic.severity.blocks)',
    '',
    'def escalatedCodes (check : Check) : List String := codes (escalated check.collect)',
    '',
    '/-- A root whose parameters exercise the primitive and collection boundary. -/',
    'def weighted (floor : Nat) (extras : List Nat) : Nat :=',
    '  extras.foldl (fun accumulator extra => accumulator + extra) floor',
    '',
    'end Library.Report',
    '',
  ].join('\n'),
};

const ROOTS = [
  'Library.Report.publish',
  'Library.Report.summary',
  'Library.Report.allInfo',
  'Library.Report.escalatedCodes',
  'Library.Report.weighted',
] as const;

let library: LeanLibraryFixture;
let emitted: LeanToTypeScriptPackage;

/** The generated module's exports, transpiled and evaluated, so a decoder can be run against it. */
function evaluateGeneratedModuleExports(code: string): Record<string, unknown> {
  const javascript = ts.transpileModule(code, {
    compilerOptions: { module: ts.ModuleKind.CommonJS, target: ts.ScriptTarget.ES2022 },
  }).outputText;
  const exported: Record<string, unknown> = {};
  new Function('exports', javascript)(exported);
  return exported;
}

function moduleCode(path: string): string {
  const module = emitted.modules.find((candidate) => candidate.path === path);
  if (module === undefined) throw new TypeError(`generated package has no module at ${path}`);
  return module.code;
}

beforeAll(() => {
  library = createLeanLibraryFixture(LIBRARY);
  const sourcePath = library.sources.get('Library.Report');
  if (sourcePath === undefined) throw new TypeError('the library fixture has no entry module');
  emitted = compileLeanToTypeScript({
    projectRoot: library.projectRoot,
    moduleName: 'Library.Report',
    sourcePath,
    declarations: [...ROOTS],
  });
}, 300_000);

afterAll(() => {
  library.dispose();
});

describe('admitted Lean families lower into one organized TypeScript package', () => {
  test('places each declaration in the file its own Lean module spells', () => {
    expect(emitted.modules.map((module) => module.path)).toEqual([
      'Library/Core.ts',
      'Library/Diagnostics.ts',
      'Library/Report.ts',
      'tslean-runtime.ts',
    ]);
    expect(emitted.manifest.semantic.modules.map((module) => module.leanModule)).toEqual([
      'Library.Core',
      'Library.Diagnostics',
      'Library.Report',
      '',
    ]);
    // Ownership, not proximity: `Severity` is declared by Core and only referred to elsewhere.
    expect(moduleCode('Library/Core.ts')).toContain('export abstract class Severity {');
    expect(moduleCode('Library/Diagnostics.ts')).not.toContain('class Severity');
    expect(moduleCode('Library/Diagnostics.ts')).toContain('import { Severity, type SeverityData } from "./Core.js";');
    expect(moduleCode('Library/Report.ts')).toContain('} from "./Diagnostics.js";');
  });

  test('emits a finite inductive with behaviour as a value object with one class per constructor', () => {
    const code = moduleCode('Library/Core.ts');
    expect(code).toContain('public abstract weight(): bigint;');
    expect(code).toContain('public blocks(): boolean {');
    expect(code).toContain('class InfoSeverity extends Severity {');
    expect(code).toContain('public override weight(): bigint {\n        return 0n;');
    expect(code).toContain('public static get failure(): Severity {');
    // The tag is the data image of a nullary-only inductive, so it round-trips as its own kind.
    expect(code).toContain('export type SeverityData = Severity["kind"];');
  });

  test('emits a generic structure and a polymorphic method with positional type parameters', () => {
    const code = moduleCode('Library/Core.ts');
    expect(code).toContain('export interface PairInit<A, B> {');
    expect(code).toContain('export class Pair<A, B> {');
    expect(code).toContain('public swap(): Pair<B, A> {');
    // A generic type has no data image, so no codec claims to represent one instantiation.
    expect(code).not.toContain('PairData');
    expect(code).not.toContain('class Pair<A, B> {\n    public static fromData');
  });

  test('emits higher-order collection operations as the arrows the Lean source wrote', () => {
    const code = moduleCode('Library/Diagnostics.ts');
    expect(code).toContain('return diagnostics.map((diagnostic: Diagnostic) => diagnostic.code);');
    expect(code).toContain('return diagnostics.filter((diagnostic: Diagnostic) => diagnostic.severity.blocks());');
    expect(code).toContain('diagnostics.reduce((accumulator: Severity, diagnostic: Diagnostic) =>');
    expect(moduleCode('Library/Report.ts')).toContain(
      'check.collect().every((diagnostic: Diagnostic) => !diagnostic.severity.blocks())',
    );
  });

  test('emits structural recursion over a List as a guarded destructuring, not a guess', () => {
    const code = moduleCode('Library/Diagnostics.ts');
    expect(code).toContain('export function joined(values: readonly string[]): string {');
    expect(code).toContain('if (values.length === 0) {');
    expect(code).toContain('const head = values[0];');
    expect(code).toContain('const tail = values.slice(1);');
    expect(code).toContain('return head + joined(tail);');
  });

  test('emits Option and Except as one shared tagged representation', () => {
    const runtime = moduleCode('tslean-runtime.ts');
    expect(runtime).toContain('export type Option<A> = {\n    readonly kind: "none";\n}');
    expect(runtime).toContain('export type Except<E, A> = {\n    readonly kind: "error";');
    const report = moduleCode('Library/Report.ts');
    expect(report).toContain('export function publish(check: Check): Except<string, Severity> {');
    expect(report).toContain('return { kind: "ok", value: worst(diagnostics) };');
    expect(report).toContain('if (value.kind === "none") {');
  });

  test('emits a payload-carrying inductive as an abstract base with dispatched overrides', () => {
    const code = moduleCode('Library/Report.ts');
    expect(code).toContain('public abstract collect(): readonly Diagnostic[];');
    // Every case class is exported alongside its abstract base: the cases are what a discriminated
    // union is for, so a consumer codec can name them instead of reaching a module-private class.
    expect(code).toContain('export class LeafCheck extends Check {');
    expect(code).toContain('export class BothCheck extends Check {');
    expect(code).toContain('return [this.diagnostic];');
    expect(code).toContain('return [...this.left.collect(), ...this.right.collect()];');
    expect(code).toContain('public count(): bigint {\n        return BigInt(this.collect().length);');
  });

  test('freezes every emitted value object, including each nullary singleton', () => {
    // A value object is immutable, so each constructor freezes the instance it built. A nullary
    // case is reached through a getter over one frozen singleton rather than a fresh allocation.
    const core = moduleCode('Library/Core.ts');
    expect(core).toContain('export class InfoSeverity extends Severity {');
    expect(core).toContain('Object.freeze(this);');
    expect(core).toContain('public static get failure(): Severity {');
  });

  test('parses external input at the boundary instead of asserting past it', () => {
    const report = moduleCode('Library/Report.ts');
    expect(report).toContain('public static fromData(value: GeneratedData): Check {');
    expect(report).toContain('const data = requireDataFields(value, "Check.leaf", ["kind", "diagnostic"]);');
    const runtime = moduleCode('tslean-runtime.ts');
    expect(runtime).toContain('export function requireString(value: GeneratedData, name: string): string {');
    expect(runtime).toContain('export function requireNat(value: GeneratedData, name: string): bigint {');
    expect(runtime).toContain('typeof value === "bigint" && value >= 0n');
    // A root's result travels the other way, so nothing decodes it.
    expect(runtime).not.toContain('requireBoolean');
  });

  test('prints one shared declaration for the guarded opcode the library reaches', () => {
    const runtime = moduleCode('tslean-runtime.ts');
    expect(runtime).toContain('function listHead<A>(value: readonly A[])');
    // Nothing in the library subtracts, so its guarded helper is not printed.
    expect(runtime).not.toContain('function natSubtract(');
  });

  test('records every generated declaration against the Lean span it came from', () => {
    const declarations = emitted.manifest.semantic.modules.flatMap((module) => module.declarations);
    const publish = declarations.find((declaration) => declaration.declaration === 'Library.Report.publish');
    expect(publish?.emitted).toBe('publish');
    expect(publish?.span.startLine).toBeGreaterThan(0);
    expect(publish?.line).toBeGreaterThan(0);
    for (const declaration of declarations) {
      expect(declaration.span.endLine).toBeGreaterThanOrEqual(declaration.span.startLine);
    }
  });

  test('is a function of the Lean source alone', () => {
    const sourcePath = library.sources.get('Library.Report');
    if (sourcePath === undefined) throw new TypeError('the library fixture has no entry module');
    const again = compileLeanToTypeScript({
      projectRoot: library.projectRoot,
      moduleName: 'Library.Report',
      sourcePath,
      declarations: [...ROOTS],
    });
    expect(again.modules).toEqual(emitted.modules);
    expect(again.manifest.semantic).toEqual(emitted.manifest.semantic);
  }, 300_000);
});

describe('generated structure comes from elaborated evidence, never from a name', () => {
  test('a method is a method because its receiver parameter carries its own namespace type', () => {
    // `Severity.weight` takes a `Severity`, so it is dispatched inside the class. `Library.Report`
    // also declares `counted`, whose name shares no namespace with a type: it stays a function.
    expect(moduleCode('Library/Core.ts')).toContain('public abstract weight(): bigint;');
    expect(moduleCode('Library/Report.ts')).toContain('function counted(check: Check): Pair<bigint, string> {');
    expect(moduleCode('Library/Report.ts')).not.toContain('public counted(');
  });

  test('a declaration whose name only looks like a method stays a plain function', () => {
    const fixture = createLeanProjectFixture(
      [
        'namespace Fixture',
        'structure Config where',
        '  enabled : Bool',
        '-- The namespace matches, but no parameter carries a Config, so this is not dot notation.',
        'def Config.describe (flag : Bool) : Bool := !flag',
        'def entry (config : Config) : Bool := Config.describe config.enabled',
        'end Fixture',
        '',
      ].join('\n'),
    );
    try {
      const compiled = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: ['Fixture.entry'],
      });
      const [module] = compiled.modules;
      if (module === undefined) throw new TypeError('the compilation produced no module');
      expect(module.code).toContain('function describe(flag: boolean): boolean {');
      expect(module.code).toContain('return describe(config.enabled);');
      // No class: a structure with no behaviour of its own stays structural.
      expect(module.code).toContain('export interface Config {');
      expect(module.code).not.toContain('class Config');
    } finally {
      fixture.dispose();
    }
  }, 300_000);

  test('a dot-notation method declared apart from its receiver is refused', () => {
    const fixture = createLeanLibraryFixture({
      'Split.Data': ['namespace Split.Data', 'structure Config where', '  enabled : Bool', 'end Split.Data', ''].join(
        '\n',
      ),
      'Split.Entry': [
        'import Split.Data',
        'namespace Split',
        'open Split.Data',
        'def Data.Config.toggle (config : Config) : Config := { config with enabled := !config.enabled }',
        'def entry (config : Config) : Bool := (Data.Config.toggle config).enabled',
        'end Split',
        '',
      ].join('\n'),
    });
    try {
      const sourcePath = fixture.sources.get('Split.Entry');
      if (sourcePath === undefined) throw new TypeError('the fixture has no entry module');
      expect(() =>
        compileLeanToTypeScript({
          projectRoot: fixture.projectRoot,
          moduleName: 'Split.Entry',
          sourcePath,
          declarations: ['Split.entry'],
        }),
      ).toThrowError(/declare it beside its type/u);
    } finally {
      fixture.dispose();
    }
  }, 300_000);

  test('the generated tree type-checks as one program in the layout a consumer receives', () => {
    // `compileLeanToTypeScript` already type-checks the package it returns; this writes the same
    // bytes into the layout a consumer receives and checks them again under `noUnusedLocals`, so a
    // helper the package does not need would fail here too.
    const root = mkdtempSync(join(tmpdir(), 'tslean-coverage-typecheck-'));
    try {
      const paths = emitted.modules.map((module) => {
        const path = join(root, module.path);
        mkdirSync(dirname(path), { recursive: true });
        writeFileSync(path, module.code, 'utf8');
        return path;
      });
      const program = ts.createProgram(paths, {
        module: ts.ModuleKind.NodeNext,
        moduleResolution: ts.ModuleResolutionKind.NodeNext,
        noEmit: true,
        noUnusedLocals: true,
        lib: ['lib.es2022.d.ts'],
        strict: true,
        target: ts.ScriptTarget.ES2022,
      });
      const diagnostics = ts
        .getPreEmitDiagnostics(program)
        .map((diagnostic) => ts.flattenDiagnosticMessageText(diagnostic.messageText, '\n'));
      expect(diagnostics).toEqual([]);
    } finally {
      rmSync(root, { force: true, recursive: true });
    }
  });
});

describe('constructs with no deterministic representation fail before publication', () => {
  const ADVERSARIAL = [
    'namespace Adversarial',
    '',
    'inductive Colour where',
    '  | red',
    '  | green',
    '',
    'partial def loops (value : Nat) : Nat := loops value',
    '',
    'unsafe def unsafely (value : Bool) : Bool := value',
    '',
    'opaque hidden (value : Bool) : Bool',
    '',
    'axiom assumed (value : Bool) : Bool',
    '',
    'def dependentResult (flag : Bool) : (if flag then Bool else Bool) :=',
    '  match flag with',
    '  | true => true',
    '  | false => false',
    '',
    'def withInstance {a : Type} [BEq a] (left right : a) : Bool := left == right',
    '',
    'def effectful : IO Unit := pure ()',
    '',
    'def usesInt (value : Int) : Int := value + 1',
    '',
    'def usesFloat (value : Float) : Float := value',
    '',
    'def usesChar (value : Char) : Char := value',
    '',
    'def natMatched (value : Nat) : Bool :=',
    '  match value with',
    '  | 0 => true',
    '  | _ + 1 => false',
    '',
    'def twoDiscriminants (left right : Colour) : Bool :=',
    '  match left, right with',
    '  | .red, .red => true',
    '  | _, _ => false',
    '',
    'def letInArgument (condition : Bool) : Bool :=',
    '  Bool.and (let inner := condition; inner) true',
    '',
    'def stringLength (value : String) : Nat := value.length',
    '',
    'theorem proved : True := trivial',
    '',
    'def polymorphicRoot {a : Type} (value : a) : a := value',
    '',
    'def guessedRecursion (value : Nat) : Nat :=',
    '  if value < 2 then 0 else guessedRecursion (value - 2) + 1',
    'termination_by value',
    'decreasing_by omega',
    '',
    'end Adversarial',
    '',
  ].join('\n');

  let fixture: LeanProjectFixture;

  beforeAll(() => {
    fixture = createLeanProjectFixture(ADVERSARIAL);
  });

  afterAll(() => {
    fixture.dispose();
  });

  function compile(declaration: string): LeanToTypeScriptPackage {
    return compileLeanToTypeScript({
      projectRoot: fixture.projectRoot,
      moduleName: 'Fixture',
      sourcePath: fixture.sourcePath,
      declarations: [declaration],
    });
  }

  test.each([
    ['a partial definition', 'Adversarial.loops', /partial definitions are outside the checked fragment/u],
    ['an unsafe definition', 'Adversarial.unsafely', /unsafe definitions are outside the checked fragment/u],
    ['an opaque definition', 'Adversarial.hidden', /opaque or partial definitions are outside the checked fragment/u],
    ['an axiom', 'Adversarial.assumed', /outside the checked fragment/u],
    ['a dependent result type', 'Adversarial.dependentResult', /outside the (?:checked fragment|frozen target)/u],
    ['an instance parameter', 'Adversarial.withInstance', /instance parameters/u],
    ['an effectful definition', 'Adversarial.effectful', /outside the (?:checked fragment|frozen target)/u],
    ['a Float', 'Adversarial.usesFloat', /Float is outside the surface: no type form carries an IEEE double/u],
    ['a match on Nat', 'Adversarial.natMatched', /a match on Nat is outside this fragment version/u],
    [
      'a match on more than one discriminant',
      'Adversarial.twoDiscriminants',
      /a match on more than one discriminant is outside this fragment version/u,
    ],
    [
      'a let inside an argument',
      'Adversarial.letInArgument',
      /a let inside an argument is outside the checked fragment/u,
    ],
    ['a proof as a root', 'Adversarial.proved', /root is not a function/u],
    ['a polymorphic root', 'Adversarial.polymorphicRoot', /a root's boundary is monomorphic/u],
  ])(
    'refuses %s',
    (_label, declaration, diagnostic) => {
      let thrown: unknown;
      try {
        compile(declaration);
      } catch (error: unknown) {
        thrown = error;
      }
      expect(thrown).toBeInstanceOf(Error);
      expect((thrown as Error).message).toMatch(diagnostic);
    },
    300_000,
  );

  test.each([
    // The three rows the surface gained in v6, taken from the same adversarial fixture that used
    // to prove them refused. Each one has an exact target image rather than an approximation.
    ['an Int', 'Adversarial.usesInt', 'export function usesInt(value: bigint): bigint {', 'return value + 1n;'],
    ['a Char', 'Adversarial.usesChar', 'export function usesChar(value: string): string {', 'return value;'],
    [
      'a String length',
      'Adversarial.stringLength',
      'export function stringLength(value: string): bigint {',
      'return BigInt([...value].length);',
    ],
  ])(
    'admits %s, which v6 carries with an exact image',
    (_label, declaration, signature, body) => {
      const compiled = compile(declaration);
      const [module] = compiled.modules;
      if (module === undefined) throw new TypeError('the compilation produced no module');
      expect(module.code).toContain(signature);
      expect(module.code).toContain(body);
    },
    300_000,
  );

  test('admits a well-founded recursion Lean proved, and emits the same call graph', () => {
    const compiled = compile('Adversarial.guessedRecursion');
    const [module] = compiled.modules;
    if (module === undefined) throw new TypeError('the compilation produced no module');
    expect(module.code).toContain('export function guessedRecursion(value: bigint): bigint {');
    expect(module.code).toContain('return guessedRecursion(natSubtract(value, 2n)) + 1n;');
    expect(module.code).toContain('return left < right ? 0n : left - right;');
  }, 300_000);

  test('attributes every refusal to the declaration it was reading', () => {
    let thrown: unknown;
    try {
      compile('Adversarial.natMatched');
    } catch (error: unknown) {
      thrown = error;
    }
    expect(thrown).toBeInstanceOf(UnsupportedLeanFragmentError);
    expect((thrown as UnsupportedLeanFragmentError).declaration).toBe('Adversarial.natMatched');
    expect((thrown as UnsupportedLeanFragmentError).code).toBe('UNSUPPORTED_LEAN_FRAGMENT');
  }, 300_000);
});

describe('generated names never collide with the representation or with the runtime', () => {
  function compileSource(source: string, declarations: readonly string[]): string {
    const fixture = createLeanProjectFixture(source);
    try {
      const compiled = compileLeanToTypeScript({
        projectRoot: fixture.projectRoot,
        moduleName: 'Fixture',
        sourcePath: fixture.sourcePath,
        declarations: [...declarations],
      });
      const [module] = compiled.modules;
      if (module === undefined) throw new TypeError('the compilation produced no module');
      return module.code;
    } finally {
      fixture.dispose();
    }
  }

  test('a Lean binder named after a generated validator does not shadow it', () => {
    const code = compileSource(
      [
        'namespace Fixture',
        'structure Box where',
        '  flag : Bool',
        '-- `requireDataFields` is the generated boundary validator the same body reaches.',
        'def reads (requireDataFields : Box) : Bool := requireDataFields.flag',
        'end Fixture',
        '',
      ].join('\n'),
      ['Fixture.reads'],
    );
    expect(code).toContain('function requireDataFields(value: GeneratedData, name: string, fields: readonly string[])');
    expect(code).toContain('export function reads(requireDataFields$2: Box): boolean {');
    expect(code).toContain('return requireDataFields$2.flag;');
    expect(code).not.toContain('return requireDataFields.flag;');
  }, 300_000);

  test('a Lean binder named after a global the emitted code reads does not shadow it', () => {
    const code = compileSource(
      [
        'namespace Fixture',
        '-- `BigInt` and `Object` are read by `List.length` and by every frozen value object.',
        'def counts (BigInt : List Bool) (Object : Bool) : Nat :=',
        '  if Object then BigInt.length else 0',
        'end Fixture',
        '',
      ].join('\n'),
      ['Fixture.counts'],
    );
    expect(code).toContain('export function counts(BigInt$2: readonly boolean[], Object$2: boolean): bigint {');
    expect(code).toContain('return BigInt(BigInt$2.length);');
  }, 300_000);

  test('a nested abstraction keeps reading the enclosing binder it captures', () => {
    // The outer binder is spelled like the truncated-subtraction helper the same body calls, so it
    // is renamed and the call is not. The abstraction captures it: one allocator across the nesting
    // is what keeps the capture pointing at the binder the Lean body meant.
    const code = compileSource(
      [
        'namespace Fixture',
        'def scaled (values : List Nat) : List Nat :=',
        '  let natSubtract := 3',
        '  values.map (fun value => natSubtract - value)',
        'end Fixture',
        '',
      ].join('\n'),
      ['Fixture.scaled'],
    );
    expect(code).toContain('function natSubtract(left: bigint, right: bigint): bigint {');
    expect(code).toContain('const natSubtract$2 = 3n;');
    expect(code).toContain('return values.map((value: bigint) => natSubtract(natSubtract$2, value));');
  }, 300_000);

  test('drops a binding the Lean body never reads', () => {
    const code = compileSource(
      [
        'namespace Fixture',
        'def scaled (values : List Nat) : List Nat :=',
        '  let unread := 3',
        '  values.map (fun value => value + value)',
        'end Fixture',
        '',
      ].join('\n'),
      ['Fixture.scaled'],
    );
    expect(code).not.toContain('unread');
    expect(code).toContain('return values.map((value: bigint) => value + value);');
  }, 300_000);

  test('names only the constructor fields an alternative reads', () => {
    const code = compileSource(
      [
        'namespace Fixture',
        'inductive Shape where',
        '  | dot',
        '  | line (length : Nat) (label : String)',
        'def span (shape : Shape) : Nat :=',
        '  match shape with',
        '  | .dot => 0',
        '  | .line length _ => length',
        'def heads (values : List Nat) : Nat :=',
        '  match values with',
        '  | [] => 0',
        '  | head :: _ => head',
        'end Fixture',
        '',
      ].join('\n'),
      ['Fixture.span', 'Fixture.heads'],
    );
    expect(code).toContain('const length = shape.length;');
    expect(code).not.toContain('const label =');
    expect(code).toContain('const head = values[0];');
    expect(code).not.toContain('const tail =');
  }, 300_000);

  test('compares a nested list and a nested Option elementwise, not by identity', () => {
    const code = compileSource(
      [
        'namespace Fixture',
        'structure Grid where',
        '  rows : List (List Nat)',
        '  labels : List (Option String)',
        '  chosen : Option (List Nat)',
        'def Grid.width (grid : Grid) : Nat := grid.rows.length',
        'def widthOf (grid : Grid) : Nat := grid.width',
        'end Fixture',
        '',
      ].join('\n'),
      ['Fixture.widthOf'],
    );
    // One shared comparison per mapped type, so nesting cannot make an inner binder shadow an
    // outer one and cannot read a payload whose tag a nested callback has un-narrowed.
    expect(code).toContain(
      'function equalList<A>(left: readonly A[], right: readonly A[], same: (left: A, right: A) => boolean): boolean {',
    );
    expect(code).toContain('function equalOption<A>(');
    expect(code).toContain(
      'equalList(this.rows, other.rows, (left, right) => equalList(left, right, (left$2, right$2) => left$2 === right$2))',
    );
    const exported = evaluateGeneratedModuleExports(code);
    const grid = exported['Grid'];
    if (typeof grid !== 'function') throw new TypeError('the generated module did not export Grid');
    const build = (rows: readonly (readonly bigint[])[], label: string, chosen: readonly bigint[]): unknown =>
      Reflect.construct(grid, [
        {
          rows,
          labels: [{ kind: 'some', value: label }, { kind: 'none' }],
          chosen: { kind: 'some', value: chosen },
        },
      ]);
    const equals = (left: unknown, right: unknown): unknown =>
      (left as { equals: (other: unknown) => unknown }).equals(right);
    const base = build([[1n, 2n], [3n]], 'a', [4n]);
    expect(equals(base, build([[1n, 2n], [3n]], 'a', [4n]))).toBe(true);
    // Each of these differs from `base` only inside a nested position.
    expect(equals(base, build([[1n, 9n], [3n]], 'a', [4n]))).toBe(false);
    expect(equals(base, build([[1n, 2n], [3n]], 'b', [4n]))).toBe(false);
    expect(equals(base, build([[1n, 2n], [3n]], 'a', [9n]))).toBe(false);
    expect(equals(base, build([[1n, 2n]], 'a', [4n]))).toBe(false);
  }, 300_000);

  test('refuses a prototype key on a type the representation emits as a class', () => {
    let thrown: unknown;
    try {
      compileSource(
        [
          'namespace Fixture',
          'structure Boxed where',
          '  __proto__ : Bool',
          'def Boxed.read (boxed : Boxed) : Bool := boxed.__proto__',
          'def entry (boxed : Boxed) : Bool := boxed.read',
          'end Fixture',
          '',
        ].join('\n'),
        ['Fixture.entry'],
      );
    } catch (error: unknown) {
      thrown = error;
    }
    expect(thrown).toBeInstanceOf(Error);
    expect((thrown as Error).message).toMatch(/field __proto__ has no own-property form on the class/u);
    expect((thrown as Error).message).toMatch(/rename it in the Lean source/u);
  }, 300_000);

  test.each([
    [
      'a constructor named after the tag constructor',
      [
        'namespace Fixture',
        'inductive Choice where',
        '  | from',
        '  | other',
        'def Choice.rank (choice : Choice) : Nat :=',
        '  match choice with',
        '  | .from => 0',
        '  | .other => 1',
        'def entry (choice : Choice) : Nat := choice.rank',
        'end Fixture',
        '',
      ],
      'Fixture.entry',
      /constructor from collides with the tag constructor/u,
    ],
    [
      'a field named after the discriminant',
      [
        'namespace Fixture',
        'inductive Shape where',
        '  | dot',
        '  | line (kind : Bool)',
        'def entry (shape : Shape) : Bool :=',
        '  match shape with',
        '  | .dot => false',
        '  | .line kind => kind',
        'end Fixture',
        '',
      ],
      'Fixture.entry',
      /field kind collides with the constructor discriminant/u,
    ],
    [
      'a dot-notation method named after the data image',
      [
        'namespace Fixture',
        'structure Box where',
        '  flag : Bool',
        'def Box.toData (box : Box) : Bool := box.flag',
        'def entry (box : Box) : Bool := box.toData',
        'end Fixture',
        '',
      ],
      'Fixture.entry',
      /dot-notation method toData collides with the data image/u,
    ],
  ])(
    'refuses %s',
    (_label, lines, root, diagnostic) => {
      let thrown: unknown;
      try {
        compileSource(lines.join('\n'), [root]);
      } catch (error: unknown) {
        thrown = error;
      }
      expect(thrown).toBeInstanceOf(Error);
      expect((thrown as Error).message).toMatch(diagnostic);
      expect((thrown as Error).message).toMatch(/rename it in the Lean source/u);
    },
    300_000,
  );

  test('refuses an applied projection, which is a field read where a bound function belongs', () => {
    let thrown: unknown;
    try {
      compileSource(
        [
          'namespace Fixture',
          'structure Box where',
          '  step : Bool → Bool',
          'def entry (box : Box) (flag : Bool) : Bool := box.step flag',
          'end Fixture',
          '',
        ].join('\n'),
        ['Fixture.entry'],
      );
    } catch (error: unknown) {
      thrown = error;
    }
    expect(thrown).toBeInstanceOf(Error);
    // The root's own boundary is refused first, because a structure whose field carries an arrow
    // has no data image a caller could send: the parameter is the surface a consumer touches, so
    // it is refused before the body the compiler would have read.
    expect((thrown as Error).message).toMatch(/parameter 0: Fixture\.Box has no data image/u);
  }, 300_000);

  test('refuses a termination proof that was admitted rather than checked', () => {
    let thrown: unknown;
    try {
      compileSource(
        [
          'namespace Fixture',
          'def halve (value : Nat) : Nat :=',
          '  if value < 2 then 0 else halve (value - 2) + 1',
          'termination_by value',
          'decreasing_by sorry',
          'end Fixture',
          '',
        ].join('\n'),
        ['Fixture.halve'],
      );
    } catch (error: unknown) {
      thrown = error;
    }
    expect(thrown).toBeInstanceOf(Error);
    expect((thrown as Error).message).toMatch(/depends on sorry, so its proof was admitted rather than checked/u);
  }, 300_000);

  test('refuses a definition resting on an axiom of its own', () => {
    let thrown: unknown;
    try {
      compileSource(
        [
          'namespace Fixture',
          'axiom assumed : Bool',
          'noncomputable def entry : Bool := assumed',
          'end Fixture',
          '',
        ].join('\n'),
        ['Fixture.entry'],
      );
    } catch (error: unknown) {
      thrown = error;
    }
    expect(thrown).toBeInstanceOf(Error);
    expect((thrown as Error).message).toMatch(/outside the checked fragment/u);
  }, 300_000);

  test('accepts only well-formed UTF-16 at the String boundary', () => {
    const code = compileSource(
      ['namespace Fixture', 'def identity (text : String) : String := text', 'end Fixture', ''].join('\n'),
      ['Fixture.identity'],
    );
    expect(code).toContain('must contain only well-formed UTF-16 code units');
    const exported = evaluateGeneratedModuleExports(code);
    const requireString = exported['requireString'];
    if (typeof requireString !== 'function') throw new TypeError('the generated module did not export requireString');
    const decode = requireString as (value: unknown, name: string) => string;
    const reject = (value: string): void =>
      expect(() => decode(value, 'text')).toThrowError(/^text must contain only well-formed UTF-16 code units$/u);
    reject('\ud800'); // lone high surrogate
    reject('\udc00'); // lone low surrogate
    reject('\udc00\ud800'); // reversed pair
    reject('\ud800\ud800'); // high surrogate followed by high surrogate
    const supplementary = '\ud83d\ude00';
    expect(decode(supplementary, 'text')).toBe(supplementary);
  }, 300_000);

  test('refuses a sparse array at the decode boundary', () => {
    const code = compileSource(
      [
        'namespace Fixture',
        'def total (values : List Nat) : Nat :=',
        '  values.foldl (fun accumulator value => accumulator + value) 0',
        'end Fixture',
        '',
      ].join('\n'),
      ['Fixture.total'],
    );
    expect(code).toContain('if (!Object.hasOwn(value, index)) {');
    const exported = evaluateGeneratedModuleExports(code);
    const requireList = exported['requireList'];
    const requireNat = exported['requireNat'];
    if (typeof requireList !== 'function' || typeof requireNat !== 'function') {
      throw new TypeError('the generated module did not export its list boundary');
    }
    expect(requireList([1n, 2n], 'values', requireNat)).toEqual([1n, 2n]);
    const sparse: unknown[] = [1n];
    sparse[2] = 3n;
    expect(() => requireList(sparse, 'values', requireNat)).toThrowError(/values\[1\] is missing/u);
  }, 300_000);
});
