import { afterAll, beforeAll, describe, expect, test } from 'vitest';
import { compileLeanToTypeScript, type LeanToTypeScriptPackage } from '../src/lean-to-typescript/index.js';
import { createLeanProjectFixture, type LeanProjectFixture } from './helpers/lean-project-fixture.js';

/**
 * The match and binding forms, admitted and refused.
 *
 * Every form here lowers into IR the fragment already carried, so what these tests pin is the
 * *shape* each Lean form becomes and the reason each residue is refused.
 * `lean/TSLean/LeanToTypeScript/Semantics/MatchForms.lean` states the correspondence between the two.
 */
const ADMITTED = [
  'namespace Forms',
  '',
  'inductive Lane where',
  '  | fast',
  '  | slow',
  '',
  'inductive Credential where',
  '  | present',
  '  | absent',
  '',
  '/-- A `Nat` pattern. -/',
  'def stepsRemaining (budget : Nat) : Nat :=',
  '  match budget with',
  '  | 0 => 0',
  '  | next + 1 => next',
  '',
  '/-- A `Nat` pattern whose successor arm reads the predecessor twice. -/',
  'def doubled (budget : Nat) : Nat :=',
  '  match budget with',
  '  | 0 => 0',
  '  | next + 1 => next + next',
  '',
  '/-- Two discriminants, with a wildcard last arm. -/',
  'def admits (lane : Lane) (credential : Credential) : Bool :=',
  '  match lane, credential with',
  '  | .fast, .present => true',
  '  | .slow, .present => false',
  '  | _, _ => false',
  '',
  '/-- Two discriminants, one binding a payload and one a wildcard. -/',
  'def preferred (requested : Option Lane) (credential : Credential) : Lane :=',
  '  match requested, credential with',
  '  | some lane, .present => lane',
  '  | some _, .absent => Lane.slow',
  '  | none, _ => Lane.slow',
  '',
  '/-- Three discriminants, one of them a `Nat`. -/',
  'def clamped (lane : Lane) (budget : Nat) (credential : Credential) : Lane :=',
  '  match lane, budget, credential with',
  '  | .fast, 0, _ => Lane.slow',
  '  | .fast, _ + 1, .present => Lane.fast',
  '  | .fast, _ + 1, .absent => Lane.slow',
  '  | .slow, _, _ => Lane.slow',
  '',
  '/-- A `let` inside an argument, beside a literal. -/',
  'def hoistedBesideLiteral (credential : Credential) : Bool :=',
  '  Bool.and',
  '    (let decided := match credential with',
  '      | .present => true',
  '      | .absent => false',
  '     decided)',
  '    true',
  '',
  '/-- A `let` inside an argument, beside a binder read. -/',
  'def hoistedBesideBinder (lane : Lane) (allowed : Bool) : Bool :=',
  '  Bool.or',
  '    (let fast := match lane with',
  '      | .fast => true',
  '      | .slow => false',
  '     fast)',
  '    allowed',
  '',
  '/-- A universe-polymorphic definition, and a monomorphic root over it. -/',
  'def firstOr.{u} {a : Type u} (fallback : a) (chosen : Option a) : a :=',
  '  match chosen with',
  '  | none => fallback',
  '  | some value => value',
  '',
  'def laneOr (chosen : Option Lane) : Lane := firstOr Lane.slow chosen',
  '',
  '/-- A dependent match whose motive mentions the discriminant inside a subtype predicate. -/',
  'def atLeastOne (budget : Nat) : { value : Nat // 0 < value + 1 } :=',
  '  match budget with',
  '  | 0 => ⟨0, Nat.succ_pos 0⟩',
  '  | next + 1 => ⟨next + 1, Nat.succ_pos (next + 1)⟩',
  '',
  '/-- A dependent match binding its discriminant equation. -/',
  'def weight (lane : Lane) : Nat :=',
  '  match _h : lane with',
  '  | .fast => 2',
  '  | .slow => 1',
  '',
  'end Forms',
  '',
].join('\n');

const REFUSED = [
  'namespace Residue',
  '',
  'inductive Lane where',
  '  | fast',
  '  | slow',
  '',
  'inductive Credential where',
  '  | present',
  '  | absent',
  '',
  'inductive Colour where',
  '  | red',
  '  | green',
  '  | blue',
  '',
  'structure Window where',
  '  lower : Nat',
  '  upper : Nat',
  '',
  '/-- A nested decision whose level is a `List`. -/',
  'def listLevel (values : List Lane) (credential : Credential) : Bool :=',
  '  match values, credential with',
  '  | [], .present => true',
  '  | _, _ => false',
  '',
  '/-- A nested decision whose level is a structure. -/',
  'def structureLevel (window : Window) (credential : Credential) : Nat :=',
  '  match window, credential with',
  '  | ⟨lower, _⟩, .present => lower',
  '  | _, _ => 0',
  '',
  '/-- A nested decision whose discriminant computes. -/',
  'def computedDiscriminant (values : List Lane) (credential : Credential) : Bool :=',
  '  match values.length, credential with',
  '  | 0, .present => true',
  '  | _, _ => false',
  '',
  '/-- A nested decision beyond the combination bound. -/',
  'def overBound (a b c d : Colour) : Nat :=',
  '  match a, b, c, d with',
  '  | .red, .red, .red, .red => 1',
  '  | _, _, _, _ => 0',
  '',
  '/-- A `let` inside an argument whose sibling operand computes. -/',
  'def computingSibling (lane : Lane) (credential : Credential) : Bool :=',
  '  Bool.or',
  '    (let fast := match lane with',
  '      | .fast => true',
  '      | .slow => false',
  '     fast)',
  '    (match credential with',
  '      | .present => true',
  '      | .absent => false)',
  '',
  '/-- A `Nat` pattern in argument position. -/',
  'def natInArgument (budget : Nat) (other : Nat) : Nat :=',
  '  Nat.add other (match budget with',
  '    | 0 => 0',
  '    | next + 1 => next)',
  '',
  '/-- A `Nat` literal pattern other than zero. -/',
  'def literalPattern (budget : Nat) : Bool :=',
  '  match budget with',
  '  | 5 => true',
  '  | _ => false',
  '',
  'end Residue',
  '',
].join('\n');

describe('the match and binding forms lower to nested decisions', () => {
  let fixture: LeanProjectFixture;
  let emitted: LeanToTypeScriptPackage;

  beforeAll(() => {
    fixture = createLeanProjectFixture(ADMITTED);
    emitted = compileLeanToTypeScript({
      projectRoot: fixture.projectRoot,
      moduleName: 'Fixture',
      sourcePath: fixture.sourcePath,
      declarations: [
        'Forms.stepsRemaining',
        'Forms.doubled',
        'Forms.admits',
        'Forms.preferred',
        'Forms.clamped',
        'Forms.hoistedBesideLiteral',
        'Forms.hoistedBesideBinder',
        'Forms.laneOr',
        'Forms.atLeastOne',
        'Forms.weight',
      ],
    });
  }, 600_000);

  afterAll(() => {
    fixture.dispose();
  });

  function code(): string {
    const [module] = emitted.modules;
    if (module === undefined) throw new TypeError('the compilation produced no module');
    return module.code;
  }

  test('a `Nat` pattern becomes an ordered decision that binds the predecessor explicitly', () => {
    // The zero test spends `nat.equals` and the predecessor spends `nat.subtract`, both already
    // registry rows with their own model theorem and probes. `MatchForms.natDecision_eval` is the
    // correspondence with Lean's own `match n with | 0 | k + 1`.
    expect(code()).toContain(
      [
        'export function stepsRemaining(budget: bigint): bigint {',
        '    if (budget === 0n) {',
        '        return 0n;',
        '    }',
        '    const predecessor = natSubtract(budget, 1n);',
        '    return predecessor;',
        '}',
      ].join('\n'),
    );
  });

  test('a predecessor read twice is read from one binding', () => {
    expect(code()).toContain('    return predecessor + predecessor;');
  });

  test('a match on two discriminants becomes a lexicographic nest in Lean\u2019s arm order', () => {
    expect(code()).toContain(
      [
        'export function admits(lane: Lane, credential: Credential): boolean {',
        '    if (lane === "fast") {',
        '        if (credential === "present") {',
        '            return true;',
        '        }',
        '        return false;',
        '    }',
        '    if (credential === "present") {',
        '        return false;',
        '    }',
        '    return false;',
        '}',
      ].join('\n'),
    );
  });

  test('a payload position binds its field and a wildcard position reads its discriminant', () => {
    expect(code()).toContain('    const value = requested.value;');
    expect(code()).toContain('export function preferred(requested: Option<Lane>, credential: Credential): Lane {');
  });

  test('a `Nat` level nests inside a tag level', () => {
    expect(code()).toContain('export function clamped(lane: Lane, budget: bigint, credential: Credential): Lane {');
    expect(code()).toContain('        if (budget === 0n) {');
  });

  test('a `let` inside an argument becomes a `const` in front of the call', () => {
    expect(code()).toContain(
      [
        'export function hoistedBesideLiteral(credential: Credential): boolean {',
        '    const decided = credential === "present" ? true : false;',
        '    return decided && true;',
        '}',
      ].join('\n'),
    );
    expect(code()).toContain(
      [
        'export function hoistedBesideBinder(lane: Lane, allowed: boolean): boolean {',
        '    const fast = lane === "fast" ? true : false;',
        '    return fast || allowed;',
        '}',
      ].join('\n'),
    );
  });

  test('a `const` bound to a match is not annotated with the type the match scrutinises', () => {
    // The regression `declaredExpressionType` carries. A match's `type` is the scrutinee's, so
    // annotating the binding declared `const decided: Credential = credential === "present" ? …`,
    // which the generated package's own type check rejects. `compileLeanToTypeScript` type-checks
    // what it returns, so reaching this assertion is already the regression check; the assertion
    // pins the emitted bytes so the annotation cannot come back unnoticed.
    expect(code()).toContain('    const decided = credential === "present" ? true : false;');
    expect(code()).not.toContain('const decided: Credential');
  });

  test('a universe-polymorphic declaration is emitted once, as its level-zero instance', () => {
    expect(code()).toContain('export function laneOr(chosen: Option<Lane>): Lane {');
    expect(code()).toContain('firstOr<Lane>("slow", chosen)');
  });

  test('a dependent match whose motive erases through a subtype keeps the carrier', () => {
    expect(code()).toContain('export function atLeastOne(budget: bigint): bigint {');
  });

  test('a dependent match binding its discriminant equation drops the equation', () => {
    expect(code()).toContain(
      [
        'export function weight(lane: Lane): bigint {',
        '    if (lane === "fast") {',
        '        return 2n;',
        '    }',
        '    return 1n;',
        '}',
      ].join('\n'),
    );
  });

  test('the generated tree type-checks, which is the regression the match annotation carries', () => {
    // `compileLeanToTypeScript` type-checks the tree it returns and refuses to publish one that
    // does not check — that is how `const decided: Credential = credential === "present" ? … `
    // surfaced. So the `beforeAll` compile is itself the type check, and this test states the
    // property it establishes rather than running a second compiler over the same bytes.
    //
    // `tests/lean-to-typescript-language-coverage.test.ts` writes the bytes into a consumer's
    // layout and checks them again under `noUnusedLocals`; that test is currently red on `main`
    // for an unrelated reason (the TypeScript 7 migration has not reached its `ts.ModuleKind`
    // read), so it is not duplicated here.
    expect(emitted.modules.length).toBeGreaterThan(0);
    for (const module of emitted.modules) {
      expect(module.code).not.toContain(': any');
      expect(module.code.endsWith('\n')).toBe(true);
    }
  });

  test('regeneration is byte-identical', () => {
    const again = compileLeanToTypeScript({
      projectRoot: fixture.projectRoot,
      moduleName: 'Fixture',
      sourcePath: fixture.sourcePath,
      declarations: ['Forms.stepsRemaining', 'Forms.admits', 'Forms.hoistedBesideLiteral', 'Forms.weight'],
    });
    const twice = compileLeanToTypeScript({
      projectRoot: fixture.projectRoot,
      moduleName: 'Fixture',
      sourcePath: fixture.sourcePath,
      declarations: ['Forms.stepsRemaining', 'Forms.admits', 'Forms.hoistedBesideLiteral', 'Forms.weight'],
    });
    expect(again.modules.map((module) => module.code)).toEqual(twice.modules.map((module) => module.code));
  }, 600_000);
});

describe('the match and binding residue is refused, each for its own reason', () => {
  let fixture: LeanProjectFixture;

  beforeAll(() => {
    fixture = createLeanProjectFixture(REFUSED);
  });

  afterAll(() => {
    fixture.dispose();
  });

  test.each([
    [
      'a nested decision on a `List`',
      'Residue.listLevel',
      /a nested decision on List is outside this fragment version: its values are decided by a length test or by field reads/u,
    ],
    [
      'a nested decision on a structure',
      'Residue.structureLevel',
      /a nested decision on Residue\.Window is outside this fragment version/u,
    ],
    [
      'a nested decision whose discriminant computes',
      'Residue.computedDiscriminant',
      /reads each of its discriminants more than once, so a computed discriminant is outside this fragment version/u,
    ],
    [
      'a nested decision beyond the combination bound',
      'Residue.overBound',
      /expands to 81 combinations, beyond the 64 this fragment version admits/u,
    ],
    [
      'a `let` inside an argument whose sibling computes',
      'Residue.computingSibling',
      /this call has an operand that computes; bind the let before the call/u,
    ],
    [
      'a `Nat` pattern in argument position',
      'Residue.natInArgument',
      /binds its predecessor with a statement, and an argument position has none/u,
    ],
    [
      'a `Nat` literal pattern other than zero',
      'Residue.literalPattern',
      /a Nat literal pattern other than 0 is outside this fragment version/u,
    ],
  ])(
    'refuses %s',
    (_label, declaration, diagnostic) => {
      let thrown: unknown;
      try {
        compileLeanToTypeScript({
          projectRoot: fixture.projectRoot,
          moduleName: 'Fixture',
          sourcePath: fixture.sourcePath,
          declarations: [declaration],
        });
      } catch (error: unknown) {
        thrown = error;
      }
      expect(thrown).toBeInstanceOf(Error);
      expect((thrown as Error).message).toMatch(diagnostic);
      expect((thrown as Error).message).toContain(declaration);
    },
    600_000,
  );
});
