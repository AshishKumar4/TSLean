/**
 * @module roundtrip/verify
 *
 * Take a program the whole way round, in both directions, and report what held.
 *
 * Lean to TypeScript to Lean starts from a generated package, projects each module onto the
 * profile, compiles the projection back to Lean, and requires Lean to accept the result and
 * to compute the same function. TypeScript to Lean to TypeScript starts from TypeScript in
 * the profile, compiles it to Lean, compiles that Lean back to TypeScript, and requires the
 * two TypeScript sides to declare and compute the same thing.
 *
 * Each direction also checks its own fixed point. Lean to TypeScript to Lean compares a
 * second projection and recovered Lean text. TypeScript to Lean to TypeScript compares the
 * second and third laps after it removes source locations and comments, because those record
 * where a lap happened to read its source rather than what the program declares.
 *
 * A report carries checks and counterexamples. It never carries a proof: agreement over a
 * finite domain is evidence that no counterexample was found in that domain, and the report
 * states the domain it covered.
 */

import {
  appendFileSync,
  cpSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, dirname, join, relative, resolve } from 'node:path';
import ts from 'typescript';
import { generateLeanTracked } from '../codegen/index.js';
import type { LeanFile } from '../codegen/lean-ast.js';
import { buildLeanFile } from '../codegen/v2.js';
import { PACKAGED_LEAN_PROJECT, leanAccepts, type LeanModuleSource } from '../lean-check.js';
import { compileLeanToTypeScript } from '../lean-to-typescript/compiler.js';
import { decodeManifest } from '../lean-to-typescript/manifest.js';
import {
  compareBehaviour,
  type BehaviourReport,
  type BehaviourRequest,
  type ObservedFunction,
} from './behaviour.js';
import type { LeanToTypeScriptManifest } from '../lean-to-typescript/artifact.js';
import { parseFile } from '../parser/index.js';
import { rewriteModule } from '../rewrite/index.js';
import { profileModule, resolveProfileType, type ProfileDeclaration, type ProfileType } from './profile.js';
import { projectModule, type ProjectedModule } from './projection.js';

// ─── Report ─────────────────────────────────────────────────────────────────────

export interface RoundtripCheck {
  readonly name: string;
  readonly holds: boolean;
  readonly detail: string;
}

/** One observed difference, kept so a reader can reproduce it. */
export interface RoundtripCounterexample {
  readonly check: string;
  readonly subject: string;
  readonly expected: string;
  readonly actual: string;
}

export interface RoundtripReport {
  readonly direction: 'lean-to-typescript-to-lean' | 'typescript-to-lean-to-typescript';
  readonly subject: string;
  readonly holds: boolean;
  readonly checks: readonly RoundtripCheck[];
  readonly counterexamples: readonly RoundtripCounterexample[];
  /** What the recovered Lean comparison covered, when it ran. */
  readonly behaviour?: BehaviourReport;
  /** What the original Lean source comparison covered, when it ran. */
  readonly sourceBehaviour?: BehaviourReport;
}

export interface RoundtripOptions {
  /** Lake project supplying the toolchain pin and the runtime library for recovered Lean. */
  readonly leanProjectRoot?: string;
  /**
   * Lake project holding the original Lean source of a generated package. When omitted, the
   * verifier resolves the manifest's `semantic.leanProjectPath` relative to the manifest.
   */
  readonly sourceRoot?: string;
  /** Most inputs applied to one function. Must be a positive safe integer. */
  readonly behaviourLimit?: number;
}

// ─── Lean to TypeScript to Lean ─────────────────────────────────────────────────

/**
 * Take a generated package back to Lean and check it survived.
 *
 * @param manifestPath - The package manifest. Its directory is the package root.
 */
export async function verifyLeanToTypeScriptRoundtrip(
  manifestPath: string,
  options: RoundtripOptions = {},
): Promise<RoundtripReport> {
  const checks: RoundtripCheck[] = [];
  const counterexamples: RoundtripCounterexample[] = [];
  const root = dirname(manifestPath);
  const manifest = decodeManifest(JSON.parse(readFileSync(manifestPath, 'utf8')) as unknown);
  const generatedPaths = manifest.semantic.modules.map((module) => module.path);

  const generated = openProgram(root, generatedPaths);
  checks.push(typeScriptCheck('generated typescript accepts', generated.program, counterexamples));

  // Every module the package ships is projected, not only the ones carrying a Lean module.
  // A package layout puts the shared option encoding in its own runtime artifact, and a
  // module that names an option imports the encoding from there, so dropping that artifact
  // would leave the projection unable to compile. A module contributing nothing admitted
  // projects to nothing and is left out.
  const projections = new Map<string, ProjectedModule>();
  for (const module of manifest.semantic.modules) {
    const source = generated.program.getSourceFile(join(root, module.path));
    if (source === undefined) throw new TypeError(`the package has no module at ${module.path}`);
    const projection = projectModule(source, generated.checker, module.path);
    if (module.leanModule === '' && projection.profile.admitted.length === 0) continue;
    projections.set(module.path, projection);
  }
  checks.push(declaredIntersectionCheck(manifest, projections, counterexamples));

  const projected = new Map([...projections].map(([path, entry]) => [path, entry.source]));
  const workspace = materialise(projected);
  try {
    const reprojected = openProgram(workspace, [...projected.keys()]);
    checks.push(typeScriptCheck('projection accepts', reprojected.program, counterexamples));

    const recovered = recoverLean(workspace, [...projected.keys()]);
    checks.push(placeholderCheck(recovered, counterexamples));
    const recoveredCheck = leanCheck(recovered.modules, options, counterexamples);
    checks.push(recoveredCheck);

    const observed = observableFunctions(reprojected, workspace, recovered);
    const shared = {
      typescript: projected,
      ...(options.leanProjectRoot === undefined ? {} : { projectRoot: options.leanProjectRoot }),
      ...(options.behaviourLimit === undefined ? {} : { limit: options.behaviourLimit }),
    };
    const recoveredBehaviour = recoveredCheck.holds
      ? await attemptBehaviour(() => ({
          ...shared,
          lean: recovered.modules,
          functions: observed,
          typeModules: declaringModules(reprojected, workspace, recovered),
        }), 'both sides compute the same function', counterexamples)
      : { report: undefined, failure: 'the recovered Lean was not accepted' };
    const behaviour = recoveredBehaviour.report;
    checks.push(behaviour === undefined
      ? unavailableBehaviourCheck('both sides compute the same function', recoveredBehaviour.failure ?? 'the behavior runner failed')
      : behaviourCheck(behaviour, 'both sides compute the same function', counterexamples));

    // The recovered Lean and the generated TypeScript come from the same two compilers, so
    // a bug they share would agree with itself. Compare only the callable observations the
    // manifest maps back to source Lean. Generated `toData` and `equals` helpers have no
    // source declaration and must not make this source comparison vacuous or fail it.
    const original = originalObservations(manifest, observed);
    const expectedOriginal = manifestBackedCallableLabels(manifest, projections);
    const actualOriginal = new Set(original.map((entry) => entry.label));
    for (const label of expectedOriginal) {
      if (actualOriginal.has(label)) continue;
      counterexamples.push({
        check: 'the generated typescript computes what its Lean source does',
        subject: label,
        expected: 'a manifest-backed callable observation',
        actual: 'the callable was not observed',
      });
    }

    const sourceRoot = originalSourceRoot(manifest, manifestPath, options.sourceRoot);
    if (sourceRoot.root === undefined) {
      counterexamples.push({
        check: 'the generated typescript computes what its Lean source does',
        subject: '(original Lean source root)',
        expected: 'the manifest source project or an explicit source root',
        actual: sourceRoot.failure ?? 'the original Lean source root is unavailable',
      });
    }
    const originalRoot = sourceRoot.root;
    const sourceAttempt = originalRoot === undefined
      ? { report: undefined, failure: sourceRoot.failure }
      : await attemptBehaviour(() => ({
          ...shared,
          lean: [],
          leanImports: [...new Set(original.map((entry) => entry.leanModule))],
          functions: original,
          typeModules: originalTypeModules(manifest, reprojected, workspace, recovered),
          projectRoot: originalRoot,
        }), 'the generated typescript computes what its Lean source does', counterexamples);
    const source = sourceAttempt.report;
    const sourceCheck = source === undefined
      ? unavailableBehaviourCheck(
          'the generated typescript computes what its Lean source does',
          sourceAttempt.failure ?? 'the behavior runner failed',
        )
      : behaviourCheck(source, 'the generated typescript computes what its Lean source does', counterexamples);
    checks.push({
      ...sourceCheck,
      holds: sourceCheck.holds && actualOriginal.size === expectedOriginal.size,
      detail: `${sourceCheck.detail}, ${String(actualOriginal.size)}/${String(expectedOriginal.size)} manifest callable(s) observed`,
    });

    checks.push(fixedPointCheck(reprojected, workspace, projected, recovered, counterexamples));

    return {
      direction: 'lean-to-typescript-to-lean',
      subject: manifestPath,
      holds: checks.every((check) => check.holds),
      checks,
      counterexamples,
      behaviour,
      ...(source === undefined ? {} : { sourceBehaviour: source }),
    };
  } finally {
    rmSync(workspace, { recursive: true, force: true });
  }
}

// ─── TypeScript to Lean to TypeScript ───────────────────────────────────────────

/**
 * Take TypeScript in the profile to Lean and back, and check the two TypeScript sides
 * declare and compute the same thing.
 *
 * @param sources - Absolute paths of the TypeScript modules to send round.
 */
export async function verifyTypeScriptToLeanRoundtrip(
  sources: readonly string[],
  options: RoundtripOptions = {},
): Promise<RoundtripReport> {
  const checks: RoundtripCheck[] = [];
  const counterexamples: RoundtripCounterexample[] = [];
  if (sources.length === 0) throw new TypeError('at least one TypeScript source is required');
  const root = commonRoot(sources);
  const paths = sources.map((source) => relative(root, source));

  const opened = openProgram(root, paths);
  checks.push(typeScriptCheck('source typescript accepts', opened.program, counterexamples));
  checks.push(profileCheck(opened, root, paths, counterexamples));
  const recovered = recoverLean(root, paths);
  checks.push(placeholderCheck(recovered, counterexamples));
  const recoveredCheck = leanCheck(recovered.modules, options, counterexamples);
  checks.push(recoveredCheck);

  // Acceptance by both checkers says the two artifacts are well formed. Only running them
  // says they compute the same function, so this direction executes both as well.
  const sourceTexts = new Map(paths.map((path) => [path, readFileSync(join(root, path), 'utf8')]));
  const recoveredBehaviour = recoveredCheck.holds
    ? await attemptBehaviour(() => ({
        typescript: sourceTexts,
        lean: recovered.modules,
        functions: observableFunctions(opened, root, recovered),
        typeModules: declaringModules(opened, root, recovered),
        ...(options.leanProjectRoot === undefined ? {} : { projectRoot: options.leanProjectRoot }),
        ...(options.behaviourLimit === undefined ? {} : { limit: options.behaviourLimit }),
      }), 'both sides compute the same function', counterexamples)
    : { report: undefined, failure: 'the recovered Lean was not accepted' };
  const behaviour = recoveredBehaviour.report;
  checks.push(behaviour === undefined
    ? unavailableBehaviourCheck('both sides compute the same function', recoveredBehaviour.failure ?? 'the behavior runner failed')
    : behaviourCheck(behaviour, 'both sides compute the same function', counterexamples));

  /**
   * One lap: compile the Lean back to TypeScript, project the result, and compile that back
   * to Lean. The generated package carries the emitter's data boundary just as the first one
   * did, so the projection runs on every lap.
   */
  const lap = (
    from: RecoveredLean,
    onRegenerated?: (opened: OpenedProgram, workspace: string, paths: readonly string[]) => void,
  ): RecoveredLean | null => {
    const leanProject = stageLeanProject(options.leanProjectRoot ?? PACKAGED_LEAN_PROJECT, from.modules);
    const workspace = materialise(new Map());
    const projectedWorkspace = materialise(new Map());
    try {
      const regenerated = regenerateTypeScript(leanProject, from, counterexamples);
      if (onRegenerated !== undefined) checks.push(regenerated.check);
      if (regenerated.sources === null) return null;
      writeInto(workspace, regenerated.sources);
      const regeneratedPaths = [...regenerated.sources.keys()];
      const reopened = openProgram(workspace, regeneratedPaths);
      onRegenerated?.(reopened, workspace, regeneratedPaths);

      const projected = new Map<string, string>();
      for (const path of regeneratedPaths) {
        const source = reopened.program.getSourceFile(join(workspace, path));
        if (source === undefined) throw new TypeError(`the regenerated package has no module at ${path}`);
        projected.set(path, projectModule(source, reopened.checker, path).source);
      }
      writeInto(projectedWorkspace, projected);
      return recoverLean(projectedWorkspace, [...projected.keys()]);
    } finally {
      rmSync(leanProject, { recursive: true, force: true });
      rmSync(workspace, { recursive: true, force: true });
      rmSync(projectedWorkspace, { recursive: true, force: true });
    }
  };

  const second = lap(recovered, (reopened, workspace, regeneratedPaths) => {
    checks.push(typeScriptCheck('regenerated typescript accepts', reopened.program, counterexamples));
    checks.push(declarationParityCheck(
      opened, root, paths, reopened, workspace, regeneratedPaths, counterexamples,
    ));
  });
  if (second === null) {
    return {
      direction: 'typescript-to-lean-to-typescript',
      subject: paths.join(', '),
      holds: false,
      checks,
      counterexamples,
      behaviour,
    };
  }

  // The compiler chooses its own declaration order, so the first Lean and the second differ
  // in order alone. A fixed point is `f (f x) = f x`, so the comparison is between the second
  // lap and the third.
  const third = lap(second);
  checks.push(third === null
    ? { name: 'the trip reaches a fixed point', holds: false, detail: 'a further lap did not compile' }
    : leanFixedPointCheck(second, third, counterexamples));

  return {
    direction: 'typescript-to-lean-to-typescript',
    subject: paths.join(', '),
    holds: checks.every((check) => check.holds),
    checks,
    counterexamples,
    behaviour,
  };
}

// ─── Checks ─────────────────────────────────────────────────────────────────────

function typeScriptCheck(
  name: string,
  program: ts.Program,
  counterexamples: RoundtripCounterexample[],
): RoundtripCheck {
  const diagnostics = [
    ...program.getSemanticDiagnostics(),
    ...program.getSyntacticDiagnostics(),
  ];
  for (const diagnostic of diagnostics) {
    counterexamples.push({
      check: name,
      subject: diagnostic.file?.fileName ?? '(program)',
      expected: 'no TypeScript diagnostic',
      actual: ts.flattenDiagnosticMessageText(diagnostic.messageText, ' '),
    });
  }
  return {
    name,
    holds: diagnostics.length === 0,
    detail: `${String(diagnostics.length)} diagnostic(s)`,
  };
}

/** Every declaration the manifest recorded as a Lean image has to survive the projection. */
function declaredIntersectionCheck(
  manifest: LeanToTypeScriptManifest,
  projections: ReadonlyMap<string, ProjectedModule>,
  counterexamples: RoundtripCounterexample[],
): RoundtripCheck {
  let missing = 0;
  let declared = 0;
  for (const module of manifest.semantic.modules) {
    const projection = projections.get(module.path);
    if (projection === undefined) continue;
    const admitted = new Set(projection.profile.admitted.map((entry) => entry.name));
    const emittedFor = new Map(module.declarations.map((entry) => [entry.declaration, entry.emitted]));
    for (const declaration of module.declarations) {
      declared++;
      // A member is identified by its owner and its own name together, so two classes with a
      // method of the same name cannot stand in for each other.
      const parent = declaration.declaration.slice(0, declaration.declaration.lastIndexOf('.'));
      const owner = emittedFor.get(parent);
      const identity = owner === undefined ? declaration.emitted : `${owner}.${declaration.emitted}`;
      if (admitted.has(identity)) continue;
      missing++;
      const refusal = projection.profile.refused.find((entry) => entry.name === identity);
      counterexamples.push({
        check: 'declared intersection covered',
        subject: `${module.path}#${declaration.declaration}`,
        expected: `${identity} inside the round-trip profile`,
        actual: refusal?.reason ?? 'not classified by the profile at all',
      });
    }
  }
  return {
    name: 'declared intersection covered',
    holds: missing === 0,
    detail: `${String(declared - missing)}/${String(declared)} declared image(s) inside the profile`,
  };
}

/** Every declaration of a source module has to be inside the profile. */
function profileCheck(
  opened: OpenedProgram,
  root: string,
  paths: readonly string[],
  counterexamples: RoundtripCounterexample[],
): RoundtripCheck {
  let refused = 0;
  let total = 0;
  for (const path of paths) {
    const source = opened.program.getSourceFile(join(root, path));
    if (source === undefined) throw new TypeError(`no source file at ${path}`);
    const profile = profileModule(source, opened.checker);
    total += profile.admitted.length + profile.refused.length;
    for (const entry of profile.refused) {
      refused++;
      counterexamples.push({
        check: 'source inside the profile',
        subject: `${path}#${entry.name}`,
        expected: 'inside the round-trip profile',
        actual: entry.reason,
      });
    }
  }
  return {
    name: 'source inside the profile',
    holds: refused === 0,
    detail: `${String(total - refused)}/${String(total)} declaration(s) inside the profile`,
  };
}

function placeholderCheck(
  recovered: RecoveredLean,
  counterexamples: RoundtripCounterexample[],
): RoundtripCheck {
  let placeholders = 0;
  for (const [module, markers] of recovered.degradations) {
    for (const marker of markers) {
      placeholders++;
      counterexamples.push({
        check: 'recovered lean carries no placeholder',
        subject: `${module}#${marker.site}`,
        expected: 'a translated term',
        actual: `${marker.level} placeholder`,
      });
    }
  }
  return {
    name: 'recovered lean carries no placeholder',
    holds: placeholders === 0,
    detail: `${String(placeholders)} placeholder(s)`,
  };
}

function leanCheck(
  modules: readonly LeanModuleSource[],
  options: RoundtripOptions,
  counterexamples: RoundtripCounterexample[],
): RoundtripCheck {
  const acceptance = leanAccepts(
    modules,
    options.leanProjectRoot === undefined ? {} : { projectRoot: options.leanProjectRoot },
  );
  const errors = acceptance.diagnostics.filter((entry) => entry.severity === 'error');
  for (const error of errors) {
    counterexamples.push({
      check: 'lean accepts the recovered module',
      subject: `${error.module}:${String(error.line)}:${String(error.column)}`,
      expected: `accepted by ${acceptance.toolchain}`,
      actual: error.message,
    });
  }
  return {
    name: 'lean accepts the recovered module',
    holds: acceptance.accepted,
    detail: `${acceptance.toolchain}, ${String(errors.length)} error(s)`,
  };
}

/**
 * A behavior check can only run after Lean accepted the program it would execute.
 * Reporting that dependency as a failed check keeps an invalid artifact from turning into a
 * thrown verifier error or a quietly absent behavior claim.
 */
function unavailableBehaviourCheck(name: string, reason: string): RoundtripCheck {
  return { name, holds: false, detail: `not run: ${reason}` };
}

function behaviourCheck(
  behaviour: BehaviourReport,
  name: string,
  counterexamples: RoundtripCounterexample[],
): RoundtripCheck {
  for (const disagreement of behaviour.disagreements) {
    counterexamples.push({
      check: name,
      subject: `${disagreement.function}(${disagreement.inputs.join(', ')})`,
      expected: disagreement.typescript,
      actual: disagreement.lean,
    });
  }
  const applied = behaviour.coverage.reduce((total, entry) => total + entry.applied, 0);
  const partial = behaviour.coverage.filter((entry) => !entry.exhaustive).length;
  return {
    name,
    holds: behaviour.agrees,
    detail: `${String(applied)} input(s) over ${String(behaviour.coverage.length)} function(s)` +
      (partial === 0 ? ', every domain exhausted' : `, ${String(partial)} domain(s) SAMPLED, not exhausted`),
  };
}

/**
 * A behavior comparison can fail before it produces a report: a type identity can be
 * ambiguous across modules, a generated JavaScript value can violate its declared profile
 * type, the observation driver can fail, or the configured bound can be invalid. Those are
 * counterexamples to execution, not reasons to discard the rest of a round-trip report.
 */
interface BehaviourAttempt {
  readonly report: BehaviourReport | undefined;
  readonly failure: string | undefined;
}

/**
 * Run one behavior comparison.
 *
 * The request is built here rather than by the caller, because assembling it resolves type
 * identities and that resolution refuses an ambiguous package. A refusal is a verdict about
 * the input under test, so it belongs in the report next to every other counterexample.
 */
async function attemptBehaviour(
  request: () => BehaviourRequest,
  name: string,
  counterexamples: RoundtripCounterexample[],
): Promise<BehaviourAttempt> {
  try {
    return { report: await compareBehaviour(request()), failure: undefined };
  } catch (failure) {
    const reason = failure instanceof Error ? failure.message : String(failure);
    counterexamples.push({
      check: name,
      subject: '(behavior runner)',
      expected: 'both programs execute over the declared input domain',
      actual: reason,
    });
    return { report: undefined, failure: reason };
  }
}

/** Sending the projection round again has to produce the same projection and the same Lean. */
function fixedPointCheck(
  reprojected: OpenedProgram,
  workspace: string,
  projected: ReadonlyMap<string, string>,
  recovered: RecoveredLean,
  counterexamples: RoundtripCounterexample[],
): RoundtripCheck {
  let differences = 0;
  for (const [path, source] of projected) {
    const file = reprojected.program.getSourceFile(join(workspace, path));
    if (file === undefined) throw new TypeError(`no projected module at ${path}`);
    const again = projectModule(file, reprojected.checker, path).source;
    if (again === source) continue;
    differences++;
    counterexamples.push({
      check: 'the trip reaches a fixed point',
      subject: path,
      expected: 'the same projection on the second lap',
      actual: firstDifference(source, again),
    });
  }

  const firstModules = new Map(recovered.modules.map((module) => [module.module, module.code]));
  const secondRecovered = recoverLean(workspace, [...projected.keys()]);
  const secondModules = new Map(secondRecovered.modules.map((module) => [module.module, module.code]));
  differences += moduleKeyDifferences(firstModules, secondModules, 'the trip reaches a fixed point', counterexamples);
  for (const [module, code] of firstModules) {
    const again = secondModules.get(module);
    if (again === undefined || again === code) continue;
    differences++;
    counterexamples.push({
      check: 'the trip reaches a fixed point',
      subject: module,
      expected: 'the same emitted Lean module on the second lap',
      actual: firstDifference(code, again),
    });
  }
  return {
    name: 'the trip reaches a fixed point',
    holds: differences === 0,
    detail: `${String(differences)} difference(s) on the second lap`,
  };
}

/**
 * Every module key matters. A comparison that only walks the first map misses a third-only
 * module, which is exactly the sort of growth a fixed-point check must reject.
 */
function moduleKeyDifferences(
  first: ReadonlyMap<string, unknown>,
  second: ReadonlyMap<string, unknown>,
  check: string,
  counterexamples: RoundtripCounterexample[],
): number {
  let differences = 0;
  for (const module of first.keys()) {
    if (second.has(module)) continue;
    differences++;
    counterexamples.push({
      check,
      subject: module,
      expected: 'the module is produced on the second lap',
      actual: 'the module was not produced again',
    });
  }
  for (const module of second.keys()) {
    if (first.has(module)) continue;
    differences++;
    counterexamples.push({
      check,
      subject: module,
      expected: 'no new module on the second lap',
      actual: 'an extra module was produced',
    });
  }
  return differences;
}

function leanFixedPointCheck(
  first: RecoveredLean,
  second: RecoveredLean,
  counterexamples: RoundtripCounterexample[],
): RoundtripCheck {
  let differences = moduleKeyDifferences(first.programs, second.programs, 'the trip reaches a fixed point', counterexamples);
  for (const [module, program] of first.programs) {
    const again = second.programs.get(module);
    if (again === undefined || again === program) continue;
    differences++;
    counterexamples.push({
      check: 'the trip reaches a fixed point',
      subject: module,
      expected: 'the same normalized imports, opens, and declarations after a second lap through TypeScript',
      actual: firstDifference(program, again),
    });
  }
  return {
    name: 'the trip reaches a fixed point',
    holds: differences === 0,
    detail: `${String(differences)} difference(s) after a second lap`,
  };
}

/** The two sides must declare the same enumerations, structures and signatures. */
function declarationParityCheck(
  opened: OpenedProgram,
  root: string,
  paths: readonly string[],
  regenerated: OpenedProgram,
  regeneratedRoot: string,
  regeneratedPaths: readonly string[],
  counterexamples: RoundtripCounterexample[],
): RoundtripCheck {
  const before = new Map<string, string>();
  for (const path of paths) {
    const source = opened.program.getSourceFile(join(root, path));
    if (source === undefined) throw new TypeError(`no source file at ${path}`);
    addShapes(before, declaredShapes(profileModule(source, opened.checker), opened.checker, modulePathIdentity(path)));
  }
  const after = new Map<string, string>();
  for (const path of regeneratedPaths) {
    const source = regenerated.program.getSourceFile(join(regeneratedRoot, path));
    if (source === undefined) throw new TypeError(`no regenerated module at ${path}`);
    addShapes(after, declaredShapes(
      profileModule(source, regenerated.checker),
      regenerated.checker,
      modulePathIdentity(path),
    ));
  }

  // The comparison is source → regenerated. A regenerated package legitimately adds
  // profile-admitted helpers — an interface becomes a class with `Init` and `Data` companions
  // and `toData` and `equals` members — so an after-only key is not a defect. Every source
  // key must come back with the same shape. The fixed-point check, not this one, holds the
  // later laps to an exact module set.
  let differences = 0;
  for (const [name, shape] of before) {
    const recovered = after.get(name);
    if (recovered === shape) continue;
    differences++;
    counterexamples.push({
      check: 'both sides declare the same intersection',
      subject: name,
      expected: shape,
      actual: recovered ?? 'the declaration did not come back',
    });
  }
  return {
    name: 'both sides declare the same intersection',
    holds: differences === 0,
    detail: `${String(before.size - differences)}/${String(before.size)} declaration(s) round-tripped`,
  };
}

// ─── Stages ─────────────────────────────────────────────────────────────────────

interface OpenedProgram {
  readonly program: ts.Program;
  readonly checker: ts.TypeChecker;
}

const COMPILER_OPTIONS: ts.CompilerOptions = {
  target: ts.ScriptTarget.ES2022,
  module: ts.ModuleKind.NodeNext,
  moduleResolution: ts.ModuleResolutionKind.NodeNext,
  strict: true,
  skipLibCheck: true,
  lib: ['lib.es2022.d.ts'],
};

function openProgram(root: string, paths: readonly string[]): OpenedProgram {
  const program = ts.createProgram(paths.map((path) => join(root, path)), COMPILER_OPTIONS);
  return { program, checker: program.getTypeChecker() };
}

interface RecoveredLean {
  readonly modules: readonly LeanModuleSource[];
  /** Which generated module each Lean module came from. */
  readonly origin: ReadonlyMap<string, string>;
  readonly definitions: ReadonlyMap<string, readonly string[]>;
  /**
   * Each module's declarations without the comments and spans it carried.
   *
   * A lap reads its TypeScript from a different place and that place reaches the generated
   * Lean as a comment, so the fixed point is compared over the program rather than over the
   * provenance the program was compiled from.
   */
  readonly programs: ReadonlyMap<string, string>;
  readonly degradations: ReadonlyMap<string, readonly { readonly level: string; readonly site: string }[]>;
}

/** Compile every module of a workspace to Lean, keeping the module graph. */
function recoverLean(root: string, paths: readonly string[]): RecoveredLean {
  const parsed = paths.map((path) => ({
    path,
    module: rewriteModule(parseFile({ fileName: join(root, path), projectRoot: root })),
  }));
  const collisions = new Map<string, string[]>();
  for (const entry of parsed) {
    collisions.set(entry.module.name, [...(collisions.get(entry.module.name) ?? []), entry.path]);
  }
  for (const [module, sources] of collisions) {
    if (sources.length > 1) {
      // A module name is derived from a file's base name, so two files of the same base name
      // in different directories would silently become one module and one would be lost.
      throw new TypeError(`${sources.join(' and ')} both compile to ${module}; rename one of them`);
    }
  }
  const scratch = new Map(parsed.map((entry) => [entry.module.name, scratchModule(entry.module.name)]));
  const scratchModules = new Set(scratch.values());

  const modules: LeanModuleSource[] = [];
  const origin = new Map<string, string>();
  const definitions = new Map<string, readonly string[]>();
  const programs = new Map<string, string>();
  const degradations = new Map<string, readonly { readonly level: string; readonly site: string }[]>();
  for (const entry of parsed) {
    const name = scratch.get(entry.module.name) ?? entry.module.name;
    const imports = entry.module.imports.map((imported) =>
      ({ ...imported, module: scratch.get(imported.module) ?? imported.module }));
    // Provenance names the Lean module rather than the directory the lap happened to read
    // from. The two laps read from different places by construction, so a comparison over
    // the raw path would report a difference in bookkeeping as a difference in the program.
    const loweredModule = {
      ...entry.module,
      name,
      imports,
      sourceFile: `${name.split('.').join('/')}.ts`,
    };
    const generated = generateLeanTracked(loweredModule);
    modules.push({
      module: name,
      code: generated.code,
      imports: imports.map((imported) => imported.module).filter((module) => scratchModules.has(module)),
    });
    origin.set(name, entry.path);
    definitions.set(name, entry.module.decls.flatMap(function names(declaration): string[] {
      if (declaration.tag === 'FuncDef') return [`${name}.${declaration.name}`];
      if (declaration.tag === 'Namespace') return declaration.decls.flatMap(names);
      return [];
    }));
    programs.set(name, normalisedLeanModule(buildLeanFile(loweredModule)));
    degradations.set(name, generated.degradations.map((marker) => ({
      level: marker.level,
      site: marker.site,
    })));
  }
  return { modules, origin, definitions, programs, degradations };
}

/** Omit prose while retaining the import graph, opens, and every executable declaration. */
function normalisedLeanModule(file: LeanFile): string {
  const OMIT = Symbol('omit');
  const normalise = (value: unknown): unknown | typeof OMIT => {
    if (Array.isArray(value)) {
      return value.map(normalise).filter((entry): entry is unknown => entry !== OMIT);
    }
    if (value === null || typeof value !== 'object') return value;
    const record = value as Record<string, unknown>;
    if (record['tag'] === 'Comment' || record['tag'] === 'Blank') return OMIT;
    const entries: Array<readonly [string, unknown]> = [];
    for (const [key, entry] of Object.entries(record)) {
      if (key === 'comment' || key === 'docComment') continue;
      const child = normalise(entry);
      if (child !== OMIT) entries.push([key, child]);
    }
    return Object.fromEntries(entries);
  };
  return JSON.stringify(normalise(file.decls));
}

/**
 * Where a scratch module lives.
 *
 * Lean resolves every module under a Lake library's root namespace inside that library's
 * build directory, so a module the round trip only elaborates has to sit outside the
 * runtime library's namespace or the elaborator would look for it in the wrong place.
 */
const ROUNDTRIP_NAMESPACE = 'TSLeanRoundtrip';

function scratchModule(module: string): string {
  return `${ROUNDTRIP_NAMESPACE}.${module.split('.').pop() ?? module}`;
}

/** The manifest-backed observations, renamed onto the Lean declarations they came from. */
function originalObservations(
  manifest: LeanToTypeScriptManifest,
  observed: readonly ObservedFunction[],
): readonly ObservedFunction[] {
  const declarations = new Map<string, { declaration: string; leanModule: string }>();
  for (const module of manifest.semantic.modules) {
    if (module.leanModule === '') continue;
    const emittedFor = new Map(module.declarations.map((entry) => [entry.declaration, entry.emitted]));
    for (const entry of module.declarations) {
      const parent = entry.declaration.slice(0, entry.declaration.lastIndexOf('.'));
      const owner = emittedFor.get(parent);
      const identity = `${module.path}#${owner === undefined ? entry.emitted : `${owner}.${entry.emitted}`}`;
      declarations.set(identity, { declaration: entry.declaration, leanModule: module.leanModule });
    }
  }
  const renamed: ObservedFunction[] = [];
  for (const entry of observed) {
    const original = declarations.get(entry.label);
    if (original === undefined) continue;
    renamed.push({ ...entry, leanModule: original.leanModule, lean: original.declaration });
  }
  return renamed;
}

/**
 * Callables that both the manifest and the projected module identify as source declarations.
 * The direction is manifest → observed: an emitter helper may be observable but cannot be a
 * missing source callable, while a manifest callable that disappears must fail the check.
 */
function manifestBackedCallableLabels(
  manifest: LeanToTypeScriptManifest,
  projections: ReadonlyMap<string, ProjectedModule>,
): ReadonlySet<string> {
  const labels = new Set<string>();
  for (const module of manifest.semantic.modules) {
    const projection = projections.get(module.path);
    if (projection === undefined) continue;
    const emittedFor = new Map(module.declarations.map((entry) => [entry.declaration, entry.emitted]));
    const manifestIdentities = new Set<string>();
    for (const entry of module.declarations) {
      const parent = entry.declaration.slice(0, entry.declaration.lastIndexOf('.'));
      const owner = emittedFor.get(parent);
      manifestIdentities.add(owner === undefined ? entry.emitted : `${owner}.${entry.emitted}`);
    }
    for (const declaration of projection.profile.admitted) {
      if (!declaration.exported) continue;
      if (declaration.kind !== 'function' && declaration.kind !== 'method') continue;
      if (manifestIdentities.has(declaration.name)) labels.add(`${module.path}#${declaration.name}`);
    }
  }
  return labels;
}

interface SourceRootResolution {
  readonly root: string | undefined;
  readonly failure: string | undefined;
}

/**
 * The original source lives where the manifest says it did, unless a caller supplies an
 * explicit source root. Falling back to this package's runtime project would compare against
 * a different Lean project and turn a missing source into a false success.
 */
function originalSourceRoot(
  manifest: LeanToTypeScriptManifest,
  manifestPath: string,
  explicit: string | undefined,
): SourceRootResolution {
  const root = explicit === undefined
    ? resolve(dirname(manifestPath), manifest.semantic.leanProjectPath)
    : resolve(explicit);
  if (!existsSync(root)) return { root: undefined, failure: `the original Lean source root does not exist: ${root}` };
  if (!existsSync(join(root, 'lean-toolchain'))) {
    return { root: undefined, failure: `the original Lean source root has no lean-toolchain: ${root}` };
  }
  return { root, failure: undefined };
}

/**
 * The original Lean namespace of each profile type the projection observes.
 *
 * Only type names are registered. A manifest records every emitted declaration, and two
 * legal callables can share a spelling across modules, so feeding the manifest in wholesale
 * would reject a package that round-trips.
 */
function originalTypeModules(
  manifest: LeanToTypeScriptManifest,
  opened: OpenedProgram,
  workspace: string,
  recovered: RecoveredLean,
): ReadonlyMap<string, string> {
  const manifestModules = new Map(
    manifest.semantic.modules
      .filter((module) => module.leanModule !== '')
      .map((module) => [module.path, module]),
  );
  const modules = new Map<string, string>();
  for (const [name, leanModule] of declaringModules(opened, workspace, recovered)) {
    const path = recovered.origin.get(leanModule);
    const sourceModule = path === undefined ? undefined : manifestModules.get(path);
    if (sourceModule === undefined) continue;
    const declarations = sourceModule.declarations.filter((entry) => entry.emitted === name);
    // A projection type must map back to exactly one Lean declaration. Zero means the
    // manifest does not know this type, more than one means it is ambiguous.
    if (declarations.length !== 1) continue;
    const namespace = declarations[0].declaration.slice(0, declarations[0].declaration.lastIndexOf('.'));
    registerTypeModule(modules, name, namespace, 'original');
  }
  return modules;
}

/** Which recovered Lean module declares each profile type name. */
function declaringModules(
  opened: OpenedProgram,
  workspace: string,
  recovered: RecoveredLean,
): ReadonlyMap<string, string> {
  const modules = new Map<string, string>();
  for (const [leanModule, path] of recovered.origin) {
    const source = opened.program.getSourceFile(join(workspace, path));
    if (source === undefined) continue;
    for (const declaration of profileModule(source, opened.checker).admitted) {
      if (declaration.kind === 'enumeration' || declaration.kind === 'structure') {
        registerTypeModule(modules, declaration.name, leanModule, 'recovered');
      }
    }
  }
  return modules;
}

/**
 * This version of the profile represents a type by its source spelling. A package containing
 * two different `Policy` types needs a qualified type identity before it can be observed.
 * Refuse that package here rather than letting constructor, renderer, or namespace maps
 * silently choose whichever module happened to load last.
 */
function registerTypeModule(
  modules: Map<string, string>,
  name: string,
  module: string,
  plane: string,
): void {
  const previous = modules.get(name);
  if (previous !== undefined && previous !== module) {
    throw new TypeError(`${plane} type name ${name} is declared by both ${previous} and ${module}; qualify the type identity`);
  }
  modules.set(name, module);
}

/**
 * Every profile function and method a consumer of the workspace can call, named on both
 * sides. A module-private definition is still compiled and still checked by Lean; it is
 * reached only through the exported definitions that call it, so it carries no separate
 * observation.
 */
function observableFunctions(
  opened: OpenedProgram,
  workspace: string,
  recovered: RecoveredLean,
): readonly ObservedFunction[] {
  const observed: ObservedFunction[] = [];
  for (const [leanModule, path] of recovered.origin) {
    const source = opened.program.getSourceFile(join(workspace, path));
    if (source === undefined) continue;
    const profile = profileModule(source, opened.checker);
    for (const declaration of profile.admitted) {
      if (!declaration.exported) continue;
      const entry = observeDeclaration(declaration, opened.checker, path, leanModule);
      if (entry !== null) observed.push(entry);
    }
  }
  return observed;
}

function observeDeclaration(
  declaration: ProfileDeclaration,
  checker: ts.TypeChecker,
  path: string,
  leanModule: string,
): ObservedFunction | null {
  if (declaration.kind !== 'function' && declaration.kind !== 'method') return null;
  const node = declaration.node as ts.FunctionDeclaration | ts.MethodDeclaration;
  const signature = checker.getSignatureFromDeclaration(node);
  if (signature === undefined) return null;
  const result = resolveProfileType(signature.getReturnType(), checker);
  if (result === null) return null;

  const parameters: ProfileType[] = [];
  if (declaration.kind === 'method') {
    const owner = node.parent;
    if (!ts.isClassDeclaration(owner) || owner.name === undefined) return null;
    const receiver = resolveProfileType(checker.getDeclaredTypeOfSymbol(requireSymbol(owner.name, checker)), checker);
    if (receiver === null) return null;
    parameters.push(receiver);
  }
  for (const parameter of node.parameters) {
    const type = resolveProfileType(checker.getTypeAtLocation(parameter), checker);
    if (type === null) return null;
    parameters.push(type);
  }

  const local = localName(declaration.name);
  return {
    label: `${path}#${declaration.name}`,
    javaScript: declaration.kind === 'method'
      ? { module: path, name: local, receiver: declaration.name.slice(0, declaration.name.indexOf('.')) }
      : { module: path, name: local },
    leanModule,
    lean: `${leanModule}.${declaration.name}`,
    parameters,
    result,
  };
}

/**
 * Compile the recovered Lean back to TypeScript.
 *
 * The Lean project is staged with the recovered modules inside it, because the compiler
 * reads a whole project rather than a file.
 */
function regenerateTypeScript(
  leanProject: string,
  recovered: RecoveredLean,
  counterexamples: RoundtripCounterexample[],
): { readonly check: RoundtripCheck; readonly sources: ReadonlyMap<string, string> | null } {
  const sources = new Map<string, string>();
  for (const module of recovered.modules) {
    const declarations = recovered.definitions.get(module.module) ?? [];
    if (declarations.length === 0) continue;
    try {
      const compiled = compileLeanToTypeScript({
        projectRoot: leanProject,
        moduleName: module.module,
        sourcePath: join(leanProject, `${module.module.split('.').join('/')}.lean`),
        declarations,
      });
      for (const artifact of compiled.modules) sources.set(artifact.path, artifact.code);
    } catch (error) {
      counterexamples.push({
        check: 'lean compiles back to typescript',
        subject: module.module,
        expected: 'a generated TypeScript package',
        actual: error instanceof Error ? error.message : String(error),
      });
      return {
        check: { name: 'lean compiles back to typescript', holds: false, detail: 'the compiler refused' },
        sources: null,
      };
    }
  }
  return {
    check: {
      name: 'lean compiles back to typescript',
      holds: true,
      detail: `${String(sources.size)} module(s) regenerated`,
    },
    sources,
  };
}

// ─── Workspaces ─────────────────────────────────────────────────────────────────

/** Write sources to a scratch directory so imports resolve the way they will for a consumer. */
function materialise(sources: ReadonlyMap<string, string>): string {
  const root = mkdtempSync(join(tmpdir(), 'tslean-roundtrip-'));
  writeInto(root, sources);
  return root;
}

function writeInto(root: string, sources: ReadonlyMap<string, string>): void {
  for (const [path, source] of sources) {
    const file = join(root, path);
    mkdirSync(dirname(file), { recursive: true });
    writeFileSync(file, source, 'utf8');
  }
}

/** A private copy of the Lean project with the recovered modules written into it. */
function stageLeanProject(projectRoot: string, modules: readonly LeanModuleSource[]): string {
  const root = mkdtempSync(join(tmpdir(), 'tslean-roundtrip-lean-'));
  cpSync(projectRoot, root, {
    recursive: true,
    filter: (source) => !source.includes(`${'/'}.lake`) && !source.endsWith('/.git'),
  });
  for (const module of modules) {
    const file = join(root, `${module.module.split('.').join('/')}.lean`);
    mkdirSync(dirname(file), { recursive: true });
    writeFileSync(file, module.code, 'utf8');
  }
  // The recovered modules sit outside the runtime library's namespace, so the staged copy
  // needs a library that owns theirs before Lake will build them.
  const lakefile = join(root, 'lakefile.toml');
  appendFileSync(
    lakefile,
    `\n[[lean_lib]]\nname = "${ROUNDTRIP_NAMESPACE}"\nroots = [${modules
      .map((module) => `"${module.module}"`)
      .join(', ')}]\n`,
    'utf8',
  );
  return root;
}

// ─── Helpers ────────────────────────────────────────────────────────────────────

/**
 * The declared shape of every profile type and signature, keyed by its module and owner.
 * Local names alone collapse `a/Policy.ts#Policy.equals` and `b/Policy.ts#Policy.equals`.
 */
function declaredShapes(
  profile: { readonly admitted: readonly ProfileDeclaration[] },
  checker: ts.TypeChecker,
  module: string,
): ReadonlyMap<string, string> {
  const shapes = new Map<string, string>();
  for (const declaration of profile.admitted) {
    // The option encoding declares no type of its own, so it has no shape to compare.
    if (declaration.kind === 'encoding') continue;
    const identity = `${module}#${declaration.name}`;
    if (declaration.kind === 'enumeration' || declaration.kind === 'structure') {
      const name = declaration.node as ts.TypeAliasDeclaration | ts.InterfaceDeclaration | ts.ClassDeclaration;
      if (name.name === undefined) continue;
      const type = resolveProfileType(checker.getDeclaredTypeOfSymbol(requireSymbol(name.name, checker)), checker);
      if (type !== null) shapes.set(identity, describeType(type));
      continue;
    }
    const node = declaration.node as ts.FunctionDeclaration | ts.MethodDeclaration;
    const signature = checker.getSignatureFromDeclaration(node);
    if (signature === undefined) continue;
    const parameters = node.parameters.map((parameter) => {
      const type = resolveProfileType(checker.getTypeAtLocation(parameter), checker);
      return type === null ? '?' : describeType(type);
    });
    const result = resolveProfileType(signature.getReturnType(), checker);
    shapes.set(identity, `(${parameters.join(', ')}) => ${result === null ? '?' : describeType(result)}`);
  }
  return shapes;
}

/** Refuse a duplicate qualified identity instead of silently overwriting its shape. */
function addShapes(target: Map<string, string>, additions: ReadonlyMap<string, string>): void {
  for (const [identity, shape] of additions) {
    if (target.has(identity)) throw new TypeError(`duplicate declaration identity ${identity}`);
    target.set(identity, shape);
  }
}

/** The module identity both original and regenerated file paths preserve. */
function modulePathIdentity(path: string): string {
  return basename(path).replace(/\.tsx?$/iu, '').toLowerCase();
}

/** A profile type as text, naming exactly what the two sides have to agree on. */
function describeType(type: ProfileType): string {
  switch (type.kind) {
    case 'boolean': return 'boolean';
    case 'enumeration': return `${type.name} = ${type.members.join(' | ')}`;
    case 'structure': return `${type.name} { ${type.fields.map((field) => `${field.name}: ${describeType(field.type)}`).join('; ')} }`;
    case 'option': return `${describeType(type.inner)} | undefined`;
  }
}

function requireSymbol(name: ts.Identifier, checker: ts.TypeChecker): ts.Symbol {
  const symbol = checker.getSymbolAtLocation(name);
  if (symbol === undefined) throw new TypeError(`${name.text} has no symbol`);
  return symbol;
}

/** `Class.member` names a member; anything else names itself. */
function localName(name: string): string {
  const cut = name.indexOf('.');
  return cut < 0 ? name : name.slice(cut + 1);
}

/** The first line where two texts differ, so a report names the difference rather than dumping both. */
function firstDifference(left: string, right: string): string {
  const leftLines = left.split('\n');
  const rightLines = right.split('\n');
  for (let index = 0; index < Math.max(leftLines.length, rightLines.length); index++) {
    const before = leftLines[index] ?? '';
    const after = rightLines[index] ?? '(missing)';
    if (before === after) continue;
    let column = 0;
    while (column < before.length && before[column] === after[column]) column++;
    // A single-line rendering needs the window around the difference, not the whole line.
    const window = (text: string): string => JSON.stringify(text.slice(Math.max(0, column - 40), column + 120));
    return `line ${String(index + 1)} column ${String(column + 1)}: expected ${window(before)}, got ${window(after)}`;
  }
  return '(no line differs)';
}

function commonRoot(paths: readonly string[]): string {
  return paths.slice(1).reduce((root, path) => {
    let candidate = root;
    while (relative(candidate, path).startsWith('..')) candidate = dirname(candidate);
    return candidate;
  }, dirname(paths[0]));
}
