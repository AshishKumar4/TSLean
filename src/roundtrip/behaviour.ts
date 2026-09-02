/**
 * @module roundtrip/behaviour
 *
 * Run the TypeScript side and the Lean side over the same inputs and compare what they
 * return.
 *
 * Acceptance by both checkers says the two artifacts are well-formed. It does not say they
 * compute the same function: a lowering that silently drops a call still type-checks. This
 * module answers the remaining question by executing both, so a disagreement arrives as a
 * concrete input and two concrete results.
 *
 * The comparison keeps counterexamples rather than a verdict. Agreement over a finite
 * domain is evidence that no counterexample exists in that domain; it is not a theorem
 * about the compiler, and nothing here reports one.
 */

import { spawnSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { leanRun, type LeanCheckOptions, type LeanModuleSource } from '../lean-check.js';
import type { ProfileType } from './profile.js';
import {
  domainSize,
  enumerateTuples,
  javaScriptValue,
  leanType,
  profileValue,
  renderValue,
  type ProfileValue,
} from './values.js';

/** One profile function, named on both sides, with the types the comparison enumerates. */
export interface ObservedFunction {
  /** How the comparison reports it. */
  readonly label: string;
  /** The exported name, and for a method the class it is reached through. */
  readonly javaScript: { readonly module: string; readonly name: string; readonly receiver?: string };
  /** The Lean module the declaration lives in, which also qualifies its types. */
  readonly leanModule: string;
  /** The fully qualified Lean name. */
  readonly lean: string;
  /** Parameter types, the receiver first when there is one. */
  readonly parameters: readonly ProfileType[];
  readonly result: ProfileType;
}

/** One input on which the two sides disagreed. */
export interface BehaviourDisagreement {
  readonly function: string;
  readonly inputs: readonly string[];
  readonly typescript: string;
  readonly lean: string;
}

export interface BehaviourReport {
  readonly agrees: boolean;
  /** Inputs applied per function, and whether that covered the whole domain. */
  readonly coverage: readonly {
    readonly function: string;
    readonly applied: number;
    readonly domain: number;
    readonly exhaustive: boolean;
  }[];
  readonly disagreements: readonly BehaviourDisagreement[];
}

export interface BehaviourRequest extends LeanCheckOptions {
  /** Projected TypeScript sources, keyed by their path inside the package. */
  readonly typescript: ReadonlyMap<string, string>;
  /** Recovered Lean modules the driver imports, and which are elaborated first. */
  readonly lean: readonly LeanModuleSource[];
  /**
   * Further modules the driver imports without elaborating them, because the Lean project
   * already provides them. This is how the original Lean module is observed alongside the
   * recovered one.
   */
  readonly leanImports?: readonly string[];
  readonly functions: readonly ObservedFunction[];
  /** Which recovered Lean module declares each profile type name. */
  readonly typeModules: ReadonlyMap<string, string>;
  /** Most inputs applied to one function. */
  readonly limit?: number;
}

/** The default input budget per function. */
export const DEFAULT_BEHAVIOUR_LIMIT = 4096;

/**
 * Compare the two sides over the enumerated input domain of every observed function.
 *
 * @throws TypeError when either side cannot be run at all, because a side that did not run
 * agrees with nothing.
 */
export async function compareBehaviour(request: BehaviourRequest): Promise<BehaviourReport> {
  const limit = request.limit ?? DEFAULT_BEHAVIOUR_LIMIT;
  if (!Number.isSafeInteger(limit) || limit <= 0) {
    throw new TypeError('the behaviour limit must be a positive safe integer');
  }
  const plans = request.functions.map((observed) => ({
    observed,
    inputs: enumerateTuples(observed.parameters, limit),
    domain: observed.parameters.reduce((total, type) => total * domainSize(type), 1),
  }));

  const javaScript = await evaluateJavaScript(request.typescript, plans);
  const lean = evaluateLean(request.lean, request.leanImports ?? [], plans, request.typeModules, request);

  const disagreements: BehaviourDisagreement[] = [];
  for (const [index, plan] of plans.entries()) {
    for (const [row, inputs] of plan.inputs.entries()) {
      const left = javaScript[index][row];
      const right = lean[index][row];
      if (left === right) continue;
      disagreements.push({
        function: plan.observed.label,
        inputs: inputs.map(renderValue),
        typescript: left,
        lean: right,
      });
    }
  }

  return {
    agrees: disagreements.length === 0,
    coverage: plans.map((plan) => ({
      function: plan.observed.label,
      applied: plan.inputs.length,
      domain: plan.domain,
      exhaustive: plan.inputs.length === plan.domain,
    })),
    disagreements,
  };
}

interface ObservationPlan {
  readonly observed: ObservedFunction;
  readonly inputs: readonly (readonly ProfileValue[])[];
  readonly domain: number;
}

// ─── TypeScript side ────────────────────────────────────────────────────────────

/** Emit the projected sources as JavaScript, import them, and apply every input. */
async function evaluateJavaScript(
  sources: ReadonlyMap<string, string>,
  plans: readonly ObservationPlan[],
): Promise<readonly (readonly string[])[]> {
  const root = mkdtempSync(join(tmpdir(), 'tslean-roundtrip-js-'));
  const javaScript = join(root, 'js');
  try {
    emitJavaScript(sources, join(root, 'ts'), javaScript);

    // A structure declared in one module is constructed from another, so construction reads
    // the whole package while a call still goes through the module that declares it. The
    // profile identifies a structure by its local name today; reject a duplicate name rather
    // than letting one constructor overwrite another in this aggregate map.
    const requiredConstructors = new Set<string>();
    for (const plan of plans) {
      for (const type of [...plan.observed.parameters, plan.observed.result]) {
        collectStructureNames(type, requiredConstructors);
      }
    }
    const loaded = new Map<string, Readonly<Record<string, unknown>>>();
    const constructors: Record<string, unknown> = {};
    for (const path of sources.keys()) {
      // The module under observation is written to a scratch directory by this call, so its
      // specifier does not exist at author time and no static import can name it. The cast
      // records what a generated module offers a caller: names of unknown type.
      const exported = (await import(
        pathToFileURL(join(javaScript, path.replace(/\.ts$/u, '.js'))).href
      )) as Readonly<Record<string, unknown>>;
      loaded.set(path, exported);
      for (const [name, value] of Object.entries(exported)) {
        if (!requiredConstructors.has(name)) continue;
        if (name in constructors && constructors[name] !== value) {
          throw new TypeError(`constructor name ${name} is exported by more than one observed module; qualify the type identity`);
        }
        constructors[name] = value;
      }
    }

    const rows: string[][] = [];
    for (const plan of plans) {
      const exported = loaded.get(plan.observed.javaScript.module);
      if (exported === undefined) {
        throw new TypeError(`the package has no module at ${plan.observed.javaScript.module}`);
      }
      rows.push(applyJavaScript(plan, exported, constructors));
    }
    return rows;
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}

/**
 * The compiler binary this package runs, resolved next to this module rather than by name,
 * so the observation runs the same compiler version the rest of the pipeline reads with.
 */
const COMPILER = join(dirname(createRequire(import.meta.url).resolve('typescript/package.json')), 'bin', 'tsc');

/**
 * Emit every projected source as JavaScript in one run of the compiler.
 *
 * `noCheck` is what makes the run transpile-only. The observation executes the projected
 * package to see what it computes, and whether that package type-checks is a separate
 * verdict the round trip reports on its own; an emit that depended on checking would turn
 * one failed check into two and would leave the comparison unable to run at all.
 *
 * The emitted tree keeps the input layout with only the extension changed, because a
 * generated module's own import specifiers already name `.js` siblings.
 */
function emitJavaScript(
  sources: ReadonlyMap<string, string>,
  typeScript: string,
  javaScript: string,
): void {
  if (sources.size === 0) return;
  for (const [path, source] of sources) {
    const file = join(typeScript, path);
    mkdirSync(dirname(file), { recursive: true });
    writeFileSync(file, source, 'utf8');
  }
  const configuration = join(typeScript, 'tsconfig.json');
  writeFileSync(
    configuration,
    JSON.stringify({
      compilerOptions: {
        target: 'ES2022',
        module: 'ESNext',
        moduleResolution: 'Bundler',
        outDir: javaScript,
        rootDir: typeScript,
        noCheck: true,
      },
      files: [...sources.keys()],
    }),
    'utf8',
  );
  const run = spawnSync(process.execPath, [COMPILER, '-p', configuration], { encoding: 'utf8' });
  if (run.error !== undefined) {
    throw new TypeError(`the compiler could not be run over the projected package: ${run.error.message}`);
  }
  if (run.status !== 0) {
    // The compiler reports refusals on its output stream and only crashes on its error
    // stream, so whichever one spoke is what the failure carries.
    throw new TypeError(
      `the compiler refused to emit the projected package: ${run.stderr === '' ? run.stdout : run.stderr}`,
    );
  }
}

function applyJavaScript(
  plan: ObservationPlan,
  exported: Readonly<Record<string, unknown>>,
  constructors: Readonly<Record<string, unknown>>,
): string[] {
  const { observed } = plan;
  const results: string[] = [];
  for (const inputs of plan.inputs) {
    const values = inputs.map((value, index) => javaScriptValue(observed.parameters[index], value, constructors));
    const result = observed.javaScript.receiver === undefined
      ? callExport(exported, observed.javaScript.name, values)
      : callMethod(values, observed.javaScript.name);
    results.push(renderValue(profileValue(observed.result, result)));
  }
  return results;
}

/** Every structure name a value can require a JavaScript constructor for. */
function collectStructureNames(type: ProfileType, into: Set<string>): void {
  if (type.kind === 'option') {
    collectStructureNames(type.inner, into);
    return;
  }
  if (type.kind !== 'structure') return;
  into.add(type.name);
  for (const field of type.fields) collectStructureNames(field.type, into);
}

function callExport(
  exported: Readonly<Record<string, unknown>>,
  name: string,
  values: readonly unknown[],
): unknown {
  const target = exported[name];
  if (typeof target !== 'function') {
    throw new TypeError(`the projected module does not export a function named ${name}`);
  }
  return Reflect.apply(target, undefined, values);
}

function callMethod(values: readonly unknown[], name: string): unknown {
  const [receiver, ...rest] = values;
  const target = (receiver as Record<string, unknown>)[name];
  if (typeof target !== 'function') throw new TypeError(`the receiver has no method named ${name}`);
  return Reflect.apply(target, receiver, rest);
}

// ─── Lean side ──────────────────────────────────────────────────────────────────

/**
 * The module the observation driver lives in. It sits outside the runtime library's root
 * namespace so the elaborator resolves the library's own modules in the library, and it
 * declares `main` at the top level because that is where `lean --run` looks for it.
 */
const DRIVER_MODULE = 'TSLeanRoundtripObserve';

/** Build a driver that prints one canonical line per input, run it, and split the output. */
function evaluateLean(
  modules: readonly LeanModuleSource[],
  provided: readonly string[],
  plans: readonly ObservationPlan[],
  typeModules: ReadonlyMap<string, string>,
  options: LeanCheckOptions,
): readonly (readonly string[])[] {
  const expected = plans.reduce((total, plan) => total + plan.inputs.length, 0);
  if (expected === 0) return plans.map(() => []);

  const run = leanRun(modules, {
    module: DRIVER_MODULE,
    code: driverSource([...modules.map((entry) => entry.module), ...provided], plans, typeModules),
    imports: modules.map((entry) => entry.module),
  }, options);
  if (!run.accepted) {
    throw new TypeError(
      `the recovered Lean was not accepted, so it cannot be observed: ${run.diagnostics
        .filter((entry) => entry.severity === 'error')
        .map((entry) => `${entry.module}:${String(entry.line)} ${entry.message}`)
        .join(' | ')}`,
    );
  }

  const lines = run.output.split('\n').filter((line) => line !== '');
  if (lines.length !== expected) {
    throw new TypeError(`the Lean driver printed ${String(lines.length)} results for ${String(expected)} inputs`);
  }
  const rows: string[][] = [];
  let cursor = 0;
  for (const plan of plans) {
    rows.push(lines.slice(cursor, cursor + plan.inputs.length));
    cursor += plan.inputs.length;
  }
  return rows;
}

/**
 * The driver module.
 *
 * It walks each domain in Lean rather than carrying one literal per input, so the module
 * stays small however large the domain is. Results are rendered through generated
 * functions rather than through `Repr`, so both sides write a value exactly one way and a
 * difference in the text is a difference in the value.
 */
function driverSource(
  imported: readonly string[],
  plans: readonly ObservationPlan[],
  typeModules: ReadonlyMap<string, string>,
): string {
  /** A profile type name resolves against the module that declares it, not the caller's. */
  const qualify = (name: string): string => {
    const module = typeModules.get(name);
    if (module === undefined) throw new TypeError(`no recovered module declares ${name}`);
    return `${module}.${name}`;
  };
  const renderers = new Map<string, string>();
  const rows: string[] = [];

  for (const [index, plan] of plans.entries()) {
    collectRenderers(plan.observed.result, qualify, renderers);
    rows.push(`def ${ROWS}${String(index)} : List String :=\n  ${application(plan, qualify)}`);
  }

  return [
    ...imported.map((module) => `import ${module}`),
    '',
    ...renderers.values(),
    '',
    ...rows,
    '',
    'def main : IO Unit := do',
    ...plans.map((_, index) => `  (${ROWS}${String(index)}).forM IO.println`),
    '',
  ].join('\n');
}

/** The prefix each function's result list is named under. */
const ROWS = 'roundtripRows';

/**
 * One expression producing the rendered result of every input in odometer order.
 *
 * `List.range` bounds the Lean work before any product is constructed. The prior form built
 * `fieldA.flatMap fun a => fieldB.flatMap ...` and only called `take` afterwards, so a sampled
 * domain could allocate its entire Cartesian product before it returned its first row.
 */
function application(plan: ObservationPlan, qualify: (name: string) => string): string {
  const call = (arguments_: readonly string[]): string =>
    `${rendererName(plan.observed.result)} (${plan.observed.lean}${arguments_.map((term) => ` ${term}`).join('')})`;
  if (plan.observed.parameters.length === 0) return `[${call([])}]`;

  const arguments_ = plan.observed.parameters.map((type, position) => {
    const following = plan.observed.parameters.slice(position + 1);
    const stride = following.reduce((product, next) => product * domainSize(next), 1);
    const size = domainSize(type);
    return leanValueAt(type, `((index / ${String(stride)}) % ${String(size)})`, qualify);
  });
  return `(List.range ${String(plan.inputs.length)}).map fun index => ${call(arguments_)}`;
}

/** A Lean term for one bounded index into a profile type's domain. */
function leanValueAt(
  type: ProfileType,
  index: string,
  qualify: (name: string) => string,
): string {
  // Every case parenthesises, because a term is spliced as a function argument and as the
  // operand of `some`, and neither position starts a bare `if`.
  if (type.kind === 'boolean') return `(if ${index} = 0 then false else true)`;
  if (type.kind === 'enumeration') {
    const arms = type.members.map((member, position) => `| ${String(position)} => .${member}`);
    return `(match ${index} with ${[...arms, `| _ => .${type.members[0]}`].join(' ')})`;
  }
  if (type.kind === 'option') {
    return `(match ${index} with | 0 => none | _ => some ${leanValueAt(type.inner, `(${index} - 1)`, qualify)})`;
  }
  const fields = type.fields.map((field, position) => {
    const following = type.fields.slice(position + 1);
    const stride = following.reduce((product, next) => product * domainSize(next.type), 1);
    const size = domainSize(field.type);
    const fieldIndex = `((${index} / ${String(stride)}) % ${String(size)})`;
    return `${field.name} := ${leanValueAt(field.type, fieldIndex, qualify)}`;
  });
  return `({ ${fields.join(', ')} } : ${qualify(type.name)})`;
}

/** The renderer name for a type, unique for every distinct type expression. */
function rendererName(type: ProfileType): string {
  switch (type.kind) {
    case 'boolean': return 'renderBool';
    case 'enumeration': return `render_${type.name}`;
    case 'structure': return `render_${type.name}`;
    case 'option': return `renderOption_${rendererName(type.inner)}`;
  }
}

/** Emit one renderer per type the results reach, each defined before it is used. */
function collectRenderers(
  type: ProfileType,
  qualify: (name: string) => string,
  into: Map<string, string>,
): void {
  const name = rendererName(type);
  if (into.has(name)) return;
  if (type.kind === 'boolean') {
    into.set(name, 'def renderBool (value : Bool) : String := if value then "true" else "false"');
    return;
  }
  if (type.kind === 'enumeration') {
    const arms = type.members.map((member) => `  | .${member} => "${member}"`);
    into.set(name, [`def ${name} (value : ${qualify(type.name)}) : String := match value with`, ...arms].join('\n'));
    return;
  }
  if (type.kind === 'option') {
    collectRenderers(type.inner, qualify, into);
    into.set(name, [
      `def ${name} (value : Option (${leanType(type.inner, qualify)})) : String := match value with`,
      '  | none => "none"',
      `  | some inner => "some(" ++ ${rendererName(type.inner)} inner ++ ")"`,
    ].join('\n'));
    return;
  }
  for (const field of type.fields) collectRenderers(field.type, qualify, into);
  const parts = type.fields.map((field) => `${rendererName(field.type)} value.${field.name}`);
  into.set(name, [
    `def ${name} (value : ${qualify(type.name)}) : String :=`,
    `  "{" ++ ${parts.join(' ++ "," ++ ')} ++ "}"`,
  ].join('\n'));
}
