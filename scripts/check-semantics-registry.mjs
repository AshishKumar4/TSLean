import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync, existsSync, readdirSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { argv, stdout } from 'node:process';
import { fileURLToPath } from 'node:url';
import ts from 'typescript';

/**
 * The source and target semantics gate.
 *
 * Three registries have to agree: the operations `src/lean-to-typescript/ir.ts` decodes, the
 * operations `src/lean-to-typescript/emitter.ts` lowers, and the operations the Lean semantics
 * proves. Drift on either side is a failure, and so is an assumption an opcode names but the plane
 * does not declare, or one the plane declares that no opcode names.
 *
 * The Lean side is not parsed. `lake exe semantics-registry` prints it, derived from the Lean
 * definitions, so this script never restates what Lean already knows.
 */

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const leanDirectory = join(root, 'lean');
const lockedRegistryPath = join(root, 'spec/semantics/registry.json');
const probesPath = join(root, 'spec/semantics/probes.json');
const allowedAxioms = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const usage = 'Usage: check-semantics-registry.mjs [--generate | --check | --self-test]';

/** The Lean modules that carry the semantics, and must all be free of the forbidden constructs. */
const semanticsDirectory = join(leanDirectory, 'TSLean/LeanToTypeScript/Semantics');

/**
 * Every construct that can introduce an axiom the allowlist does not carry. `native_decide` is on
 * the list because it discharges a goal by trusting compiled evaluation, which the kernel records as
 * a `Lean.ofReduceBool` application.
 */
const forbiddenTokens = /\b(sorry|admit|axiom|opaque|partial|unsafe|noncomputable|native_decide)\b/;

function fail(message) {
  throw new Error(`semantics registry gate failed: ${message}`);
}

function parseArgs(args) {
  const modes = new Set(args);
  for (const argument of args) {
    if (!['--generate', '--check', '--self-test'].includes(argument)) fail(`${usage}\nunknown argument ${argument}`);
  }
  if (modes.size > 1) fail(usage);
  return {
    generate: modes.has('--generate'),
    check: modes.has('--check') || modes.size === 0,
    selfTest: modes.has('--self-test'),
  };
}

function runLake(args, { allowFailure = false } = {}) {
  const result = spawnSync('lake', args, { cwd: leanDirectory, encoding: 'utf8' });
  if (result.error) fail(`cannot run lake: ${result.error.message}`);
  if (!allowFailure && result.status !== 0) {
    fail(`lake ${args.join(' ')} exited with ${result.status}:\n${result.stderr}${result.stdout}`);
  }
  return result;
}

/** The registry as Lean reports it. */
function leanRegistry() {
  runLake(['build', 'LeanToTypeScriptSemantics', 'semantics-registry', '--quiet', '--no-ansi']);
  const result = spawnSync(join(leanDirectory, '.lake/build/bin/semantics-registry'), [], {
    cwd: leanDirectory,
    encoding: 'utf8',
  });
  if (result.status !== 0) fail(`semantics-registry exited with ${result.status}: ${result.stderr}`);
  return JSON.parse(result.stdout);
}

/** Every string literal a `case` clause of the named function's switch tests. */
function switchCaseLiterals(file, functionName) {
  const source = ts.createSourceFile(file, readFileSync(file, 'utf8'), ts.ScriptTarget.ESNext, true);
  const literals = [];
  let found = false;
  const visit = (node) => {
    if (ts.isFunctionDeclaration(node) && node.name?.text === functionName) {
      found = true;
      const collect = (inner) => {
        if (ts.isSwitchStatement(inner)) {
          for (const clause of inner.caseBlock.clauses) {
            if (ts.isCaseClause(clause) && ts.isStringLiteral(clause.expression)) {
              literals.push(clause.expression.text);
            }
          }
        }
        ts.forEachChild(inner, collect);
      };
      collect(node);
      return;
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  if (!found) fail(`${file} declares no function ${functionName}`);
  if (literals.length === 0) fail(`${file}#${functionName} tests no string literal`);
  return literals;
}

/** Every declaration kind the emitter's declaration dispatch admits, read from the IR decoder. */
function decoderKinds() {
  const irFile = join(root, 'src/lean-to-typescript/ir.ts');
  return {
    expressions: switchCaseLiterals(irFile, 'decodeExpression'),
    declarations: switchCaseLiterals(irFile, 'decodeDeclaration'),
    types: switchCaseLiterals(irFile, 'decodeType'),
  };
}

/**
 * The runtime opcode table `ir.ts` declares, as `kind -> { modelTheorem, assumptions }`.
 *
 * The table is the only place the compiler names a primitive operation, so it is the only thing the
 * opcode half of the Lean registry can be joined against. Its absence is reported rather than
 * skipped: an unjoined opcode registry is a registry nothing checks.
 */
function declaredOpcodes() {
  const file = join(root, 'src/lean-to-typescript/ir.ts');
  const source = ts.createSourceFile(file, readFileSync(file, 'utf8'), ts.ScriptTarget.ESNext, true);
  let table;
  const visit = (node) => {
    if (
      ts.isVariableDeclaration(node) &&
      ts.isIdentifier(node.name) &&
      node.name.text === 'LEAN_RUNTIME_OPCODES'
    ) {
      table = node.initializer;
      return;
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  if (table === undefined) return undefined;
  const literal = ts.isCallExpression(table) ? table.arguments[0] : table;
  if (literal === undefined || !ts.isObjectLiteralExpression(literal)) {
    fail('ir.ts LEAN_RUNTIME_OPCODES is not an object literal');
  }
  const rows = new Map();
  for (const property of literal.properties) {
    if (!ts.isPropertyAssignment(property)) fail('ir.ts LEAN_RUNTIME_OPCODES carries a non-row member');
    const kind = ts.isStringLiteral(property.name)
      ? property.name.text
      : ts.isIdentifier(property.name)
        ? property.name.text
        : undefined;
    if (kind === undefined) fail('ir.ts LEAN_RUNTIME_OPCODES carries a computed row key');
    if (!ts.isObjectLiteralExpression(property.initializer)) {
      fail(`ir.ts opcode row ${kind} is not an object literal`);
    }
    let modelTheorem;
    let assumptions;
    for (const field of property.initializer.properties) {
      if (!ts.isPropertyAssignment(field) || !ts.isIdentifier(field.name)) continue;
      if (field.name.text === 'modelTheorem') {
        modelTheorem = ts.isStringLiteral(field.initializer)
          ? field.initializer.text
          : field.initializer.getText(source);
      }
      if (field.name.text === 'assumptions' && ts.isArrayLiteralExpression(field.initializer)) {
        assumptions = field.initializer.elements.map((element) =>
          ts.isStringLiteral(element) ? element.text : element.getText(source),
        );
      }
    }
    if (modelTheorem === undefined) fail(`ir.ts opcode row ${kind} names no modelTheorem`);
    if (assumptions === undefined) fail(`ir.ts opcode row ${kind} names no assumptions`);
    rows.set(kind, { modelTheorem, assumptions });
  }
  return rows;
}

/**
 * Joins the Lean opcode registry against the table `ir.ts` declares: the same kinds, the same
 * theorem per kind, and the same ordered assumption closure per kind.
 */
export function joinOpcodes(registry, declared) {
  if (declared === undefined) {
    fail(
      'opcode registry is not joined: src/lean-to-typescript/ir.ts declares no LEAN_RUNTIME_OPCODES table, ' +
        `so the ${registry.opcodes.length} Lean opcode rows are checked against nothing`,
    );
  }
  const leanKinds = registry.opcodes.map((opcode) => opcode.opcode).sort();
  const declaredKinds = [...declared.keys()].sort();
  requireSameSet('runtime opcodes', declaredKinds, 'ir.ts', leanKinds, 'the Lean semantics');
  for (const opcode of registry.opcodes) {
    const row = declared.get(opcode.opcode);
    const expected = opcode.theorem;
    if (row.modelTheorem !== expected) {
      fail(`opcode ${opcode.opcode} names theorem ${row.modelTheorem} in ir.ts but ${expected} in Lean`);
    }
    if (JSON.stringify(row.assumptions) !== JSON.stringify(opcode.requires)) {
      fail(
        `opcode ${opcode.opcode} names closure ${JSON.stringify(row.assumptions)} in ir.ts but ` +
          `${JSON.stringify(opcode.requires)} in Lean`,
      );
    }
  }
  return declaredKinds.length;
}

/** Every expression kind the emitter lowers. */
function emitterKinds() {
  return switchCaseLiterals(join(root, 'src/lean-to-typescript/emitter.ts'), 'emitExpression');
}

function sortedUnique(values, label) {
  const unique = [...new Set(values)];
  if (unique.length !== values.length) fail(`${label} repeats a kind`);
  return unique.sort();
}

function requireSameSet(label, left, leftLabel, right, rightLabel) {
  const missing = left.filter((kind) => !right.includes(kind));
  const extra = right.filter((kind) => !left.includes(kind));
  if (missing.length > 0) fail(`${label}: ${leftLabel} admits ${missing.join(', ')} but ${rightLabel} does not`);
  if (extra.length > 0) fail(`${label}: ${rightLabel} admits ${extra.join(', ')} but ${leftLabel} does not`);
}

/**
 * Runs every probe in the host engine and compares the result with the value the Lean model predicts.
 * A probe that disagrees is an assumption the engine does not satisfy, which is the only way an
 * assumption in this plane can be wrong.
 */
export function runProbes(suite) {
  if (suite.schemaVersion !== 1) fail(`unsupported probe schema ${suite.schemaVersion}`);
  const groups = new Map();
  let total = 0;
  for (const group of suite.groups ?? []) {
    if (typeof group.id !== 'string' || group.id.length === 0) fail('a probe group has no id');
    if (groups.has(group.id)) fail(`duplicate probe group ${group.id}`);
    if (!Array.isArray(group.probes) || group.probes.length === 0) {
      fail(`probe group ${group.id} carries no probe`);
    }
    const seen = new Set();
    const families = new Set();
    for (const probe of group.probes) {
      if (typeof probe.family !== 'string' || probe.family.length === 0) {
        fail(`probe ${group.id}/${probe.id} declares no coverage family`);
      }
      families.add(probe.family);
      if (typeof probe.id !== 'string' || seen.has(probe.id)) {
        fail(`probe group ${group.id} repeats or omits a probe id`);
      }
      seen.add(probe.id);
      const observed = describeValue(evaluateProbe(group.id, probe));
      const expected = JSON.stringify(probe.expect);
      if (observed !== expected) {
        fail(`probe ${group.id}/${probe.id} observed ${observed} but the model predicts ${expected}`);
      }
      total += 1;
    }
    groups.set(group.id, families);
  }
  if (groups.size === 0) fail('spec/semantics/probes.json declares no probe group');
  return { groups, total };
}

function evaluateProbe(groupId, probe) {
  if (typeof probe.source !== 'string' || probe.source.length === 0) {
    fail(`probe ${groupId}/${probe.id} carries no source`);
  }
  try {
    return new Function(`"use strict"; return (${probe.source});`)();
  } catch (error) {
    fail(`probe ${groupId}/${probe.id} did not evaluate: ${error instanceof Error ? error.message : error}`);
  }
}

/** The tagged form a probe's expectation is written in, so a comparison never coerces. */
function describeValue(value) {
  if (value === undefined) return JSON.stringify({ undefined: true });
  if (typeof value === 'boolean') return JSON.stringify({ boolean: value });
  if (typeof value === 'number') return JSON.stringify({ number: value });
  if (typeof value === 'bigint') return JSON.stringify({ bigint: value.toString() });
  if (typeof value === 'string') return JSON.stringify({ string: value });
  if (Array.isArray(value)) {
    return `{"array":[${value.map((element) => describeValue(element)).join(',')}]}`;
  }
  fail(`a probe produced a value the tagged form does not cover: ${String(value)}`);
}

/** The probe groups an assumption's oracle may name. */
function probeGroups(suite) {
  return runProbes(suite).groups;
}

function canonicalWordingOf(assumption) {
  const parts = [...assumption.clauses, assumption.statement, assumption.oracle, ...assumption.coverage];
  return parts.map((part) => `${part.length}:${part}`).join(':');
}

/**
 * The whole join, as one pure function so `--self-test` can run it against mutated inputs.
 *
 * Every check reports through `fail`, so the first difference names itself.
 */
export function joinRegistries(registry, kinds, emitted, groups) {
  if (registry.schemaVersion !== 1) fail(`unsupported registry schema ${registry.schemaVersion}`);
  const leanExpressions = sortedUnique(
    registry.expressionOperations.map((entry) => entry.kind),
    'Lean expression registry',
  );
  const leanDeclarations = sortedUnique(
    registry.declarationFamilies.map((entry) => entry.kind),
    'Lean declaration registry',
  );
  const leanTypes = sortedUnique(registry.typeForms.map((entry) => entry.kind), 'Lean type registry');
  requireSameSet(
    'expression operations',
    sortedUnique(kinds.expressions, 'ir.ts decodeExpression'),
    'ir.ts',
    leanExpressions,
    'the Lean semantics',
  );
  requireSameSet(
    'declaration families',
    sortedUnique(kinds.declarations, 'ir.ts decodeDeclaration'),
    'ir.ts',
    leanDeclarations,
    'the Lean semantics',
  );
  requireSameSet('type forms', sortedUnique(kinds.types, 'ir.ts decodeType'), 'ir.ts', leanTypes, 'the Lean semantics');
  requireSameSet(
    'expression operations',
    sortedUnique(kinds.expressions, 'ir.ts decodeExpression'),
    'ir.ts',
    sortedUnique(emitted, 'emitter.ts emitExpression'),
    'emitter.ts',
  );

  const declared = new Set(registry.assumptions.map((assumption) => assumption.id));
  if (declared.size !== registry.assumptions.length) fail('the assumption plane repeats a name');
  for (const assumption of registry.assumptions) {
    for (const field of ['id', 'sourceUrl', 'sourceArtifact', 'sourceDigest', 'statement', 'oracle', 'canonicalWording']) {
      if (typeof assumption[field] !== 'string' || assumption[field].length === 0) {
        fail(`assumption ${assumption.id} records no ${field}`);
      }
    }
    for (const field of ['clauses', 'coverage']) {
      if (!Array.isArray(assumption[field]) || assumption[field].length === 0) {
        fail(`assumption ${assumption.id} records no ${field}`);
      }
    }
    if (assumption.canonicalWording !== canonicalWordingOf(assumption)) {
      fail(`assumption ${assumption.id} carries a canonical wording that does not match its recorded fields`);
    }
    const oraclePrefix = 'semantics-probes/';
    if (!assumption.oracle.startsWith(oraclePrefix)) {
      fail(`assumption ${assumption.id} names oracle ${assumption.oracle}, which is not an executed probe group`);
    }
    const group = groups.get(assumption.oracle.slice(oraclePrefix.length));
    if (group === undefined) {
      fail(`assumption ${assumption.id} names probe group ${assumption.oracle}, which spec/semantics/probes.json does not declare`);
    }
    for (const family of assumption.coverage) {
      if (!group.has(family)) {
        fail(`assumption ${assumption.id} requires coverage family ${family}, which no probe in ${assumption.oracle} measures`);
      }
    }
    for (const family of group) {
      if (!assumption.coverage.includes(family)) {
        fail(`probe group ${assumption.oracle} measures family ${family}, which assumption ${assumption.id} does not require`);
      }
    }
  }

  const used = new Set();
  for (const opcode of registry.opcodes) {
    for (const field of ['opcode', 'runtimeSymbol', 'model', 'relation']) {
      if (typeof opcode[field] !== 'string' || opcode[field].length === 0) {
        fail(`opcode ${opcode.opcode} records no ${field}`);
      }
    }
    if (opcode.relation !== 'source = model') fail(`opcode ${opcode.opcode} states relation ${opcode.relation}`);
    if (typeof opcode.emittedForm !== 'string' || opcode.emittedForm.length === 0) {
      fail(`opcode ${opcode.opcode} records no emitted form`);
    }
    if (typeof opcode.theorem !== 'string' || opcode.theorem.length === 0) {
      fail(`opcode ${opcode.opcode} records no theorem`);
    }
    if (opcode.requires.length === 0) fail(`opcode ${opcode.opcode} names no assumption`);
    if (new Set(opcode.requires).size !== opcode.requires.length) {
      fail(`opcode ${opcode.opcode} repeats an assumption in its closure`);
    }
    for (const name of opcode.requires) {
      if (!declared.has(name)) fail(`opcode ${opcode.opcode} requires undeclared assumption ${name}`);
      used.add(name);
    }
  }
  for (const name of declared) {
    if (!used.has(name)) fail(`assumption ${name} is declared but no opcode requires it`);
  }
  const artifacts = new Set(registry.assumptions.map((assumption) => assumption.sourceArtifact));
  if (artifacts.size !== 1) fail(`the assumptions cite ${artifacts.size} frozen artifacts; one page, one digest, one join`);
  const theorems = registry.opcodes.map((opcode) => opcode.theorem);
  if (new Set(theorems).size !== theorems.length) fail('two opcodes name the same theorem');
  return {
    expressions: leanExpressions.length,
    declarations: leanDeclarations.length,
    types: leanTypes.length,
    opcodes: registry.opcodes.length,
    assumptions: registry.assumptions.length,
  };
}

/** Each opcode's recorded theorem is declared, and is the one the registry pairs it with. */
function checkTheoremNames(registry) {
  const source = readFileSync(join(semanticsDirectory, 'Opcode.lean'), 'utf8');
  const clauses = new Map(
    [...source.matchAll(/^ {2}\| \.([A-Za-z]+) => ([A-Za-z]+) runtime$/gm)].map((match) => [match[1], match[2]]),
  );
  if (clauses.size !== registry.opcodes.length) {
    fail(`Opcode.registry pairs ${clauses.size} opcodes but the registry reports ${registry.opcodes.length}`);
  }
  const qualifier = 'TSLean.LeanToTypeScript.Semantics.Opcode.';
  for (const opcode of registry.opcodes) {
    if (!opcode.theorem.startsWith(qualifier)) {
      fail(`opcode ${opcode.opcode} names an unqualified theorem ${opcode.theorem}`);
    }
    const local = opcode.theorem.slice(qualifier.length);
    if (!new RegExp(`^theorem ${local} \\(runtime : Runtime\\)$`, 'm').test(source)) {
      fail(`opcode ${opcode.opcode} names theorem ${opcode.theorem}, which Opcode.lean does not declare`);
    }
    if (![...clauses.values()].includes(local)) {
      fail(`opcode ${opcode.opcode} names theorem ${opcode.theorem}, which Opcode.registry does not use`);
    }
  }
  return clauses.size;
}

function leanSourceFiles(directory) {
  const files = [];
  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    const path = join(directory, entry.name);
    if (entry.isSymbolicLink()) fail(`semantics source tree contains a symlink: ${path}`);
    else if (entry.isDirectory()) files.push(...leanSourceFiles(path));
    else if (entry.isFile() && entry.name.endsWith('.lean')) files.push(path);
  }
  return files;
}

/** Comments carry prose about refused constructs, so they are stripped before the token scan. */
export function stripLeanComments(source) {
  let result = '';
  let depth = 0;
  let index = 0;
  while (index < source.length) {
    if (source.startsWith('/-', index)) {
      depth += 1;
      index += 2;
    } else if (depth > 0 && source.startsWith('-/', index)) {
      depth -= 1;
      index += 2;
    } else if (depth === 0 && source.startsWith('--', index)) {
      const newline = source.indexOf('\n', index);
      index = newline === -1 ? source.length : newline;
    } else {
      if (depth === 0) result += source[index];
      index += 1;
    }
  }
  return result;
}

/** No module of the semantics may use a construct able to introduce an axiom. */
export function forbiddenTokenViolations(sources) {
  const violations = [];
  for (const { label, source } of sources) {
    for (const line of stripLeanComments(source).split('\n')) {
      if (forbiddenTokens.test(line)) violations.push(`${label}: ${line.trim()}`);
    }
  }
  return violations;
}

function semanticsSources() {
  return leanSourceFiles(semanticsDirectory).map((file) => ({
    label: file.slice(root.length + 1),
    source: readFileSync(file, 'utf8'),
  }));
}

/** The axiom dependencies of every authored declaration of the semantics. */
function auditAxioms() {
  const result = runLake(['env', 'lean', 'audit/LeanToTypeScriptSemantics.lean']);
  const records = new Map();
  for (const line of result.stdout.split('\n')) {
    const marker = line.indexOf('JS_AUDIT\t');
    if (marker === -1) continue;
    const [name, dependencies] = line.slice(marker + 'JS_AUDIT\t'.length).split('\t');
    records.set(name, dependencies === undefined || dependencies === '' ? [] : dependencies.split(','));
  }
  if (records.size === 0) fail('the axiom audit reported no declaration');
  for (const [name, axioms] of records) {
    for (const axiom of axioms) {
      if (!allowedAxioms.has(axiom)) fail(`${name} depends on disallowed axiom ${axiom}`);
    }
  }
  return records.size;
}

/**
 * The frozen specification page every clause citation resolves against. Its digest is recomputed
 * from the bytes, so a declared digest that no longer matches the file, and an artefact that is not
 * in the tree, are both refusals.
 */
export function checkFrozenSource(registry, read = (path) => readFileSync(join(root, path))) {
  const [assumption] = registry.assumptions;
  const path = assumption.sourceArtifact;
  let bytes;
  try {
    bytes = read(path);
  } catch {
    fail(`the frozen specification page is absent: ${path} is not in the tree, so the declared digest ${assumption.sourceDigest} is unverified`);
  }
  const prefix = 'sha256:';
  if (!assumption.sourceDigest.startsWith(prefix)) {
    fail(`the frozen source digest ${assumption.sourceDigest} does not name its hash; write it as sha256:<hex>`);
  }
  const observed = `${prefix}${createHash('sha256').update(bytes).digest('hex')}`;
  if (observed !== assumption.sourceDigest) {
    fail(`the frozen specification page ${path} hashes to ${observed} but the registry declares ${assumption.sourceDigest}`);
  }
  // Every cited clause has to resolve inside that edition. Clauses are anchor ids, not section
  // numbers, because TC39 renumbers sections far more often than it renames anchors.
  const page = bytes.toString('utf8');
  for (const row of registry.assumptions) {
    for (const clause of row.clauses) {
      if (!clause.startsWith('sec-')) {
        fail(`assumption ${row.id} cites ${clause}, which is not an anchor id`);
      }
      if (!page.includes(`id="${clause}"`)) {
        fail(`assumption ${row.id} cites clause ${clause}, which does not resolve in ${path}`);
      }
    }
  }
  return observed;
}

/** A Lean file that has to be refused, and the reason it has to be refused for. */
function expectLeanFailure(fixture, expected) {
  const result = runLake(['env', 'lean', join('..', 'tests/lean-fixtures', fixture)], { allowFailure: true });
  if (result.status === 0) fail(`negative fixture ${fixture} was accepted`);
  const output = `${result.stdout}${result.stderr}`;
  if (!output.includes(expected)) {
    fail(`negative fixture ${fixture} failed for the wrong reason:\n${output}`);
  }
}

/** The locked registry is byte-exact. Any closure change, including an extra declared assumption
the join would accept, differs here. */
export function compareWithLocked(registry, locked) {
  if (`${JSON.stringify(registry, null, 2)}\n` !== locked) {
    fail('spec/semantics/registry.json is stale; run --generate');
  }
}

function expectJoinFailure(label, registry, kinds, emitted, scenarios, expected) {
  try {
    joinRegistries(registry, kinds, emitted, scenarios);
  } catch (error) {
    if (error instanceof Error && error.message.includes(expected)) return;
    throw error;
  }
  fail(`${label} was accepted`);
}

function selfTest() {
  const registry = leanRegistry();
  const suite = JSON.parse(readFileSync(probesPath, 'utf8'));
  const scenarios = probeGroups(suite);
  // The fixtures test the join, not the tree. Their baseline is a decoder that admits exactly what
  // Lean proves, so a staged migration -- Lean ahead of `ir.ts`, or behind it -- changes which
  // refusal `--check` reports without changing whether the join still discriminates. The live
  // `ir.ts` and `emitter.ts` are joined in `main`, where a difference between the two sides is the
  // finding rather than a broken harness.
  const kinds = {
    expressions: registry.expressionOperations.map((entry) => entry.kind),
    declarations: registry.declarationFamilies.map((entry) => entry.kind),
    types: registry.typeForms.map((entry) => entry.kind),
  };
  const emitted = [...kinds.expressions];
  joinRegistries(registry, kinds, emitted, scenarios);

  expectLeanFailure('semantics-wrong-model.lean', 'unsolved goals');
  expectLeanFailure('semantics-incomplete-theorem.lean', 'Type mismatch');
  expectLeanFailure('semantics-wrong-operation.lean', 'Type mismatch');
  expectLeanFailure('semantics-arrow-drops-trace.lean', 'unsolved goals');
  expectLeanFailure('semantics-arrow-free-fuel.lean', 'unsolved goals');
  expectLeanFailure('semantics-arrow-wrong-theorem.lean', 'Type mismatch');

  const withoutAssumption = structuredClone(registry);
  const multiple = withoutAssumption.opcodes.find((opcode) => opcode.requires.length > 1);
  if (multiple === undefined) fail('no opcode carries more than one assumption to drop');
  const dropped = multiple.requires.pop();
  expectJoinFailure(
    'a missing assumption',
    withoutAssumption,
    kinds,
    emitted,
    scenarios,
    `assumption ${dropped} is declared but no opcode requires it`,
  );

  const withUndeclaredAssumption = structuredClone(registry);
  withUndeclaredAssumption.opcodes[0].requires.push('boolean.two-valued');
  expectJoinFailure(
    'an undeclared assumption',
    withUndeclaredAssumption,
    kinds,
    emitted,
    scenarios,
    'requires undeclared assumption boolean.two-valued',
  );

  const locked = readFileSync(lockedRegistryPath, 'utf8');
  compareWithLocked(registry, locked);
  const withExtraAssumption = structuredClone(registry);
  withExtraAssumption.opcodes[0].requires.push('bigint.relational');
  joinRegistries(withExtraAssumption, kinds, emitted, scenarios);
  try {
    compareWithLocked(withExtraAssumption, locked);
    fail('an extra declared assumption was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('is stale')) throw error;
  }

  const withWrongOperation = structuredClone(registry);
  withWrongOperation.expressionOperations.push({ constructor: 'Fixture.bogus', kind: 'variables' });
  expectJoinFailure(
    'an operation the decoder does not admit',
    withWrongOperation,
    kinds,
    emitted,
    scenarios,
    'the Lean semantics admits variables but ir.ts does not',
  );

  const withMissingOperation = structuredClone(registry);
  const droppedOperation = withMissingOperation.expressionOperations.pop().kind;
  expectJoinFailure(
    'a dropped operation',
    withMissingOperation,
    kinds,
    emitted,
    scenarios,
    `ir.ts admits ${droppedOperation} but the Lean semantics does not`,
  );

  // The v5 arrow kinds are named, not sampled: a registry that stopped proving either one fails
  // here rather than passing quietly with fifteen rows.
  for (const kind of ['lambda', 'apply']) {
    const withoutKind = structuredClone(registry);
    withoutKind.expressionOperations = withoutKind.expressionOperations.filter(
      (entry) => entry.kind !== kind,
    );
    if (withoutKind.expressionOperations.length === registry.expressionOperations.length) {
      fail(`the Lean expression registry proves no ${kind} operation`);
    }
    expectJoinFailure(
      `a dropped ${kind} operation`,
      withoutKind,
      kinds,
      emitted,
      scenarios,
      `ir.ts admits ${kind} but the Lean semantics does not`,
    );
  }

  const declared = new Map(
    registry.opcodes.map((opcode) => [
      opcode.opcode,
      {
        modelTheorem: opcode.theorem,
        assumptions: [...opcode.requires],
      },
    ]),
  );
  joinOpcodes(registry, declared);
  const withDriftedClosure = new Map(declared);
  const firstKind = registry.opcodes[0].opcode;
  withDriftedClosure.set(firstKind, {
    modelTheorem: declared.get(firstKind).modelTheorem,
    assumptions: [...declared.get(firstKind).assumptions, 'bigint.relational'],
  });
  try {
    joinOpcodes(registry, withDriftedClosure);
    fail('an opcode closure drifted from ir.ts was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('names closure')) throw error;
  }
  const withDriftedTheorem = new Map(declared);
  withDriftedTheorem.set(firstKind, {
    modelTheorem: 'Elsewhere.wrongTheorem',
    assumptions: [...declared.get(firstKind).assumptions],
  });
  try {
    joinOpcodes(registry, withDriftedTheorem);
    fail('an opcode theorem drifted from ir.ts was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('names theorem')) throw error;
  }
  try {
    joinOpcodes(registry, undefined);
    fail('an absent ir.ts opcode table was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('is not joined')) throw error;
  }

  try {
    checkFrozenSource(registry, () => {
      throw new Error('absent');
    });
    fail('an absent frozen specification page was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('is absent')) throw error;
  }
  try {
    checkFrozenSource(registry, () => Buffer.from('not the specification'));
    fail('a frozen specification page that does not match its digest was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('hashes to')) throw error;
  }
  const bareDigest = structuredClone(registry);
  bareDigest.assumptions[0].sourceDigest = bareDigest.assumptions[0].sourceDigest.slice(7);
  try {
    checkFrozenSource(bareDigest, () => Buffer.from('anything'));
    fail('a digest that does not name its hash was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('does not name its hash')) throw error;
  }
  const unresolvedClause = structuredClone(registry);
  unresolvedClause.assumptions[0].clauses = ['sec-not-a-clause'];
  const clausePage = Buffer.from('<span id="sec-binary-logical-operators"></span>');
  unresolvedClause.assumptions[0].sourceDigest = `sha256:${createHash('sha256')
    .update(clausePage)
    .digest('hex')}`;
  try {
    checkFrozenSource(unresolvedClause, () => clausePage);
    fail('a clause that does not resolve in the frozen page was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('does not resolve')) throw error;
  }

  const brokenProbe = structuredClone(suite);
  brokenProbe.groups[0].probes[0].expect = { boolean: true };
  try {
    runProbes(brokenProbe);
    fail('a probe disagreeing with the engine was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('but the model predicts')) throw error;
  }

  const withDriftedDigest = structuredClone(registry);
  withDriftedDigest.assumptions[0].statement = 'something else';
  expectJoinFailure(
    'a drifted canonical wording',
    withDriftedDigest,
    kinds,
    emitted,
    scenarios,
    'carries a canonical wording that does not match its recorded fields',
  );

  const cleanScan = forbiddenTokenViolations([
    { label: 'clean', source: '/-- A comment mentioning sorry and axiom. -/\ntheorem clean : True := trivial\n' },
  ]);
  if (cleanScan.length > 0) fail(`the token scan reported a clean module: ${cleanScan.join(', ')}`);
  const dirtyScan = forbiddenTokenViolations([
    { label: 'dirty', source: 'theorem broken : True := by sorry\n' },
  ]);
  if (dirtyScan.length !== 1) fail('the token scan accepted a sorry');
  stdout.write(
    'semantics registry self-test passed: 8 join fixtures, 3 opcode-join fixtures, ' +
      '4 frozen-source fixtures, 1 lock fixture, 1 probe fixture, 6 Lean fixtures, ' +
      '2 token scans\n',
  );
}

function main() {
  const args = parseArgs(argv.slice(2));
  if (args.selfTest) return selfTest();
  const registry = leanRegistry();
  const suite = JSON.parse(readFileSync(probesPath, 'utf8'));
  const probes = runProbes(suite);
  const counts = joinRegistries(registry, decoderKinds(), emitterKinds(), probes.groups);
  const paired = checkTheoremNames(registry);
  const violations = forbiddenTokenViolations(semanticsSources());
  if (violations.length > 0) {
    fail(`the semantics carries ${violations.length} forbidden construct(s):\n  ${violations.sort().join('\n  ')}`);
  }
  const audited = auditAxioms();
  const serialized = `${JSON.stringify(registry, null, 2)}\n`;
  if (args.generate) {
    writeFileSync(lockedRegistryPath, serialized);
    stdout.write(`Wrote ${lockedRegistryPath.slice(root.length + 1)}\n`);
  } else {
    if (!existsSync(lockedRegistryPath)) fail(`${lockedRegistryPath.slice(root.length + 1)} is absent; run --generate`);
    compareWithLocked(registry, readFileSync(lockedRegistryPath, 'utf8'));
  }
  // The frozen-source and opcode joins run last so a refusal cannot stop the lock from being
  // refreshed: the run still fails, but `--generate` writes what Lean reported first.
  checkFrozenSource(registry);
  // The opcode join runs last so a refusal cannot stop the lock from being refreshed: the run still
  // fails, but `--generate` writes what Lean reported before reporting the unjoined registry.
  const joinedOpcodes = joinOpcodes(registry, declaredOpcodes());
  stdout.write(
    `Semantics registry gate passed: ${counts.expressions} expression operations, ` +
      `${counts.declarations} declaration families, ${counts.types} type forms, ` +
      `${counts.opcodes} opcodes paired with ${paired} theorems and joined to ${joinedOpcodes} ir.ts rows, ` +
      `${counts.assumptions} assumptions ` +
      `measured by ${probes.total} executed probes in ${probes.groups.size} groups, ` +
      `${audited} audited declarations\n`,
  );
}

if (import.meta.main) main();
