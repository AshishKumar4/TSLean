import { Buffer } from 'node:buffer';
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

/** Self-test tables are plain JSON, so a parse of their serialization is an exact copy. */
function cloneJson(value) {
  return JSON.parse(JSON.stringify(value));
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

/**
 * The kinds one declaration's own dispatch admits, keyed on the declaration and on the value it
 * discriminates.
 *
 * The reader takes the switch `functionName` runs on `discriminant` in its own body, and nothing
 * else. A switch inside a nested function belongs to that function; a second dispatch on the same
 * value is a lowering path this join would only half see; a case whose test is not a string literal
 * names a kind the gate cannot read; a `default` clause that does anything but throw admits a kind
 * no plane declares. Each one is a refusal, because each is a way for the joined set to stop being
 * the set the declaration actually admits. Taking the text as an argument is what lets `--self-test`
 * exercise the reader on sources of its own.
 */
export function readDispatchedKinds(file, text, functionName, discriminant) {
  const source = ts.createSourceFile(file, text, ts.ScriptTarget.ESNext, true);
  const declarations = [];
  const visit = (node) => {
    if (ts.isFunctionDeclaration(node) && node.name?.text === functionName) declarations.push(node);
    ts.forEachChild(node, visit);
  };
  visit(source);
  if (declarations.length === 0) fail(`${file} declares no function ${functionName}`);
  if (declarations.length > 1) {
    fail(`${file} declares ${declarations.length} functions named ${functionName}, so the dispatch is ambiguous`);
  }
  const [declaration] = declarations;
  if (declaration.body === undefined) fail(`${file}#${functionName} declares no body`);
  const dispatches = ownSwitches(declaration.body).filter((statement) =>
    discriminatesOn(statement.expression, discriminant),
  );
  if (dispatches.length === 0) fail(`${file}#${functionName} runs no switch on ${discriminant}`);
  if (dispatches.length > 1) {
    fail(`${file}#${functionName} runs ${dispatches.length} switches on ${discriminant}`);
  }
  const [dispatch] = dispatches;
  const kinds = [];
  for (const clause of dispatch.caseBlock.clauses) {
    if (ts.isDefaultClause(clause)) {
      const [only] = clause.statements;
      if (clause.statements.length !== 1 || only === undefined || !ts.isThrowStatement(only)) {
        fail(`${file}#${functionName} carries a default clause that does not refuse the kinds it did not test`);
      }
      continue;
    }
    if (!ts.isStringLiteral(clause.expression)) {
      fail(`${file}#${functionName} tests a case the gate cannot read as a kind`);
    }
    if (kinds.includes(clause.expression.text)) {
      fail(`${file}#${functionName} tests ${clause.expression.text} twice`);
    }
    kinds.push(clause.expression.text);
  }
  if (kinds.length === 0) fail(`${file}#${functionName} tests no string literal`);
  return kinds;
}

/** Every switch a body runs itself. A nested function's dispatch is that function's own. */
function ownSwitches(body) {
  const switches = [];
  const collect = (node) => {
    if (
      ts.isFunctionDeclaration(node) ||
      ts.isFunctionExpression(node) ||
      ts.isArrowFunction(node) ||
      ts.isClassDeclaration(node) ||
      ts.isClassExpression(node) ||
      ts.isMethodDeclaration(node)
    ) {
      return;
    }
    if (ts.isSwitchStatement(node)) switches.push(node);
    ts.forEachChild(node, collect);
  };
  ts.forEachChild(body, collect);
  return switches;
}

/** Whether a switch subject is exactly the named value: one identifier, or a dotted read of one. */
function discriminatesOn(expression, discriminant) {
  const parts = [];
  let node = expression;
  while (ts.isPropertyAccessExpression(node)) {
    if (!ts.isIdentifier(node.name)) return false;
    parts.unshift(node.name.text);
    node = node.expression;
  }
  if (!ts.isIdentifier(node)) return false;
  parts.unshift(node.text);
  return parts.join('.') === discriminant;
}

/** The kinds the live source's named dispatch admits. */
function dispatchedKinds(file, functionName, discriminant) {
  return readDispatchedKinds(file, readFileSync(file, 'utf8'), functionName, discriminant);
}

/**
 * Every declaration kind the emitter's declaration dispatch admits, read from the IR decoder. Each
 * decoder reads the kind out of the encoded object first and dispatches on that binding, so the
 * discriminant is the binding rather than a property read.
 */
function decoderKinds() {
  const irFile = join(root, 'src/lean-to-typescript/ir.ts');
  return {
    expressions: dispatchedKinds(irFile, 'decodeExpression', 'kind'),
    declarations: dispatchedKinds(irFile, 'decodeDeclaration', 'kind'),
    types: dispatchedKinds(irFile, 'decodeType', 'kind'),
  };
}

/**
 * The literal string constants a module declares, as `name -> value`.
 *
 * The opcode table spells each theorem name as `${MODEL_NAMESPACE}.<name>`, so the reader resolves
 * that constant instead of comparing the template's source text. Only a constant of the same module
 * with a literal string initialiser is resolvable; `literalText` refuses everything else rather than
 * guessing.
 */
function literalConstants(source) {
  const constants = new Map();
  const visit = (node) => {
    if (
      ts.isVariableDeclaration(node) &&
      ts.isIdentifier(node.name) &&
      node.initializer !== undefined &&
      (ts.isStringLiteral(node.initializer) || ts.isNoSubstitutionTemplateLiteral(node.initializer))
    ) {
      constants.set(node.name.text, node.initializer.text);
    }
    ts.forEachChild(node, visit);
  };
  visit(source);
  return constants;
}

/**
 * One recorded string of the opcode table, with the single sanctioned interpolation resolved.
 *
 * A plain literal is its own text. A template is admitted in exactly one form — `${CONSTANT}rest`,
 * where `CONSTANT` is a literal string constant of the same module — because that is the one form
 * `ir.ts` writes, and resolving it is what lets a theorem name be joined against Lean rather than
 * compared as template source text. Every other shape is a refusal: a value this reader cannot
 * resolve would be joined against nothing, which is the failure mode the join exists to prevent.
 */
function literalText(node, label, constants) {
  if (ts.isStringLiteral(node) || ts.isNoSubstitutionTemplateLiteral(node)) return node.text;
  if (!ts.isTemplateExpression(node)) {
    fail(`ir.ts ${label} is neither a string nor a template, so the gate cannot join it`);
  }
  if (node.head.text !== '') {
    fail(`ir.ts ${label} interpolates after leading text, which this reader does not resolve`);
  }
  if (node.templateSpans.length !== 1) {
    fail(`ir.ts ${label} interpolates ${node.templateSpans.length} values; exactly one is admitted`);
  }
  const [span] = node.templateSpans;
  if (!ts.isIdentifier(span.expression)) {
    fail(`ir.ts ${label} interpolates an expression rather than a declared constant`);
  }
  const value = constants.get(span.expression.text);
  if (value === undefined) {
    fail(
      `ir.ts ${label} interpolates ${span.expression.text}, which the module declares no literal ` +
        'string constant for',
    );
  }
  return `${value}${span.literal.text}`;
}

/**
 * The runtime opcode table a module declares, as `kind -> { modelTheorem, runtimeSymbol,
 * assumptions, components }`.
 *
 * The table is the only place the compiler names a primitive operation, so it is the only thing the
 * opcode half of the Lean registry can be joined against. Its absence is reported rather than
 * skipped: an unjoined opcode registry is a registry nothing checks. Taking the text as an argument
 * is what lets `--self-test` exercise this reader on a source of its own.
 */
export function readDeclaredOpcodes(file, text) {
  const source = ts.createSourceFile(file, text, ts.ScriptTarget.ESNext, true);
  const constants = literalConstants(source);
  let table;
  const visit = (node) => {
    if (ts.isVariableDeclaration(node) && ts.isIdentifier(node.name) && node.name.text === 'LEAN_RUNTIME_OPCODES') {
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
    let runtimeSymbol;
    let components = [];
    for (const field of property.initializer.properties) {
      if (!ts.isPropertyAssignment(field) || !ts.isIdentifier(field.name)) continue;
      if (field.name.text === 'modelTheorem') {
        modelTheorem = literalText(field.initializer, `opcode row ${kind} modelTheorem`, constants);
      }
      if (field.name.text === 'runtimeSymbol') {
        runtimeSymbol = literalText(field.initializer, `opcode row ${kind} runtimeSymbol`, constants);
      }
      if (field.name.text === 'assumptions' && ts.isArrayLiteralExpression(field.initializer)) {
        assumptions = field.initializer.elements.map((element, index) =>
          literalText(element, `opcode row ${kind} assumption ${index}`, constants),
        );
      }
      if (field.name.text === 'components' && ts.isArrayLiteralExpression(field.initializer)) {
        components = field.initializer.elements.map((element, index) =>
          literalText(element, `opcode row ${kind} component ${index}`, constants),
        );
      }
    }
    if (modelTheorem === undefined) fail(`ir.ts opcode row ${kind} names no modelTheorem`);
    if (assumptions === undefined) fail(`ir.ts opcode row ${kind} names no assumptions`);
    if (runtimeSymbol === undefined) fail(`ir.ts opcode row ${kind} names no runtimeSymbol`);
    rows.set(kind, { modelTheorem, assumptions, runtimeSymbol, components });
  }
  return rows;
}

/** The runtime opcode table the live `ir.ts` declares. */
function declaredOpcodes() {
  const file = join(root, 'src/lean-to-typescript/ir.ts');
  return readDeclaredOpcodes(file, readFileSync(file, 'utf8'));
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
    // The tagged runtime symbol is the same spelling on both sides, so the emitted role each opcode
    // reaches the target as is joined rather than restated: an opcode the emitter inlines and the
    // semantics proves as a helper, or the reverse, differs here.
    if (row.runtimeSymbol !== opcode.runtimeSymbol) {
      fail(
        `opcode ${opcode.opcode} names runtime symbol ${row.runtimeSymbol} in ir.ts but ` +
          `${opcode.runtimeSymbol} in Lean`,
      );
    }
    if (JSON.stringify(row.components) !== JSON.stringify(opcode.components)) {
      fail(
        `opcode ${opcode.opcode} composes ${JSON.stringify(row.components)} in ir.ts but ` +
          `${JSON.stringify(opcode.components)} in Lean`,
      );
    }
  }
  return declaredKinds.length;
}

/**
 * Joins the emitted form the Lean registry records for each inline opcode against the form the live
 * `emitter.ts` prints for it.
 *
 * The forms come from `inlineOperationForms`, which builds each opcode's emitted syntax through the
 * one function that emitter lowers an operation with and prints it canonically over the operand
 * names the row declares. Comparing the two strings byte for byte is what makes an inline opcode's
 * certificate a claim about emitted structure: the digest a package records is over this print, so a
 * form that drifted from the row is refused here and at every package verification instead of being
 * digested from the row and agreeing with itself.
 */
export function joinInlineForms(registry, forms) {
  const inline = registry.opcodes.filter((opcode) => opcode.runtimeSymbol.startsWith('inline:'));
  requireSameSet(
    'inline emitted forms',
    [...forms.keys()].sort(),
    'emitter.ts',
    inline.map((opcode) => opcode.opcode).sort(),
    'the Lean semantics',
  );
  for (const opcode of inline) {
    const printed = forms.get(opcode.opcode);
    if (printed !== opcode.emittedForm) {
      fail(
        `opcode ${opcode.opcode} emits ${JSON.stringify(printed)} but the Lean semantics records ` +
          `${JSON.stringify(opcode.emittedForm)}`,
      );
    }
  }
  return inline.length;
}

/** The inline forms the live emitter prints, read through the module the compiler lowers with. */
async function emittedInlineForms() {
  const { inlineOperationForms } = await import('../src/lean-to-typescript/emitter.ts');
  return inlineOperationForms();
}

/** Every expression kind the emitter lowers. */
function emitterKinds() {
  return dispatchedKinds(join(root, 'src/lean-to-typescript/emitter.ts'), 'emitExpression', 'expression.kind');
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
  const leanTypes = sortedUnique(
    registry.typeForms.map((entry) => entry.kind),
    'Lean type registry',
  );
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
    for (const field of [
      'id',
      'sourceUrl',
      'sourceArtifact',
      'sourceDigest',
      'statement',
      'oracle',
      'canonicalWording',
    ]) {
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
      fail(
        `assumption ${assumption.id} names probe group ${assumption.oracle}, which spec/semantics/probes.json does not declare`,
      );
    }
    for (const family of assumption.coverage) {
      if (!group.has(family)) {
        fail(
          `assumption ${assumption.id} requires coverage family ${family}, which no probe in ${assumption.oracle} measures`,
        );
      }
    }
    for (const family of group) {
      if (!assumption.coverage.includes(family)) {
        fail(
          `probe group ${assumption.oracle} measures family ${family}, which assumption ${assumption.id} does not require`,
        );
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
    if (!Array.isArray(opcode.components)) {
      fail(`opcode ${opcode.opcode} records no components list`);
    }
    // Every runtime symbol says how the opcode reaches the target, not only what it is spelled as.
    // `inline:` is a form the emitter writes at the use site and has no body to bind; `helper:` is a
    // generated helper, which does, and which certifies the semantic components it composes. A row
    // that claimed neither could not be joined against the emitted bytes at all.
    const tag = ['inline:', 'helper:'].find((prefix) => opcode.runtimeSymbol.startsWith(prefix));
    if (tag === undefined) {
      fail(
        `opcode ${opcode.opcode} records runtime symbol ${opcode.runtimeSymbol}, which names no ` +
          'emitted role; write it as inline:<form> or helper:<name>',
      );
    }
    if (opcode.runtimeSymbol.length === tag.length) {
      fail(`opcode ${opcode.opcode} records the bare tag ${tag} and no emitted role`);
    }
    if (tag === 'inline:' && opcode.runtimeSymbol !== `inline:${opcode.opcode}`) {
      fail(
        `opcode ${opcode.opcode} is emitted inline but its runtime symbol ` +
          `${opcode.runtimeSymbol} names a different opcode`,
      );
    }
    if (opcode.components.length > 0 !== (tag === 'helper:')) {
      fail(
        tag === 'helper:'
          ? `opcode ${opcode.opcode} reaches the target as a generated helper but certifies no components`
          : `opcode ${opcode.opcode} is emitted inline but certifies helper components`,
      );
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
  if (artifacts.size !== 1)
    fail(`the assumptions cite ${artifacts.size} frozen artifacts; one page, one digest, one join`);
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
    fail(
      `the frozen specification page is absent: ${path} is not in the tree, so the declared digest ${assumption.sourceDigest} is unverified`,
    );
  }
  const prefix = 'sha256:';
  if (!assumption.sourceDigest.startsWith(prefix)) {
    fail(`the frozen source digest ${assumption.sourceDigest} does not name its hash; write it as sha256:<hex>`);
  }
  const observed = `${prefix}${createHash('sha256').update(bytes).digest('hex')}`;
  if (observed !== assumption.sourceDigest) {
    fail(
      `the frozen specification page ${path} hashes to ${observed} but the registry declares ${assumption.sourceDigest}`,
    );
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
  // The v5 kinds: the dense-array representation, the lazy boolean operators, the dense array read
  // and the element order the higher-order opcodes enter their callback in.
  expectLeanFailure('semantics-list-as-tagged-object.lean', 'Type mismatch');
  expectLeanFailure('semantics-eager-boolean-and.lean', 'unsolved goals');
  expectLeanFailure('semantics-array-hole-reads-undefined.lean', 'unsolved goals');
  expectLeanFailure('semantics-map-reverses-event-order.lean', 'unsolved goals');

  const withoutAssumption = cloneJson(registry);
  // The dropped assumption has to be one no other opcode requires, or the plane still has a requirer
  // and the refusal this fixture exists to provoke never fires. Taking the first multi-assumption row
  // and popping its last entry does not guarantee that, so the pair is searched for and its absence
  // is itself a failure: a fixture that silently stops discriminating is worse than no fixture.
  const orphanable = withoutAssumption.opcodes.flatMap((opcode) =>
    opcode.requires.length > 1
      ? opcode.requires
          .filter((id) => withoutAssumption.opcodes.every((other) => other === opcode || !other.requires.includes(id)))
          .map((id) => ({ opcode, id }))
      : [],
  );
  if (orphanable.length === 0) {
    fail('no opcode carries an assumption that dropping it would leave unrequired');
  }
  const [{ opcode: donor, id: dropped }] = orphanable;
  donor.requires = donor.requires.filter((id) => id !== dropped);
  expectJoinFailure(
    'a missing assumption',
    withoutAssumption,
    kinds,
    emitted,
    scenarios,
    `assumption ${dropped} is declared but no opcode requires it`,
  );

  const withUndeclaredAssumption = cloneJson(registry);
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
  const withExtraAssumption = cloneJson(registry);
  withExtraAssumption.opcodes[0].requires.push('bigint.relational');
  joinRegistries(withExtraAssumption, kinds, emitted, scenarios);
  try {
    compareWithLocked(withExtraAssumption, locked);
    fail('an extra declared assumption was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('is stale')) throw error;
  }

  const withWrongOperation = cloneJson(registry);
  withWrongOperation.expressionOperations.push({ constructor: 'Fixture.bogus', kind: 'variables' });
  expectJoinFailure(
    'an operation the decoder does not admit',
    withWrongOperation,
    kinds,
    emitted,
    scenarios,
    'the Lean semantics admits variables but ir.ts does not',
  );

  const withMissingOperation = cloneJson(registry);
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
    const withoutKind = cloneJson(registry);
    withoutKind.expressionOperations = withoutKind.expressionOperations.filter((entry) => entry.kind !== kind);
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
        runtimeSymbol: opcode.runtimeSymbol,
        components: [...opcode.components],
      },
    ]),
  );
  joinOpcodes(registry, declared);
  const withDriftedClosure = new Map(declared);
  const firstKind = registry.opcodes[0].opcode;
  withDriftedClosure.set(firstKind, {
    modelTheorem: declared.get(firstKind).modelTheorem,
    assumptions: [...declared.get(firstKind).assumptions, 'bigint.relational'],
    runtimeSymbol: declared.get(firstKind).runtimeSymbol,
    components: [...declared.get(firstKind).components],
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
    runtimeSymbol: declared.get(firstKind).runtimeSymbol,
    components: [...declared.get(firstKind).components],
  });
  try {
    joinOpcodes(registry, withDriftedTheorem);
    fail('an opcode theorem drifted from ir.ts was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('names theorem')) throw error;
  }
  const withDriftedSymbol = new Map(declared);
  withDriftedSymbol.set(firstKind, {
    modelTheorem: declared.get(firstKind).modelTheorem,
    assumptions: [...declared.get(firstKind).assumptions],
    runtimeSymbol: 'helper:invented-role',
    components: [...declared.get(firstKind).components],
  });
  try {
    joinOpcodes(registry, withDriftedSymbol);
    fail('an opcode runtime symbol drifted from ir.ts was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('names runtime symbol')) throw error;
  }
  try {
    joinOpcodes(registry, undefined);
    fail('an absent ir.ts opcode table was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('is not joined')) throw error;
  }

  // `ir.ts` spells each theorem name as `${MODEL_NAMESPACE}.<name>`. The reader has to resolve that
  // one interpolation, because comparing the template's source text against Lean's resolved name
  // joins nothing and fails every row. It also has to refuse an interpolation it cannot resolve,
  // rather than fall back to source text and start passing again.
  const templateTable = [
    "const MODEL_NAMESPACE = 'Fixture.Namespace';",
    'export const LEAN_RUNTIME_OPCODES = {',
    "  'bool.and': {",
    "    runtimeSymbol: 'inline:bool.and',",
    '    modelTheorem: `${MODEL_NAMESPACE}.boolAndModelsAnd`,',
    "    assumptions: ['boolean.logical-operators'],",
    '  },',
    '};',
  ].join('\n');
  const resolvedRow = readDeclaredOpcodes('fixture.ts', templateTable).get('bool.and');
  if (resolvedRow === undefined) fail('the opcode reader read no row from the template fixture');
  if (resolvedRow.modelTheorem !== 'Fixture.Namespace.boolAndModelsAnd') {
    fail('the opcode reader did not resolve the sanctioned interpolation: it read ' + `${resolvedRow.modelTheorem}`);
  }
  try {
    readDeclaredOpcodes('fixture.ts', templateTable.replace('MODEL_NAMESPACE}', 'INVENTED}'));
    fail('an unresolvable interpolation in the opcode table was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('declares no literal string constant')) {
      throw error;
    }
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
  const bareDigest = cloneJson(registry);
  bareDigest.assumptions[0].sourceDigest = bareDigest.assumptions[0].sourceDigest.slice(7);
  try {
    checkFrozenSource(bareDigest, () => Buffer.from('anything'));
    fail('a digest that does not name its hash was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('does not name its hash')) throw error;
  }
  const unresolvedClause = cloneJson(registry);
  unresolvedClause.assumptions[0].clauses = ['sec-not-a-clause'];
  const clausePage = Buffer.from('<span id="sec-binary-logical-operators"></span>');
  unresolvedClause.assumptions[0].sourceDigest = `sha256:${createHash('sha256').update(clausePage).digest('hex')}`;
  try {
    checkFrozenSource(unresolvedClause, () => clausePage);
    fail('a clause that does not resolve in the frozen page was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('does not resolve')) throw error;
  }

  const brokenProbe = cloneJson(suite);
  brokenProbe.groups[0].probes[0].expect = { boolean: true };
  try {
    runProbes(brokenProbe);
    fail('a probe disagreeing with the engine was accepted');
  } catch (error) {
    if (!(error instanceof Error) || !error.message.includes('but the model predicts')) throw error;
  }

  const withUntaggedSymbol = cloneJson(registry);
  withUntaggedSymbol.opcodes[0].runtimeSymbol = '&&';
  expectJoinFailure(
    'an untagged runtime symbol',
    withUntaggedSymbol,
    kinds,
    emitted,
    scenarios,
    'which names no emitted role',
  );

  const withDriftedDigest = cloneJson(registry);
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
  const dirtyScan = forbiddenTokenViolations([{ label: 'dirty', source: 'theorem broken : True := by sorry\n' }]);
  if (dirtyScan.length !== 1) fail('the token scan accepted a sorry');

  // The inline-form join, against a printed map the fixture owns. The live emitter is joined in
  // `main`, where a difference between what it prints and what Lean records is the finding; here the
  // point is that the comparison discriminates at all.
  const inlineOpcodes = registry.opcodes.filter((opcode) => opcode.runtimeSymbol.startsWith('inline:'));
  const [firstInline] = inlineOpcodes;
  if (firstInline === undefined) fail('the registry records no inline opcode to join a printed form against');
  const printedForms = new Map(inlineOpcodes.map((opcode) => [opcode.opcode, opcode.emittedForm]));
  joinInlineForms(registry, printedForms);
  const expectFormFailure = (label, forms, expected) => {
    try {
      joinInlineForms(registry, forms);
    } catch (error) {
      if (error instanceof Error && error.message.includes(expected)) return;
      throw error;
    }
    fail(`${label} was accepted`);
  };
  const driftedForm = new Map(printedForms);
  driftedForm.set(firstInline.opcode, `(${firstInline.emittedForm})`);
  expectFormFailure(
    'an inline form the emitter prints differently from the registry',
    driftedForm,
    'but the Lean semantics records',
  );
  const unprintedForm = new Map(printedForms);
  unprintedForm.delete(firstInline.opcode);
  expectFormFailure(
    'an inline opcode the emitter prints no form for',
    unprintedForm,
    `the Lean semantics admits ${firstInline.opcode} but emitter.ts does not`,
  );
  const helperOpcode = registry.opcodes.find((opcode) => opcode.runtimeSymbol.startsWith('helper:'));
  if (helperOpcode === undefined) fail('the registry records no helper opcode to keep out of the inline join');
  const inlinedHelper = new Map(printedForms);
  inlinedHelper.set(helperOpcode.opcode, helperOpcode.emittedForm);
  expectFormFailure(
    'an inline form printed for an opcode the semantics proves as a helper',
    inlinedHelper,
    `emitter.ts admits ${helperOpcode.opcode} but the Lean semantics does not`,
  );

  // The dispatch reader is keyed on the declaration and on the value it discriminates, so a nested
  // function's switch, a second dispatch, a case the gate cannot read, a repeated case, a default
  // that admits instead of refusing, and an ambiguous declaration are refusals rather than a quietly
  // different joined set.
  const nestedDispatch = [
    'function decodeFixture(value) {',
    "  const kind = value['kind'];",
    '  const nested = (inner) => {',
    '    switch (kind) {',
    "      case 'nested':",
    '        return inner;',
    '    }',
    '  };',
    '  switch (kind) {',
    "    case 'variable':",
    "    case 'operation':",
    '      return nested(value);',
    '    default:',
    "      throw new TypeError('unsupported');",
    '  }',
    '}',
  ].join('\n');
  const readKinds = readDispatchedKinds('fixture.ts', nestedDispatch, 'decodeFixture', 'kind');
  if (JSON.stringify(readKinds) !== JSON.stringify(['variable', 'operation'])) {
    fail(`the dispatch reader read ${JSON.stringify(readKinds)} from the nested-switch fixture`);
  }
  const expectDispatchFailure = (label, text, expected) => {
    try {
      readDispatchedKinds('fixture.ts', text, 'decodeFixture', 'kind');
    } catch (error) {
      if (error instanceof Error && error.message.includes(expected)) return;
      throw error;
    }
    fail(`${label} was accepted`);
  };
  expectDispatchFailure(
    'a second dispatch on the same value',
    nestedDispatch.replace(
      '  switch (kind) {\n    case ',
      "  switch (kind) {\n    case 'extra':\n      return value;\n  }\n  switch (kind) {\n    case ",
    ),
    'runs 2 switches on kind',
  );
  expectDispatchFailure(
    'a case the gate cannot read as a kind',
    nestedDispatch.replace("    case 'variable':", '    case names[0]:'),
    'tests a case the gate cannot read as a kind',
  );
  expectDispatchFailure(
    'a repeated case',
    nestedDispatch.replace("    case 'operation':", "    case 'variable':"),
    'tests variable twice',
  );
  expectDispatchFailure(
    'a default clause that admits the kinds it did not test',
    nestedDispatch.replace("      throw new TypeError('unsupported');", '      return value;'),
    'does not refuse the kinds it did not test',
  );
  expectDispatchFailure(
    'two declarations of the same dispatch',
    `${nestedDispatch}\n${nestedDispatch}`,
    'so the dispatch is ambiguous',
  );
  expectDispatchFailure(
    'a dispatch on a different value',
    nestedDispatch.replaceAll('switch (kind) {', 'switch (value.kind) {'),
    'runs no switch on kind',
  );
  stdout.write(
    'semantics registry self-test passed: 9 join fixtures, 4 opcode-join fixtures, ' +
      '2 opcode-reader fixtures, 4 inline-form fixtures, 7 dispatch-reader fixtures, ' +
      '4 frozen-source fixtures, 1 lock fixture, 1 probe fixture, ' +
      '10 Lean fixtures, 2 token scans\n',
  );
}

async function main() {
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
  const joinedForms = joinInlineForms(registry, await emittedInlineForms());
  stdout.write(
    `Semantics registry gate passed: ${counts.expressions} expression operations, ` +
      `${counts.declarations} declaration families, ${counts.types} type forms, ` +
      `${counts.opcodes} opcodes paired with ${paired} theorems and joined to ${joinedOpcodes} ir.ts rows, ` +
      `${joinedForms} inline forms printed by emitter.ts and compared byte for byte, ` +
      `${counts.assumptions} assumptions ` +
      `measured by ${probes.total} executed probes in ${probes.groups.size} groups, ` +
      `${audited} audited declarations\n`,
  );
}

if (import.meta.main) await main();
