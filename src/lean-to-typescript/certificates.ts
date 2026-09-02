/**
 * @module lean-to-typescript/certificates
 *
 * A runtime declaration's digest is defined by the printer that wrote the declaration, so the
 * re-parse and re-print that take one run on the emission compiler
 * {@link module:typescript-api/emitted-syntax} holds — the compiler the emitter printed the
 * package with.
 */

import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

import { emitted as ts } from '../typescript-api/emitted-syntax.js';
import { compareCodePoints } from './ordering.js';

const specRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..', '..', 'spec');

/**
 * What Lean declares about an external bridge. Engine version, disposition and executed counts are
 * deliberately absent: those are observations of a running engine, not normative declarations, and
 * they live with the runtime evidence keyed by this id.
 */
export interface RuntimeAssumption {
  readonly id: string;
  readonly sourceUrl: string;
  readonly sourceArtifact: string;
  readonly sourceDigest: string;
  readonly clauses: readonly string[];
  readonly coverage: readonly string[];
  readonly oracle: string;
}

export interface RuntimeCertificate {
  readonly opcode: string;
  readonly theorem: string;
  readonly runtimeSymbol: string;
  readonly model: string;
  readonly relation: string;
  readonly emittedForm: string;
  readonly components: readonly string[];
  readonly assumptions: readonly string[];
}

/** The Lean-owned closed registry: the one declaration source this compiler reads. */
export interface RuntimeCertificateCatalog {
  readonly assumptions: readonly RuntimeAssumption[];
  readonly certificates: readonly RuntimeCertificate[];
}

/** The only compiler input that may witness the executing engine binary. */
export const RUNTIME_BINARY_INPUT = 'compiler:runtime';

/** The only compiler input that may witness the declaration registry. */
export const RUNTIME_REGISTRY_INPUT = 'compiler:spec:semantics/registry.json';

/** The only compiler input that may witness the executed probe corpus. */
export const RUNTIME_EVIDENCE_INPUT = 'compiler:spec:semantics/probes.json';

/**
 * What a generated package records about a certificate it spends: which opcode, which registry
 * runtime symbol, which declaration that symbol resolved to in this package, and the digest of the
 * bytes behind it. Theorem, model and assumption closure are deliberately absent, because they
 * belong to the registry and a copy here would be a second source that could drift from the proof.
 * The declaration is the opposite: it is an observation of this package's own bytes, which nothing
 * else records, and it is empty for an inline opcode because inline code has no declaration.
 */
export interface RuntimeCertificateBinding {
  readonly opcode: string;
  readonly runtimeSymbol: string;
  readonly declaration: string;
  readonly runtimeBodySha256: string;
}

/**
 * One certificate's named assumption, and the evidence that witnessed it. The engine is not
 * repeated here: the environment attestation records it once and may be re-attested, so a copy in
 * every row would be a second reading of the same fact that re-attestation could contradict.
 */
export interface RuntimeConformanceAttestation {
  readonly certificate: string;
  readonly assumption: string;
  readonly oracle: string;
  readonly binaryInput: string;
  readonly binarySha256: string;
  readonly evidenceInput: string;
  readonly oracleSha256: string;
  readonly runtimeSymbol: string;
  readonly runtimeBodySha256: string;
}

/**
 * Reads the Lean-owned registry. Only the fields this compiler binds are taken: the prose
 * statement and the canonical wording exist to detect drift inside the proof library and are its
 * business, not the artifact's.
 */
export function decodeRuntimeCertificateCatalog(value: unknown, location: string): RuntimeCertificateCatalog {
  const registry = object(value, location);
  if (registry['schemaVersion'] !== 1) throw new TypeError(`${location}.schemaVersion is unsupported`);
  const assumptions = list(registry['assumptions'], `${location}.assumptions`).map((entry, index) =>
    decodeAssumption(entry, `${location}.assumptions[${index}]`),
  );
  // The registry's row order is generated from Lean and carries meaning there; this reader only
  // requires that no row is named twice.
  requireDistinct(
    assumptions.map((assumption) => assumption.id),
    `${location}.assumptions`,
  );
  const knownAssumptions = new Set(assumptions.map((assumption) => assumption.id));
  const certificates = list(registry['opcodes'], `${location}.opcodes`).map((entry, index) =>
    decodeCertificate(entry, knownAssumptions, `${location}.opcodes[${index}]`),
  );
  requireDistinct(
    certificates.map((certificate) => certificate.opcode),
    `${location}.opcodes`,
  );
  return { assumptions, certificates };
}

function requireDistinct(values: readonly string[], location: string): void {
  if (new Set(values).size !== values.length) throw new TypeError(`${location} must not name a row twice`);
}

/**
 * The one registry this compiler reads, with the bytes it read, so an artifact can bind the exact
 * declaration source rather than a copy of it.
 */
export function loadRuntimeCertificateRegistry(): {
  readonly catalog: RuntimeCertificateCatalog;
  readonly path: string;
  readonly sha256: string;
} {
  const path = join(specRoot, 'semantics', 'registry.json');
  const bytes = readFileSync(path);
  return {
    catalog: decodeRuntimeCertificateCatalog(JSON.parse(bytes.toString('utf8')), path),
    path,
    sha256: `sha256:${createHash('sha256').update(bytes).digest('hex')}`,
  };
}

/** The executed probe corpus the Lean registry gate runs; bound here, never re-executed. */
export function loadRuntimeProbeCorpus(): { readonly path: string; readonly sha256: string } {
  const path = join(specRoot, 'semantics', 'probes.json');
  const bytes = readFileSync(path);
  return { path, sha256: `sha256:${createHash('sha256').update(bytes).digest('hex')}` };
}

export function certificateForOpcode(catalog: RuntimeCertificateCatalog, opcode: string): RuntimeCertificate {
  const certificate = catalog.certificates.find((entry) => entry.opcode === opcode);
  if (certificate === undefined) throw new TypeError(`runtime opcode has no Lean certificate: ${opcode}`);
  return certificate;
}

/** Refusal raised before any artifact exists, naming the opcode whose certificate is missing. */
export class RuntimeCertificateUnresolvedError extends TypeError {
  readonly opcode: string;

  constructor(opcode: string, reason: string) {
    super(`runtime-certificate-unresolved: ${opcode}: ${reason}`);
    this.name = 'RuntimeCertificateUnresolvedError';
    this.opcode = opcode;
  }
}

/**
 * Every opcode a program references must carry a Lean certificate that stands on something the
 * registry declares. A row stands on an engine assumption, or — where its emitted form is an
 * identity on an image two Lean types share — on the ordered model composition that makes it one.
 * A row with neither would be a lowering nothing accounts for. Compilation calls this before it
 * builds anything, so an opcode without a proved lowering cannot reach a manifest, a generated
 * module, or a reviewer.
 */
export function assertRuntimeOpcodeCertificates(opcodes: readonly string[], catalog: RuntimeCertificateCatalog): void {
  requireCanonicalOrder(opcodes, 'referenced runtime opcodes');
  for (const referenced of opcodes) {
    const certificate = catalog.certificates.find((entry) => entry.opcode === referenced);
    if (certificate === undefined) {
      throw new RuntimeCertificateUnresolvedError(referenced, 'no Lean certificate names this opcode');
    }
    if (certificate.assumptions.length === 0 && certificate.components.length === 0) {
      throw new RuntimeCertificateUnresolvedError(
        referenced,
        'certificate names neither an external assumption nor a model composition',
      );
    }
    for (const id of certificate.assumptions) {
      const assumption = catalog.assumptions.find((entry) => entry.id === id);
      if (assumption === undefined) {
        throw new RuntimeCertificateUnresolvedError(referenced, `assumption ${id} has no catalog record`);
      }
      if (assumption.coverage.length === 0) {
        throw new RuntimeCertificateUnresolvedError(referenced, `assumption ${id} declares no evidence coverage`);
      }
    }
  }
}

/**
 * Every opcode the compiler can emit carries a Lean certificate, and every certificate names an
 * opcode the compiler can emit. This is the coverage half of the join: `assertRuntimeOpcodeCertificates`
 * checks the opcodes one program reached, while this checks the registry against the whole admitted
 * set, so a row the Lean side proved and this compiler cannot emit — or the reverse — is refused
 * before any program is compiled rather than the first time one happens to use it.
 */
export function assertRuntimeCertificateCoverage(
  opcodes: readonly string[],
  catalog: RuntimeCertificateCatalog,
): void {
  const certified = new Set(catalog.certificates.map((certificate) => certificate.opcode));
  const admitted = new Set(opcodes);
  for (const opcode of opcodes) {
    if (!certified.has(opcode)) {
      throw new RuntimeCertificateUnresolvedError(opcode, 'the compiler admits this opcode and no Lean row certifies it');
    }
  }
  for (const certificate of catalog.certificates) {
    if (!admitted.has(certificate.opcode)) {
      throw new RuntimeCertificateUnresolvedError(
        certificate.opcode,
        'a Lean row certifies this opcode and the compiler does not admit it',
      );
    }
  }
}

/**
 * Checks every recorded binding against the registry and the bytes the package actually emitted. A
 * helper's digest is over the declaration the package prints; an inline opcode's digest is over the
 * form the emitter printed for it, so the comparison against `emittedForm` is a join between what
 * this compiler emits and what the Lean row states, byte for byte.
 */
export function assertRuntimeCertificateBindings(
  catalog: RuntimeCertificateCatalog,
  bindings: readonly RuntimeCertificateBinding[],
  bodies: readonly string[],
): void {
  requireCanonicalOrder(
    bindings.map((binding) => binding.opcode),
    'runtime certificate bindings',
  );
  for (const binding of bindings) {
    const certificate = certificateForOpcode(catalog, binding.opcode);
    if (binding.runtimeSymbol !== certificate.runtimeSymbol) {
      throw new TypeError(`runtime certificate binding does not match the registry: ${binding.opcode}`);
    }
    if (binding.runtimeSymbol.startsWith('inline:')) {
      if (binding.declaration !== '') {
        throw new TypeError(`an inline runtime form has no declaration: ${binding.opcode}`);
      }
      if (binding.runtimeBodySha256 !== runtimeBodyDigest(certificate.emittedForm)) {
        throw new TypeError(`inline runtime form digest does not match the registry: ${binding.opcode}`);
      }
      continue;
    }
    if (binding.declaration === '') {
      throw new TypeError(`a helper certificate must record the declaration it resolved: ${binding.opcode}`);
    }
    assertRuntimeCertificateBody(binding.declaration, binding.runtimeBodySha256, bodies);
  }
}

/**
 * The one place a claimed runtime body is checked against real source: the symbol must declare
 * exactly once across the candidate bodies, and that declaration must hash to the claimed digest.
 */
export function assertRuntimeCertificateBody(
  symbol: string,
  runtimeBodySha256: string,
  candidates: readonly string[],
): void {
  const carriers = candidates.filter((body) => declaresRuntimeSymbol(body, symbol));
  const [carrier] = carriers;
  if (carriers.length !== 1 || carrier === undefined) {
    throw new TypeError(`runtime certificate symbol must resolve exactly once: ${symbol}`);
  }
  if (runtimeDeclarationDigest(symbol, carrier) !== runtimeBodySha256) {
    throw new TypeError(`runtime certificate body digest does not match: ${symbol}`);
  }
}

/** Where a certificate's runtime symbol resolves: an emitted declaration, or an inline form. */
export type RuntimeSymbolBinding =
  | { readonly kind: 'declaration'; readonly declaration: string; readonly digest: string }
  | { readonly kind: 'inline'; readonly form: string; readonly digest: string };

/**
 * What the emitter knows after printing: which helper roles it declared under which names, and the
 * canonical print of every inline opcode's emitted form. The forms come from the emitter, never from
 * the registry: digesting them is what lets `assertRuntimeCertificateBindings` compare emitted
 * structure with the form Lean states instead of comparing the registry with itself.
 */
export interface RuntimeSymbolContext {
  readonly helperDeclarations: ReadonlyMap<string, string>;
  readonly inlineForms: ReadonlyMap<string, string>;
  readonly bodies: readonly string[];
}

/**
 * Resolves the tagged runtime symbol a certificate names. `inline:<opcode>` has no declaration and
 * binds to the form the emitter printed for that opcode; `helper:<role>` binds to the declaration
 * the emitter allocated for that role, which is not a fixed name; anything else is a declaration
 * name. Every case ends in a digest over real emitted text.
 */
export function bindRuntimeSymbol(runtimeSymbol: string, context: RuntimeSymbolContext): RuntimeSymbolBinding {
  const separator = runtimeSymbol.indexOf(':');
  const tag = separator < 0 ? '' : runtimeSymbol.slice(0, separator);
  const rest = runtimeSymbol.slice(separator + 1);
  if (tag === 'inline') {
    const form = context.inlineForms.get(rest);
    if (form === undefined) throw new TypeError(`runtime certificate names an unemitted inline form: ${rest}`);
    return { kind: 'inline', form, digest: runtimeBodyDigest(form) };
  }
  if (tag === 'helper') {
    const declaration = context.helperDeclarations.get(rest);
    if (declaration === undefined) throw new TypeError(`runtime certificate names an unprinted helper role: ${rest}`);
    return declarationBinding(declaration, context.bodies);
  }
  if (separator >= 0) throw new TypeError(`runtime certificate names an unknown symbol kind: ${tag}`);
  return declarationBinding(runtimeSymbol, context.bodies);
}

function declarationBinding(declaration: string, bodies: readonly string[]): RuntimeSymbolBinding {
  const carriers = bodies.filter((body) => declaresRuntimeSymbol(body, declaration));
  const [carrier] = carriers;
  if (carriers.length !== 1 || carrier === undefined) {
    throw new TypeError(`runtime certificate symbol must resolve exactly once: ${declaration}`);
  }
  return { kind: 'declaration', declaration, digest: runtimeDeclarationDigest(declaration, carrier) };
}

export function runtimeBodyDigest(body: string): string {
  return `sha256:${createHash('sha256').update(body).digest('hex')}`;
}

/** Canonically prints the unique top-level declaration carrying an emitted runtime symbol. */
export function runtimeDeclarationDigest(symbol: string, emittedModuleBody: string): string {
  const source = ts.createSourceFile('generated-runtime.ts', emittedModuleBody, ts.ScriptTarget.Latest, true);
  const declarations = source.statements.filter((statement) => declarationName(statement) === symbol);
  if (declarations.length !== 1) {
    throw new TypeError(`runtime certificate symbol must resolve exactly once: ${symbol}`);
  }
  const [declaration] = declarations;
  if (declaration === undefined) throw new TypeError(`runtime certificate symbol is absent: ${symbol}`);
  return runtimeBodyDigest(
    ts.createPrinter({ newLine: ts.NewLineKind.LineFeed }).printNode(ts.EmitHint.Unspecified, declaration, source),
  );
}

/** Whether a generated module declares the runtime symbol at all, at any multiplicity. */
export function declaresRuntimeSymbol(emittedModuleBody: string, symbol: string): boolean {
  const source = ts.createSourceFile('generated-runtime.ts', emittedModuleBody, ts.ScriptTarget.Latest, true);
  return source.statements.some((statement) => declarationName(statement) === symbol);
}

function declarationName(statement: ts.Statement): string | undefined {
  if ((ts.isFunctionDeclaration(statement) || ts.isClassDeclaration(statement)) && statement.name !== undefined) {
    return statement.name.text;
  }
  if (ts.isVariableStatement(statement) && statement.declarationList.declarations.length === 1) {
    const [declaration] = statement.declarationList.declarations;
    return declaration !== undefined && ts.isIdentifier(declaration.name) ? declaration.name.text : undefined;
  }
  return undefined;
}

function decodeAssumption(value: unknown, location: string): RuntimeAssumption {
  const assumption = object(value, location);
  exactKeys(
    assumption,
    [
      'id',
      'sourceUrl',
      'sourceArtifact',
      'sourceDigest',
      'clauses',
      'statement',
      'coverage',
      'oracle',
      'canonicalWording',
    ],
    location,
  );
  const clauses = strings(assumption['clauses'], `${location}.clauses`);
  const coverage = strings(assumption['coverage'], `${location}.coverage`);
  if (clauses.length === 0 || coverage.length === 0) throw new TypeError(`${location} must name clauses and coverage`);
  return {
    id: identifier(assumption['id'], `${location}.id`),
    sourceUrl: url(assumption['sourceUrl'], `${location}.sourceUrl`),
    sourceArtifact: relativeArtifactPath(assumption['sourceArtifact'], `${location}.sourceArtifact`),
    sourceDigest: digest(assumption['sourceDigest'], `${location}.sourceDigest`),
    clauses,
    coverage,
    oracle: identifier(assumption['oracle'], `${location}.oracle`),
  };
}

/** A committed path under `spec`, never one that could escape it. */
function relativeArtifactPath(value: unknown, location: string): string {
  const name = text(value, location);
  if (!/^[A-Za-z0-9][A-Za-z0-9._-]*(?:\/[A-Za-z0-9][A-Za-z0-9._-]*)*$/u.test(name) || name.includes('..')) {
    throw new TypeError(`${location} must be a committed path under spec`);
  }
  return name;
}

function decodeCertificate(
  value: unknown,
  knownAssumptions: ReadonlySet<string>,
  location: string,
): RuntimeCertificate {
  const certificate = object(value, location);
  exactKeys(
    certificate,
    ['opcode', 'emittedForm', 'runtimeSymbol', 'theorem', 'model', 'relation', 'requires', 'components'],
    location,
  );
  const assumptions = strings(certificate['requires'], `${location}.requires`);
  const components = strings(certificate['components'], `${location}.components`);
  if (assumptions.length === 0 && components.length === 0) {
    throw new TypeError(`${location} must name an assumption closure or a model composition`);
  }
  for (const assumption of assumptions) {
    if (!knownAssumptions.has(assumption)) {
      throw new TypeError(`${location}.requires references unknown assumption ${assumption}`);
    }
  }
  const relation = text(certificate['relation'], `${location}.relation`);
  if (relation !== 'source = model') throw new TypeError(`${location}.relation must orient source to model`);
  return {
    opcode: opcode(certificate['opcode'], `${location}.opcode`),
    theorem: qualifiedLeanName(certificate['theorem'], `${location}.theorem`),
    runtimeSymbol: taggedRuntimeSymbol(certificate['runtimeSymbol'], `${location}.runtimeSymbol`),
    model: qualifiedLeanName(certificate['model'], `${location}.model`),
    relation,
    emittedForm: text(certificate['emittedForm'], `${location}.emittedForm`),
    components,
    assumptions,
  };
}

/** A certificate names its runtime symbol by role, never by a guessed identifier. */
export function taggedRuntimeSymbol(value: unknown, location: string): string {
  const decoded = text(value, location);
  if (!/^(?:inline|helper):[a-z][A-Za-z0-9]*(?:[.-][a-zA-Z0-9]+)*$/u.test(decoded)) {
    throw new TypeError(`${location} must be an inline or helper runtime symbol`);
  }
  return decoded;
}

function object(value: unknown, location: string): Record<string, unknown> {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) {
    throw new TypeError(`${location} must be an object`);
  }
  return value as Record<string, unknown>;
}

function list(value: unknown, location: string): readonly unknown[] {
  if (!Array.isArray(value)) throw new TypeError(`${location} must be an array`);
  return value;
}

function strings(value: unknown, location: string): readonly string[] {
  return list(value, location).map((entry, index) => text(entry, `${location}[${index}]`));
}

function text(value: unknown, location: string): string {
  if (typeof value !== 'string' || value.length === 0) throw new TypeError(`${location} must be a nonempty string`);
  return value;
}

/**
 * A lowercase name in dot, dash or slash separated segments: assumption ids and probe-group
 * oracles are both written this way, and neither may carry case, whitespace or an empty segment.
 */
function identifier(value: unknown, location: string): string {
  const decoded = text(value, location);
  if (!/^[a-z][a-z0-9]*(?:[.\-/][a-z0-9]+)*$/u.test(decoded)) {
    throw new TypeError(`${location} is not a canonical identifier`);
  }
  return decoded;
}

function qualifiedLeanName(value: unknown, location: string): string {
  const decoded = text(value, location);
  if (!/^[^\s.\p{Cc}]+(?:\.[^\s.\p{Cc}]+)+$/u.test(decoded)) {
    throw new TypeError(`${location} is not a qualified Lean declaration name`);
  }
  return decoded;
}

/** A dotted opcode whose segments read the way the registry writes them, `list.foldLeft` included. */
function opcode(value: unknown, location: string): string {
  const decoded = text(value, location);
  if (!/^[a-z][A-Za-z0-9]*(?:[.-][a-zA-Z0-9]+)*$/u.test(decoded)) {
    throw new TypeError(`${location} is not a canonical opcode`);
  }
  return decoded;
}

function url(value: unknown, location: string): string {
  const decoded = text(value, location);
  if (!decoded.startsWith('https://tc39.es/ecma262/2025/')) {
    throw new TypeError(`${location} must cite the frozen ECMAScript 2025 source`);
  }
  return decoded;
}

function digest(value: unknown, location: string): string {
  const decoded = text(value, location);
  if (!isSha256(decoded)) throw new TypeError(`${location} is not a SHA-256 digest`);
  return decoded;
}

function isSha256(value: string): boolean {
  return /^sha256:[0-9a-f]{64}$/u.test(value);
}

function exactKeys(value: Record<string, unknown>, expected: readonly string[], location: string): void {
  const actual = Object.keys(value).sort(compareCodePoints);
  const canonical = [...expected].sort(compareCodePoints);
  if (actual.length !== canonical.length || actual.some((key, index) => key !== canonical[index])) {
    throw new TypeError(`${location} fields must be exactly ${canonical.join(', ')}`);
  }
}

function requireCanonicalOrder(values: readonly string[], location: string): void {
  for (let index = 1; index < values.length; index += 1) {
    const previous = values[index - 1];
    const current = values[index];
    if (previous === undefined || current === undefined || compareCodePoints(previous, current) >= 0) {
      throw new TypeError(`${location} must be strictly ordered and unique`);
    }
  }
}
