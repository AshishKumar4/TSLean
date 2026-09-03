import ts from 'typescript';
import { createHash } from 'node:crypto';
import type {
  LeanToTypeScriptCodecSurface,
  LeanToTypeScriptEnvironmentAttestation,
  LeanToTypeScriptGeneratedDeclaration,
  LeanToTypeScriptHelperDeclaration,
  LeanToTypeScriptHostBoundary,
  LeanToTypeScriptModuleArtifact,
  LeanToTypeScriptModuleIdentity,
  LeanToTypeScriptPackage,
  LeanToTypeScriptSemanticIdentity,
} from './artifact.js';
import {
  bindRuntimeSymbol,
  certificateForOpcode,
  declaresRuntimeSymbol,
  type RuntimeCertificateBinding,
  type RuntimeCertificateCatalog,
} from './certificates.js';
import { attestRuntimeConformance } from './runtime-conformance.js';
import type {
  LeanDeclaration,
  LeanEnumConstructor,
  LeanExpression,
  LeanExpressionLiveness,
  LeanField,
  LeanHostOpcode,
  LeanFunctionDeclaration,
  LeanOpcode,
  LeanParameter,
  LeanReceiver,
  LeanRuntimeHelperRole,
  LeanSemanticProgram,
  LeanType,
} from './ir.js';
import {
  constructorsOf,
  analyzeExpressionLiveness,
  LEAN_RUNTIME_HELPER_ROLES,
  LEAN_RUNTIME_OPCODES,
  referencedRuntimeOpcodes,
  renderType,
  runtimeHelperRole,
  sameType,
  substituteType,
} from './ir.js';
import {
  canonicalManifest,
  generatedPackageDigest,
  LEAN_TO_TYPESCRIPT_MANIFEST_SCHEMA_VERSION,
  PROVENANCE_HEADER_LINES,
  provenanceHeader,
  verifyLeanToTypeScriptPackage,
} from './manifest.js';
import { attributeUnsupportedFragment, UnsupportedLeanFragmentError } from './fragment.js';
import { compareCodePoints } from './ordering.js';
import {
  compareGeneratedPaths,
  declaredNames,
  exportedDeclaration,
  generatedModulePath,
  groupByLeanModule,
  importStatement,
  isExportedStatement,
  LEAN_TO_TYPESCRIPT_HOST_MODULE_PATH,
  LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH,
  type ModuleImport,
  moduleImports,
  referencedNames,
  relativeModuleSpecifier,
} from './package-layout.js';

export interface LeanToTypeScriptProvenance {
  /**
   * Everything the caller knows before emission. The module identities, the closure, the
   * certificates and the host, helper and codec inventories are observations of the emitted tree,
   * so the emitter derives them here rather than accepting a caller's copy.
   */
  readonly semantic: Omit<
    LeanToTypeScriptSemanticIdentity,
    | 'generatedBodySha256'
    | 'modules'
    | 'closure'
    | 'leanProjectPath'
    | 'certificates'
    | 'hosts'
    | 'helpers'
    | 'codecs'
  >;
  readonly environment: Omit<LeanToTypeScriptEnvironmentAttestation, 'runtimeConformance'>;
  /** The Lean-owned registry every spent opcode is certified against. */
  readonly certificates: RuntimeCertificateCatalog;
  /** Each Lean module's source path, relative to the target project root. */
  readonly sources: ReadonlyMap<string, string>;
  /**
   * Where the Lean project root sits relative to the generated package root, so a source map
   * resolves from its own location to the Lean source a consumer can actually open. It decides
   * emitted bytes, so it is part of the semantic identity.
   */
  readonly leanProjectPath: string;
}

/** One generated module while it is being assembled. */
interface ModuleDraft {
  readonly leanModule: string;
  readonly path: string;
  readonly statements: ts.Statement[];
  /** Lean declaration name to the index of the statement that carries it. */
  readonly carriers: Map<string, number>;
  /**
   * Statement index to the one declaration that produced it. A dot-notation method is carried by
   * its receiver's statement, so several names share an index and only one of them starts a line.
   */
  readonly primary: Map<number, string>;
}

/**
 * One Lean package becomes one TypeScript source tree: a file per Lean module at the path its
 * module name spells, cross-module references resolved as relative ESM imports, and the shared
 * boundary validators lifted into one runtime module as soon as a second module exists.
 */
export function emitTypeScriptPackage(
  program: LeanSemanticProgram,
  provenance: LeanToTypeScriptProvenance,
): LeanToTypeScriptPackage {
  const context = planProgram(program);
  // The emitted package is the rooted export closure, and this is the one source of truth for it:
  // module emission, the printed tree and the certificate obligations all read the same program, so
  // an opcode can never be certified for code the package does not contain, and a helper the tree
  // cannot reach cannot leave a certificate behind. The model keeps proving over the full declared
  // graph, which is why the prune lives here and not in the decoder.
  const contained = pruneToEmissionClosure(program, context);
  const drafts = emitModuleDeclarations(contained, context);
  appendGeneratedDecoders(drafts, context);
  const runtime = placeBoundaryPrimitives(drafts, context);
  // One canonical order for every emitted module, the shared runtime included: the manifest, the
  // package digest and the printed headers all read the same sequence regardless of locale.
  const ordered = [...drafts, ...(runtime === undefined ? [] : [runtime])].sort((left, right) =>
    compareGeneratedPaths(left.path, right.path),
  );
  const printed = printPackage(ordered, contained, context, provenance);
  const certificates = emittedRuntimeCertificates(contained, provenance.certificates, printed);
  const manifest = canonicalManifest({
    schemaVersion: LEAN_TO_TYPESCRIPT_MANIFEST_SCHEMA_VERSION,
    semantic: {
      ...provenance.semantic,
      leanProjectPath: provenance.leanProjectPath,
      modules: printed.map((module) => module.identity),
      closure: program.closure,
      certificates,
      generatedBodySha256: generatedPackageDigest(printed.map((module) => module.identity)),
      hosts: hostInventory(context),
      helpers: helperInventory(context, printed),
      codecs: codecInventory(context),
    },
    environment: {
      ...provenance.environment,
      runtimeConformance: attestRuntimeConformance(
        provenance.certificates,
        certificates,
        provenance.semantic.inputs,
        provenance.environment.inputs,
      ),
    },
  });

  const emitted: LeanToTypeScriptPackage = {
    modules: printed.map((module): LeanToTypeScriptModuleArtifact => {
      const header = provenanceHeader(manifest, module.identity.path);
      return { path: module.identity.path, code: `${header}${module.body}`, sourceMap: module.sourceMap };
    }),
    manifest,
  };
  verifyLeanToTypeScriptPackage(emitted);
  return emitted;
}

/** The host boundaries the emitted package imports, ordered by the Lean declaration they came from. */
function hostInventory(context: EmitContext): readonly LeanToTypeScriptHostBoundary[] {
  return [...context.hosts]
    .map(([binding, host]) => ({ declaration: host.declaration, host: host.host, binding, module: host.module }))
    .sort((left, right) => compareCodePoints(left.declaration, right.declaration));
}

/**
 * The generated helpers the package actually printed. A role the program never reached prints no
 * declaration, so recording it would claim a body the tree does not carry.
 */
function helperInventory(
  context: EmitContext,
  printed: readonly { readonly body: string }[],
): readonly LeanToTypeScriptHelperDeclaration[] {
  return LEAN_RUNTIME_HELPER_ROLES.filter((role) =>
    printed.some((module) => declaresRuntimeSymbol(module.body, requiredHelper(context, role))),
  )
    .map((role) => ({ role, declaration: requiredHelper(context, role) }))
    .sort((left, right) => compareCodePoints(left.role, right.role));
}

/**
 * The codec statics the package emitted, per data type. A ground type carries `equals`, `toData`
 * and `fromData`; a generic one carries none, because a codec per instantiation would be a second
 * representation of one type.
 */
function codecInventory(context: EmitContext): readonly LeanToTypeScriptCodecSurface[] {
  return [...context.types.values()]
    .filter((plan) => plan.ground && plan.nominal)
    .map((plan) => ({
      declaration: plan.declaration.name,
      type: plan.typeName,
      statics: ['equals', 'fromData', 'toData'],
    }))
    .sort((left, right) => compareCodePoints(left.declaration, right.declaration));
}

/**
 * Certificates the emitted package actually relies on, bound to the bytes just printed. A helper
 * resolves through the declaration the allocator gave its role; an inline opcode has no declaration
 * and binds to the canonical print of the form this emitter builds for it, which
 * `assertRuntimeCertificateBindings` then compares against the form the Lean registry states.
 */
function emittedRuntimeCertificates(
  program: LeanSemanticProgram,
  catalog: RuntimeCertificateCatalog,
  printed: readonly { readonly body: string }[],
): readonly RuntimeCertificateBinding[] {
  const helperDeclarations = new Map(
    leanToTypeScriptHelperBindings(program).map((helper) => [helper.role, helper.declaration]),
  );
  const inlineForms = inlineOperationForms();
  const bodies = printed.map((module) => module.body);
  return [...referencedRuntimeOpcodes(program)].sort(compareCodePoints).map((opcode) => {
    const certificate = certificateForOpcode(catalog, opcode);
    const binding = bindRuntimeSymbol(certificate.runtimeSymbol, { helperDeclarations, inlineForms, bodies });
    return {
      opcode: certificate.opcode,
      runtimeSymbol: certificate.runtimeSymbol,
      declaration: binding.kind === 'declaration' ? binding.declaration : '',
      runtimeBodySha256: binding.digest,
    };
  });
}

/**
 * One generated helper a certificate has to resolve: the opcode that spends it, the abstract role
 * the registry names it by, and the identifier the emitter allocated for it in this package.
 */
export interface LeanToTypeScriptHelperBinding {
  readonly opcode: LeanOpcode;
  readonly role: LeanRuntimeHelperRole;
  readonly declaration: string;
}

/**
 * The helper declarations one program prints, with the name each one was allocated. An opcode whose
 * exact Lean semantics need a guard is emitted as one shared declaration, and the identifier comes
 * from the emitter's allocator rather than from a fixed name, so a certificate that binds a helper
 * to emitted bytes resolves the name through here instead of guessing it. A role the program never
 * reaches is absent, because no declaration is printed for it.
 */
export function leanToTypeScriptHelperBindings(program: LeanSemanticProgram): readonly LeanToTypeScriptHelperBinding[] {
  const context = planProgram(program);
  const bindings: LeanToTypeScriptHelperBinding[] = [];
  for (const opcode of referencedRuntimeOpcodes(program)) {
    const role = runtimeHelperRole(LEAN_RUNTIME_OPCODES[opcode].runtimeSymbol);
    if (role === undefined) continue;
    bindings.push({ opcode, role, declaration: requiredHelper(context, role) });
  }
  return bindings;
}

function emitModuleDeclarations(program: LeanSemanticProgram, context: EmitContext): readonly ModuleDraft[] {
  const drafts: ModuleDraft[] = [];
  for (const [leanModule, declarations] of groupByLeanModule(orderedDeclarations(program))) {
    const draft: ModuleDraft = {
      leanModule,
      path: generatedModulePath(leanModule),
      statements: [],
      carriers: new Map(),
      primary: new Map(),
    };
    for (const declaration of declarations) {
      let produced: readonly ts.Statement[];
      try {
        produced = emitDeclaration(declaration, context);
      } catch (error: unknown) {
        throw attributeUnsupportedFragment(error, declaration.name);
      }
      // A dot-notation method is emitted inside its receiver's class, so it has no statement of
      // its own; `planProgram` already refused one whose receiver lives in another module.
      if (produced.length === 0) continue;
      draft.primary.set(draft.statements.length, declaration.name);
      draft.carriers.set(declaration.name, draft.statements.length);
      for (const method of context.types.get(declaration.name)?.methods ?? []) {
        draft.carriers.set(method.declaration.name, draft.statements.length);
      }
      draft.statements.push(...produced);
    }
    drafts.push(draft);
  }
  return drafts;
}

/**
 * The generated decoders, each in the module that declares the type it reads, together with the
 * `fromData` boundary for a type an external caller has to build itself. A decoder reached only
 * through another decoder is discovered when that one is built, so the set is closed by repeating
 * until no new decoder appears.
 */
function appendGeneratedDecoders(drafts: readonly ModuleDraft[], context: EmitContext): void {
  const owners = new Map(drafts.map((draft) => [draft.leanModule, draft]));
  const built = new Map<string, { readonly leanName: string; readonly statements: readonly ts.Statement[] }[]>();
  const emitted = new Set<string>();
  const decoders = [...context.prelude.decoders].sort(([left], [right]) => compareCodePoints(left, right));
  for (let progressed = true; progressed;) {
    progressed = false;
    for (const [leanName, name] of decoders) {
      if (!context.used.has(name) || emitted.has(name)) continue;
      emitted.add(name);
      const declaration = context.types.get(leanName)?.declaration;
      if (declaration === undefined) throw new TypeError(`missing generated decoder owner for ${leanName}`);
      const owner = owners.get(declaration.module);
      if (owner === undefined) throw new TypeError(`generated decoder for ${leanName} has no module`);
      const existing = built.get(declaration.module);
      const entry = { leanName, statements: emitBoundaryDecoder(leanName, name, context) };
      if (existing === undefined) built.set(declaration.module, [entry]);
      else existing.push(entry);
      progressed = true;
    }
  }
  for (const [leanModule, entries] of built) {
    const owner = owners.get(leanModule);
    if (owner === undefined) throw new TypeError(`generated decoders have no module: ${leanModule}`);
    for (const entry of [...entries].sort((left, right) => compareCodePoints(left.leanName, right.leanName))) {
      owner.statements.push(...entry.statements);
    }
  }
}

/**
 * The boundary type and its primitive validators. A package with one module keeps them in that
 * module; a package with more shares one runtime module, because duplicating them per file would
 * give the same boundary two implementations.
 */
function placeBoundaryPrimitives(drafts: readonly ModuleDraft[], context: EmitContext): ModuleDraft | undefined {
  const primitives = emitBoundaryPrimitives(context);
  if (primitives.length === 0) return undefined;
  const [only] = drafts;
  if (drafts.length === 1 && only !== undefined) {
    only.statements.push(...primitives);
    return undefined;
  }
  // Export promotion is left to the package pass, so the runtime module exports exactly the
  // helpers another module actually imports and keeps the rest private.
  return {
    leanModule: '',
    path: LEAN_TO_TYPESCRIPT_RUNTIME_MODULE_PATH,
    statements: [...primitives],
    carriers: new Map(),
    primary: new Map(),
  };
}

interface PrintedModule {
  readonly identity: LeanToTypeScriptModuleIdentity;
  readonly body: string;
  readonly sourceMap: { readonly path: string; readonly contents: string } | undefined;
}

function printPackage(
  drafts: readonly ModuleDraft[],
  program: LeanSemanticProgram,
  context: EmitContext,
  provenance: LeanToTypeScriptProvenance,
): readonly PrintedModule[] {
  const owners = new Map<string, string>();
  for (const draft of drafts) {
    for (const name of declaredNames(draft.statements)) owners.set(name, draft.path);
  }
  const imports = new Map(
    drafts.map((draft) => [
      draft.path,
      [...hostImports(draft, context), ...moduleImports(draft.path, draft.statements, owners)],
    ]),
  );
  const required = new Set([...imports.values()].flatMap((entries) => entries.flatMap((entry) => entry.names)));
  const declarations = new Map(program.declarations.map((declaration) => [declaration.name, declaration]));
  return drafts.map((draft) => {
    const entries = imports.get(draft.path) ?? [];
    const statements = draft.statements.map((statement) => exportedDeclaration(statement, required));
    assertImportsAreExported(draft, entries, drafts, owners);
    const body = printModuleBody(entries.map(importStatement), statements);
    const generated = moduleDeclarations(draft, declarations, context, body.lines, provenance);
    const sourceMap = buildSourceMap(draft, generated, provenance);
    return {
      identity: {
        path: draft.path,
        leanModule: draft.leanModule,
        imports: entries.map((entry) => resolvedImportPath(draft.path, entry.specifier)).sort(compareCodePoints),
        declarations: generated,
        bodySha256: sha256(body.text),
        sourceMapSha256: sourceMap === undefined ? '' : sha256(sourceMap.contents),
      },
      body: body.text,
      sourceMap,
    };
  });
}

/**
 * What one generated module imports from the substrate: the host binding of every `foreign`
 * declaration it declares, plus every one it calls. A host operation is not defined by the emitted
 * package — its correctness is the named premise `Preservation.HostAgrees` between the substrate's
 * implementation and the exported reference body — so the module names it through an import and
 * never through a local definition it would then have to prove something about.
 */
function hostImports(draft: ModuleDraft, context: EmitContext): readonly ModuleImport[] {
  if (context.hosts.size === 0) return [];
  const referenced = referencedNames(draft.statements);
  const names = [...context.hosts]
    .filter(([binding, host]) => host.module === draft.leanModule || referenced.all.has(binding))
    .map(([binding]) => binding)
    .sort(compareCodePoints);
  if (names.length === 0) return [];
  return [
    {
      specifier: relativeModuleSpecifier(draft.path, LEAN_TO_TYPESCRIPT_HOST_MODULE_PATH),
      names,
      typeOnly: new Set(),
    },
  ];
}

/**
 * Every imported name is exported by the module that owns it. A generated helper is promoted to
 * an export exactly where another module names it, so a reference that cannot be exported is a
 * compiler defect and is refused rather than emitted as a broken import.
 *
 * The substrate's host module is the one exception, and not an exemption: the emitted package does
 * not generate it, so there is no owning draft to check. What the import has to line up with is the
 * host registry, which the decoder already refused anything outside of.
 */
function assertImportsAreExported(
  draft: ModuleDraft,
  entries: readonly { readonly specifier: string; readonly names: readonly string[] }[],
  drafts: readonly ModuleDraft[],
  owners: ReadonlyMap<string, string>,
): void {
  const hostSpecifier = relativeModuleSpecifier(draft.path, LEAN_TO_TYPESCRIPT_HOST_MODULE_PATH);
  for (const entry of entries) {
    if (entry.specifier === hostSpecifier) continue;
    for (const name of entry.names) {
      const path = owners.get(name);
      const owner = drafts.find((candidate) => candidate.path === path);
      if (owner === undefined) throw new TypeError(`imported name ${name} has no owning generated module`);
      const exported = owner.statements.some(
        (statement) =>
          declaredNames([statement]).includes(name) &&
          (isExportedStatement(statement) || (ts.isFunctionDeclaration(statement) && statement.name?.text === name)),
      );
      if (!exported) {
        throw new UnsupportedLeanFragmentError(
          draft.leanModule,
          `generated module ${draft.path} refers to ${name}, which ${owner.path} cannot export`,
        );
      }
    }
  }
}

function resolvedImportPath(fromPath: string, specifier: string): string {
  const segments = fromPath.split('/').slice(0, -1);
  for (const segment of specifier.split('/')) {
    if (segment === '.') continue;
    if (segment === '..') segments.pop();
    else segments.push(segment);
  }
  const last = segments.pop();
  if (last === undefined) throw new TypeError(`import specifier resolves to nothing: ${specifier}`);
  return [...segments, last.replace(/\.js$/u, '.ts')].join('/');
}

/**
 * The printed module body and the 1-based line each declaration statement starts on. Imports are
 * printed as one adjacent block; declarations are separated by a blank line, which the printer
 * never emits on its own and a formatter never removes.
 */
function printModuleBody(
  imports: readonly ts.Statement[],
  statements: readonly ts.Statement[],
): { readonly text: string; readonly lines: readonly number[] } {
  const file = ts.createSourceFile('generated.ts', '', ts.ScriptTarget.Latest, false, ts.ScriptKind.TS);
  const printer = ts.createPrinter({ newLine: ts.NewLineKind.LineFeed });
  const render = (statement: ts.Statement): string => printer.printNode(ts.EmitHint.Unspecified, statement, file);
  const importText = imports.map(render).join('\n');
  const rendered = statements.map(render);
  const lines: number[] = [];
  let line = importText === '' ? 1 : importText.split('\n').length + 2;
  for (const text of rendered) {
    lines.push(line);
    line += text.split('\n').length + 1;
  }
  const declarationText = `${rendered.join('\n\n')}\n`;
  return { text: importText === '' ? declarationText : `${importText}\n\n${declarationText}`, lines };
}

function moduleDeclarations(
  draft: ModuleDraft,
  declarations: ReadonlyMap<string, LeanDeclaration>,
  context: EmitContext,
  lines: readonly number[],
  provenance: LeanToTypeScriptProvenance,
): readonly LeanToTypeScriptGeneratedDeclaration[] {
  const source = provenance.sources.get(draft.leanModule);
  if (draft.leanModule !== '' && source === undefined) {
    throw new TypeError(`no Lean source is recorded for module ${draft.leanModule}`);
  }
  return [...draft.carriers]
    .sort(([left], [right]) => compareCodePoints(left, right))
    .map(([name, index]): LeanToTypeScriptGeneratedDeclaration => {
      const declaration = declarations.get(name);
      const line = lines[index];
      if (declaration === undefined || line === undefined) {
        throw new TypeError(`generated declaration ${name} has no recorded position`);
      }
      return {
        declaration: name,
        // A method shares its receiver's statement but has its own member name. Every other
        // carrier is top-level and uses the allocated declaration name the emitter printed.
        emitted: context.methods.get(name)?.name ?? requiredDeclarationName(context.declarationNames, name),
        line: PROVENANCE_HEADER_LINES + line,
        span: { source: source ?? '', ...declaration.span },
      };
    });
}

/**
 * A declaration-level source map. The emitter builds a fresh TypeScript AST from a semantic IR
 * with no token positions, so a finer correspondence than "this generated declaration came from
 * that Lean declaration" would be invented rather than measured. One segment per generated line,
 * from the declaration that starts it: a dot-notation method shares its receiver's line and is
 * recorded in the manifest instead, where it does not have to compete for a position.
 */
function buildSourceMap(
  draft: ModuleDraft,
  declarations: readonly LeanToTypeScriptGeneratedDeclaration[],
  provenance: LeanToTypeScriptProvenance,
): { readonly path: string; readonly contents: string } | undefined {
  const source = provenance.sources.get(draft.leanModule);
  if (source === undefined) return undefined;
  const primary = new Set(draft.primary.values());
  const ordered = declarations
    .filter((declaration) => primary.has(declaration.declaration))
    .sort((left, right) => left.line - right.line);
  if (ordered.length === 0) return undefined;
  const groups: string[] = [];
  let previousLine = 0;
  let sourceLine = 0;
  let sourceColumn = 0;
  for (const declaration of ordered) {
    while (previousLine < declaration.line - 1) {
      groups.push('');
      previousLine += 1;
    }
    groups.push(
      [
        variableLengthQuantity(0),
        variableLengthQuantity(0),
        variableLengthQuantity(declaration.span.startLine - 1 - sourceLine),
        variableLengthQuantity(declaration.span.startColumn - sourceColumn),
      ].join(''),
    );
    sourceLine = declaration.span.startLine - 1;
    sourceColumn = declaration.span.startColumn;
    previousLine += 1;
  }
  // A consumer resolves `sources` against the map's own directory, so the recorded path climbs out
  // of the generated tree and back down through the Lean project. `leanProjectPath` is where that
  // project sits relative to the package root, which is why it belongs to the semantic identity.
  const ascent = Array.from({ length: draft.path.split('/').length - 1 }, () => '..');
  const map = {
    version: 3,
    file: draft.path.split('/').slice(-1)[0],
    sourceRoot: '',
    sources: [
      [...ascent, ...provenance.leanProjectPath.split('/').filter((segment) => segment !== ''), source].join('/'),
    ],
    names: [],
    mappings: groups.join(';'),
  };
  return { path: `${draft.path}.map`, contents: `${JSON.stringify(map, undefined, 2)}\n` };
}

const BASE64_DIGITS = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/';

function variableLengthQuantity(value: number): string {
  let remaining = value < 0 ? (-value << 1) | 1 : value << 1;
  let encoded = '';
  do {
    let digit = remaining & 0b11111;
    remaining >>>= 5;
    if (remaining > 0) digit |= 0b100000;
    const character = BASE64_DIGITS[digit];
    if (character === undefined) throw new TypeError('source map digit is out of range');
    encoded += character;
  } while (remaining > 0);
  return encoded;
}

function sha256(value: string): string {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}

type LeanFunction = LeanFunctionDeclaration;
type LeanEnum = Extract<LeanDeclaration, { readonly kind: 'enum' }>;
type LeanStructure = Extract<LeanDeclaration, { readonly kind: 'record' }>;
type LeanData = LeanEnum | LeanStructure;

/**
 * One Lean function emitted as a method on its receiver's class. Which function is a method comes
 * from the IR's own receiver record, which the exporter read out of the elaborated environment, so
 * the shape of a Lean name never decides where code lands.
 */
interface MethodPlan {
  readonly declaration: LeanFunction;
  readonly name: string;
  readonly receiver: LeanReceiver;
  /** The declared parameters other than the receiver, in declared order. */
  readonly parameters: readonly LeanParameter[];
  /** Emitted names for every type parameter the declaration takes, positionally. */
  readonly typeParameters: readonly string[];
  readonly dispatches: boolean;
}

interface CasePlan {
  readonly constructor: LeanEnumConstructor;
  readonly className: string;
  readonly singleton: string;
}

/** One source field and the binder that carries it inside one generated class member. */
interface CaseFieldBinder {
  readonly field: LeanField;
  readonly binder: string;
}

/**
 * The binders one class member gives a constructor's fields. A static factory and a case-class
 * constructor are separate scopes, so each allocates its own: a field keeps its Lean spelling
 * unless that spelling is genuinely in scope there, such as the case class the factory constructs.
 */
function caseFieldBinders(
  entry: CasePlan,
  context: EmitContext,
  inScope: readonly string[],
): readonly CaseFieldBinder[] {
  const allocator = new IdentifierAllocator([...context.reserved, ...context.typeParameters, ...inScope]);
  return entry.constructor.fields.map((field) => ({ field, binder: allocator.allocate(field.name) }));
}

/**
 * How one Lean data type is represented. A type whose namespace carries dot-notation methods over
 * it has behaviour, so it becomes a nominal class exactly as a handwritten value object is written;
 * a type with no behaviour stays structural, because promoting it would add a constructor and an
 * identity the Lean source does not have.
 *
 * A generic type has no data image: a codec per instantiation would be a second representation of
 * one type, so `fromData`, `toData` and `equals` exist only where the type is ground.
 */
interface TypePlan {
  readonly declaration: LeanData;
  readonly typeName: string;
  /** Emitted type parameter names, positional so a Lean binder name cannot change a signature. */
  readonly typeParameters: readonly string[];
  readonly ground: boolean;
  readonly nominal: boolean;
  readonly cases: readonly CasePlan[];
  readonly methods: readonly MethodPlan[];
  readonly dataName: string;
  readonly initName: string;
}

interface PreludeNames {
  readonly dataBoundary: string;
  readonly isDataObject: string;
  readonly requireDataFields: string;
  readonly requireBoolean: string;
  readonly requireNat: string;
  readonly requireString: string;
  readonly requireList: string;
  readonly optionType: string;
  readonly exceptType: string;
  readonly jsonType: string;
  readonly requireInt: string;
  readonly requireChar: string;
  readonly requirePair: string;
  readonly requireJson: string;
  readonly requireOption: string;
  readonly requireExcept: string;
  readonly equalOption: string;
  readonly equalExcept: string;
  readonly equalList: string;
  /** The generated helper for each runtime opcode whose exact semantics need a guard. */
  readonly helpers: ReadonlyMap<LeanRuntimeHelperRole, string>;
  /** The decoder of each ground structural data type, in the module that declares the type. */
  readonly decoders: ReadonlyMap<string, string>;
}

/** Parameter and local names the generated codecs bind, allocated so they cannot shadow a
 * declaration the same function refers to. */
interface CodecLocals {
  readonly value: string;
  readonly name: string;
  readonly data: string;
  readonly fields: string;
  readonly field: string;
  readonly element: string;
  readonly index: string;
  readonly entry: string;
  readonly other: string;
  readonly codeUnit: string;
}

/**
 * What the generated package exports for a caller to decode with: a `fromData` for every data type
 * a root declaration accepts, and the shared validator behind every primitive one, so an external
 * input is parsed at the boundary instead of asserted past it.
 */
interface BoundaryPlan {
  /** Structural Lean data types whose declaring module exports `fromData` for them. */
  readonly types: ReadonlySet<string>;
  /** Prelude validators the boundary hands a caller directly. */
  readonly validators: ReadonlySet<string>;
}

/**
 * One host binding the emitted package imports: the substrate's implementation of a host identity,
 * under the name the Lean declaration spells, and the Lean module the boundary was declared in.
 */
export interface LeanToTypeScriptHostBinding {
  readonly declaration: string;
  readonly host: LeanHostOpcode;
  readonly module: string;
}

interface EmitContext {
  readonly roots: ReadonlySet<string>;
  readonly declarationNames: ReadonlyMap<string, string>;
  readonly declarations: ReadonlyMap<string, LeanDeclaration>;
  readonly types: ReadonlyMap<string, TypePlan>;
  readonly methods: ReadonlyMap<string, MethodPlan>;
  readonly reserved: readonly string[];
  readonly prelude: PreludeNames;
  readonly locals: CodecLocals;
  readonly boundary: BoundaryPlan;
  readonly used: Set<string>;
  /** The imported host binding of every `foreign` declaration, keyed by its emitted name. */
  readonly hosts: ReadonlyMap<string, LeanToTypeScriptHostBinding>;
  /** The enclosing declaration's type parameters, in order, as emitted names. */
  readonly typeParameters: readonly string[];
}

type Binding =
  | { readonly kind: 'identifier'; readonly name: string }
  | { readonly kind: 'this' }
  /** A binder the generated code reads back out of a value it already holds. */
  | { readonly kind: 'expression'; readonly value: ts.Expression }
  /**
   * A binder the enclosing body never reads. It occupies its de Bruijn position so every index
   * above it still counts, and emitting it is a compiler defect rather than a refused program.
   */
  | { readonly kind: 'unread' };

/**
 * Type parameters are positional. Their emitted names come from a fixed sequence rather than from a
 * Lean binder name, so renaming `α` in Lean cannot change a generated signature, and a Lean library
 * that spells its parameters in Greek still lowers.
 */
/**
 * The globals emitted code reads by name. A Lean binder that shadowed one would silently change
 * what `BigInt(...)`, `Object.freeze(...)` or `throw new TypeError(...)` resolves to.
 */
const EMITTED_GLOBALS: readonly string[] = ['undefined', 'this', 'Array', 'BigInt', 'Object', 'TypeError'];

function positionalTypeParameter(index: number): string {
  return index < 26 ? String.fromCodePoint(65 + index) : `T${index}`;
}

function allocateTypeParameters(count: number, reserved: readonly string[]): readonly string[] {
  const allocator = new IdentifierAllocator(reserved);
  return Array.from({ length: count }, (_, index) => allocator.allocate(positionalTypeParameter(index)));
}

function withTypeParameters(context: EmitContext, typeParameters: readonly string[]): EmitContext {
  return { ...context, typeParameters };
}

function typeParameterDeclarations(names: readonly string[]): readonly ts.TypeParameterDeclaration[] | undefined {
  if (names.length === 0) return undefined;
  return names.map((name) => ts.factory.createTypeParameterDeclaration(undefined, name));
}

function typeParameterReferences(names: readonly string[]): readonly ts.TypeNode[] | undefined {
  return names.length === 0 ? undefined : names.map((name) => ts.factory.createTypeReferenceNode(name));
}

/**
 * The members the generated representation owns. A Lean name that lands on one of these would be
 * emitted beside it, so the collision is refused in the Lean source rather than resolved silently.
 */
const RESERVED_REPRESENTATION_MEMBERS: Readonly<Record<string, string>> = {
  kind: 'constructor discriminant',
  from: 'tag constructor',
  fromData: 'decode boundary',
  toData: 'data image',
  equals: 'structural equality',
};

/**
 * A structural type carries `__proto__` as an own data property, because an object literal with a
 * computed key creates one and element access reads it. A class cannot: its constructor assigns
 * each field, and an assignment to `__proto__` reaches the prototype setter however it is spelled.
 * So the name is refused exactly where the representation is a class.
 */
const PROTOTYPE_KEY = '__proto__';

function reservedMemberRole(name: string): string | undefined {
  return Object.hasOwn(RESERVED_REPRESENTATION_MEMBERS, name) ? RESERVED_REPRESENTATION_MEMBERS[name] : undefined;
}

function refuseReservedMember(owner: string, what: string, name: string, role: string): never {
  throw new UnsupportedLeanFragmentError(
    owner,
    `${what} ${name} collides with the ${role} the generated representation emits for ${owner}; rename it in the Lean source`,
  );
}

/**
 * Refuses a data type whose own names collide with the representation the emitter gives it. A
 * value object carries `kind`, `fromData`, `toData`, `equals` and, when every constructor is
 * nullary, `from`; a tagged union carries `kind`. Anything a Lean source spells that lands on one
 * of those has no second place to go.
 */
function assertRepresentationNames(plan: TypePlan): void {
  const owner = plan.declaration.name;
  const tagged =
    plan.declaration.kind === 'enum' && plan.declaration.constructors.some((entry) => entry.fields.length > 0);
  const fields =
    plan.declaration.kind === 'record'
      ? plan.declaration.fields
      : plan.declaration.constructors.flatMap((constructor) => constructor.fields);
  for (const field of fields) {
    if (plan.nominal && field.name === PROTOTYPE_KEY) {
      throw new UnsupportedLeanFragmentError(
        owner,
        `field ${PROTOTYPE_KEY} has no own-property form on the class the generated representation emits for ${owner}, because a class constructor assigns its fields and that assignment reaches the prototype setter; rename it in the Lean source`,
      );
    }
    const role = reservedMemberRole(field.name);
    if (role === undefined) continue;
    if (plan.nominal || (tagged && field.name === 'kind')) refuseReservedMember(owner, 'field', field.name, role);
  }
  if (!plan.nominal) return;
  for (const method of plan.methods) {
    const role = reservedMemberRole(method.name);
    if (role !== undefined) refuseReservedMember(owner, 'dot-notation method', method.name, role);
  }
  if (plan.declaration.kind !== 'enum') return;
  for (const constructor of plan.declaration.constructors) {
    const role = reservedMemberRole(constructor.name);
    if (role !== undefined) refuseReservedMember(owner, 'constructor', constructor.name, role);
  }
}

function planProgram(program: LeanSemanticProgram): EmitContext {
  // A declaration binds at module scope, where it can shadow a global the generated class body
  // reads. Allocate the local spelling before any plan exists, in canonical declaration order, so
  // Object/BigInt/Array/TypeError are handled exactly like a binder inside a function.
  const declarationAllocator = new IdentifierAllocator(EMITTED_GLOBALS);
  const declarationNames = new Map(
    [...program.declarations]
      .sort((left, right) => compareCodePoints(left.name, right.name))
      .map((declaration) => [declaration.name, declarationAllocator.allocate(localName(declaration.name))]),
  );
  const declarations = new Map(program.declarations.map((declaration) => [declaration.name, declaration]));
  const declaredIdentifiers = [...declarationNames.values()];
  const allocator = new IdentifierAllocator([...declaredIdentifiers, ...EMITTED_GLOBALS]);
  const functions = program.declarations.filter(
    (declaration): declaration is LeanFunction => declaration.kind === 'function',
  );
  const data = program.declarations
    // Selected positively: a `foreign` declaration is a callable the module imports, not a data
    // type, and a negative filter would cast it to `LeanData` and read constructors it has none of.
    .filter((declaration): declaration is LeanData => declaration.kind === 'enum' || declaration.kind === 'record')
    .sort((left, right) => compareCodePoints(left.name, right.name));
  const types = new Map<string, TypePlan>();
  const methods = new Map<string, MethodPlan>();
  for (const declaration of data) {
    const typeName = requiredDeclarationName(declarationNames, declaration.name);
    const owned = functions
      .filter((candidate) => candidate.receiver?.type === declaration.name)
      .map((candidate): MethodPlan => {
        const receiver = candidate.receiver;
        if (receiver === undefined) throw new TypeError(`${candidate.name} lost its receiver record`);
        return {
          declaration: candidate,
          name: localName(candidate.name),
          receiver,
          parameters: candidate.parameters.filter((_, index) => index !== receiver.parameter),
          typeParameters: allocateTypeParameters(candidate.typeParameters.length, declaredIdentifiers),
          dispatches: declaration.kind === 'enum' && dispatchesOnReceiver(candidate, receiver),
        };
      });
    const nominal = owned.length > 0;
    const ground = declaration.typeParameters.length === 0;
    const cases =
      declaration.kind === 'enum' && nominal
        ? declaration.constructors.map((constructor): CasePlan => ({
            constructor,
            // A class name and its singleton bind at module scope. A constructor field does not:
            // its binder belongs to one class member, so reserving it here would rename every
            // Lean binder of that spelling across the whole module.
            className: allocator.allocate(`${capitalize(constructor.name)}${typeName}`),
            singleton: allocator.allocate(`${constructor.name}${typeName}`),
          }))
        : [];
    types.set(declaration.name, {
      declaration,
      typeName,
      typeParameters: allocateTypeParameters(declaration.typeParameters.length, declaredIdentifiers),
      ground,
      nominal,
      cases,
      methods: owned,
      dataName: nominal ? allocator.allocate(`${typeName}Data`) : typeName,
      initName: nominal ? allocator.allocate(`${typeName}Init`) : typeName,
    });
    for (const method of owned) methods.set(method.declaration.name, method);
    const plan = types.get(declaration.name);
    if (plan === undefined) throw new TypeError(`missing type plan for ${declaration.name}`);
    assertRepresentationNames(plan);
  }
  const decoders = new Map<string, string>();
  for (const declaration of data) {
    const plan = types.get(declaration.name);
    if (plan === undefined || plan.nominal || !plan.ground) continue;
    decoders.set(declaration.name, allocator.allocate(`require${capitalize(localName(declaration.name))}`));
  }
  const prelude: PreludeNames = {
    dataBoundary: allocator.allocate('GeneratedData'),
    isDataObject: allocator.allocate('isDataObject'),
    requireDataFields: allocator.allocate('requireDataFields'),
    requireBoolean: allocator.allocate('requireBoolean'),
    requireNat: allocator.allocate('requireNat'),
    requireString: allocator.allocate('requireString'),
    requireList: allocator.allocate('requireList'),
    optionType: allocator.allocate('Option'),
    exceptType: allocator.allocate('Except'),
    jsonType: allocator.allocate('JsonValue'),
    requireInt: allocator.allocate('requireInt'),
    requireChar: allocator.allocate('requireChar'),
    requirePair: allocator.allocate('requirePair'),
    requireJson: allocator.allocate('requireJson'),
    requireOption: allocator.allocate('requireOption'),
    requireExcept: allocator.allocate('requireExcept'),
    equalOption: allocator.allocate('equalOption'),
    equalExcept: allocator.allocate('equalExcept'),
    equalList: allocator.allocate('equalList'),
    helpers: new Map<LeanRuntimeHelperRole, string>(
      LEAN_RUNTIME_HELPER_ROLES.map((role) => [role, allocator.allocate(HELPER_DECLARATION_HINTS[role])]),
    ),
    decoders,
  };
  // Every generated name an emitted function body can reach: the shared helpers it calls, the
  // decoders it names, and the globals it reads. A Lean binder never shadows one of these. The
  // codec locals below are deliberately outside the set: they exist only inside generated codec
  // bodies, which hold no Lean binder, and reserving them would rename ordinary Lean parameters.
  const reserved = allocator.allocated();
  const locals: CodecLocals = {
    value: allocator.allocate('value'),
    name: allocator.allocate('name'),
    data: allocator.allocate('data'),
    fields: allocator.allocate('fields'),
    field: allocator.allocate('field'),
    element: allocator.allocate('element'),
    index: allocator.allocate('index'),
    entry: allocator.allocate('entry'),
    other: allocator.allocate('other'),
    codeUnit: allocator.allocate('codeUnit'),
  };
  const roots = new Set(program.roots);
  const hosts = new Map<string, LeanToTypeScriptHostBinding>();
  for (const declaration of program.declarations) {
    if (declaration.kind !== 'foreign') continue;
    const emitted = requiredDeclarationName(declarationNames, declaration.name);
    // The substrate exports the host binding under the declaration's own Lean name, so a package
    // that had to rename it — because a global or another declaration already holds the spelling —
    // could not import it under that name. Refuse in the Lean source rather than import an alias
    // the substrate never published.
    if (emitted !== localName(declaration.name)) {
      throw new UnsupportedLeanFragmentError(
        declaration.module,
        `host boundary ${declaration.name} would be imported as ${emitted}, which is not the name the substrate publishes it under; rename the colliding declaration in the Lean source`,
      );
    }
    hosts.set(emitted, { declaration: declaration.name, host: declaration.host, module: declaration.module });
  }
  const base: EmitContext = {
    roots,
    declarationNames,
    declarations,
    types,
    methods,
    reserved,
    prelude,
    locals,
    boundary: { types: new Set(), validators: new Set() },
    used: new Set(),
    hosts,
    typeParameters: [],
  };
  const boundary = planBoundary(program, base);
  const used = new Set(boundary.validators);
  for (const name of boundary.types) {
    const decoder = decoders.get(name);
    if (decoder === undefined) throw new TypeError(`missing generated decoder for ${name}`);
    used.add(decoder);
  }
  return { ...base, boundary, used };
}

/**
 * The decode boundary an external caller has to cross: the type of every parameter a root takes,
 * with the shared validator each primitive one is read by. A root's result travels the other way
 * and is never decoded, and a type reached only through another type's field is read by that type's
 * own codec, so the boundary is exactly the callable surface and never wider.
 */
function planBoundary(program: LeanSemanticProgram, context: EmitContext): BoundaryPlan {
  const boundaryTypes = new Set<string>();
  const validators = new Set<string>();
  const walk = (type: LeanType): void => {
    switch (type.kind) {
      case 'boolean':
        validators.add(context.prelude.requireBoolean);
        return;
      case 'nat':
        validators.add(context.prelude.requireNat);
        return;
      case 'string':
        validators.add(context.prelude.requireString);
        return;
      case 'int':
        validators.add(context.prelude.requireInt);
        return;
      case 'char':
        validators.add(context.prelude.requireChar);
        return;
      case 'json':
        validators.add(context.prelude.requireJson);
        return;
      case 'pair':
        validators.add(context.prelude.requirePair);
        walk(type.first);
        walk(type.second);
        return;
      case 'option':
        validators.add(context.prelude.requireOption);
        walk(type.value);
        return;
      case 'except':
        validators.add(context.prelude.requireExcept);
        walk(type.error);
        walk(type.value);
        return;
      case 'list':
        validators.add(context.prelude.requireList);
        walk(type.element);
        return;
      // An Array is read by the List validator, because the two share one dense image.
      case 'array':
        validators.add(context.prelude.requireList);
        walk(type.element);
        return;
      case 'parameter':
      case 'function':
      case 'bytes':
      case 'hashMap':
      case 'treeMap':
        throw new TypeError(`a root declaration cannot expose ${renderType(type)} at its boundary`);
      case 'named': {
        const plan = context.types.get(type.name);
        if (plan === undefined) throw new TypeError(`root parameter names an undeclared type ${type.name}`);
        // A value object already carries `fromData`; a structural type gets one beside its decoder.
        if (!plan.nominal) boundaryTypes.add(type.name);
        return;
      }
    }
  };
  for (const declaration of program.declarations) {
    if (declaration.kind !== 'function' || !context.roots.has(declaration.name)) continue;
    for (const parameter of declaration.parameters) walk(parameter.type);
  }
  return { types: boundaryTypes, validators };
}

/**
 * Whether a method decides its receiver's constructors directly, which is what lets it lower to one
 * abstract method with an override per case class instead of a tag comparison inside one body.
 */
function dispatchesOnReceiver(declaration: LeanFunction, receiver: LeanReceiver): boolean {
  const body = declaration.body;
  if (body.kind !== 'match' || body.scrutinee.kind !== 'variable') return false;
  const parameter = declaration.parameters[receiver.parameter];
  if (parameter === undefined) return false;
  return (
    sameType(body.type, parameter.type) &&
    body.scrutinee.index === declaration.parameters.length - 1 - receiver.parameter
  );
}

function emitDeclaration(declaration: LeanDeclaration, context: EmitContext): readonly ts.Statement[] {
  if (declaration.kind === 'function') {
    if (context.methods.has(declaration.name)) return [];
    return [emitFunction(declaration, context)];
  }
  // A host boundary is imported, never defined: the substrate owns the implementation, and the
  // module that names it carries an import instead of a statement. `hostImports` places it. A root
  // is the package's callable surface, so a host boundary that is one is re-exported under the name
  // the substrate published it under — otherwise a caller could not reach the boundary at all and
  // the import itself would be unread.
  if (declaration.kind === 'foreign') {
    if (!context.roots.has(declaration.name)) return [];
    const emitted = requiredDeclarationName(context.declarationNames, declaration.name);
    return [
      ts.factory.createExportDeclaration(
        undefined,
        false,
        ts.factory.createNamedExports([
          ts.factory.createExportSpecifier(false, undefined, ts.factory.createIdentifier(emitted)),
        ]),
      ),
    ];
  }
  const plan = requiredTypePlan(context, declaration.name);
  const scoped = withTypeParameters(context, plan.typeParameters);
  if (declaration.kind === 'enum') {
    return plan.nominal ? emitNominalEnum(plan, declaration, scoped) : [emitStructuralEnum(plan, declaration, scoped)];
  }
  return plan.nominal
    ? emitNominalRecord(plan, declaration, scoped)
    : [emitStructuralRecord(plan, declaration, scoped)];
}

function emitFunction(declaration: LeanFunction, context: EmitContext): ts.Statement {
  const scoped = withTypeParameters(
    context,
    allocateTypeParameters(declaration.typeParameters.length, [...context.declarationNames.values()]),
  );
  const allocator = newAllocator(scoped);
  const parameters = declaration.parameters.map((parameter) => ({
    ...parameter,
    emittedName: allocator.allocate(parameter.name),
  }));
  const scope: readonly Binding[] = parameters
    .map((parameter): Binding => ({ kind: 'identifier', name: parameter.emittedName }))
    .reverse();
  const body = emitFunctionBody(declaration.body, scope, allocator, scoped);
  return documented(
    ts.factory.createFunctionDeclaration(
      context.roots.has(declaration.name) ? [modifier(ts.SyntaxKind.ExportKeyword)] : undefined,
      undefined,
      requiredDeclarationName(context.declarationNames, declaration.name),
      typeParameterDeclarations(scoped.typeParameters),
      markUnreadParameters(
        parameters.map((parameter) =>
          ts.factory.createParameterDeclaration(
            undefined,
            undefined,
            parameter.emittedName,
            undefined,
            emitType(parameter.type, scoped),
          ),
        ),
        body,
        allocator,
      ),
      emitType(declaration.result, scoped),
      body,
    ),
    declaration.doc,
  );
}

/**
 * Parameters an emitted body never names, respelled with a leading underscore.
 *
 * A Lean declaration may ignore a parameter, and one override of a dispatched method may decide its
 * case without reading an argument another case reads. The parameter still has to be declared —
 * it holds its position in the signature — so it is spelled the way TypeScript's own unused-binding
 * rule reads as deliberate, rather than left to a consumer's compiler options. The body is already
 * built when this runs, and the allocator gives every binder in it a distinct name, so an
 * identifier that does not occur in the body is genuinely unread.
 */
function markUnreadParameters(
  parameters: readonly ts.ParameterDeclaration[],
  body: ts.Node,
  allocator: IdentifierAllocator,
): readonly ts.ParameterDeclaration[] {
  const read = new Set<string>();
  const visit = (node: ts.Node): void => {
    if (ts.isIdentifier(node)) read.add(node.text);
    ts.forEachChild(node, visit);
  };
  visit(body);
  return parameters.map((parameter) => {
    if (!ts.isIdentifier(parameter.name) || read.has(parameter.name.text)) return parameter;
    return ts.factory.updateParameterDeclaration(
      parameter,
      parameter.modifiers,
      parameter.dotDotDotToken,
      allocator.allocate(`_${parameter.name.text}`),
      parameter.questionToken,
      parameter.type,
      parameter.initializer,
    );
  });
}

/** A nullary inductive with no behaviour is a tag; one with payloads is a discriminated union. */
function emitStructuralEnum(plan: TypePlan, declaration: LeanEnum, context: EmitContext): ts.Statement {
  const carriesData = declaration.constructors.some((constructor) => constructor.fields.length > 0);
  const members = declaration.constructors.map((constructor) =>
    carriesData ? variantObjectType(constructor, context) : literalType(constructor.name),
  );
  return documented(
    ts.factory.createTypeAliasDeclaration(
      [modifier(ts.SyntaxKind.ExportKeyword)],
      plan.typeName,
      typeParameterDeclarations(plan.typeParameters),
      ts.factory.createUnionTypeNode(members),
    ),
    declaration.doc,
  );
}

function variantObjectType(constructor: LeanEnumConstructor, context: EmitContext): ts.TypeNode {
  return ts.factory.createTypeLiteralNode([
    readonlyProperty('kind', literalType(constructor.name)),
    ...constructor.fields.map((field) => readonlyProperty(field.name, emitType(field.type, context))),
  ]);
}

function emitStructuralRecord(plan: TypePlan, declaration: LeanStructure, context: EmitContext): ts.Statement {
  return documented(
    ts.factory.createInterfaceDeclaration(
      [modifier(ts.SyntaxKind.ExportKeyword)],
      plan.typeName,
      typeParameterDeclarations(plan.typeParameters),
      undefined,
      declaration.fields.map((field) =>
        documented(readonlyProperty(field.name, emitType(field.type, context)), field.doc),
      ),
    ),
    declaration.doc,
  );
}

/**
 * A behaviour-carrying inductive becomes an abstract base with one private subclass per
 * constructor. A nullary constructor of a ground type has exactly one inhabitant, so it is a
 * singleton behind a static getter; a nullary constructor of a generic type has one inhabitant per
 * instantiation, so it is a static factory instead. A payload constructor is a factory over its
 * fields either way.
 */
function emitNominalEnum(plan: TypePlan, declaration: LeanEnum, context: EmitContext): readonly ts.Statement[] {
  const self = selfType(plan);
  const nullary = plan.cases.every((entry) => entry.constructor.fields.length === 0);
  const members: ts.ClassElement[] = plan.cases.map((entry) =>
    documented(emitCaseFactory(entry, plan, context), entry.constructor.doc),
  );
  if (nullary && plan.ground) members.push(emitTagConstructor(plan, self, context));
  if (plan.ground) members.push(emitEnumFromData(plan, declaration, self, context));
  members.push(
    ts.factory.createPropertyDeclaration(
      [
        modifier(ts.SyntaxKind.PublicKeyword),
        modifier(ts.SyntaxKind.AbstractKeyword),
        modifier(ts.SyntaxKind.ReadonlyKeyword),
      ],
      'kind',
      undefined,
      ts.factory.createUnionTypeNode(plan.cases.map((entry) => literalType(entry.constructor.name))),
      undefined,
    ),
  );
  for (const method of plan.methods) members.push(emitBaseMethod(method, plan, context));
  if (plan.ground) members.push(...emitEnumRepresentation(plan, self, nullary, context));
  const declarationStatement = documented(
    ts.factory.createClassDeclaration(
      [modifier(ts.SyntaxKind.ExportKeyword), modifier(ts.SyntaxKind.AbstractKeyword)],
      plan.typeName,
      typeParameterDeclarations(plan.typeParameters),
      undefined,
      members,
    ),
    declaration.doc,
  );
  return [
    ...(plan.ground ? [emitEnumDataType(plan, declaration, nullary, context)] : []),
    declarationStatement,
    ...plan.cases.map((entry) => emitCaseClass(entry, plan, nullary, context)),
    ...(plan.ground
      ? plan.cases
          .filter((entry) => entry.constructor.fields.length === 0)
          .map((entry) =>
            constantStatement(
              entry.singleton,
              ts.factory.createNewExpression(ts.factory.createIdentifier(entry.className), undefined, []),
            ),
          )
      : []),
  ];
}

function selfType(plan: TypePlan): ts.TypeNode {
  return ts.factory.createTypeReferenceNode(plan.typeName, typeParameterReferences(plan.typeParameters));
}

/** The static constructor for one case: a getter where the value is unique, a factory otherwise. */
function emitCaseFactory(entry: CasePlan, plan: TypePlan, context: EmitContext): ts.ClassElement {
  const self = selfType(plan);
  // The body constructs the case class and names the enclosing type, so both are in scope here.
  const fields = caseFieldBinders(entry, context, [entry.className, plan.typeName, entry.singleton]);
  const construct = ts.factory.createNewExpression(
    ts.factory.createIdentifier(entry.className),
    typeParameterReferences(plan.typeParameters),
    fields.map(({ binder }) => ts.factory.createIdentifier(binder)),
  );
  if (entry.constructor.fields.length === 0 && plan.ground) {
    return ts.factory.createGetAccessorDeclaration(
      [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.StaticKeyword)],
      entry.constructor.name,
      [],
      self,
      block(ts.factory.createReturnStatement(ts.factory.createIdentifier(entry.singleton))),
    );
  }
  return ts.factory.createMethodDeclaration(
    [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.StaticKeyword)],
    undefined,
    entry.constructor.name,
    undefined,
    typeParameterDeclarations(plan.typeParameters),
    fields.map(({ field, binder }) =>
      ts.factory.createParameterDeclaration(undefined, undefined, binder, undefined, emitType(field.type, context)),
    ),
    self,
    block(ts.factory.createReturnStatement(construct)),
  );
}

/** `kind` back to the one value that carries it: total, and only where every case is nullary. */
function emitTagConstructor(plan: TypePlan, base: ts.TypeNode, context: EmitContext): ts.ClassElement {
  const kind = newAllocator(context).allocate('kind');
  return ts.factory.createMethodDeclaration(
    [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.StaticKeyword)],
    undefined,
    'from',
    undefined,
    undefined,
    [
      ts.factory.createParameterDeclaration(
        undefined,
        undefined,
        kind,
        undefined,
        ts.factory.createIndexedAccessTypeNode(base, literalType('kind')),
      ),
    ],
    base,
    block(
      ts.factory.createSwitchStatement(
        ts.factory.createIdentifier(kind),
        ts.factory.createCaseBlock(
          plan.cases.map((entry) =>
            ts.factory.createCaseClause(ts.factory.createStringLiteral(entry.constructor.name), [
              ts.factory.createReturnStatement(
                ts.factory.createPropertyAccessExpression(
                  ts.factory.createIdentifier(plan.typeName),
                  entry.constructor.name,
                ),
              ),
            ]),
          ),
        ),
      ),
    ),
  );
}

/** The type scope inside a method: its receiver's parameters first, then its own. */
function methodContext(method: MethodPlan, context: EmitContext): EmitContext {
  return withTypeParameters(context, method.typeParameters);
}

/** The type parameters a method declares beyond the ones its receiver's class already binds. */
function methodOwnTypeParameters(method: MethodPlan, plan: TypePlan): readonly string[] {
  return method.typeParameters.slice(plan.typeParameters.length);
}

function emitBaseMethod(method: MethodPlan, plan: TypePlan, context: EmitContext): ts.ClassElement {
  const scoped = methodContext(method, context);
  const allocator = newAllocator(scoped);
  const parameters = methodParameters(method, allocator, scoped);
  const own = typeParameterDeclarations(methodOwnTypeParameters(method, plan));
  if (method.dispatches) {
    return documented(
      ts.factory.createMethodDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.AbstractKeyword)],
        undefined,
        method.name,
        undefined,
        own,
        parameters,
        emitType(method.declaration.result, scoped),
        undefined,
      ),
      method.declaration.doc,
    );
  }
  const body = emitFunctionBody(method.declaration.body, methodScope(method, parameters), allocator, scoped);
  return documented(
    ts.factory.createMethodDeclaration(
      [modifier(ts.SyntaxKind.PublicKeyword)],
      undefined,
      method.name,
      undefined,
      own,
      markUnreadParameters(parameters, body, allocator),
      emitType(method.declaration.result, scoped),
      body,
    ),
    method.declaration.doc,
  );
}

function emitCaseClass(entry: CasePlan, plan: TypePlan, nullary: boolean, context: EmitContext): ts.Statement {
  const members: ts.ClassElement[] = [
    ts.factory.createPropertyDeclaration(
      [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.ReadonlyKeyword)],
      propertyName('kind'),
      undefined,
      undefined,
      ts.factory.createAsExpression(
        ts.factory.createStringLiteral(entry.constructor.name),
        ts.factory.createTypeReferenceNode('const'),
      ),
    ),
  ];
  const constructorFields = caseFieldBinders(entry, context, [entry.className, plan.typeName]);
  if (constructorFields.length > 0) {
    // A parameter property would make the source field name a local binder too. Keep the public
    // property under its Lean name, but allocate the constructor binder and assign it explicitly.
    members.push(
      ...constructorFields.map(({ field }) =>
        ts.factory.createPropertyDeclaration(
          [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.ReadonlyKeyword)],
          propertyName(field.name),
          undefined,
          emitType(field.type, context),
          undefined,
        ),
      ),
      ts.factory.createConstructorDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword)],
        constructorFields.map(({ field, binder }) =>
          ts.factory.createParameterDeclaration(undefined, undefined, binder, undefined, emitType(field.type, context)),
        ),
        block(
          ts.factory.createExpressionStatement(
            ts.factory.createCallExpression(ts.factory.createSuper(), undefined, []),
          ),
          ...constructorFields.map(({ field, binder }) =>
            ts.factory.createExpressionStatement(
              ts.factory.createBinaryExpression(
                fieldAccess(ts.factory.createThis(), field.name),
                ts.SyntaxKind.EqualsToken,
                ts.factory.createIdentifier(binder),
              ),
            ),
          ),
          freezeThis(),
        ),
      ),
    );
  } else {
    // A payload constructor freezes in the constructor above. A nullary one has no field to assign
    // and would otherwise be the one mutable value the generated representation hands out, so it
    // declares the constructor that freezes it — every instance, not only the shared singleton.
    members.push(
      ts.factory.createConstructorDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword)],
        [],
        block(
          ts.factory.createExpressionStatement(
            ts.factory.createCallExpression(ts.factory.createSuper(), undefined, []),
          ),
          freezeThis(),
        ),
      ),
    );
  }
  for (const method of plan.methods) {
    if (!method.dispatches) continue;
    const dispatch = method.declaration.body;
    if (dispatch.kind !== 'match') throw new TypeError(`dispatching method ${method.declaration.name} lost its match`);
    const arm = dispatch.cases.find((candidate) => candidate.constructor === entry.constructor.name);
    if (arm === undefined) {
      throw new TypeError(`method ${method.declaration.name} decides no ${entry.constructor.name} case`);
    }
    const scoped = methodContext(method, context);
    const allocator = newAllocator(scoped);
    const declared = methodParameters(method, allocator, scoped);
    const scope = [...armBindings(entry.constructor), ...methodScope(method, declared)];
    const body = emitFunctionBody(arm.value, scope, allocator, scoped);
    members.push(
      ts.factory.createMethodDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.OverrideKeyword)],
        undefined,
        method.name,
        undefined,
        typeParameterDeclarations(methodOwnTypeParameters(method, plan)),
        // One override per case, so a parameter one case decides without reading is genuinely
        // unread there while the abstract signature still declares it.
        markUnreadParameters(declared, body, allocator),
        emitType(method.declaration.result, scoped),
        body,
      ),
    );
  }
  if (!nullary && plan.ground) {
    members.push(
      overrideMethod(
        'toData',
        [],
        ts.factory.createTypeReferenceNode(plan.dataName),
        ts.factory.createReturnStatement(
          ts.factory.createObjectLiteralExpression(
            [
              ts.factory.createPropertyAssignment(
                propertyName('kind'),
                ts.factory.createStringLiteral(entry.constructor.name),
              ),
              ...entry.constructor.fields.map((field) =>
                ts.factory.createPropertyAssignment(
                  propertyName(field.name),
                  encodeExpression(receiverField(field.name), field.type, context),
                ),
              ),
            ],
            true,
          ),
        ),
      ),
      overrideMethod(
        'equals',
        [ts.factory.createParameterDeclaration(undefined, undefined, context.locals.other, undefined, selfType(plan))],
        ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
        ts.factory.createReturnStatement(
          conjunction([
            ts.factory.createBinaryExpression(
              ts.factory.createIdentifier(context.locals.other),
              ts.SyntaxKind.InstanceOfKeyword,
              ts.factory.createIdentifier(entry.className),
            ),
            ...entry.constructor.fields.map((field) =>
              equalityExpression(
                receiverField(field.name),
                fieldAccess(ts.factory.createIdentifier(context.locals.other), field.name),
                field.type,
                equalityAllocator(context),
                context,
              ),
            ),
          ]),
        ),
      ),
    );
  }
  return ts.factory.createClassDeclaration(
    [modifier(ts.SyntaxKind.ExportKeyword)],
    entry.className,
    typeParameterDeclarations(plan.typeParameters),
    [
      ts.factory.createHeritageClause(ts.SyntaxKind.ExtendsKeyword, [
        ts.factory.createExpressionWithTypeArguments(
          ts.factory.createIdentifier(plan.typeName),
          typeParameterReferences(plan.typeParameters),
        ),
      ]),
    ],
    members,
  );
}

/**
 * A record with behaviour becomes an immutable class: `readonly` fields assigned from one named
 * init object, frozen on construction, with its transition helpers falling out of the Lean
 * functions that return the record itself.
 */
function emitNominalRecord(plan: TypePlan, declaration: LeanStructure, context: EmitContext): readonly ts.Statement[] {
  const self = selfType(plan);
  const members: ts.ClassElement[] = declaration.fields.map((field) =>
    documented(
      ts.factory.createPropertyDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.ReadonlyKeyword)],
        propertyName(field.name),
        undefined,
        emitType(field.type, context),
        undefined,
      ),
      field.doc,
    ),
  );
  members.push(
    ts.factory.createConstructorDeclaration(
      [modifier(ts.SyntaxKind.PublicKeyword)],
      [
        ts.factory.createParameterDeclaration(
          undefined,
          undefined,
          'init',
          undefined,
          ts.factory.createTypeReferenceNode(plan.initName, typeParameterReferences(plan.typeParameters)),
        ),
      ],
      block(
        ...declaration.fields.map((field) =>
          ts.factory.createExpressionStatement(
            ts.factory.createBinaryExpression(
              fieldAccess(ts.factory.createThis(), field.name),
              ts.SyntaxKind.EqualsToken,
              fieldAccess(ts.factory.createIdentifier('init'), field.name),
            ),
          ),
        ),
        freezeThis(),
      ),
    ),
  );
  if (plan.ground) members.push(emitRecordFromData(plan, declaration, context));
  for (const method of plan.methods) members.push(emitBaseMethod(method, plan, context));
  if (plan.ground) {
    members.push(
      ts.factory.createMethodDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword)],
        undefined,
        'toData',
        undefined,
        undefined,
        [],
        ts.factory.createTypeReferenceNode(plan.dataName),
        block(
          ts.factory.createReturnStatement(
            ts.factory.createObjectLiteralExpression(
              declaration.fields.map((field) =>
                ts.factory.createPropertyAssignment(
                  propertyName(field.name),
                  encodeExpression(receiverField(field.name), field.type, context),
                ),
              ),
              true,
            ),
          ),
        ),
      ),
      ts.factory.createMethodDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword)],
        undefined,
        'equals',
        undefined,
        undefined,
        [ts.factory.createParameterDeclaration(undefined, undefined, context.locals.other, undefined, self)],
        ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
        block(
          ts.factory.createReturnStatement(
            conjunction(
              declaration.fields.map((field) =>
                equalityExpression(
                  receiverField(field.name),
                  fieldAccess(ts.factory.createIdentifier(context.locals.other), field.name),
                  field.type,
                  equalityAllocator(context),
                  context,
                ),
              ),
            ),
          ),
        ),
      ),
    );
  }
  return [
    interfaceOfFields(plan.initName, plan.typeParameters, declaration.fields, (field) => emitType(field.type, context)),
    ...(plan.ground
      ? [interfaceOfFields(plan.dataName, [], declaration.fields, (field) => dataType(field.type, context))]
      : []),
    documented(
      ts.factory.createClassDeclaration(
        [modifier(ts.SyntaxKind.ExportKeyword)],
        plan.typeName,
        typeParameterDeclarations(plan.typeParameters),
        undefined,
        members,
      ),
      declaration.doc,
    ),
  ];
}

function interfaceOfFields(
  name: string,
  typeParameters: readonly string[],
  fields: readonly LeanField[],
  type: (field: LeanField) => ts.TypeNode,
): ts.Statement {
  return ts.factory.createInterfaceDeclaration(
    [modifier(ts.SyntaxKind.ExportKeyword)],
    name,
    typeParameterDeclarations(typeParameters),
    undefined,
    fields.map((field) => readonlyProperty(field.name, type(field))),
  );
}

function emitEnumDataType(plan: TypePlan, declaration: LeanEnum, nullary: boolean, context: EmitContext): ts.Statement {
  const image = nullary
    ? ts.factory.createIndexedAccessTypeNode(ts.factory.createTypeReferenceNode(plan.typeName), literalType('kind'))
    : ts.factory.createUnionTypeNode(
        declaration.constructors.map((constructor) =>
          ts.factory.createTypeLiteralNode([
            readonlyProperty('kind', literalType(constructor.name)),
            ...constructor.fields.map((field) => readonlyProperty(field.name, dataType(field.type, context))),
          ]),
        ),
      );
  return ts.factory.createTypeAliasDeclaration(
    [modifier(ts.SyntaxKind.ExportKeyword)],
    plan.dataName,
    undefined,
    image,
  );
}

/** The representation of a nullary-only inductive is its tag; otherwise a tagged data object. */
function emitEnumRepresentation(
  plan: TypePlan,
  base: ts.TypeNode,
  nullary: boolean,
  context: EmitContext,
): readonly ts.ClassElement[] {
  if (!nullary) {
    return [
      abstractMethod('toData', [], ts.factory.createTypeReferenceNode(plan.dataName)),
      abstractMethod(
        'equals',
        [ts.factory.createParameterDeclaration(undefined, undefined, context.locals.other, undefined, base)],
        ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
      ),
    ];
  }
  return [
    publicMethod(
      'toData',
      [],
      ts.factory.createTypeReferenceNode(plan.dataName),
      ts.factory.createReturnStatement(receiverField('kind')),
    ),
    publicMethod(
      'equals',
      [ts.factory.createParameterDeclaration(undefined, undefined, context.locals.other, undefined, base)],
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
      ts.factory.createReturnStatement(
        ts.factory.createBinaryExpression(
          ts.factory.createThis(),
          ts.SyntaxKind.EqualsEqualsEqualsToken,
          ts.factory.createIdentifier(context.locals.other),
        ),
      ),
    ),
  ];
}

function emitEnumFromData(
  plan: TypePlan,
  declaration: LeanEnum,
  base: ts.TypeNode,
  context: EmitContext,
): ts.ClassElement {
  const value = ts.factory.createIdentifier(context.locals.value);
  const nullary = declaration.constructors.every((constructor) => constructor.fields.length === 0);
  const constructorCase = (entry: CasePlan): ts.Expression =>
    ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier(plan.typeName), entry.constructor.name);
  // A nullary constructor's data image is its own tag, so the switch decides the whole domain: no
  // `typeof` pre-check is needed, and anything the tags do not name falls to the default refusal.
  const statements: readonly ts.Statement[] = nullary
    ? [
        ts.factory.createSwitchStatement(
          value,
          ts.factory.createCaseBlock([
            ...plan.cases.map((entry) =>
              ts.factory.createCaseClause(ts.factory.createStringLiteral(entry.constructor.name), [
                ts.factory.createReturnStatement(constructorCase(entry)),
              ]),
            ),
            ts.factory.createDefaultClause([throwStatement(`${plan.typeName} data must name a constructor`)]),
          ]),
        ),
      ]
    : [
        guard(
          ts.factory.createPrefixUnaryExpression(
            ts.SyntaxKind.ExclamationToken,
            callPrelude(context, context.prelude.isDataObject, [value]),
          ),
          `${plan.typeName} data must be an object`,
        ),
        ts.factory.createSwitchStatement(
          elementAccess(value, 'kind'),
          ts.factory.createCaseBlock([
            ...plan.cases.map((entry) =>
              ts.factory.createCaseClause(ts.factory.createStringLiteral(entry.constructor.name), [
                ts.factory.createBlock(
                  emitDataDecoder(
                    entry.constructor.fields,
                    `${plan.typeName}.${entry.constructor.name}`,
                    entry.constructor.name,
                    context,
                    (values) =>
                      ts.factory.createReturnStatement(
                        values.length === 0
                          ? constructorCase(entry)
                          : ts.factory.createCallExpression(constructorCase(entry), undefined, values),
                      ),
                  ),
                  true,
                ),
              ]),
            ),
            ts.factory.createDefaultClause([throwStatement(`${plan.typeName} data must name a constructor`)]),
          ]),
        ),
      ];
  return staticMethod('fromData', base, statements, context);
}

function emitRecordFromData(plan: TypePlan, declaration: LeanStructure, context: EmitContext): ts.ClassElement {
  return staticMethod(
    'fromData',
    ts.factory.createTypeReferenceNode(plan.typeName),
    emitDataDecoder(declaration.fields, plan.typeName, undefined, context, (values) =>
      ts.factory.createReturnStatement(
        ts.factory.createNewExpression(ts.factory.createIdentifier(plan.typeName), undefined, [
          objectLiteral(declaration.fields, values),
        ]),
      ),
    ),
    context,
  );
}

/**
 * Reads one data object: the exact field set is validated before any field is read, and each
 * field is decoded in declaration order into the value the caller builds.
 */
function emitDataDecoder(
  fields: readonly LeanField[],
  owner: string,
  taggedKind: string | undefined,
  context: EmitContext,
  build: (values: readonly ts.Expression[]) => ts.Statement,
): readonly ts.Statement[] {
  const keys =
    taggedKind === undefined ? fields.map((field) => field.name) : ['kind', ...fields.map((field) => field.name)];
  const validated = callPrelude(context, context.prelude.requireDataFields, [
    ts.factory.createIdentifier(context.locals.value),
    ts.factory.createStringLiteral(owner),
    ts.factory.createArrayLiteralExpression(keys.map((key) => ts.factory.createStringLiteral(key))),
  ]);
  if (fields.length === 0) return [ts.factory.createExpressionStatement(validated), build([])];
  const data = ts.factory.createIdentifier(context.locals.data);
  return [
    constantStatement(context.locals.data, validated),
    build(
      fields.map((field) =>
        decodeExpression(
          elementAccess(data, field.name),
          field.type,
          ts.factory.createStringLiteral(`${owner} ${field.name}`),
          context,
        ),
      ),
    ),
  ];
}

/**
 * A value's data image. A value object encodes through its own `toData`; everything else is already
 * its own image, so encoding is the identity. A type that nests a value object under a mapped type
 * would need a per-instantiation encoder, which would be a second representation of one type, so it
 * is refused with the source-level remedy instead.
 */
function encodeExpression(value: ts.Expression, type: LeanType, context: EmitContext): ts.Expression {
  if (type.kind === 'named') {
    const plan = requiredTypePlan(context, type.name);
    if (plan.nominal) {
      return ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(value, 'toData'), undefined, []);
    }
  }
  assertIdentityDataImage(type, context);
  return value;
}

/**
 * Every type inside this one is its own data image. A nested value object is not, and neither is a
 * type parameter or an arrow, so each is refused by name and by the path that reached it rather
 * than encoded by guesswork.
 */
function assertIdentityDataImage(type: LeanType, context: EmitContext, path: readonly string[] = []): void {
  const at = path.length === 0 ? '' : ` at ${path.join('.')}`;
  switch (type.kind) {
    // Every case in this group is its own data image; a JsonValue's is the tagged union it
    // already is, exactly as an Option's is. A bare comment between two case labels is not a
    // statement to the linter, so the note lives above the group it explains.
    case 'boolean':
    case 'nat':
    case 'string':
    case 'int':
    case 'char':
    case 'json':
      return;
    case 'parameter':
    case 'function':
    case 'bytes':
    case 'hashMap':
    case 'treeMap':
      throw new TypeError(`${renderType(type)}${at} has no data image`);
    case 'option':
      assertIdentityDataImage(type.value, context, path);
      return;
    case 'except':
      assertIdentityDataImage(type.error, context, path);
      assertIdentityDataImage(type.value, context, path);
      return;
    case 'list':
    case 'array':
      assertIdentityDataImage(type.element, context, path);
      return;
    case 'pair':
      assertIdentityDataImage(type.first, context, path);
      assertIdentityDataImage(type.second, context, path);
      return;
    case 'named': {
      const plan = requiredTypePlan(context, type.name);
      if (plan.nominal) {
        throw new TypeError(
          `the value object ${plan.typeName}${at} has no data image of its own; give the type that holds it behaviour so it becomes a value object too`,
        );
      }
      if (!plan.ground) {
        throw new TypeError(
          `the generic type ${plan.typeName}${at} has no data image; a codec per instantiation would represent one type twice`,
        );
      }
      const fields =
        plan.declaration.kind === 'record'
          ? plan.declaration.fields
          : plan.declaration.constructors.flatMap((constructor) => constructor.fields);
      for (const field of fields) {
        assertIdentityDataImage(field.type, context, [...path, plan.typeName, field.name]);
      }
      return;
    }
  }
}

function decodeExpression(
  value: ts.Expression,
  type: LeanType,
  label: ts.Expression,
  context: EmitContext,
): ts.Expression {
  switch (type.kind) {
    case 'boolean':
      return callPrelude(context, context.prelude.requireBoolean, [value, label]);
    case 'nat':
      return callPrelude(context, context.prelude.requireNat, [value, label]);
    case 'string':
      return callPrelude(context, context.prelude.requireString, [value, label]);
    case 'int':
      return callPrelude(context, context.prelude.requireInt, [value, label]);
    case 'char':
      return callPrelude(context, context.prelude.requireChar, [value, label]);
    case 'json':
      return callPrelude(context, context.prelude.requireJson, [value, label]);
    case 'pair':
      return callPrelude(context, context.prelude.requirePair, [
        value,
        label,
        elementDecoder(type.first, context),
        elementDecoder(type.second, context),
      ]);
    // A ByteArray and a Map are engine objects with internal slots rather than JSON-shaped values,
    // and no admitted opcode observes either, so neither has a decoder to reach here.
    case 'parameter':
    case 'function':
    case 'bytes':
    case 'hashMap':
    case 'treeMap':
      throw new TypeError(`${renderType(type)} cannot be decoded at the package boundary`);
    case 'option':
      return callPrelude(context, context.prelude.requireOption, [value, label, elementDecoder(type.value, context)]);
    case 'except':
      return callPrelude(context, context.prelude.requireExcept, [
        value,
        label,
        elementDecoder(type.error, context),
        elementDecoder(type.value, context),
      ]);
    case 'list':
      return callPrelude(context, context.prelude.requireList, [value, label, elementDecoder(type.element, context)]);
    // An Array shares the List image, so it is read by the same validator over the same elements.
    case 'array':
      return callPrelude(context, context.prelude.requireList, [value, label, elementDecoder(type.element, context)]);
    case 'named': {
      const plan = requiredTypePlan(context, type.name);
      if (!plan.ground) {
        throw new TypeError(`the generic type ${plan.typeName} cannot be decoded at the package boundary`);
      }
      if (plan.nominal) {
        return ts.factory.createCallExpression(
          ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier(plan.typeName), 'fromData'),
          undefined,
          [value],
        );
      }
      const decoder = context.prelude.decoders.get(type.name);
      if (decoder === undefined) throw new TypeError(`missing generated decoder for ${type.name}`);
      return callPrelude(context, decoder, [value, label]);
    }
  }
}

/** The payload decoder a mapped type's validator is handed, as `(value, name) => decoded`. */
function elementDecoder(type: LeanType, context: EmitContext): ts.Expression {
  return ts.factory.createArrowFunction(
    undefined,
    undefined,
    [dataParameter(context.locals.element, context), stringParameter(context.locals.name)],
    undefined,
    undefined,
    decodeExpression(
      ts.factory.createIdentifier(context.locals.element),
      type,
      ts.factory.createIdentifier(context.locals.name),
      context,
    ),
  );
}

/**
 * Structural equality at one type. A list comparison binds its own element and index, and a nested
 * list binds fresh ones: reusing the names would let an inner binder shadow the outer index the
 * inner comparison still reads, and the comparison would silently read the wrong element.
 */
function equalityExpression(
  left: ts.Expression,
  right: ts.Expression,
  type: LeanType,
  allocator: IdentifierAllocator,
  context: EmitContext,
): ts.Expression {
  switch (type.kind) {
    case 'boolean':
    case 'nat':
    case 'string':
    case 'int':
    case 'char':
      return ts.factory.createBinaryExpression(left, ts.SyntaxKind.EqualsEqualsEqualsToken, right);
    case 'pair':
      return conjunction([
        equalityExpression(fieldAccess(left, 'fst'), fieldAccess(right, 'fst'), type.first, allocator, context),
        equalityExpression(fieldAccess(left, 'snd'), fieldAccess(right, 'snd'), type.second, allocator, context),
      ]);
    // A JsonValue is a payload-carrying union, and a Map or a ByteArray is an engine object whose
    // contents no admitted opcode reads, so each is refused here for the same reason a user union
    // with payloads is: this fragment version proves no structural comparison for it.
    case 'parameter':
    case 'function':
    case 'json':
    case 'bytes':
    case 'hashMap':
    case 'treeMap':
      throw new TypeError(`${renderType(type)} has no structural equality`);
    case 'named': {
      const plan = requiredTypePlan(context, type.name);
      if (!plan.nominal) return structuralEquality(left, right, plan, type, allocator, context);
      return ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(left, 'equals'), undefined, [
        right,
      ]);
    }
    case 'option':
      return callPrelude(context, context.prelude.equalOption, [
        left,
        right,
        comparator(type.value, allocator, context),
      ]);
    case 'except':
      return callPrelude(context, context.prelude.equalExcept, [
        left,
        right,
        comparator(type.error, allocator, context),
        comparator(type.value, allocator, context),
      ]);
    case 'list':
      return callPrelude(context, context.prelude.equalList, [
        left,
        right,
        comparator(type.element, allocator, context),
      ]);
    case 'array':
      return callPrelude(context, context.prelude.equalList, [
        left,
        right,
        comparator(type.element, allocator, context),
      ]);
  }
}

/** The payload comparison a shared comparison helper is handed, as `(left, right) => same`. */
function comparator(type: LeanType, allocator: IdentifierAllocator, context: EmitContext): ts.Expression {
  const leftName = allocator.allocate('left');
  const rightName = allocator.allocate('right');
  return ts.factory.createArrowFunction(
    undefined,
    undefined,
    [
      ts.factory.createParameterDeclaration(undefined, undefined, leftName),
      ts.factory.createParameterDeclaration(undefined, undefined, rightName),
    ],
    undefined,
    undefined,
    equalityExpression(
      ts.factory.createIdentifier(leftName),
      ts.factory.createIdentifier(rightName),
      type,
      allocator,
      context,
    ),
  );
}

/**
 * A structural type is its own value, so equality is the structural comparison of its parts. A
 * discriminated union compares its tag first; a tag compares directly.
 */
function structuralEquality(
  left: ts.Expression,
  right: ts.Expression,
  plan: TypePlan,
  type: Extract<LeanType, { readonly kind: 'named' }>,
  allocator: IdentifierAllocator,
  context: EmitContext,
): ts.Expression {
  if (plan.declaration.kind === 'enum') {
    if (plan.declaration.constructors.every((constructor) => constructor.fields.length === 0)) {
      return ts.factory.createBinaryExpression(left, ts.SyntaxKind.EqualsEqualsEqualsToken, right);
    }
    throw new TypeError(
      `structural equality of the payload-carrying union ${plan.declaration.name} is outside this fragment version`,
    );
  }
  return conjunction(
    plan.declaration.fields.map((field) =>
      equalityExpression(
        fieldAccess(left, field.name),
        fieldAccess(right, field.name),
        substituteType(field.type, type.arguments),
        allocator,
        context,
      ),
    ),
  );
}

/** The data image of a Lean type: a value object is its data, and every other type is its own. */
function dataType(type: LeanType, context: EmitContext): ts.TypeNode {
  if (type.kind === 'named') {
    const plan = requiredTypePlan(context, type.name);
    if (plan.nominal) return ts.factory.createTypeReferenceNode(plan.dataName);
  }
  assertIdentityDataImage(type, context);
  return emitType(type, context);
}

/**
 * The boundary type and the primitive validators every generated codec shares, plus the two mapped
 * type aliases and the helpers whose opcode semantics need a guard. Each is emitted only where the
 * package actually reached it, so an unused validator never lands in a generated file.
 */
function emitBoundaryPrimitives(context: EmitContext): readonly ts.Statement[] {
  const { prelude, locals } = context;
  const value = ts.factory.createIdentifier(locals.value);
  const name = ts.factory.createIdentifier(locals.name);
  const fields = ts.factory.createIdentifier(locals.fields);
  const dataRecord = dataRecordType(prelude.dataBoundary);
  const boundaryExport = (validator: string): readonly ts.Modifier[] | undefined =>
    context.boundary.validators.has(validator) ? [modifier(ts.SyntaxKind.ExportKeyword)] : undefined;
  const statements: ts.Statement[] = [];
  // Built last-to-first so a validator reached only through another one is still emitted, then
  // returned in a fixed order so the bytes are stable.
  // Every guarded opcode the package reached, in one fixed order so the bytes are stable.
  for (const role of [...LEAN_RUNTIME_HELPER_ROLES].reverse()) {
    if (context.used.has(requiredHelper(context, role))) statements.push(emitRuntimeHelper(role, context));
  }
  if (context.used.has(prelude.requireJson)) statements.push(emitJsonValidator(context));
  if (context.used.has(prelude.requirePair)) statements.push(emitPairValidator(context));
  if (context.used.has(prelude.requireChar)) statements.push(emitCharValidator(context));
  if (context.used.has(prelude.requireInt)) statements.push(emitIntValidator(context));
  if (context.used.has(prelude.equalList)) statements.push(emitEqualListHelper(context));
  if (context.used.has(prelude.equalExcept)) statements.push(emitEqualExceptHelper(context));
  if (context.used.has(prelude.equalOption)) statements.push(emitEqualOptionHelper(context));
  if (context.used.has(prelude.requireExcept)) statements.push(emitExceptValidator(context));
  if (context.used.has(prelude.requireOption)) statements.push(emitOptionValidator(context));
  if (context.used.has(prelude.requireList)) statements.push(emitListValidator(context));
  if (context.used.has(prelude.requireString)) {
    statements.push(
      ts.factory.createFunctionDeclaration(
        boundaryExport(prelude.requireString),
        undefined,
        prelude.requireString,
        undefined,
        [dataParameter(locals.value, context), stringParameter(locals.name)],
        ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword),
        block(
          guard(
            ts.factory.createPrefixUnaryExpression(ts.SyntaxKind.ExclamationToken, typeOfIs(value, 'string')),
            namedMessage(context, 'must be a string'),
          ),
          // Lean String is a sequence of Unicode scalar values. JavaScript admits lone UTF-16
          // surrogates, so decode the boundary rather than letting an ill-formed code-unit sequence
          // enter a value the string opcodes model as scalar text.
          ts.factory.createForStatement(
            ts.factory.createVariableDeclarationList(
              [
                ts.factory.createVariableDeclaration(
                  locals.index,
                  undefined,
                  undefined,
                  ts.factory.createNumericLiteral(0),
                ),
              ],
              ts.NodeFlags.Let,
            ),
            ts.factory.createBinaryExpression(
              ts.factory.createIdentifier(locals.index),
              ts.SyntaxKind.LessThanToken,
              ts.factory.createPropertyAccessExpression(value, 'length'),
            ),
            ts.factory.createBinaryExpression(
              ts.factory.createIdentifier(locals.index),
              ts.SyntaxKind.PlusEqualsToken,
              ts.factory.createNumericLiteral(1),
            ),
            block(
              constantStatement(locals.codeUnit, charCodeAt(value, ts.factory.createIdentifier(locals.index))),
              ts.factory.createIfStatement(
                codeUnitInRange(ts.factory.createIdentifier(locals.codeUnit), 0xd800, 0xdbff),
                block(
                  guard(
                    ts.factory.createBinaryExpression(
                      ts.factory.createBinaryExpression(
                        ts.factory.createBinaryExpression(
                          ts.factory.createIdentifier(locals.index),
                          ts.SyntaxKind.PlusToken,
                          ts.factory.createNumericLiteral(1),
                        ),
                        ts.SyntaxKind.GreaterThanEqualsToken,
                        ts.factory.createPropertyAccessExpression(value, 'length'),
                      ),
                      ts.SyntaxKind.BarBarToken,
                      ts.factory.createPrefixUnaryExpression(
                        ts.SyntaxKind.ExclamationToken,
                        codeUnitInRange(
                          charCodeAt(
                            value,
                            ts.factory.createBinaryExpression(
                              ts.factory.createIdentifier(locals.index),
                              ts.SyntaxKind.PlusToken,
                              ts.factory.createNumericLiteral(1),
                            ),
                          ),
                          0xdc00,
                          0xdfff,
                        ),
                      ),
                    ),
                    namedMessage(context, 'must contain only well-formed UTF-16 code units'),
                  ),
                  ts.factory.createExpressionStatement(
                    ts.factory.createBinaryExpression(
                      ts.factory.createIdentifier(locals.index),
                      ts.SyntaxKind.PlusEqualsToken,
                      ts.factory.createNumericLiteral(1),
                    ),
                  ),
                ),
                ts.factory.createIfStatement(
                  codeUnitInRange(ts.factory.createIdentifier(locals.codeUnit), 0xdc00, 0xdfff),
                  block(throwNamed(context, 'must contain only well-formed UTF-16 code units')),
                ),
              ),
            ),
          ),
          ts.factory.createReturnStatement(value),
        ),
      ),
    );
  }
  if (context.used.has(prelude.requireNat)) {
    statements.push(
      ts.factory.createFunctionDeclaration(
        boundaryExport(prelude.requireNat),
        undefined,
        prelude.requireNat,
        undefined,
        [dataParameter(locals.value, context), stringParameter(locals.name)],
        ts.factory.createKeywordTypeNode(ts.SyntaxKind.BigIntKeyword),
        block(
          ts.factory.createIfStatement(
            ts.factory.createBinaryExpression(
              typeOfIs(value, 'bigint'),
              ts.SyntaxKind.AmpersandAmpersandToken,
              ts.factory.createBinaryExpression(
                value,
                ts.SyntaxKind.GreaterThanEqualsToken,
                ts.factory.createBigIntLiteral('0n'),
              ),
            ),
            block(ts.factory.createReturnStatement(value)),
          ),
          throwNamed(context, 'must be a nonnegative integer'),
        ),
      ),
    );
  }
  if (context.used.has(prelude.requireBoolean)) {
    statements.push(
      ts.factory.createFunctionDeclaration(
        boundaryExport(prelude.requireBoolean),
        undefined,
        prelude.requireBoolean,
        undefined,
        [dataParameter(locals.value, context), stringParameter(locals.name)],
        ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
        block(
          // Decided by value, not by `typeof`: the boundary union already names every arrival, so
          // the two inhabitants of Bool are recognised directly and everything else is rejected.
          ts.factory.createIfStatement(
            disjunction([
              ts.factory.createBinaryExpression(value, ts.SyntaxKind.EqualsEqualsEqualsToken, ts.factory.createTrue()),
              ts.factory.createBinaryExpression(value, ts.SyntaxKind.EqualsEqualsEqualsToken, ts.factory.createFalse()),
            ]),
            block(ts.factory.createReturnStatement(value)),
          ),
          throwNamed(context, 'must be a boolean'),
        ),
      ),
    );
  }
  if (context.used.has(prelude.requireDataFields)) {
    statements.push(
      ts.factory.createFunctionDeclaration(
        undefined,
        undefined,
        prelude.requireDataFields,
        undefined,
        [
          dataParameter(locals.value, context),
          stringParameter(locals.name),
          ts.factory.createParameterDeclaration(
            undefined,
            undefined,
            locals.fields,
            undefined,
            ts.factory.createTypeOperatorNode(
              ts.SyntaxKind.ReadonlyKeyword,
              ts.factory.createArrayTypeNode(ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword)),
            ),
          ),
        ],
        dataRecord,
        block(
          guard(
            ts.factory.createPrefixUnaryExpression(
              ts.SyntaxKind.ExclamationToken,
              callPrelude(context, prelude.isDataObject, [value]),
            ),
            namedMessage(context, 'data must be an object'),
          ),
          guard(
            ts.factory.createBinaryExpression(
              ts.factory.createBinaryExpression(
                ts.factory.createPropertyAccessExpression(
                  ts.factory.createCallExpression(
                    ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier('Object'), 'keys'),
                    undefined,
                    [value],
                  ),
                  'length',
                ),
                ts.SyntaxKind.ExclamationEqualsEqualsToken,
                ts.factory.createPropertyAccessExpression(fields, 'length'),
              ),
              ts.SyntaxKind.BarBarToken,
              ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(fields, 'some'), undefined, [
                ts.factory.createArrowFunction(
                  undefined,
                  undefined,
                  [stringParameter(locals.field)],
                  undefined,
                  undefined,
                  ts.factory.createPrefixUnaryExpression(
                    ts.SyntaxKind.ExclamationToken,
                    ts.factory.createCallExpression(
                      ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier('Object'), 'hasOwn'),
                      undefined,
                      [value, ts.factory.createIdentifier(locals.field)],
                    ),
                  ),
                ),
              ]),
            ),
            ts.factory.createTemplateExpression(ts.factory.createTemplateHead(''), [
              ts.factory.createTemplateSpan(name, ts.factory.createTemplateMiddle(' data fields must be exactly ')),
              ts.factory.createTemplateSpan(
                ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(fields, 'join'), undefined, [
                  ts.factory.createStringLiteral(', '),
                ]),
                ts.factory.createTemplateTail(''),
              ),
            ]),
          ),
          ts.factory.createReturnStatement(value),
        ),
      ),
    );
  }
  if (context.used.has(prelude.isDataObject)) {
    statements.push(
      ts.factory.createFunctionDeclaration(
        undefined,
        undefined,
        prelude.isDataObject,
        undefined,
        [dataParameter(locals.value, context)],
        ts.factory.createTypePredicateNode(undefined, ts.factory.createIdentifier(locals.value), dataRecord),
        block(
          ts.factory.createReturnStatement(
            conjunction([
              typeOfIs(value, 'object'),
              ts.factory.createBinaryExpression(
                value,
                ts.SyntaxKind.ExclamationEqualsEqualsToken,
                ts.factory.createNull(),
              ),
              ts.factory.createPrefixUnaryExpression(ts.SyntaxKind.ExclamationToken, isArrayCall(value)),
            ]),
          ),
        ),
      ),
    );
  }
  // Built last: each alias is emitted only once something above has actually referenced it.
  const aliases: ts.Statement[] = [];
  if (context.used.has(prelude.jsonType)) aliases.push(emitJsonAlias(prelude.jsonType));
  if (context.used.has(prelude.exceptType)) aliases.push(emitExceptAlias(prelude.exceptType));
  if (context.used.has(prelude.optionType)) aliases.push(emitOptionAlias(prelude.optionType));
  if (context.used.has(prelude.dataBoundary)) aliases.push(emitDataBoundaryAlias(prelude.dataBoundary));
  return [...aliases.reverse(), ...statements.reverse()];
}

/** Reads one UTF-16 code unit without widening a decoded string to an untyped value. */
function charCodeAt(value: ts.Expression, index: ts.Expression): ts.Expression {
  return ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(value, 'charCodeAt'), undefined, [
    index,
  ]);
}

/** Whether one code-unit expression lies in one inclusive UTF-16 surrogate range. */
function codeUnitInRange(value: ts.Expression, lower: number, upper: number): ts.Expression {
  return ts.factory.createBinaryExpression(
    ts.factory.createBinaryExpression(
      value,
      ts.SyntaxKind.GreaterThanEqualsToken,
      ts.factory.createNumericLiteral(lower),
    ),
    ts.SyntaxKind.AmpersandAmpersandToken,
    ts.factory.createBinaryExpression(value, ts.SyntaxKind.LessThanEqualsToken, ts.factory.createNumericLiteral(upper)),
  );
}

function typeOfIs(value: ts.Expression, expected: string): ts.Expression {
  return ts.factory.createBinaryExpression(
    ts.factory.createTypeOfExpression(value),
    ts.SyntaxKind.EqualsEqualsEqualsToken,
    ts.factory.createStringLiteral(expected),
  );
}

function isArrayCall(value: ts.Expression): ts.Expression {
  return ts.factory.createCallExpression(
    ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier('Array'), 'isArray'),
    undefined,
    [value],
  );
}

/** `Option<A>`, the tagged union every admitted `Option` lowers to. */
function emitOptionAlias(name: string): ts.Statement {
  return ts.factory.createTypeAliasDeclaration(
    [modifier(ts.SyntaxKind.ExportKeyword)],
    name,
    [ts.factory.createTypeParameterDeclaration(undefined, 'A')],
    ts.factory.createUnionTypeNode([
      ts.factory.createTypeLiteralNode([readonlyProperty('kind', literalType('none'))]),
      ts.factory.createTypeLiteralNode([
        readonlyProperty('kind', literalType('some')),
        readonlyProperty('value', ts.factory.createTypeReferenceNode('A')),
      ]),
    ]),
  );
}

/** `Except<E, A>`, the tagged union every admitted `Except` lowers to. */
function emitExceptAlias(name: string): ts.Statement {
  return ts.factory.createTypeAliasDeclaration(
    [modifier(ts.SyntaxKind.ExportKeyword)],
    name,
    [
      ts.factory.createTypeParameterDeclaration(undefined, 'E'),
      ts.factory.createTypeParameterDeclaration(undefined, 'A'),
    ],
    ts.factory.createUnionTypeNode([
      ts.factory.createTypeLiteralNode([
        readonlyProperty('kind', literalType('error')),
        readonlyProperty('error', ts.factory.createTypeReferenceNode('E')),
      ]),
      ts.factory.createTypeLiteralNode([
        readonlyProperty('kind', literalType('ok')),
        readonlyProperty('value', ts.factory.createTypeReferenceNode('A')),
      ]),
    ]),
  );
}

/**
 * `JsonValue`, the one inductive the fragment owns rather than the target. It lowers to the same
 * tagged-object image every other union has, so a match on it is the tag chain a user inductive
 * gets and its data image is itself.
 */
function emitJsonAlias(name: string): ts.Statement {
  const self = ts.factory.createTypeReferenceNode(name);
  const variant = (tag: string, payload?: ts.TypeNode): ts.TypeNode =>
    ts.factory.createTypeLiteralNode([
      readonlyProperty('kind', literalType(tag)),
      ...(payload === undefined ? [] : [readonlyProperty('value', payload)]),
    ]);
  return ts.factory.createTypeAliasDeclaration(
    [modifier(ts.SyntaxKind.ExportKeyword)],
    name,
    undefined,
    ts.factory.createUnionTypeNode([
      variant('null'),
      variant('bool', ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword)),
      variant('int', ts.factory.createKeywordTypeNode(ts.SyntaxKind.BigIntKeyword)),
      variant('string', ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword)),
      variant('array', readonlyArrayType(self)),
      variant(
        'object',
        readonlyArrayType(
          ts.factory.createTypeLiteralNode([
            readonlyProperty('fst', ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword)),
            readonlyProperty('snd', self),
          ]),
        ),
      ),
    ]),
  );
}

/** The identifier hint each helper role's declaration is allocated from. */
const HELPER_DECLARATION_HINTS: Readonly<Record<LeanRuntimeHelperRole, string>> = {
  'nat-truncated-subtraction': 'natSubtract',
  'list-head-option': 'listHead',
  'int-truncated-division': 'intTruncatedDivide',
  'int-truncated-modulo': 'intTruncatedModulo',
  'int-to-nat-clamp': 'intToNat',
  'char-of-nat': 'charOfNat',
  'char-less-code-point': 'charLess',
};

/**
 * The first code point of a Char image.
 *
 * A Char image is a one-code-point string, so `codePointAt(0)` is present by construction.
 * TypeScript cannot express that refinement on `string`, however, and gives the method type
 * `number | undefined`. The explicit fallback makes the emitted JavaScript total without
 * introducing a refusal: on the proved Char domain it is unreachable, while outside that domain it
 * gives the same scalar the Lean `Char.ofNat` fallback uses. The exact `?? 0` is recorded in
 * the opcode registry and compared byte-for-byte by the semantics gate.
 */
function firstCodePoint(value: ts.Expression): ts.Expression {
  return ts.factory.createBinaryExpression(
    ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(value, 'codePointAt'), undefined, [
      ts.factory.createNumericLiteral(0),
    ]),
    ts.SyntaxKind.QuestionQuestionToken,
    ts.factory.createNumericLiteral(0),
  );
}
/** `[...value]`: the code points of a string, or a fresh dense copy of an array. */
function spreadArray(value: ts.Expression): ts.Expression {
  return ts.factory.createArrayLiteralExpression([ts.factory.createSpreadElement(value)], false);
}

/**
 * The one emitted shape every generated helper's body has, over operands already emitted.
 *
 * This is the helper counterpart of `operationForm`: an opcode whose exact Lean semantics need a
 * guard reaches the target as a declaration rather than as a use-site form, and this is the only
 * place that declaration's body exists. `helperOperationForms` prints it over the operand names
 * its registry row declares, so the row's `emittedForm` is joined against emitted structure rather
 * than against a copy of itself.
 */
function helperBodyForm(role: LeanRuntimeHelperRole, operands: readonly ts.Expression[]): ts.Expression {
  const operand = (index: number): ts.Expression => {
    const only = operands[index];
    if (only === undefined) throw new TypeError(`the ${role} helper is missing operand ${index}`);
    return only;
  };
  const zero = ts.factory.createBigIntLiteral('0n');
  const select = (condition: ts.Expression, consequent: ts.Expression, alternate: ts.Expression): ts.Expression =>
    ts.factory.createConditionalExpression(condition, undefined, consequent, undefined, alternate);
  const compare = (left: ts.Expression, token: ts.BinaryOperator, right: ts.Expression): ts.Expression =>
    ts.factory.createBinaryExpression(left, token, right);
  switch (role) {
    case 'nat-truncated-subtraction':
      return select(
        compare(operand(0), ts.SyntaxKind.LessThanToken, operand(1)),
        zero,
        compare(operand(0), ts.SyntaxKind.MinusToken, operand(1)),
      );
    case 'list-head-option':
      return select(
        isEmptyList(operand(0)),
        noneLiteral(),
        someLiteral(ts.factory.createElementAccessExpression(operand(0), ts.factory.createNumericLiteral(0))),
      );
    // BigInt division throws on a zero divisor, and Lean's `Int.tdiv` is total with `0` there, so
    // the guard decides before the division runs.
    case 'int-truncated-division':
      return select(
        compare(operand(1), ts.SyntaxKind.EqualsEqualsEqualsToken, zero),
        zero,
        compare(operand(0), ts.SyntaxKind.SlashToken, operand(1)),
      );
    case 'int-truncated-modulo':
      return select(
        compare(operand(1), ts.SyntaxKind.EqualsEqualsEqualsToken, zero),
        operand(0),
        compare(operand(0), ts.SyntaxKind.PercentToken, operand(1)),
      );
    case 'int-to-nat-clamp':
      return select(compare(operand(0), ts.SyntaxKind.LessThanToken, zero), zero, operand(0));
    // `Nat.isValidChar`: a scalar value below the maximum code point and outside the surrogate
    // range. Anything else is `Char.ofNat`'s default, which is U+0000.
    case 'char-of-nat':
      return select(
        conjunction([
          compare(operand(0), ts.SyntaxKind.GreaterThanEqualsToken, zero),
          compare(operand(0), ts.SyntaxKind.LessThanEqualsToken, ts.factory.createBigIntLiteral('1114111n')),
          ts.factory.createPrefixUnaryExpression(
            ts.SyntaxKind.ExclamationToken,
            conjunction([
              compare(operand(0), ts.SyntaxKind.GreaterThanEqualsToken, ts.factory.createBigIntLiteral('55296n')),
              compare(operand(0), ts.SyntaxKind.LessThanEqualsToken, ts.factory.createBigIntLiteral('57343n')),
            ]),
          ),
        ]),
        ts.factory.createCallExpression(
          ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier('String'), 'fromCodePoint'),
          undefined,
          [ts.factory.createCallExpression(ts.factory.createIdentifier('Number'), undefined, [operand(0)])],
        ),
        ts.factory.createStringLiteral('\u0000'),
      );
    // Lean orders Char by code point; JavaScript `<` on strings orders UTF-16 code units, and the
    // two disagree above the BMP, so the comparison reads the code points.
    case 'char-less-code-point':
      return compare(firstCodePoint(operand(0)), ts.SyntaxKind.LessThanToken, firstCodePoint(operand(1)));
  }
}

/** The parameters and result one generated helper declares, over the operands its row names. */
interface HelperSignature {
  readonly typeParameters: readonly ts.TypeParameterDeclaration[] | undefined;
  readonly parameters: readonly { readonly name: string; readonly type: ts.TypeNode }[];
  readonly result: ts.TypeNode;
}

function helperSignature(role: LeanRuntimeHelperRole, context: EmitContext): HelperSignature {
  const bigintType = ts.factory.createKeywordTypeNode(ts.SyntaxKind.BigIntKeyword);
  const stringType = ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword);
  const pair = (type: ts.TypeNode): HelperSignature['parameters'] => [
    { name: 'left', type },
    { name: 'right', type },
  ];
  switch (role) {
    case 'list-head-option': {
      const element = ts.factory.createTypeReferenceNode('A');
      return {
        typeParameters: [ts.factory.createTypeParameterDeclaration(undefined, 'A')],
        parameters: [{ name: context.locals.value, type: readonlyArrayType(element) }],
        result: optionTypeNode(context, element),
      };
    }
    case 'nat-truncated-subtraction':
    case 'int-truncated-division':
    case 'int-truncated-modulo':
      return { typeParameters: undefined, parameters: pair(bigintType), result: bigintType };
    case 'int-to-nat-clamp':
      return {
        typeParameters: undefined,
        parameters: [{ name: 'operand', type: bigintType }],
        result: bigintType,
      };
    case 'char-of-nat':
      return {
        typeParameters: undefined,
        parameters: [{ name: 'operand', type: bigintType }],
        result: stringType,
      };
    case 'char-less-code-point':
      return {
        typeParameters: undefined,
        parameters: pair(stringType),
        result: ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
      };
  }
}

/** One generated helper: the signature its role fixes, returning the body its registry row fixes. */
function emitRuntimeHelper(role: LeanRuntimeHelperRole, context: EmitContext): ts.Statement {
  const signature = helperSignature(role, context);
  return ts.factory.createFunctionDeclaration(
    undefined,
    undefined,
    requiredHelper(context, role),
    signature.typeParameters,
    signature.parameters.map((parameter) =>
      ts.factory.createParameterDeclaration(undefined, undefined, parameter.name, undefined, parameter.type),
    ),
    signature.result,
    block(
      ts.factory.createReturnStatement(
        helperBodyForm(
          role,
          signature.parameters.map((parameter) => ts.factory.createIdentifier(parameter.name)),
        ),
      ),
    ),
  );
}

/**
 * Every generated helper's body, canonically printed over the operand names its registry row
 * declares. The Lean row's `emittedForm` for a `helper:` symbol states the body, so the gate joins
 * this print against it exactly as it joins an inline form, and the two halves of the registry are
 * covered rather than only the inline half.
 */
export function helperOperationForms(): ReadonlyMap<LeanOpcode, string> {
  const file = ts.createSourceFile('runtime-form.ts', '', ts.ScriptTarget.Latest, false, ts.ScriptKind.TS);
  const printer = ts.createPrinter({ newLine: ts.NewLineKind.LineFeed });
  const forms = new Map<LeanOpcode, string>();
  for (const row of Object.values(LEAN_RUNTIME_OPCODES)) {
    const role = runtimeHelperRole(row.runtimeSymbol);
    if (role === undefined) continue;
    const form = helperBodyForm(
      role,
      row.operands.map((operand) => ts.factory.createIdentifier(operand)),
    );
    forms.set(row.opcode, printer.printNode(ts.EmitHint.Unspecified, form, file));
  }
  return forms;
}

function requiredHelper(context: EmitContext, role: LeanRuntimeHelperRole): string {
  const helper = context.prelude.helpers.get(role);
  if (helper === undefined) throw new TypeError(`missing generated helper for ${role}`);
  return helper;
}

/** Resolves an operation's helper through its tagged runtime symbol, never through an opcode switch. */
function requiredOpcodeHelper(context: EmitContext, opcode: LeanOpcode): string {
  const role = runtimeHelperRole(LEAN_RUNTIME_OPCODES[opcode].runtimeSymbol);
  if (role === undefined) throw new TypeError(`${opcode} does not name a generated runtime helper`);
  return requiredHelper(context, role);
}

function readonlyArrayType(element: ts.TypeNode): ts.TypeNode {
  return ts.factory.createTypeOperatorNode(ts.SyntaxKind.ReadonlyKeyword, ts.factory.createArrayTypeNode(element));
}

function optionTypeNode(context: EmitContext, element: ts.TypeNode): ts.TypeNode {
  return ts.factory.createTypeReferenceNode(usePrelude(context, context.prelude.optionType), [element]);
}

function isEmptyList(value: ts.Expression): ts.Expression {
  return ts.factory.createBinaryExpression(
    ts.factory.createPropertyAccessExpression(value, 'length'),
    ts.SyntaxKind.EqualsEqualsEqualsToken,
    ts.factory.createNumericLiteral(0),
  );
}

function taggedLiteral(
  tag: string,
  payload?: { readonly field: string; readonly value: ts.Expression },
): ts.Expression {
  return ts.factory.createObjectLiteralExpression(
    [
      ts.factory.createPropertyAssignment(propertyName('kind'), ts.factory.createStringLiteral(tag)),
      ...(payload === undefined
        ? []
        : [ts.factory.createPropertyAssignment(propertyName(payload.field), payload.value)]),
    ],
    false,
  );
}

function noneLiteral(): ts.Expression {
  return taggedLiteral('none');
}

function someLiteral(value: ts.Expression): ts.Expression {
  return taggedLiteral('some', { field: 'value', value });
}

/** A comparison parameter, as `(left: T, right: T) => boolean`. */
function comparatorParameter(name: string, payload: ts.TypeNode): ts.ParameterDeclaration {
  return ts.factory.createParameterDeclaration(
    undefined,
    undefined,
    name,
    undefined,
    ts.factory.createFunctionTypeNode(
      undefined,
      [
        ts.factory.createParameterDeclaration(undefined, undefined, 'left', undefined, payload),
        ts.factory.createParameterDeclaration(undefined, undefined, 'right', undefined, payload),
      ],
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
    ),
  );
}

function comparedParameter(name: string, type: ts.TypeNode): ts.ParameterDeclaration {
  return ts.factory.createParameterDeclaration(undefined, undefined, name, undefined, type);
}

/**
 * Compares two `Option` values. The payload is read inside this declaration, where each side is a
 * parameter the type system narrows, so a nested comparison can never read a payload whose tag has
 * not been decided.
 */
function emitEqualOptionHelper(context: EmitContext): ts.Statement {
  const payload = ts.factory.createTypeReferenceNode('A');
  const option = optionTypeNode(context, payload);
  const left = ts.factory.createIdentifier('left');
  const right = ts.factory.createIdentifier('right');
  return ts.factory.createFunctionDeclaration(
    undefined,
    undefined,
    context.prelude.equalOption,
    [ts.factory.createTypeParameterDeclaration(undefined, 'A')],
    [comparedParameter('left', option), comparedParameter('right', option), comparatorParameter('same', payload)],
    ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
    block(
      ts.factory.createIfStatement(
        tagEquals(left, 'none'),
        block(ts.factory.createReturnStatement(tagEquals(right, 'none'))),
      ),
      ts.factory.createReturnStatement(
        ts.factory.createBinaryExpression(
          tagEquals(right, 'some'),
          ts.SyntaxKind.AmpersandAmpersandToken,
          ts.factory.createCallExpression(ts.factory.createIdentifier('same'), undefined, [
            ts.factory.createPropertyAccessExpression(left, 'value'),
            ts.factory.createPropertyAccessExpression(right, 'value'),
          ]),
        ),
      ),
    ),
  );
}

/** Compares two `Except` values, reading each payload behind its own decided tag. */
function emitEqualExceptHelper(context: EmitContext): ts.Statement {
  const error = ts.factory.createTypeReferenceNode('E');
  const value = ts.factory.createTypeReferenceNode('A');
  const except = ts.factory.createTypeReferenceNode(usePrelude(context, context.prelude.exceptType), [error, value]);
  const left = ts.factory.createIdentifier('left');
  const right = ts.factory.createIdentifier('right');
  const compare = (name: string, field: string): ts.Expression =>
    ts.factory.createBinaryExpression(
      tagEquals(right, field === 'error' ? 'error' : 'ok'),
      ts.SyntaxKind.AmpersandAmpersandToken,
      ts.factory.createCallExpression(ts.factory.createIdentifier(name), undefined, [
        ts.factory.createPropertyAccessExpression(left, field),
        ts.factory.createPropertyAccessExpression(right, field),
      ]),
    );
  return ts.factory.createFunctionDeclaration(
    undefined,
    undefined,
    context.prelude.equalExcept,
    [
      ts.factory.createTypeParameterDeclaration(undefined, 'E'),
      ts.factory.createTypeParameterDeclaration(undefined, 'A'),
    ],
    [
      comparedParameter('left', except),
      comparedParameter('right', except),
      comparatorParameter('sameError', error),
      comparatorParameter('sameValue', value),
    ],
    ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
    block(
      ts.factory.createIfStatement(
        tagEquals(left, 'error'),
        block(ts.factory.createReturnStatement(compare('sameError', 'error'))),
      ),
      ts.factory.createReturnStatement(compare('sameValue', 'value')),
    ),
  );
}

/** Compares two lists elementwise. The paired element arrives as a parameter of `same`. */
function emitEqualListHelper(context: EmitContext): ts.Statement {
  const payload = ts.factory.createTypeReferenceNode('A');
  const list = readonlyArrayType(payload);
  const left = ts.factory.createIdentifier('left');
  const right = ts.factory.createIdentifier('right');
  return ts.factory.createFunctionDeclaration(
    undefined,
    undefined,
    context.prelude.equalList,
    [ts.factory.createTypeParameterDeclaration(undefined, 'A')],
    [comparedParameter('left', list), comparedParameter('right', list), comparatorParameter('same', payload)],
    ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
    block(
      ts.factory.createIfStatement(
        ts.factory.createBinaryExpression(
          ts.factory.createPropertyAccessExpression(left, 'length'),
          ts.SyntaxKind.ExclamationEqualsEqualsToken,
          ts.factory.createPropertyAccessExpression(right, 'length'),
        ),
        block(ts.factory.createReturnStatement(ts.factory.createFalse())),
      ),
      ts.factory.createReturnStatement(
        ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(left, 'every'), undefined, [
          ts.factory.createArrowFunction(
            undefined,
            undefined,
            [
              ts.factory.createParameterDeclaration(undefined, undefined, context.locals.element),
              ts.factory.createParameterDeclaration(undefined, undefined, context.locals.index),
            ],
            undefined,
            undefined,
            ts.factory.createCallExpression(ts.factory.createIdentifier('same'), undefined, [
              ts.factory.createIdentifier(context.locals.element),
              ts.factory.createElementAccessExpression(right, ts.factory.createIdentifier(context.locals.index)),
            ]),
          ),
        ]),
      ),
    ),
  );
}

function tagEquals(target: ts.Expression, tag: string): ts.Expression {
  return ts.factory.createBinaryExpression(
    ts.factory.createPropertyAccessExpression(target, 'kind'),
    ts.SyntaxKind.EqualsEqualsEqualsToken,
    ts.factory.createStringLiteral(tag),
  );
}

/** Reads an array at the boundary, decoding each element with the caller's own element decoder. */
function emitListValidator(context: EmitContext): ts.Statement {
  const { locals, prelude } = context;
  const value = ts.factory.createIdentifier(locals.value);
  const element = ts.factory.createTypeReferenceNode('A');
  return ts.factory.createFunctionDeclaration(
    context.boundary.validators.has(prelude.requireList) ? [modifier(ts.SyntaxKind.ExportKeyword)] : undefined,
    undefined,
    prelude.requireList,
    [ts.factory.createTypeParameterDeclaration(undefined, 'A')],
    [
      dataParameter(locals.value, context),
      stringParameter(locals.name),
      decoderParameter(locals.element, element, context),
    ],
    readonlyArrayType(element),
    block(
      guard(
        ts.factory.createPrefixUnaryExpression(ts.SyntaxKind.ExclamationToken, isArrayCall(value)),
        namedMessage(context, 'must be an array'),
      ),
      ts.factory.createVariableStatement(
        undefined,
        ts.factory.createVariableDeclarationList(
          [
            ts.factory.createVariableDeclaration(
              locals.entry,
              undefined,
              ts.factory.createArrayTypeNode(element),
              ts.factory.createArrayLiteralExpression([], false),
            ),
          ],
          ts.NodeFlags.Const,
        ),
      ),
      // Every index is read, and a hole is refused: `map` skips holes, so a sparse array would
      // decode to a shorter list than the one it claims to be.
      ts.factory.createForStatement(
        ts.factory.createVariableDeclarationList(
          [
            ts.factory.createVariableDeclaration(
              locals.index,
              undefined,
              undefined,
              ts.factory.createNumericLiteral(0),
            ),
          ],
          ts.NodeFlags.Let,
        ),
        ts.factory.createBinaryExpression(
          ts.factory.createIdentifier(locals.index),
          ts.SyntaxKind.LessThanToken,
          ts.factory.createPropertyAccessExpression(value, 'length'),
        ),
        ts.factory.createBinaryExpression(
          ts.factory.createIdentifier(locals.index),
          ts.SyntaxKind.PlusEqualsToken,
          ts.factory.createNumericLiteral(1),
        ),
        block(
          guard(
            ts.factory.createPrefixUnaryExpression(
              ts.SyntaxKind.ExclamationToken,
              ts.factory.createCallExpression(
                ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier('Object'), 'hasOwn'),
                undefined,
                [value, ts.factory.createIdentifier(locals.index)],
              ),
            ),
            indexedMessage(context, 'is missing'),
          ),
          ts.factory.createExpressionStatement(
            ts.factory.createCallExpression(
              ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier(locals.entry), 'push'),
              undefined,
              [
                ts.factory.createCallExpression(ts.factory.createIdentifier(locals.element), undefined, [
                  ts.factory.createElementAccessExpression(value, ts.factory.createIdentifier(locals.index)),
                  indexedName(context),
                ]),
              ],
            ),
          ),
        ),
      ),
      ts.factory.createReturnStatement(ts.factory.createIdentifier(locals.entry)),
    ),
  );
}

/** `${name}[${index}] <suffix>`, so a refused element names the position that carried it. */
function indexedMessage(context: EmitContext, suffix: string): ts.Expression {
  return ts.factory.createTemplateExpression(ts.factory.createTemplateHead(''), [
    ts.factory.createTemplateSpan(
      ts.factory.createIdentifier(context.locals.name),
      ts.factory.createTemplateMiddle('['),
    ),
    ts.factory.createTemplateSpan(
      ts.factory.createIdentifier(context.locals.index),
      ts.factory.createTemplateTail(`] ${suffix}`),
    ),
  ]);
}

/** `${name}[${index}]`, so an element's diagnostic names the position that rejected the input. */
function indexedName(context: EmitContext): ts.Expression {
  return ts.factory.createTemplateExpression(ts.factory.createTemplateHead(''), [
    ts.factory.createTemplateSpan(
      ts.factory.createIdentifier(context.locals.name),
      ts.factory.createTemplateMiddle('['),
    ),
    ts.factory.createTemplateSpan(
      ts.factory.createIdentifier(context.locals.index),
      ts.factory.createTemplateTail(']'),
    ),
  ]);
}

function decoderParameter(name: string, result: ts.TypeNode, context: EmitContext): ts.ParameterDeclaration {
  return ts.factory.createParameterDeclaration(
    undefined,
    undefined,
    name,
    undefined,
    ts.factory.createFunctionTypeNode(
      undefined,
      [dataParameter(context.locals.value, context), stringParameter(context.locals.name)],
      result,
    ),
  );
}

/**
 * Reads a tagged union at the boundary: one constructor decides, and its payload is decoded. How a
 * payload is read is the caller's, because `Option` and `Except` are read by a decoder their own
 * caller supplies while `JsonValue` reads its two recursive arms through the boundary decoder for
 * the type each arm carries.
 */
function emitTaggedValidator(
  name: string,
  typeParameters: readonly string[],
  result: ts.TypeNode,
  cases: readonly {
    readonly tag: string;
    readonly field?: string;
    readonly decode?: (payload: ts.Expression, label: ts.Expression) => ts.Expression;
  }[],
  decoders: readonly ts.ParameterDeclaration[],
  context: EmitContext,
): ts.Statement {
  const { locals } = context;
  const value = ts.factory.createIdentifier(locals.value);
  const clauses = cases.map((entry) => {
    const payload = entry.field;
    const decode = entry.decode;
    if (payload === undefined || decode === undefined) {
      return ts.factory.createCaseClause(ts.factory.createStringLiteral(entry.tag), [
        ts.factory.createBlock(
          [
            ts.factory.createExpressionStatement(
              callPrelude(context, context.prelude.requireDataFields, [
                value,
                ts.factory.createIdentifier(locals.name),
                ts.factory.createArrayLiteralExpression([ts.factory.createStringLiteral('kind')]),
              ]),
            ),
            ts.factory.createReturnStatement(taggedLiteral(entry.tag)),
          ],
          true,
        ),
      ]);
    }
    return ts.factory.createCaseClause(ts.factory.createStringLiteral(entry.tag), [
      ts.factory.createBlock(
        [
          constantStatement(
            locals.data,
            callPrelude(context, context.prelude.requireDataFields, [
              value,
              ts.factory.createIdentifier(locals.name),
              ts.factory.createArrayLiteralExpression([
                ts.factory.createStringLiteral('kind'),
                ts.factory.createStringLiteral(payload),
              ]),
            ]),
          ),
          ts.factory.createReturnStatement(
            taggedLiteral(entry.tag, {
              field: payload,
              value: decode(
                elementAccess(ts.factory.createIdentifier(locals.data), payload),
                ts.factory.createIdentifier(locals.name),
              ),
            }),
          ),
        ],
        true,
      ),
    ]);
  });
  return ts.factory.createFunctionDeclaration(
    context.boundary.validators.has(name) ? [modifier(ts.SyntaxKind.ExportKeyword)] : undefined,
    undefined,
    name,
    typeParameters.map((parameter) => ts.factory.createTypeParameterDeclaration(undefined, parameter)),
    [dataParameter(locals.value, context), stringParameter(locals.name), ...decoders],
    result,
    block(
      guard(
        ts.factory.createPrefixUnaryExpression(
          ts.SyntaxKind.ExclamationToken,
          callPrelude(context, context.prelude.isDataObject, [value]),
        ),
        namedMessage(context, 'data must be an object'),
      ),
      ts.factory.createSwitchStatement(
        elementAccess(value, 'kind'),
        ts.factory.createCaseBlock([
          ...clauses,
          ts.factory.createDefaultClause([throwNamed(context, 'data must name a constructor')]),
        ]),
      ),
    ),
  );
}

/** The call one supplied decoder parameter makes on a payload, as `decoder(payload, name)`. */
function suppliedDecoder(
  decoder: string,
): (payload: ts.Expression, label: ts.Expression) => ts.Expression {
  return (payload, label) =>
    ts.factory.createCallExpression(ts.factory.createIdentifier(decoder), undefined, [payload, label]);
}

function emitOptionValidator(context: EmitContext): ts.Statement {
  return emitTaggedValidator(
    context.prelude.requireOption,
    ['A'],
    optionTypeNode(context, ts.factory.createTypeReferenceNode('A')),
    [{ tag: 'none' }, { tag: 'some', field: 'value', decode: suppliedDecoder(context.locals.element) }],
    [decoderParameter(context.locals.element, ts.factory.createTypeReferenceNode('A'), context)],
    context,
  );
}

function emitExceptValidator(context: EmitContext): ts.Statement {
  return emitTaggedValidator(
    context.prelude.requireExcept,
    ['E', 'A'],
    ts.factory.createTypeReferenceNode(usePrelude(context, context.prelude.exceptType), [
      ts.factory.createTypeReferenceNode('E'),
      ts.factory.createTypeReferenceNode('A'),
    ]),
    [
      { tag: 'error', field: 'error', decode: suppliedDecoder(context.locals.field) },
      { tag: 'ok', field: 'value', decode: suppliedDecoder(context.locals.element) },
    ],
    [
      decoderParameter(context.locals.field, ts.factory.createTypeReferenceNode('E'), context),
      decoderParameter(context.locals.element, ts.factory.createTypeReferenceNode('A'), context),
    ],
    context,
  );
}

/** Reads an `Int` at the boundary: any bigint, where a `Nat` also has to be nonnegative. */
function emitIntValidator(context: EmitContext): ts.Statement {
  const { locals, prelude } = context;
  const value = ts.factory.createIdentifier(locals.value);
  return ts.factory.createFunctionDeclaration(
    context.boundary.validators.has(prelude.requireInt) ? [modifier(ts.SyntaxKind.ExportKeyword)] : undefined,
    undefined,
    prelude.requireInt,
    undefined,
    [dataParameter(locals.value, context), stringParameter(locals.name)],
    ts.factory.createKeywordTypeNode(ts.SyntaxKind.BigIntKeyword),
    block(
      ts.factory.createIfStatement(typeOfIs(value, 'bigint'), block(ts.factory.createReturnStatement(value))),
      throwNamed(context, 'must be an integer'),
    ),
  );
}

/**
 * Reads a `Char` at the boundary. A Char is one Unicode scalar value, and its image is the
 * one-code-point string the opcodes read, so a string of two code points and a lone surrogate are
 * both refused here rather than reaching `char.toNat`.
 */
function emitCharValidator(context: EmitContext): ts.Statement {
  const { locals, prelude } = context;
  const value = ts.factory.createIdentifier(locals.value);
  return ts.factory.createFunctionDeclaration(
    context.boundary.validators.has(prelude.requireChar) ? [modifier(ts.SyntaxKind.ExportKeyword)] : undefined,
    undefined,
    prelude.requireChar,
    undefined,
    [dataParameter(locals.value, context), stringParameter(locals.name)],
    ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword),
    block(
      guard(
        ts.factory.createPrefixUnaryExpression(ts.SyntaxKind.ExclamationToken, typeOfIs(value, 'string')),
        namedMessage(context, 'must be a character'),
      ),
      guard(
        ts.factory.createBinaryExpression(
          ts.factory.createPropertyAccessExpression(spreadArray(value), 'length'),
          ts.SyntaxKind.ExclamationEqualsEqualsToken,
          ts.factory.createNumericLiteral(1),
        ),
        namedMessage(context, 'must be exactly one code point'),
      ),
      guard(
        codeUnitInRange(charCodeAt(value, ts.factory.createNumericLiteral(0)), 0xd800, 0xdfff),
        namedMessage(context, 'must be a Unicode scalar value'),
      ),
      ts.factory.createReturnStatement(value),
    ),
  );
}

/** Reads a pair at the boundary: an object with exactly `fst` and `snd`, each decoded in order. */
function emitPairValidator(context: EmitContext): ts.Statement {
  const { locals, prelude } = context;
  const first = ts.factory.createTypeReferenceNode('A');
  const second = ts.factory.createTypeReferenceNode('B');
  const data = ts.factory.createIdentifier(locals.data);
  return ts.factory.createFunctionDeclaration(
    context.boundary.validators.has(prelude.requirePair) ? [modifier(ts.SyntaxKind.ExportKeyword)] : undefined,
    undefined,
    prelude.requirePair,
    [
      ts.factory.createTypeParameterDeclaration(undefined, 'A'),
      ts.factory.createTypeParameterDeclaration(undefined, 'B'),
    ],
    [
      dataParameter(locals.value, context),
      stringParameter(locals.name),
      decoderParameter(locals.field, first, context),
      decoderParameter(locals.element, second, context),
    ],
    ts.factory.createTypeLiteralNode([readonlyProperty('fst', first), readonlyProperty('snd', second)]),
    block(
      constantStatement(
        locals.data,
        callPrelude(context, prelude.requireDataFields, [
          ts.factory.createIdentifier(locals.value),
          ts.factory.createIdentifier(locals.name),
          ts.factory.createArrayLiteralExpression([
            ts.factory.createStringLiteral('fst'),
            ts.factory.createStringLiteral('snd'),
          ]),
        ]),
      ),
      ts.factory.createReturnStatement(
        ts.factory.createObjectLiteralExpression(
          [
            ts.factory.createPropertyAssignment(
              propertyName('fst'),
              ts.factory.createCallExpression(ts.factory.createIdentifier(locals.field), undefined, [
                elementAccess(data, 'fst'),
                ts.factory.createIdentifier(locals.name),
              ]),
            ),
            ts.factory.createPropertyAssignment(
              propertyName('snd'),
              ts.factory.createCallExpression(ts.factory.createIdentifier(locals.element), undefined, [
                elementAccess(data, 'snd'),
                ts.factory.createIdentifier(locals.name),
              ]),
            ),
          ],
          true,
        ),
      ),
    ),
  );
}

/**
 * Reads a `JsonValue` at the boundary. Its data image is the tagged union itself, so the reader is
 * the same tag-decided validator every other union gets, and the two recursive arms hand it back
 * to itself rather than to a second parser.
 */
function emitJsonValidator(context: EmitContext): ts.Statement {
  const { prelude } = context;
  const json: LeanType = { kind: 'json' };
  const elements: LeanType = { kind: 'list', element: json };
  const entries: LeanType = {
    kind: 'list',
    element: { kind: 'pair', first: { kind: 'string' }, second: json },
  };
  const through = (type: LeanType): ((payload: ts.Expression, label: ts.Expression) => ts.Expression) =>
    (payload, label) => decodeExpression(payload, type, label, context);
  return emitTaggedValidator(
    prelude.requireJson,
    [],
    ts.factory.createTypeReferenceNode(usePrelude(context, prelude.jsonType)),
    [
      { tag: 'null' },
      { tag: 'bool', field: 'value', decode: through({ kind: 'boolean' }) },
      { tag: 'int', field: 'value', decode: through({ kind: 'int' }) },
      { tag: 'string', field: 'value', decode: through({ kind: 'string' }) },
      { tag: 'array', field: 'value', decode: through(elements) },
      { tag: 'object', field: 'value', decode: through(entries) },
    ],
    [],
    context,
  );
}

/**
 * A structural type's decoder, and — where the type is part of the package's decode boundary — the
 * `fromData` a caller reaches it through. The companion names the type where a field decode names
 * the field it read, so an external caller and an inner field get the same validation with the
 * diagnostic each of them can act on.
 */
function emitBoundaryDecoder(leanName: string, emitted: string, context: EmitContext): readonly ts.Statement[] {
  const plan = requiredTypePlan(context, leanName);
  const scoped = withTypeParameters(context, plan.typeParameters);
  const decoder = emitStructuralDecoder(leanName, emitted, scoped);
  if (!context.boundary.types.has(leanName)) return [decoder];
  return [decoder, emitBoundaryCompanion(plan, emitted, scoped)];
}

/**
 * `T.fromData` beside `type T`: a caller decodes the same way whether the type lowered to a value
 * object or to a union, so which lowering the Lean source implies never reaches a call site. The
 * alias lives in type space and the companion in value space, so one name carries both.
 */
function emitBoundaryCompanion(plan: TypePlan, decoder: string, context: EmitContext): ts.Statement {
  return constantStatement(
    plan.typeName,
    freeze(
      ts.factory.createObjectLiteralExpression(
        [
          ts.factory.createMethodDeclaration(
            undefined,
            undefined,
            'fromData',
            undefined,
            undefined,
            [dataParameter(context.locals.value, context)],
            ts.factory.createTypeReferenceNode(plan.typeName),
            block(
              ts.factory.createReturnStatement(
                callPrelude(context, decoder, [
                  ts.factory.createIdentifier(context.locals.value),
                  ts.factory.createStringLiteral(plan.typeName),
                ]),
              ),
            ),
          ),
        ],
        true,
      ),
    ),
    [modifier(ts.SyntaxKind.ExportKeyword)],
  );
}

function emitStructuralDecoder(leanName: string, emitted: string, context: EmitContext): ts.Statement {
  const plan = requiredTypePlan(context, leanName);
  const value = ts.factory.createIdentifier(context.locals.value);
  const statements: readonly ts.Statement[] =
    plan.declaration.kind === 'record'
      ? emitDataDecoder(plan.declaration.fields, plan.typeName, undefined, context, (values) =>
          ts.factory.createReturnStatement(
            objectLiteral(plan.declaration.kind === 'record' ? plan.declaration.fields : [], values),
          ),
        )
      : plan.declaration.constructors.every((constructor) => constructor.fields.length === 0)
        ? [
            ts.factory.createIfStatement(
              disjunction(
                plan.declaration.constructors.map((constructor) =>
                  ts.factory.createBinaryExpression(
                    value,
                    ts.SyntaxKind.EqualsEqualsEqualsToken,
                    ts.factory.createStringLiteral(constructor.name),
                  ),
                ),
              ),
              block(ts.factory.createReturnStatement(value)),
            ),
            throwNamed(context, `must name a ${plan.typeName}`),
          ]
        : [
            guard(
              ts.factory.createPrefixUnaryExpression(
                ts.SyntaxKind.ExclamationToken,
                callPrelude(context, context.prelude.isDataObject, [value]),
              ),
              namedMessage(context, 'data must be an object'),
            ),
            ts.factory.createSwitchStatement(
              elementAccess(value, 'kind'),
              ts.factory.createCaseBlock([
                ...plan.declaration.constructors.map((constructor) =>
                  ts.factory.createCaseClause(ts.factory.createStringLiteral(constructor.name), [
                    ts.factory.createBlock(
                      emitDataDecoder(
                        constructor.fields,
                        `${plan.typeName}.${constructor.name}`,
                        constructor.name,
                        context,
                        (values) =>
                          ts.factory.createReturnStatement(
                            ts.factory.createObjectLiteralExpression(
                              [
                                ts.factory.createPropertyAssignment(
                                  propertyName('kind'),
                                  ts.factory.createStringLiteral(constructor.name),
                                ),
                                ...constructor.fields.map((field, index) =>
                                  ts.factory.createPropertyAssignment(
                                    propertyName(field.name),
                                    requiredValue(values, index, field.name),
                                  ),
                                ),
                              ],
                              true,
                            ),
                          ),
                      ),
                      true,
                    ),
                  ]),
                ),
                ts.factory.createDefaultClause([throwNamed(context, `must name a ${plan.typeName} constructor`)]),
              ]),
            ),
          ];
  const body = block(...statements);
  // A record's decoder labels every field read with its own owner, so it never reads the label it
  // was handed, while a union's decoder does. Both shapes declare the same signature so a caller
  // reaches either the same way, and the unread one is marked here rather than dropped, which is
  // what keeps `noUnusedParameters` clean without making the two decoders different to call.
  return ts.factory.createFunctionDeclaration(
    undefined,
    undefined,
    emitted,
    undefined,
    markUnreadParameters(
      [dataParameter(context.locals.value, context), stringParameter(context.locals.name)],
      body,
      newAllocator(context),
    ),
    ts.factory.createTypeReferenceNode(plan.typeName),
    body,
  );
}

function methodParameters(
  method: MethodPlan,
  allocator: IdentifierAllocator,
  context: EmitContext,
): readonly ts.ParameterDeclaration[] {
  return method.parameters.map((parameter) =>
    ts.factory.createParameterDeclaration(
      undefined,
      undefined,
      allocator.allocate(parameter.name),
      undefined,
      emitType(parameter.type, context),
    ),
  );
}

/**
 * de Bruijn scope for a method body. The receiver is `this` at whichever declared position it
 * holds, and the remaining parameters keep their declared order, so a receiver that is not the
 * first argument still lowers without reordering anything.
 */
function methodScope(method: MethodPlan, parameters: readonly ts.ParameterDeclaration[]): readonly Binding[] {
  const emitted = parameters.map((parameter): Binding => {
    if (!ts.isIdentifier(parameter.name)) throw new TypeError('emitted parameter is not an identifier');
    return { kind: 'identifier', name: parameter.name.text };
  });
  const declared: Binding[] = [];
  let next = 0;
  for (let index = 0; index < method.declaration.parameters.length; index += 1) {
    if (index === method.receiver.parameter) {
      declared.push({ kind: 'this' });
      continue;
    }
    const binding = emitted[next];
    if (binding === undefined) throw new TypeError(`method ${method.declaration.name} lost a parameter`);
    next += 1;
    declared.push(binding);
  }
  return declared.reverse();
}

/** A dispatched arm reads its constructor's fields off the receiver, innermost binder last. */
function armBindings(constructor: LeanEnumConstructor): readonly Binding[] {
  return [...constructor.fields]
    .reverse()
    .map((field): Binding => ({ kind: 'expression', value: receiverField(field.name) }));
}

function emitType(type: LeanType, context: EmitContext): ts.TypeNode {
  switch (type.kind) {
    case 'boolean':
      return ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword);
    case 'nat':
      return ts.factory.createKeywordTypeNode(ts.SyntaxKind.BigIntKeyword);
    case 'string':
      return ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword);
    case 'int':
      return ts.factory.createKeywordTypeNode(ts.SyntaxKind.BigIntKeyword);
    // A Char is the one-code-point string its opcodes read and write, which is why `char.equals`
    // is strict equality and `string.singleton` is the identity.
    case 'char':
      return ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword);
    case 'bytes':
      return ts.factory.createTypeReferenceNode('Uint8Array');
    case 'json':
      return ts.factory.createTypeReferenceNode(usePrelude(context, context.prelude.jsonType));
    case 'parameter': {
      const name = context.typeParameters[type.index];
      if (name === undefined) {
        throw new TypeError(`type parameter ${type.index} is not in scope for this declaration`);
      }
      return ts.factory.createTypeReferenceNode(name);
    }
    case 'named': {
      const plan = requiredTypePlan(context, type.name);
      return ts.factory.createTypeReferenceNode(
        plan.typeName,
        type.arguments.length === 0 ? undefined : type.arguments.map((argument) => emitType(argument, context)),
      );
    }
    case 'option':
      return optionTypeNode(context, emitType(type.value, context));
    case 'except':
      return ts.factory.createTypeReferenceNode(usePrelude(context, context.prelude.exceptType), [
        emitType(type.error, context),
        emitType(type.value, context),
      ]);
    case 'list':
      return readonlyArrayType(emitType(type.element, context));
    // An Array shares the dense readonly-array image a List has, which is what makes `array.toList`
    // and `array.ofList` identities rather than conversions.
    case 'array':
      return readonlyArrayType(emitType(type.element, context));
    case 'pair':
      return ts.factory.createTypeLiteralNode([
        readonlyProperty('fst', emitType(type.first, context)),
        readonlyProperty('snd', emitType(type.second, context)),
      ]);
    case 'hashMap':
    case 'treeMap':
      return ts.factory.createTypeReferenceNode('ReadonlyMap', [
        emitType(type.key, context),
        emitType(type.value, context),
      ]);
    case 'function':
      return ts.factory.createFunctionTypeNode(
        undefined,
        type.parameters.map((parameter, index) =>
          ts.factory.createParameterDeclaration(
            undefined,
            undefined,
            `argument${index}`,
            undefined,
            emitType(parameter, context),
          ),
        ),
        emitType(type.result, context),
      );
  }
}

function emitFunctionBody(
  expression: LeanExpression,
  scope: readonly Binding[],
  allocator: IdentifierAllocator,
  context: EmitContext,
): ts.Block {
  const liveness = analyzeExpressionLiveness(expression, context.declarations);
  return ts.factory.createBlock(emitReturn(expression, scope, allocator, liveness, context), true);
}

/**
 * The statements a generated function returns through. A `let` becomes a `const`, an `if` becomes
 * an `if` whose branch returns, and a `match` becomes one test per alternative with the payload
 * bound as a `const` inside the branch that decided it. Every branch returns, so TypeScript narrows
 * the scrutinee as the tests fall through and no branch reads a payload it has not yet decided is
 * present.
 */
function emitReturn(
  expression: LeanExpression,
  scope: readonly Binding[],
  allocator: IdentifierAllocator,
  liveness: LeanExpressionLiveness,
  context: EmitContext,
): readonly ts.Statement[] {
  switch (expression.kind) {
    case 'let': {
      // Every admitted expression is pure and total, so a binding the body never reads has no
      // observable effect and no emitted form. Naming it would leave an unread `const` behind,
      // which the generated package's own type check refuses.
      if (!liveness.uses(expression.body, 0)) {
        return emitReturn(expression.body, [{ kind: 'unread' }, ...scope], allocator, liveness, context);
      }
      const emittedName = allocator.allocate(expression.name);
      return [
        constantStatement(
          emittedName,
          emitExpression(expression.value, scope, allocator, context),
          undefined,
          declaredExpressionType(expression.value, context),
        ),
        ...emitReturn(
          expression.body,
          [{ kind: 'identifier', name: emittedName }, ...scope],
          allocator,
          liveness,
          context,
        ),
      ];
    }
    case 'if':
      return [
        ts.factory.createIfStatement(
          emitExpression(expression.condition, scope, allocator, context),
          ts.factory.createBlock(emitReturn(expression.consequent, scope, allocator, liveness, context), true),
        ),
        ...emitReturn(expression.alternate, scope, allocator, liveness, context),
      ];
    case 'match':
      return emitMatchStatements(expression, scope, allocator, liveness, context);
    default:
      return [ts.factory.createReturnStatement(emitExpression(expression, scope, allocator, context))];
  }
}

/**
 * One alternative's payload bindings, as `const` statements over the value that decided it. A field
 * the alternative never reads is not named: the binding keeps its de Bruijn position so every index
 * above it still counts, and no unread `const` reaches the generated file.
 */
function bindConstructorFields(
  scrutinee: ts.Expression,
  fields: readonly LeanField[],
  type: LeanType,
  body: LeanExpression,
  allocator: IdentifierAllocator,
  liveness: LeanExpressionLiveness,
): { readonly statements: readonly ts.Statement[]; readonly bindings: readonly Binding[] } {
  const statements: ts.Statement[] = [];
  const bindings: Binding[] = [];
  fields.forEach((field, position) => {
    // The alternative binds its fields innermost last, so field `position` sits at this index.
    if (!liveness.uses(body, fields.length - 1 - position)) {
      bindings.push({ kind: 'unread' });
      return;
    }
    const emittedName = allocator.allocate(field.name);
    statements.push(constantStatement(emittedName, constructorFieldAccess(scrutinee, field.name, type)));
    bindings.push({ kind: 'identifier', name: emittedName });
  });
  return { statements, bindings: [...bindings].reverse() };
}

/**
 * How one alternative reads a constructor field. A user type carries its fields as properties; a
 * `List` carries them as the first element and the rest of the array, which are the `list.first`
 * and `list.rest` runtime opcodes.
 */
function constructorFieldAccess(scrutinee: ts.Expression, field: string, type: LeanType): ts.Expression {
  if (type.kind !== 'list') return fieldAccess(scrutinee, field);
  if (field === 'head') {
    return ts.factory.createElementAccessExpression(scrutinee, ts.factory.createNumericLiteral(0));
  }
  return ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(scrutinee, 'slice'), undefined, [
    ts.factory.createNumericLiteral(1),
  ]);
}

/** The test that decides one alternative of a match, given the scrutinee's representation. */
function alternativeTest(
  scrutinee: ts.Expression,
  type: LeanType,
  constructor: string,
  context: EmitContext,
): ts.Expression {
  if (type.kind === 'list') {
    return constructor === 'nil'
      ? isEmptyList(scrutinee)
      : ts.factory.createBinaryExpression(
          ts.factory.createPropertyAccessExpression(scrutinee, 'length'),
          ts.SyntaxKind.GreaterThanToken,
          ts.factory.createNumericLiteral(0),
        );
  }
  if (type.kind === 'named') {
    const plan = requiredTypePlan(context, type.name);
    if (plan.declaration.kind === 'enum' && plan.declaration.constructors.every((entry) => entry.fields.length === 0)) {
      return ts.factory.createBinaryExpression(
        scrutinee,
        ts.SyntaxKind.EqualsEqualsEqualsToken,
        ts.factory.createStringLiteral(constructor),
      );
    }
  }
  return ts.factory.createBinaryExpression(
    ts.factory.createPropertyAccessExpression(scrutinee, 'kind'),
    ts.SyntaxKind.EqualsEqualsEqualsToken,
    ts.factory.createStringLiteral(constructor),
  );
}

/**
 * A `match` in return position. The scrutinee is bound once, every alternative but the last is a
 * test that returns, and the last alternative falls through to the narrowed remainder.
 *
 * `Compile.returnBody` in the semantics lowers exactly this shape to `Target.Body.branch`, and
 * `Preservation.branchBody` proves it refines the source match: the subject is evaluated once, the
 * alternatives are decided in declaration order with the last unconditional, and the alternative
 * that decided names its payload with `const`s in declaration order, which is the scope the source
 * arm binds. The two differences left are recorded rather than assumed: the emitter drops a `const`
 * for a field no alternative reads, which is unobservable because the initializer is an own
 * data-property read, and it names a non-identifier scrutinee with a `const` where the model
 * evaluates the subject expression once — one statement, no de Bruijn slot, same value.
 */
function emitMatchStatements(
  expression: Extract<LeanExpression, { readonly kind: 'match' }>,
  scope: readonly Binding[],
  allocator: IdentifierAllocator,
  liveness: LeanExpressionLiveness,
  context: EmitContext,
): readonly ts.Statement[] {
  const constructors = constructorsOf(expression.type, context.declarations);
  dispatchOnValueObject(expression, context);
  const statements: ts.Statement[] = [];
  let scrutinee = emitExpression(expression.scrutinee, scope, allocator, context);
  if (!ts.isIdentifier(scrutinee)) {
    const bound = allocator.allocate(context.locals.value);
    statements.push(constantStatement(bound, scrutinee));
    scrutinee = ts.factory.createIdentifier(bound);
  }
  expression.cases.forEach((entry, index) => {
    const constructor = constructors[index];
    if (constructor === undefined) throw new TypeError(`${renderType(expression.type)} has no alternative ${index}`);
    const bound = bindConstructorFields(
      scrutinee,
      constructor.fields,
      expression.type,
      entry.value,
      allocator,
      liveness,
    );
    const armStatements = [
      ...bound.statements,
      ...emitReturn(entry.value, [...bound.bindings, ...scope], allocator, liveness, context),
    ];
    if (index === expression.cases.length - 1) {
      statements.push(...armStatements);
      return;
    }
    statements.push(
      ts.factory.createIfStatement(
        alternativeTest(scrutinee, expression.type, constructor.name, context),
        ts.factory.createBlock(armStatements, true),
      ),
    );
  });
  return statements;
}

/** A value object decides its constructors through dispatch, never through a tag comparison. */
function dispatchOnValueObject(
  expression: Extract<LeanExpression, { readonly kind: 'match' }>,
  context: EmitContext,
): void {
  if (expression.type.kind !== 'named') return;
  const plan = context.types.get(expression.type.name);
  if (plan?.nominal !== true) return;
  throw new TypeError(
    `a match on the value object ${plan.typeName} outside dot-notation dispatch position is outside this fragment version`,
  );
}

function emitExpression(
  expression: LeanExpression,
  scope: readonly Binding[],
  allocator: IdentifierAllocator,
  context: EmitContext,
): ts.Expression {
  switch (expression.kind) {
    case 'variable': {
      const binding = scope[expression.index];
      if (binding === undefined) throw new TypeError(`unbound de Bruijn index ${expression.index}`);
      return emitBinding(binding);
    }
    case 'boolean':
      return expression.value ? ts.factory.createTrue() : ts.factory.createFalse();
    case 'nat':
      return ts.factory.createBigIntLiteral(`${expression.value}n`);
    case 'string':
      return ts.factory.createStringLiteral(expression.value);
    case 'let':
      throw new TypeError('a let outside return position must be lifted before emission');
    case 'field':
      return fieldAccess(emitExpression(expression.target, scope, allocator, context), expression.field);
    case 'if':
      return ts.factory.createConditionalExpression(
        emitExpression(expression.condition, scope, allocator, context),
        undefined,
        emitExpression(expression.consequent, scope, allocator, context),
        undefined,
        emitExpression(expression.alternate, scope, allocator, context),
      );
    case 'operation':
      return emitOperation(expression, scope, allocator, context);
    case 'lambda': {
      const parameters = expression.parameters.map((parameter) => ({
        ...parameter,
        emittedName: allocator.allocate(parameter.name),
      }));
      const inner: readonly Binding[] = parameters
        .map((parameter): Binding => ({ kind: 'identifier', name: parameter.emittedName }))
        .reverse()
        .concat(scope);
      return ts.factory.createArrowFunction(
        undefined,
        undefined,
        parameters.map((parameter) =>
          ts.factory.createParameterDeclaration(
            undefined,
            undefined,
            parameter.emittedName,
            undefined,
            emitType(parameter.type, context),
          ),
        ),
        undefined,
        undefined,
        emitExpression(expression.body, inner, allocator, context),
      );
    }
    case 'apply':
      return ts.factory.createCallExpression(
        emitExpression(expression.target, scope, allocator, context),
        undefined,
        expression.arguments.map((argument) => emitExpression(argument, scope, allocator, context)),
      );
    case 'variant':
      return emitVariant(expression, scope, allocator, context);
    case 'match':
      return emitMatchExpression(expression, scope, allocator, context);
    case 'record': {
      const literal = ts.factory.createObjectLiteralExpression(
        expression.fields.map((field) =>
          ts.factory.createPropertyAssignment(
            propertyName(field.name),
            emitExpression(field.value, scope, allocator, context),
          ),
        ),
        true,
      );
      // A pair is a mapped structure rather than a declared one, so it has no type plan and no
      // nominal form: its image is the object literal carrying `fst` then `snd` in that order,
      // which is the representation `Effect.pairValue_represents` proves.
      if (expression.type.kind === 'pair') return literal;
      if (expression.type.kind !== 'named') throw new TypeError('a record construction lost its type');
      const plan = requiredTypePlan(context, expression.type.name);
      return plan.nominal
        ? ts.factory.createNewExpression(ts.factory.createIdentifier(plan.typeName), undefined, [literal])
        : literal;
    }
    case 'call': {
      const method = context.methods.get(expression.function);
      if (method === undefined) {
        return ts.factory.createCallExpression(
          ts.factory.createIdentifier(requiredDeclarationName(context.declarationNames, expression.function)),
          expression.typeArguments.length === 0
            ? undefined
            : expression.typeArguments.map((argument) => emitType(argument, context)),
          expression.arguments.map((argument) => emitExpression(argument, scope, allocator, context)),
        );
      }
      const receiver = expression.arguments[method.receiver.parameter];
      if (receiver === undefined) throw new TypeError(`method call ${expression.function} has no receiver`);
      const rest = expression.arguments.filter((_, index) => index !== method.receiver.parameter);
      const own = expression.typeArguments.slice(requiredTypePlan(context, method.receiver.type).typeParameters.length);
      return ts.factory.createCallExpression(
        ts.factory.createPropertyAccessExpression(emitExpression(receiver, scope, allocator, context), method.name),
        own.length === 0 ? undefined : own.map((argument) => emitType(argument, context)),
        rest.map((argument) => emitExpression(argument, scope, allocator, context)),
      );
    }
  }
}

/** One runtime opcode, in the single TypeScript form its registry row fixes. */
function emitOperation(
  expression: Extract<LeanExpression, { readonly kind: 'operation' }>,
  scope: readonly Binding[],
  allocator: IdentifierAllocator,
  context: EmitContext,
): ts.Expression {
  return operationForm(
    expression.opcode,
    expression.arguments.map((argument) => emitExpression(argument, scope, allocator, context)),
    {
      allocator,
      binders: { accumulator: context.locals.value, element: context.locals.element },
      helper: (opcode, operands) => callPrelude(context, requiredOpcodeHelper(context, opcode), operands),
    },
  );
}

/**
 * What building one operation's form needs besides its operands: the allocator that names a binder
 * the form introduces, the hints those binders take, and the call an opcode whose exact semantics
 * need a guard reaches its generated helper through.
 */
interface OperationEnvironment {
  readonly allocator: IdentifierAllocator;
  readonly binders: { readonly accumulator: string; readonly element: string };
  readonly helper: (opcode: LeanOpcode, operands: readonly ts.Expression[]) => ts.Expression;
}

/**
 * The one emitted shape every runtime opcode has, over operands already emitted. This is the only
 * place that shape exists: `inlineOperationForms` prints it over the operand names the registry row
 * names, and the certificate binding digests that print, so an emitted form that drifted from the
 * Lean row is refused before a package exists instead of being certified against a copy of the row.
 */
function operationForm(
  opcode: LeanOpcode,
  operands: readonly ts.Expression[],
  environment: OperationEnvironment,
): ts.Expression {
  const binary = (index: number): [ts.Expression, ts.Expression] => {
    const left = operands[0];
    const right = operands[index];
    if (left === undefined || right === undefined) {
      throw new TypeError(`${opcode} is missing an operand`);
    }
    return [left, right];
  };
  const unary = (): ts.Expression => {
    const only = operands[0];
    if (only === undefined) throw new TypeError(`${opcode} is missing its operand`);
    return only;
  };
  const infix = (token: ts.BinaryOperator): ts.Expression => {
    const [left, right] = binary(1);
    return ts.factory.createBinaryExpression(left, token, right);
  };
  const callback = (index: number, arity: number): ts.Expression => {
    const target = operands[index];
    if (target === undefined) throw new TypeError(`${opcode} is missing its callback`);
    if (ts.isArrowFunction(target) && target.parameters.length === arity) return target;
    // The wrapper's own binders come from the enclosing allocator, because the callback it applies
    // may be a binding the same body holds under one of these names.
    const names = (
      arity === 1 ? [environment.binders.element] : [environment.binders.accumulator, environment.binders.element]
    ).map((hint) => environment.allocator.allocate(hint));
    return ts.factory.createArrowFunction(
      undefined,
      undefined,
      names.map((parameter) => ts.factory.createParameterDeclaration(undefined, undefined, parameter)),
      undefined,
      undefined,
      ts.factory.createCallExpression(
        target,
        undefined,
        names.map((parameter) => ts.factory.createIdentifier(parameter)),
      ),
    );
  };
  const method = (receiver: number, name: string, argumentsList: readonly ts.Expression[]): ts.Expression => {
    const target = operands[receiver];
    if (target === undefined) throw new TypeError(`${opcode} is missing its receiver`);
    return ts.factory.createCallExpression(
      ts.factory.createPropertyAccessExpression(target, name),
      undefined,
      argumentsList,
    );
  };
  switch (opcode) {
    case 'bool.and':
      return infix(ts.SyntaxKind.AmpersandAmpersandToken);
    case 'bool.or':
      return infix(ts.SyntaxKind.BarBarToken);
    case 'bool.not':
      return ts.factory.createPrefixUnaryExpression(ts.SyntaxKind.ExclamationToken, unary());
    case 'bool.equals':
    case 'nat.equals':
    case 'string.equals':
    case 'int.equals':
    case 'char.equals':
      return infix(ts.SyntaxKind.EqualsEqualsEqualsToken);
    case 'int.add':
      return infix(ts.SyntaxKind.PlusToken);
    case 'int.subtract':
      return infix(ts.SyntaxKind.MinusToken);
    case 'int.multiply':
      return infix(ts.SyntaxKind.AsteriskToken);
    case 'int.negate':
      return ts.factory.createPrefixUnaryExpression(ts.SyntaxKind.MinusToken, unary());
    case 'int.less':
      return infix(ts.SyntaxKind.LessThanToken);
    case 'int.lessOrEqual':
      return infix(ts.SyntaxKind.LessThanEqualsToken);
    // Four identities on a shared image: a Nat and a nonnegative Int are one bigint, a Char is the
    // one-code-point string its singleton denotes, and a List and an Array are one dense array.
    case 'int.ofNat':
    case 'string.singleton':
    case 'array.toList':
    case 'array.ofList':
      return unary();
    case 'int.tdiv':
    case 'int.tmod':
      return environment.helper(opcode, binary(1));
    case 'int.toNat':
    case 'char.ofNat':
      return environment.helper(opcode, [unary()]);
    case 'char.less':
      return environment.helper(opcode, binary(1));
    case 'char.toNat':
      return ts.factory.createCallExpression(ts.factory.createIdentifier('BigInt'), undefined, [firstCodePoint(unary())]);
    // Lean counts code points, so the length is taken over the spread sequence rather than over
    // the UTF-16 code units `value.length` reports.
    case 'string.length':
      return ts.factory.createCallExpression(ts.factory.createIdentifier('BigInt'), undefined, [
        ts.factory.createPropertyAccessExpression(spreadArray(unary()), 'length'),
      ]);
    case 'string.isEmpty':
    case 'array.isEmpty':
      return isEmptyList(unary());
    case 'string.push':
      return infix(ts.SyntaxKind.PlusToken);
    case 'string.toList':
      return spreadArray(unary());
    case 'string.ofList':
      return method(0, 'join', [ts.factory.createStringLiteral('')]);
    case 'array.size':
      return ts.factory.createCallExpression(ts.factory.createIdentifier('BigInt'), undefined, [
        ts.factory.createPropertyAccessExpression(unary(), 'length'),
      ]);
    case 'array.push': {
      const [value, element] = binary(1);
      return ts.factory.createArrayLiteralExpression([ts.factory.createSpreadElement(value), element], false);
    }
    case 'array.append': {
      const [left, right] = binary(1);
      return ts.factory.createArrayLiteralExpression(
        [ts.factory.createSpreadElement(left), ts.factory.createSpreadElement(right)],
        false,
      );
    }
    case 'array.reverse':
      return ts.factory.createCallExpression(
        ts.factory.createPropertyAccessExpression(spreadArray(unary()), 'reverse'),
        undefined,
        [],
      );
    case 'nat.add':
    case 'string.append':
      return infix(ts.SyntaxKind.PlusToken);
    case 'nat.multiply':
      return infix(ts.SyntaxKind.AsteriskToken);
    case 'nat.less':
      return infix(ts.SyntaxKind.LessThanToken);
    case 'nat.lessOrEqual':
      return infix(ts.SyntaxKind.LessThanEqualsToken);
    case 'nat.successor':
      return ts.factory.createBinaryExpression(unary(), ts.SyntaxKind.PlusToken, ts.factory.createBigIntLiteral('1n'));
    case 'nat.subtract':
      return environment.helper(opcode, binary(1));
    case 'list.head':
      return environment.helper(opcode, [unary()]);
    case 'list.length':
      return ts.factory.createCallExpression(ts.factory.createIdentifier('BigInt'), undefined, [
        ts.factory.createPropertyAccessExpression(unary(), 'length'),
      ]);
    case 'list.isEmpty':
      return isEmptyList(unary());
    case 'list.append': {
      const [left, right] = binary(1);
      return ts.factory.createArrayLiteralExpression(
        [ts.factory.createSpreadElement(left), ts.factory.createSpreadElement(right)],
        false,
      );
    }
    case 'list.reverse':
      return ts.factory.createCallExpression(
        ts.factory.createPropertyAccessExpression(
          ts.factory.createArrayLiteralExpression([ts.factory.createSpreadElement(unary())], false),
          'reverse',
        ),
        undefined,
        [],
      );
    case 'list.map':
      return method(1, 'map', [callback(0, 1)]);
    case 'list.filter':
      return method(1, 'filter', [callback(0, 1)]);
    case 'list.any':
      return method(0, 'some', [callback(1, 1)]);
    case 'list.all':
      return method(0, 'every', [callback(1, 1)]);
    case 'list.foldLeft': {
      const initial = operands[1];
      if (initial === undefined) throw new TypeError('list.foldLeft is missing its initial value');
      return method(2, 'reduce', [callback(0, 2), initial]);
    }
    case 'list.foldRight': {
      const initial = operands[1];
      if (initial === undefined) throw new TypeError('list.foldRight is missing its initial value');
      return method(2, 'reduceRight', [reversedCallback(operands, environment), initial]);
    }
    case 'list.first':
      return ts.factory.createElementAccessExpression(unary(), ts.factory.createNumericLiteral(0));
    case 'list.rest':
      return method(0, 'slice', [ts.factory.createNumericLiteral(1)]);
  }
}

/**
 * The binder names a canonically printed callback wrapper introduces. A use site takes them from the
 * enclosing codec locals, which the allocator renames when the body already holds one; the canonical
 * print takes the two names the Lean rows are written in, so the print is compared against the form
 * the registry states rather than against a renaming of it.
 */
const CANONICAL_OPERATION_BINDERS = { accumulator: 'accumulator', element: 'element' } as const;

/**
 * Every inline opcode's emitted form, canonically printed over the operand names its registry row
 * declares. An inline opcode has no declaration to resolve, so this print is what its certificate
 * digests: the Lean row's `emittedForm` is joined against the structure `operationForm` builds
 * rather than against a second copy of itself. A helper opcode is absent here because its form
 * reaches the target as a generated declaration, whose printed bytes its certificate binds instead.
 */
export function inlineOperationForms(): ReadonlyMap<LeanOpcode, string> {
  const file = ts.createSourceFile('runtime-form.ts', '', ts.ScriptTarget.Latest, false, ts.ScriptKind.TS);
  const printer = ts.createPrinter({ newLine: ts.NewLineKind.LineFeed });
  const forms = new Map<LeanOpcode, string>();
  for (const row of Object.values(LEAN_RUNTIME_OPCODES)) {
    if (runtimeHelperRole(row.runtimeSymbol) !== undefined) continue;
    const form = operationForm(
      row.opcode,
      row.operands.map((operand) => ts.factory.createIdentifier(operand)),
      {
        allocator: new IdentifierAllocator(row.operands),
        binders: CANONICAL_OPERATION_BINDERS,
        helper: () => {
          throw new TypeError(`${row.opcode} is emitted inline and reaches no helper`);
        },
      },
    );
    forms.set(row.opcode, printer.printNode(ts.EmitHint.Unspecified, form, file));
  }
  return forms;
}

/**
 * `reduceRight` hands the accumulator first and Lean's `foldr` hands the element first, so the
 * generated callback swaps them rather than relying on the two orders happening to agree.
 */
function reversedCallback(operands: readonly ts.Expression[], environment: OperationEnvironment): ts.Expression {
  const step = operands[0];
  if (step === undefined) throw new TypeError('list.foldRight is missing its step function');
  if (ts.isArrowFunction(step) && step.parameters.length === 2) {
    const [element, accumulator] = step.parameters;
    if (element === undefined || accumulator === undefined) {
      throw new TypeError('list.foldRight step function lost a binder');
    }
    return ts.factory.updateArrowFunction(
      step,
      step.modifiers,
      step.typeParameters,
      [accumulator, element],
      step.type,
      step.equalsGreaterThanToken,
      step.body,
    );
  }
  const accumulator = environment.allocator.allocate(environment.binders.accumulator);
  const element = environment.allocator.allocate(environment.binders.element);
  return ts.factory.createArrowFunction(
    undefined,
    undefined,
    [accumulator, element].map((parameter) => ts.factory.createParameterDeclaration(undefined, undefined, parameter)),
    undefined,
    undefined,
    ts.factory.createCallExpression(step, undefined, [
      ts.factory.createIdentifier(element),
      ts.factory.createIdentifier(accumulator),
    ]),
  );
}

/** One constructor application, in the representation its type's plan fixes. */
function emitVariant(
  expression: Extract<LeanExpression, { readonly kind: 'variant' }>,
  scope: readonly Binding[],
  allocator: IdentifierAllocator,
  context: EmitContext,
): ts.Expression {
  const values = expression.arguments.map((argument) => emitExpression(argument, scope, allocator, context));
  const constructors = constructorsOf(expression.type, context.declarations);
  const constructor = constructors.find((candidate) => candidate.name === expression.name);
  if (constructor === undefined) {
    throw new TypeError(`unknown constructor ${renderType(expression.type)}.${expression.name}`);
  }
  if (expression.type.kind === 'list') {
    if (expression.name === 'nil') return ts.factory.createArrayLiteralExpression([], false);
    const [head, tail] = values;
    if (head === undefined || tail === undefined) throw new TypeError('list.cons is missing an argument');
    // A chain of conses over literals is one dense literal, not a literal spread into a literal.
    // The difference is observable to the type checker: an array literal inside a spread is typed
    // on its own, so `[Tag.a, Tag.b]` would widen its elements to `string` and stop being the
    // annotated element type, while one flat literal takes the element type from its context.
    if (ts.isArrayLiteralExpression(tail)) {
      return ts.factory.createArrayLiteralExpression([head, ...tail.elements], false);
    }
    return ts.factory.createArrayLiteralExpression([head, ts.factory.createSpreadElement(tail)], false);
  }
  // `pair` has one constructor and no tag: its image is the two own keys, in that order.
  if (expression.type.kind === 'pair') {
    const [first, second] = values;
    if (first === undefined || second === undefined) throw new TypeError('a pair is missing a component');
    return ts.factory.createObjectLiteralExpression(
      [
        ts.factory.createPropertyAssignment(propertyName('fst'), first),
        ts.factory.createPropertyAssignment(propertyName('snd'), second),
      ],
      false,
    );
  }
  if (expression.type.kind === 'option' || expression.type.kind === 'except' || expression.type.kind === 'json') {
    const field = constructor.fields[0];
    const [payload] = values;
    if (field === undefined || payload === undefined) return taggedLiteral(expression.name);
    return taggedLiteral(expression.name, { field: field.name, value: payload });
  }
  if (expression.type.kind !== 'named') {
    throw new TypeError(`${renderType(expression.type)} has no constructor representation`);
  }
  const plan = requiredTypePlan(context, expression.type.name);
  if (!plan.nominal) {
    if (
      constructor.fields.length === 0 &&
      plan.declaration.kind === 'enum' &&
      plan.declaration.constructors.every((candidate) => candidate.fields.length === 0)
    ) {
      return ts.factory.createStringLiteral(expression.name);
    }
    return ts.factory.createObjectLiteralExpression(
      [
        ts.factory.createPropertyAssignment(propertyName('kind'), ts.factory.createStringLiteral(expression.name)),
        ...constructor.fields.map((field, index) => {
          const value = values[index];
          if (value === undefined) throw new TypeError(`missing constructor field ${field.name}`);
          return ts.factory.createPropertyAssignment(propertyName(field.name), value);
        }),
      ],
      true,
    );
  }
  const member = ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier(plan.typeName), expression.name);
  if (constructor.fields.length === 0 && plan.ground) return member;
  return ts.factory.createCallExpression(
    member,
    plan.ground ? undefined : expression.type.arguments.map((argument) => emitType(argument, context)),
    values,
  );
}

/**
 * Whether a scrutinee can be read again without recomputing anything. A binding can; a field of a
 * re-readable value can; anything else computes, and the condition is transitive because a field of
 * a call would otherwise smuggle the call in behind one property read.
 *
 * This is the condition `Compile.readableScrutinee` decides, clause for clause, so a tag chain this
 * emitter builds is one the preservation theorem admits rather than a wider set of them. It is the
 * argument-position condition only: in return position `emitMatchStatements` names the scrutinee and
 * `Target.Body.branch` evaluates the subject exactly once, so nothing there needs to be re-readable.
 */
function isRereadable(expression: LeanExpression): boolean {
  if (expression.kind === 'variable') return true;
  return expression.kind === 'field' && isRereadable(expression.target);
}

/**
 * A `match` in argument position, where no `const` can be bound. The scrutinee is read once per
 * test, so only a binding or a chain of field reads over one is admitted: anything that computes
 * has to be named by a `let` first rather than be silently re-evaluated per alternative.
 */
function emitMatchExpression(
  expression: Extract<LeanExpression, { readonly kind: 'match' }>,
  scope: readonly Binding[],
  allocator: IdentifierAllocator,
  context: EmitContext,
): ts.Expression {
  dispatchOnValueObject(expression, context);
  if (!isRereadable(expression.scrutinee)) {
    throw new TypeError(
      `a match on a computed ${renderType(expression.type)} outside return position is outside this fragment version: bind the scrutinee with let first`,
    );
  }
  const scrutinee = emitExpression(expression.scrutinee, scope, allocator, context);
  const constructors = constructorsOf(expression.type, context.declarations);
  const arms = expression.cases.map((entry, index) => {
    const constructor = constructors[index];
    if (constructor === undefined) throw new TypeError(`${renderType(expression.type)} has no alternative ${index}`);
    const bindings = [...constructor.fields].reverse().map((field): Binding => ({
      kind: 'expression',
      value: constructorFieldAccess(scrutinee, field.name, expression.type),
    }));
    return {
      constructor: constructor.name,
      value: emitExpression(entry.value, [...bindings, ...scope], allocator, context),
    };
  });
  const fallback = arms.at(-1);
  if (fallback === undefined) throw new TypeError(`match on ${renderType(expression.type)} decides no alternative`);
  return arms
    .slice(0, -1)
    .reduceRight(
      (alternate, arm) =>
        ts.factory.createConditionalExpression(
          alternativeTest(scrutinee, expression.type, arm.constructor, context),
          undefined,
          arm.value,
          undefined,
          alternate,
        ),
      fallback.value,
    );
}

function emitBinding(binding: Binding): ts.Expression {
  switch (binding.kind) {
    case 'identifier':
      return ts.factory.createIdentifier(binding.name);
    case 'this':
      return ts.factory.createThis();
    case 'expression':
      return binding.value;
    case 'unread':
      throw new TypeError('an unread binding reached emission');
  }
}

/**
 * The emission order of one program's declarations: data types first, then functions in dependency
 * order. A mutual group Lean recorded is emitted as one adjacent block of `function` declarations,
 * which hoist, so a forward reference inside the group is legal wherever the block is placed.
 */
function orderedDeclarations(program: LeanSemanticProgram): readonly LeanDeclaration[] {
  const types = program.declarations
    .filter((declaration) => declaration.kind !== 'function' && declaration.kind !== 'foreign')
    .sort((left, right) => {
      const kindOrder = Number(left.kind === 'record') - Number(right.kind === 'record');
      return kindOrder || compareCodePoints(left.name, right.name);
    });
  const functions = new Map(
    program.declarations
      .filter((declaration): declaration is LeanFunction => declaration.kind === 'function')
      .map((declaration) => [declaration.name, declaration]),
  );
  const ordered: LeanFunction[] = [];
  const visiting = new Set<string>();
  const visited = new Set<string>();
  const visit = (name: string): void => {
    if (visited.has(name)) return;
    const declaration = functions.get(name);
    if (declaration === undefined) return;
    const recursion = declaration.recursion;
    const group = recursion?.kind === 'mutual' ? recursion.group : [name];
    if (group.some((member) => visited.has(member))) return;
    if (visiting.has(name)) {
      throw new TypeError(`mutual recursion outside a recorded group: ${name}`);
    }
    for (const member of group) visiting.add(member);
    for (const member of group) {
      for (const dependency of calledFunctions(functions.get(member)?.body)) {
        if (!group.includes(dependency)) visit(dependency);
      }
    }
    for (const member of group) {
      visiting.delete(member);
      visited.add(member);
      const peer = functions.get(member);
      if (peer !== undefined) ordered.push(peer);
    }
  };
  for (const root of program.roots) visit(root);
  for (const name of [...functions.keys()].sort(compareCodePoints)) visit(name);
  // A host boundary emits an import and, when it is a root, a re-export. Neither participates in
  // the definition-before-use ordering the functions need, so they are appended rather than
  // threaded through the dependency walk — but they are not dropped, or the boundary a program
  // declared would never be emitted at all.
  const foreign = program.declarations
    .filter((declaration) => declaration.kind === 'foreign')
    .sort((left, right) => compareCodePoints(left.name, right.name));
  return [...types, ...ordered, ...foreign];
}

/**
 * The program the emitted package contains: the declared graph pruned to what its roots reach.
 *
 * Data declarations are kept whatever reaches them, because each is exported — a caller outside the
 * package reaches it by name, so it is never dead — and its generated decoder is part of the decode
 * boundary rather than of any one call graph. What is pruned is the functions, which are private
 * unless they are roots, and so are exactly what a dead edge would leave behind.
 */
function pruneToEmissionClosure(program: LeanSemanticProgram, context: EmitContext): LeanSemanticProgram {
  const live = reachableFunctions(program, context);
  return {
    ...program,
    declarations: program.declarations.filter(
      (declaration) => declaration.kind !== 'function' || live.has(declaration.name),
    ),
  };
}

/**
 * The functions the emitted tree can reach from the package's roots.
 *
 * A generated module is pruned to that closure, because a declaration nothing printed reaches is
 * dead code the package's own type check rejects. A host boundary contributes no expression edges:
 * its reference body is never printed, since the substrate owns the implementation and the body
 * exists so the model can prove `HostSubstrate` against it. A helper only that body traverses is
 * therefore dead in the emitted tree while remaining declared for the model, which is the one place
 * the two graphs differ. A dot-notation method is printed inside its receiver rather than as a
 * statement of its own, so its body is walked even though it never becomes one.
 */
function reachableFunctions(program: LeanSemanticProgram, context: EmitContext): ReadonlySet<string> {
  const functions = new Map(
    program.declarations
      .filter((declaration): declaration is LeanFunction => declaration.kind === 'function')
      .map((declaration) => [declaration.name, declaration]),
  );
  const live = new Set<string>();
  const pending = [...program.roots];
  for (const plan of context.types.values()) {
    for (const method of plan.methods) pending.push(method.declaration.name);
  }
  while (pending.length > 0) {
    const name = pending.pop();
    if (name === undefined || live.has(name)) continue;
    live.add(name);
    const declaration = functions.get(name);
    if (declaration === undefined) continue;
    const recursion = declaration.recursion;
    // A mutual block is emitted whole: its members name each other, and a member reached only
    // through the group is still printed beside the one that reached it.
    if (recursion?.kind === 'mutual') for (const member of recursion.group) pending.push(member);
    for (const called of calledFunctions(declaration.body)) pending.push(called);
  }
  return live;
}
function calledFunctions(expression: LeanExpression | undefined): readonly string[] {
  const names = new Set<string>();
  const visit = (node: LeanExpression): void => {
    switch (node.kind) {
      case 'call':
        names.add(node.function);
        node.arguments.forEach(visit);
        return;
      case 'operation':
      case 'variant':
        node.arguments.forEach(visit);
        return;
      case 'let':
        visit(node.value);
        visit(node.body);
        return;
      case 'field':
        visit(node.target);
        return;
      case 'if':
        visit(node.condition);
        visit(node.consequent);
        visit(node.alternate);
        return;
      case 'record':
        node.fields.forEach((field) => visit(field.value));
        return;
      case 'match':
        visit(node.scrutinee);
        node.cases.forEach((entry) => visit(entry.value));
        return;
      case 'lambda':
        visit(node.body);
        return;
      case 'apply':
        visit(node.target);
        node.arguments.forEach(visit);
        return;
      case 'variable':
      case 'boolean':
      case 'nat':
      case 'string':
        return;
    }
  };
  if (expression !== undefined) visit(expression);
  return [...names];
}

/** The binder scope of one generated `equals`: its own parameter, plus everything reserved. */
function equalityAllocator(context: EmitContext): IdentifierAllocator {
  return new IdentifierAllocator([...context.reserved, ...context.typeParameters, context.locals.other]);
}

function newAllocator(context: EmitContext): IdentifierAllocator {
  return new IdentifierAllocator([...context.reserved, ...context.typeParameters]);
}

function requiredTypePlan(context: EmitContext, name: string): TypePlan {
  const plan = context.types.get(name);
  if (plan === undefined) throw new TypeError(`missing type plan for ${name}`);
  return plan;
}

/** Records that the package reached one prelude declaration, so only what is used is emitted. */
function usePrelude(context: EmitContext, name: string): string {
  context.used.add(name);
  return name;
}

function callPrelude(context: EmitContext, name: string, argumentsList: readonly ts.Expression[]): ts.CallExpression {
  return ts.factory.createCallExpression(
    ts.factory.createIdentifier(usePrelude(context, name)),
    undefined,
    argumentsList,
  );
}

function conjunction(operands: readonly ts.Expression[]): ts.Expression {
  const [first, ...rest] = operands;
  if (first === undefined) return ts.factory.createTrue();
  return rest.reduce(
    (left, right) => ts.factory.createBinaryExpression(left, ts.SyntaxKind.AmpersandAmpersandToken, right),
    first,
  );
}

function receiverField(field: string): ts.Expression {
  return fieldAccess(ts.factory.createThis(), field);
}

/**
 * `__proto__` is a data property here, never the prototype setter: element access on read and a
 * computed key on write create and read an own property.
 */
function fieldAccess(target: ts.Expression, field: string): ts.Expression {
  return field === '__proto__'
    ? elementAccess(target, field)
    : ts.factory.createPropertyAccessExpression(target, field);
}

function elementAccess(target: ts.Expression, key: string): ts.Expression {
  return ts.factory.createElementAccessExpression(target, ts.factory.createStringLiteral(key));
}

function propertyName(field: string): ts.PropertyName {
  return field === '__proto__'
    ? ts.factory.createComputedPropertyName(ts.factory.createStringLiteral(field))
    : ts.factory.createIdentifier(field);
}

function readonlyProperty(field: string, type: ts.TypeNode): ts.PropertySignature {
  return ts.factory.createPropertySignature(
    [ts.factory.createModifier(ts.SyntaxKind.ReadonlyKeyword)],
    field === '__proto__' ? ts.factory.createStringLiteral(field) : ts.factory.createIdentifier(field),
    undefined,
    type,
  );
}

/**
 * The emitted type of a value the IR states the type of. A constructed value, a record and a match
 * each carry their own Lean type, so a binding over one is annotated rather than inferred: a bare
 * array literal of tag strings would otherwise widen its elements to `string` and stop being the
 * union its own declaration spells. Every other value is emitted from something already annotated —
 * a parameter, a declared function's result, an opcode's form — so its inferred type is exact and
 * an annotation would restate it.
 */
function declaredExpressionType(expression: LeanExpression, context: EmitContext): ts.TypeNode | undefined {
  if (expression.kind !== 'variant' && expression.kind !== 'record' && expression.kind !== 'match') return undefined;
  return emitType(expression.type, context);
}

function constantStatement(
  name: string,
  initializer: ts.Expression,
  modifiers?: readonly ts.Modifier[],
  type?: ts.TypeNode,
): ts.Statement {
  return ts.factory.createVariableStatement(
    modifiers,
    ts.factory.createVariableDeclarationList(
      [ts.factory.createVariableDeclaration(name, undefined, type, initializer)],
      ts.NodeFlags.Const,
    ),
  );
}

function block(...statements: readonly ts.Statement[]): ts.Block {
  return ts.factory.createBlock(statements, true);
}

function freeze(value: ts.Expression): ts.Expression {
  return ts.factory.createCallExpression(
    ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier('Object'), 'freeze'),
    undefined,
    [value],
  );
}

function freezeThis(): ts.Statement {
  return ts.factory.createExpressionStatement(freeze(ts.factory.createThis()));
}

function guard(condition: ts.Expression, message: ts.Expression | string): ts.Statement {
  return ts.factory.createIfStatement(condition, block(throwStatement(message)));
}

function throwStatement(message: ts.Expression | string): ts.Statement {
  return ts.factory.createThrowStatement(
    ts.factory.createNewExpression(ts.factory.createIdentifier('TypeError'), undefined, [
      typeof message === 'string' ? ts.factory.createStringLiteral(message) : message,
    ]),
  );
}

/** `${name} <suffix>`, so a decoder reports which field of which record rejected its input. */
function namedMessage(context: EmitContext, suffix: string): ts.Expression {
  return ts.factory.createTemplateExpression(ts.factory.createTemplateHead(''), [
    ts.factory.createTemplateSpan(
      ts.factory.createIdentifier(context.locals.name),
      ts.factory.createTemplateTail(` ${suffix}`),
    ),
  ]);
}

function throwNamed(context: EmitContext, suffix: string): ts.Statement {
  return throwStatement(namedMessage(context, suffix));
}

function disjunction(operands: readonly ts.Expression[]): ts.Expression {
  const [first, ...rest] = operands;
  if (first === undefined) return ts.factory.createFalse();
  return rest.reduce((left, right) => ts.factory.createBinaryExpression(left, ts.SyntaxKind.BarBarToken, right), first);
}

function objectLiteral(fields: readonly LeanField[], values: readonly ts.Expression[]): ts.Expression {
  return ts.factory.createObjectLiteralExpression(
    fields.map((field, index) =>
      ts.factory.createPropertyAssignment(propertyName(field.name), requiredValue(values, index, field.name)),
    ),
    true,
  );
}

function requiredValue(values: readonly ts.Expression[], index: number, field: string): ts.Expression {
  const value = values[index];
  if (value === undefined) throw new TypeError(`missing emitted value for field ${field}`);
  return value;
}

/**
 * Every generated codec reads from one named boundary type instead of `unknown`: a decoder that
 * takes `unknown` forces its caller to prove nothing, and a consumer whose own lint forbids
 * unparsed parameters cannot adopt the artifact at all. The union admits every value a JSON
 * document can deliver — including the `undefined` an absent property yields — so narrowing stays
 * the decoder's job and never the caller's.
 */
function dataParameter(name: string, context: EmitContext): ts.ParameterDeclaration {
  return ts.factory.createParameterDeclaration(undefined, undefined, name, undefined, dataBoundaryType(context));
}

function dataBoundaryType(context: EmitContext): ts.TypeNode {
  context.used.add(context.prelude.dataBoundary);
  return ts.factory.createTypeReferenceNode(context.prelude.dataBoundary);
}

function emitDataBoundaryAlias(name: string): ts.Statement {
  return ts.factory.createTypeAliasDeclaration(
    [modifier(ts.SyntaxKind.ExportKeyword)],
    name,
    undefined,
    ts.factory.createUnionTypeNode([
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BigIntKeyword),
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.NumberKeyword),
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword),
      ts.factory.createLiteralTypeNode(ts.factory.createNull()),
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.UndefinedKeyword),
      ts.factory.createTypeOperatorNode(
        ts.SyntaxKind.ReadonlyKeyword,
        ts.factory.createArrayTypeNode(ts.factory.createTypeReferenceNode(name)),
      ),
      dataRecordType(name),
    ]),
  );
}

/**
 * The one shape a decoded data object has, shared by the boundary union and every validator. A
 * readonly index signature rather than `Readonly<Record<…>>`: the boundary union refers to itself
 * through this node, and a homomorphic mapped type cannot carry that reference.
 */
function dataRecordType(boundary: string): ts.TypeNode {
  return ts.factory.createTypeLiteralNode([
    ts.factory.createIndexSignature(
      [modifier(ts.SyntaxKind.ReadonlyKeyword)],
      [stringParameter('key')],
      ts.factory.createTypeReferenceNode(boundary),
    ),
  ]);
}

function stringParameter(name: string): ts.ParameterDeclaration {
  return ts.factory.createParameterDeclaration(
    undefined,
    undefined,
    name,
    undefined,
    ts.factory.createKeywordTypeNode(ts.SyntaxKind.StringKeyword),
  );
}

function staticMethod(
  name: string,
  result: ts.TypeNode,
  statements: readonly ts.Statement[],
  context: EmitContext,
): ts.ClassElement {
  return ts.factory.createMethodDeclaration(
    [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.StaticKeyword)],
    undefined,
    name,
    undefined,
    undefined,
    [dataParameter(context.locals.value, context)],
    result,
    block(...statements),
  );
}

function publicMethod(
  name: string,
  parameters: readonly ts.ParameterDeclaration[],
  result: ts.TypeNode,
  ...statements: readonly ts.Statement[]
): ts.ClassElement {
  return ts.factory.createMethodDeclaration(
    [modifier(ts.SyntaxKind.PublicKeyword)],
    undefined,
    name,
    undefined,
    undefined,
    parameters,
    result,
    block(...statements),
  );
}

function overrideMethod(
  name: string,
  parameters: readonly ts.ParameterDeclaration[],
  result: ts.TypeNode,
  ...statements: readonly ts.Statement[]
): ts.ClassElement {
  return ts.factory.createMethodDeclaration(
    [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.OverrideKeyword)],
    undefined,
    name,
    undefined,
    undefined,
    parameters,
    result,
    block(...statements),
  );
}

function abstractMethod(
  name: string,
  parameters: readonly ts.ParameterDeclaration[],
  result: ts.TypeNode,
): ts.ClassElement {
  return ts.factory.createMethodDeclaration(
    [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.AbstractKeyword)],
    undefined,
    name,
    undefined,
    undefined,
    parameters,
    result,
    undefined,
  );
}

function documented<Node extends ts.Node>(node: Node, doc: string | undefined): Node {
  if (doc === undefined) return node;
  const lines = doc.replace(/\s+$/u, '').split('\n');
  const text = `*\n${lines.map((line) => (line.length === 0 ? ' *' : ` * ${line}`)).join('\n')}\n `;
  return ts.addSyntheticLeadingComment(node, ts.SyntaxKind.MultiLineCommentTrivia, text, true);
}

function modifier(kind: ts.ModifierSyntaxKind): ts.Modifier {
  return ts.factory.createModifier(kind);
}

function literalType(value: string): ts.TypeNode {
  return ts.factory.createLiteralTypeNode(ts.factory.createStringLiteral(value));
}

function capitalize(value: string): string {
  return `${value.slice(0, 1).toUpperCase()}${value.slice(1)}`;
}

class IdentifierAllocator {
  readonly #used: Set<string>;

  public constructor(reserved: Iterable<string>) {
    this.#used = new Set(reserved);
  }

  public allocate(hint: string): string {
    const stem = safeIdentifierStem(hint);
    let candidate = stem;
    let suffix = 2;
    while (this.#used.has(candidate)) {
      candidate = `${stem}$${suffix}`;
      suffix += 1;
    }
    this.#used.add(candidate);
    return candidate;
  }

  public allocated(): readonly string[] {
    return [...this.#used];
  }
}

function safeIdentifierStem(hint: string): string {
  const sanitized = hint.replace(/[^$0-9A-Z_a-z]/gu, '_');
  const prefixed = /^[$A-Z_a-z]/u.test(sanitized) ? sanitized : `value_${sanitized}`;
  const candidate = prefixed.length === 0 ? 'value' : prefixed;
  const scanner = ts.createScanner(ts.ScriptTarget.Latest, false, ts.LanguageVariant.Standard, candidate);
  if (
    scanner.scan() !== ts.SyntaxKind.Identifier ||
    scanner.scan() !== ts.SyntaxKind.EndOfFileToken ||
    candidate === 'arguments' ||
    candidate === 'eval'
  ) {
    return `value_${candidate}`;
  }
  return candidate;
}

function requiredDeclarationName(names: ReadonlyMap<string, string>, name: string): string {
  const emitted = names.get(name);
  if (emitted === undefined) throw new TypeError(`missing emitted declaration name for ${name}`);
  return emitted;
}

function localName(name: string): string {
  const part = name.split('.').at(-1);
  if (part === undefined) throw new TypeError('empty Lean name');
  return part;
}
