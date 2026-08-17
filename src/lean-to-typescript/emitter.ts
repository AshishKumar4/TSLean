import ts from 'typescript';
import { createHash } from 'node:crypto';
import type {
  LeanToTypeScriptArtifact,
  LeanToTypeScriptEnvironmentAttestation,
  LeanToTypeScriptSemanticIdentity,
} from './artifact.js';
import type {
  LeanDeclaration,
  LeanEnumConstructor,
  LeanExpression,
  LeanField,
  LeanSemanticProgram,
  LeanType,
} from './ir.js';
import {
  canonicalManifest,
  LEAN_TO_TYPESCRIPT_MANIFEST_SCHEMA_VERSION,
  provenanceHeader,
  verifyLeanToTypeScriptArtifact,
} from './manifest.js';
import { attributeUnsupportedFragment } from './fragment.js';
import { compareCodePoints } from './ordering.js';

export interface LeanToTypeScriptProvenance {
  readonly semantic: Omit<LeanToTypeScriptSemanticIdentity, 'generatedBodySha256'>;
  readonly environment: LeanToTypeScriptEnvironmentAttestation;
}

export function emitTypeScript(
  program: LeanSemanticProgram,
  provenance: LeanToTypeScriptProvenance,
): LeanToTypeScriptArtifact {
  const context = planProgram(program);
  const statements = orderedDeclarations(program).flatMap((declaration) => {
    try {
      return emitDeclaration(declaration, context);
    } catch (error: unknown) {
      throw attributeUnsupportedFragment(error, declaration.name);
    }
  });
  const file = ts.factory.updateSourceFile(
    ts.createSourceFile('generated.ts', '', ts.ScriptTarget.Latest, false, ts.ScriptKind.TS),
    [...statements, ...emitPrelude(context)],
  );
  // One blank line between top-level declarations: the printer emits none, and a formatter
  // preserves blank lines but never introduces them.
  const printer = ts.createPrinter({ newLine: ts.NewLineKind.LineFeed });
  const body = `${file.statements
    .map((statement) => printer.printNode(ts.EmitHint.Unspecified, statement, file))
    .join('\n\n')}\n`;
  const manifest = canonicalManifest({
    schemaVersion: LEAN_TO_TYPESCRIPT_MANIFEST_SCHEMA_VERSION,
    semantic: { ...provenance.semantic, generatedBodySha256: sha256(body) },
    environment: provenance.environment,
  });
  const artifact = { code: `${provenanceHeader(manifest)}${body}`, manifest };
  verifyLeanToTypeScriptArtifact(artifact);
  return artifact;
}

function sha256(value: string): string {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}

type LeanFunction = Extract<LeanDeclaration, { readonly kind: 'function' }>;
type LeanEnum = Extract<LeanDeclaration, { readonly kind: 'enum' }>;
type LeanRecord = Extract<LeanDeclaration, { readonly kind: 'record' }>;
type LeanData = LeanEnum | LeanRecord;

interface MethodPlan {
  readonly declaration: LeanFunction;
  readonly name: string;
  readonly dispatches: boolean;
}

interface CasePlan {
  readonly constructor: LeanEnumConstructor;
  readonly className: string;
  readonly singleton: string;
}

/**
 * How one Lean data type is represented. A type whose namespace carries dot-notation functions
 * over it has behaviour, so it becomes a nominal class exactly as the handwritten value objects
 * are written; a type with no behaviour stays structural, because promoting it would add a
 * constructor and an identity the Lean source does not have. The distinction is read off the
 * source, so the same Lean always lowers to the same TypeScript.
 */
interface TypePlan {
  readonly declaration: LeanData;
  readonly typeName: string;
  readonly nominal: boolean;
  readonly cases: readonly CasePlan[];
  readonly methods: readonly MethodPlan[];
  readonly dataName: string;
  readonly initName: string;
}

interface PreludeNames {
  readonly dataBoundary: string;
  readonly isDataObject: string;
  readonly dataFields: string;
  readonly requireBoolean: string;
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
}

interface EmitContext {
  readonly roots: ReadonlySet<string>;
  readonly declarationNames: ReadonlyMap<string, string>;
  readonly types: ReadonlyMap<string, TypePlan>;
  readonly methods: ReadonlyMap<string, MethodPlan>;
  readonly reserved: readonly string[];
  readonly prelude: PreludeNames;
  readonly locals: CodecLocals;
  readonly used: Set<string>;
}

type Binding =
  | { readonly kind: 'identifier'; readonly name: string }
  | { readonly kind: 'receiver' }
  | { readonly kind: 'receiverField'; readonly field: string };

function planProgram(program: LeanSemanticProgram): EmitContext {
  const declarationNames = new Map(
    program.declarations.map((declaration) => [declaration.name, localName(declaration.name)]),
  );
  const allocator = new IdentifierAllocator([...declarationNames.values(), 'undefined', 'this']);
  const functions = program.declarations.filter(
    (declaration): declaration is LeanFunction => declaration.kind === 'function',
  );
  const data = program.declarations
    .filter((declaration): declaration is LeanData => declaration.kind !== 'function')
    .sort((left, right) => compareCodePoints(left.name, right.name));
  const types = new Map<string, TypePlan>();
  const methods = new Map<string, MethodPlan>();
  for (const declaration of data) {
    const typeName = requiredDeclarationName(declarationNames, declaration.name);
    const plan: MethodPlan[] = functions
      .filter((candidate) => isDotNotationMethod(candidate, declaration))
      .map((candidate) => ({
        declaration: candidate,
        name: localName(candidate.name),
        dispatches: dispatchesOnReceiver(candidate, declaration.name),
      }));
    const nominal = plan.length > 0;
    const cases =
      declaration.kind === 'enum' && nominal
        ? declaration.constructors.map((constructor): CasePlan => ({
            constructor,
            className: allocator.allocate(`${capitalize(constructor.name)}${typeName}`),
            singleton: allocator.allocate(`${constructor.name}${typeName}`),
          }))
        : [];
    types.set(declaration.name, {
      declaration,
      typeName,
      nominal,
      cases,
      methods: plan,
      dataName: nominal ? allocator.allocate(`${typeName}Data`) : typeName,
      initName: nominal ? allocator.allocate(`${typeName}Init`) : typeName,
    });
    for (const method of plan) methods.set(method.declaration.name, method);
  }
  const decoders = new Map<string, string>();
  for (const declaration of data) {
    if (types.get(declaration.name)?.nominal === true) continue;
    decoders.set(declaration.name, allocator.allocate(`require${capitalize(localName(declaration.name))}`));
  }
  // Captured before the codec names are allocated: a Lean binder shares no scope with a generated
  // validator, so only names a Lean body can actually refer to are reserved against it.
  const reserved = allocator.allocated();
  const prelude: PreludeNames = {
    dataBoundary: allocator.allocate('GeneratedData'),
    isDataObject: allocator.allocate('isDataObject'),
    dataFields: allocator.allocate('dataFields'),
    requireBoolean: allocator.allocate('requireBoolean'),
    decoders,
  };
  const locals: CodecLocals = {
    value: allocator.allocate('value'),
    name: allocator.allocate('name'),
    data: allocator.allocate('data'),
    fields: allocator.allocate('fields'),
    field: allocator.allocate('field'),
  };
  return {
    roots: new Set(program.roots),
    declarationNames,
    types,
    methods,
    reserved,
    prelude,
    locals,
    used: new Set(),
  };
}

/** Lean dot notation names the receiver, so `T.f (t : T) …` is a method on `T`. */
function isDotNotationMethod(declaration: LeanFunction, data: LeanData): boolean {
  if (!declaration.name.startsWith(`${data.name}.`)) return false;
  if (declaration.name.slice(data.name.length + 1).includes('.')) return false;
  const receiver = declaration.parameters[0];
  return receiver !== undefined && receiver.type.kind === 'named' && receiver.type.name === data.name;
}

function dispatchesOnReceiver(declaration: LeanFunction, enumName: string): boolean {
  const body = declaration.body;
  return (
    body.kind === 'match' &&
    body.type === enumName &&
    body.scrutinee.kind === 'variable' &&
    body.scrutinee.index === declaration.parameters.length - 1
  );
}

function emitDeclaration(declaration: LeanDeclaration, context: EmitContext): readonly ts.Statement[] {
  if (declaration.kind === 'function') {
    if (context.methods.has(declaration.name)) return [];
    return [emitFunction(declaration, context)];
  }
  const plan = requiredTypePlan(context, declaration.name);
  if (declaration.kind === 'enum') {
    return plan.nominal
      ? emitNominalEnum(plan, declaration, context)
      : [emitStructuralEnum(plan, declaration, context)];
  }
  return plan.nominal
    ? emitNominalRecord(plan, declaration, context)
    : [emitStructuralRecord(plan, declaration, context)];
}

function emitFunction(declaration: LeanFunction, context: EmitContext): ts.Statement {
  const allocator = newAllocator(context);
  const parameters = declaration.parameters.map((parameter) => ({
    ...parameter,
    emittedName: allocator.allocate(parameter.name),
  }));
  const scope: readonly Binding[] = parameters
    .map((parameter): Binding => ({ kind: 'identifier', name: parameter.emittedName }))
    .reverse();
  return documented(
    ts.factory.createFunctionDeclaration(
      context.roots.has(declaration.name) ? [modifier(ts.SyntaxKind.ExportKeyword)] : undefined,
      undefined,
      localName(declaration.name),
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
      emitType(declaration.result, context),
      emitFunctionBody(declaration.body, scope, allocator, context),
    ),
    declaration.doc,
  );
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
      undefined,
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

function emitStructuralRecord(plan: TypePlan, declaration: LeanRecord, context: EmitContext): ts.Statement {
  return documented(
    ts.factory.createInterfaceDeclaration(
      [modifier(ts.SyntaxKind.ExportKeyword)],
      plan.typeName,
      undefined,
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
 * constructor: a nullary constructor has exactly one inhabitant, so it is a singleton behind a
 * static getter; a payload constructor is a static factory over its fields.
 */
function emitNominalEnum(plan: TypePlan, declaration: LeanEnum, context: EmitContext): readonly ts.Statement[] {
  const base = ts.factory.createTypeReferenceNode(plan.typeName);
  const nullary = plan.cases.every((entry) => entry.constructor.fields.length === 0);
  const members: ts.ClassElement[] = plan.cases.map((entry) =>
    documented(
      entry.constructor.fields.length === 0
        ? ts.factory.createGetAccessorDeclaration(
            [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.StaticKeyword)],
            entry.constructor.name,
            [],
            base,
            block(ts.factory.createReturnStatement(ts.factory.createIdentifier(entry.singleton))),
          )
        : ts.factory.createMethodDeclaration(
            [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.StaticKeyword)],
            undefined,
            entry.constructor.name,
            undefined,
            undefined,
            entry.constructor.fields.map((field) =>
              ts.factory.createParameterDeclaration(
                undefined,
                undefined,
                field.name,
                undefined,
                emitType(field.type, context),
              ),
            ),
            base,
            block(
              ts.factory.createReturnStatement(
                ts.factory.createNewExpression(
                  ts.factory.createIdentifier(entry.className),
                  undefined,
                  entry.constructor.fields.map((field) => ts.factory.createIdentifier(field.name)),
                ),
              ),
            ),
          ),
      entry.constructor.doc,
    ),
  );
  if (nullary) members.push(emitTagConstructor(plan, base));
  members.push(emitEnumFromData(plan, declaration, base, context));
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
  for (const method of plan.methods) members.push(emitBaseMethod(method, context));
  members.push(...emitEnumRepresentation(plan, base, nullary));
  const declarationStatement = documented(
    ts.factory.createClassDeclaration(
      [modifier(ts.SyntaxKind.ExportKeyword), modifier(ts.SyntaxKind.AbstractKeyword)],
      plan.typeName,
      undefined,
      undefined,
      members,
    ),
    declaration.doc,
  );
  return [
    emitEnumDataType(plan, declaration, nullary, context),
    declarationStatement,
    ...plan.cases.map((entry) => emitCaseClass(entry, plan, nullary, context)),
    ...plan.cases
      .filter((entry) => entry.constructor.fields.length === 0)
      .map((entry) =>
        constantStatement(
          entry.singleton,
          ts.factory.createNewExpression(ts.factory.createIdentifier(entry.className), undefined, []),
        ),
      ),
  ];
}

/** `kind` back to the one value that carries it: total, and only where every case is nullary. */
function emitTagConstructor(plan: TypePlan, base: ts.TypeNode): ts.ClassElement {
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
        'kind',
        undefined,
        ts.factory.createIndexedAccessTypeNode(base, literalType('kind')),
      ),
    ],
    base,
    block(
      ts.factory.createSwitchStatement(
        ts.factory.createIdentifier('kind'),
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

function emitBaseMethod(method: MethodPlan, context: EmitContext): ts.ClassElement {
  const allocator = newAllocator(context);
  const parameters = methodParameters(method, allocator, context);
  if (method.dispatches) {
    return documented(
      ts.factory.createMethodDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.AbstractKeyword)],
        undefined,
        method.name,
        undefined,
        undefined,
        parameters,
        emitType(method.declaration.result, context),
        undefined,
      ),
      method.declaration.doc,
    );
  }
  return documented(
    ts.factory.createMethodDeclaration(
      [modifier(ts.SyntaxKind.PublicKeyword)],
      undefined,
      method.name,
      undefined,
      undefined,
      parameters,
      emitType(method.declaration.result, context),
      emitFunctionBody(method.declaration.body, methodScope(parameters), allocator, context),
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
  if (entry.constructor.fields.length > 0) {
    members.push(
      ts.factory.createConstructorDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword)],
        entry.constructor.fields.map((field) =>
          ts.factory.createParameterDeclaration(
            [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.ReadonlyKeyword)],
            undefined,
            field.name,
            undefined,
            emitType(field.type, context),
          ),
        ),
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
    const body = method.declaration.body;
    if (body.kind !== 'match') throw new TypeError(`dispatching method ${method.declaration.name} lost its match`);
    const arm = body.cases.find((candidate) => candidate.constructor === entry.constructor.name);
    if (arm === undefined) {
      throw new TypeError(`method ${method.declaration.name} decides no ${entry.constructor.name} case`);
    }
    const allocator = newAllocator(context);
    const declared = methodParameters(method, allocator, context);
    const scope = [...armBindings(entry.constructor), ...methodScope(declared)];
    const used = usedParameterCount(arm.value, scope, entry.constructor.fields.length);
    members.push(
      ts.factory.createMethodDeclaration(
        [modifier(ts.SyntaxKind.PublicKeyword), modifier(ts.SyntaxKind.OverrideKeyword)],
        undefined,
        method.name,
        undefined,
        undefined,
        declared.slice(0, used),
        emitType(method.declaration.result, context),
        emitFunctionBody(arm.value, scope, allocator, context),
      ),
    );
  }
  if (!nullary) {
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
        [
          ts.factory.createParameterDeclaration(
            undefined,
            undefined,
            'other',
            undefined,
            ts.factory.createTypeReferenceNode(plan.typeName),
          ),
        ],
        ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
        ts.factory.createReturnStatement(
          conjunction([
            ts.factory.createBinaryExpression(
              ts.factory.createIdentifier('other'),
              ts.SyntaxKind.InstanceOfKeyword,
              ts.factory.createIdentifier(entry.className),
            ),
            ...entry.constructor.fields.map((field) =>
              equalityExpression(
                receiverField(field.name),
                fieldAccess(ts.factory.createIdentifier('other'), field.name),
                field.type,
                context,
              ),
            ),
          ]),
        ),
      ),
    );
  }
  return ts.factory.createClassDeclaration(
    undefined,
    entry.className,
    undefined,
    [
      ts.factory.createHeritageClause(ts.SyntaxKind.ExtendsKeyword, [
        ts.factory.createExpressionWithTypeArguments(ts.factory.createIdentifier(plan.typeName), undefined),
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
function emitNominalRecord(plan: TypePlan, declaration: LeanRecord, context: EmitContext): readonly ts.Statement[] {
  const self = ts.factory.createTypeReferenceNode(plan.typeName);
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
          ts.factory.createTypeReferenceNode(plan.initName),
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
    emitRecordFromData(plan, declaration, context),
  );
  for (const method of plan.methods) members.push(emitBaseMethod(method, context));
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
      [ts.factory.createParameterDeclaration(undefined, undefined, 'other', undefined, self)],
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
      block(
        ts.factory.createReturnStatement(
          conjunction(
            declaration.fields.map((field) =>
              equalityExpression(
                receiverField(field.name),
                fieldAccess(ts.factory.createIdentifier('other'), field.name),
                field.type,
                context,
              ),
            ),
          ),
        ),
      ),
    ),
  );
  return [
    interfaceOfFields(plan.initName, declaration.fields, (field) => emitType(field.type, context)),
    interfaceOfFields(plan.dataName, declaration.fields, (field) => dataType(field.type, context)),
    documented(
      ts.factory.createClassDeclaration(
        [modifier(ts.SyntaxKind.ExportKeyword)],
        plan.typeName,
        undefined,
        undefined,
        members,
      ),
      declaration.doc,
    ),
  ];
}

function interfaceOfFields(
  name: string,
  fields: readonly LeanField[],
  type: (field: LeanField) => ts.TypeNode,
): ts.Statement {
  return ts.factory.createInterfaceDeclaration(
    [modifier(ts.SyntaxKind.ExportKeyword)],
    name,
    undefined,
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
function emitEnumRepresentation(plan: TypePlan, base: ts.TypeNode, nullary: boolean): readonly ts.ClassElement[] {
  if (!nullary) {
    return [
      abstractMethod('toData', [], ts.factory.createTypeReferenceNode(plan.dataName)),
      abstractMethod(
        'equals',
        [ts.factory.createParameterDeclaration(undefined, undefined, 'other', undefined, base)],
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
      [ts.factory.createParameterDeclaration(undefined, undefined, 'other', undefined, base)],
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
      ts.factory.createReturnStatement(
        ts.factory.createBinaryExpression(
          ts.factory.createThis(),
          ts.SyntaxKind.EqualsEqualsEqualsToken,
          ts.factory.createIdentifier('other'),
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

function emitRecordFromData(plan: TypePlan, declaration: LeanRecord, context: EmitContext): ts.ClassElement {
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
  const validated = callPrelude(context, context.prelude.dataFields, [
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
        decodeExpression(elementAccess(data, field.name), field.type, `${owner} ${field.name}`, context),
      ),
    ),
  ];
}

function encodeExpression(value: ts.Expression, type: LeanType, context: EmitContext): ts.Expression {
  switch (type.kind) {
    case 'boolean':
      return value;
    case 'named': {
      const plan = requiredTypePlan(context, type.name);
      return plan.nominal
        ? ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(value, 'toData'), undefined, [])
        : value;
    }
    case 'option': {
      const inner = encodeExpression(value, type.inner, context);
      if (inner === value) {
        return ts.factory.createBinaryExpression(value, ts.SyntaxKind.QuestionQuestionToken, ts.factory.createNull());
      }
      return ts.factory.createConditionalExpression(
        ts.factory.createBinaryExpression(
          value,
          ts.SyntaxKind.EqualsEqualsEqualsToken,
          ts.factory.createIdentifier('undefined'),
        ),
        undefined,
        ts.factory.createNull(),
        undefined,
        inner,
      );
    }
  }
}

function decodeExpression(value: ts.Expression, type: LeanType, name: string, context: EmitContext): ts.Expression {
  switch (type.kind) {
    case 'boolean':
      return callPrelude(context, context.prelude.requireBoolean, [value, ts.factory.createStringLiteral(name)]);
    case 'named': {
      const plan = requiredTypePlan(context, type.name);
      if (plan.nominal) {
        return ts.factory.createCallExpression(
          ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier(plan.typeName), 'fromData'),
          undefined,
          [value],
        );
      }
      const decoder = context.prelude.decoders.get(type.name);
      if (decoder === undefined) throw new TypeError(`missing generated decoder for ${type.name}`);
      return callPrelude(context, decoder, [value, ts.factory.createStringLiteral(name)]);
    }
    case 'option':
      return ts.factory.createConditionalExpression(
        ts.factory.createBinaryExpression(value, ts.SyntaxKind.EqualsEqualsEqualsToken, ts.factory.createNull()),
        undefined,
        ts.factory.createIdentifier('undefined'),
        undefined,
        decodeExpression(value, type.inner, name, context),
      );
  }
}

function equalityExpression(
  left: ts.Expression,
  right: ts.Expression,
  type: LeanType,
  context: EmitContext,
): ts.Expression {
  switch (type.kind) {
    case 'boolean':
      return ts.factory.createBinaryExpression(left, ts.SyntaxKind.EqualsEqualsEqualsToken, right);
    case 'named': {
      const plan = requiredTypePlan(context, type.name);
      if (!plan.nominal) return structuralEquality(left, right, plan, context);
      return ts.factory.createCallExpression(ts.factory.createPropertyAccessExpression(left, 'equals'), undefined, [
        right,
      ]);
    }
    case 'option': {
      const inner = equalityExpression(left, right, type.inner, context);
      return ts.factory.createConditionalExpression(
        ts.factory.createBinaryExpression(
          left,
          ts.SyntaxKind.EqualsEqualsEqualsToken,
          ts.factory.createIdentifier('undefined'),
        ),
        undefined,
        ts.factory.createBinaryExpression(
          right,
          ts.SyntaxKind.EqualsEqualsEqualsToken,
          ts.factory.createIdentifier('undefined'),
        ),
        undefined,
        ts.factory.createBinaryExpression(
          ts.factory.createBinaryExpression(
            right,
            ts.SyntaxKind.ExclamationEqualsEqualsToken,
            ts.factory.createIdentifier('undefined'),
          ),
          ts.SyntaxKind.AmpersandAmpersandToken,
          inner,
        ),
      );
    }
  }
}

/**
 * A structural type is its own value, so equality is the structural comparison of its parts. A
 * discriminated union compares its tag first; a tag compares directly.
 */
function structuralEquality(
  left: ts.Expression,
  right: ts.Expression,
  plan: TypePlan,
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
      equalityExpression(fieldAccess(left, field.name), fieldAccess(right, field.name), field.type, context),
    ),
  );
}

/** The JSON image of a Lean type: `Option` is `null` in data, and a value object is its data. */
function dataType(type: LeanType, context: EmitContext): ts.TypeNode {
  switch (type.kind) {
    case 'boolean':
      return ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword);
    case 'named': {
      const plan = requiredTypePlan(context, type.name);
      if (plan.nominal) return ts.factory.createTypeReferenceNode(plan.dataName);
      assertStructuralDataImage(plan, context, type.name);
      return ts.factory.createTypeReferenceNode(plan.typeName);
    }
    case 'option':
      return ts.factory.createUnionTypeNode([
        dataType(type.inner, context),
        ts.factory.createLiteralTypeNode(ts.factory.createNull()),
      ]);
  }
}

/**
 * A structural type is its own data image only while it holds no value object; one that does
 * would need a second image, so it is refused with the source-level remedy.
 */
function assertStructuralDataImage(plan: TypePlan, context: EmitContext, name: string): void {
  const fields =
    plan.declaration.kind === 'record'
      ? plan.declaration.fields
      : plan.declaration.constructors.flatMap((constructor) => constructor.fields);
  for (const field of fields) {
    const type = field.type.kind === 'option' ? field.type.inner : field.type;
    if (type.kind !== 'named') continue;
    const referenced = requiredTypePlan(context, type.name);
    if (referenced.nominal) {
      throw new TypeError(
        `${name} is used in data position but its field ${field.name} carries the value object ${type.name}; give ${name} behaviour so it becomes a value object too`,
      );
    }
    assertStructuralDataImage(referenced, context, type.name);
  }
}

/**
 * The generated validators, built in reverse dependency order so a helper reached only through
 * another helper is still emitted, and printed in a fixed order so the bytes are stable.
 */
function emitPrelude(context: EmitContext): readonly ts.Statement[] {
  const { prelude, locals } = context;
  const value = ts.factory.createIdentifier(locals.value);
  const name = ts.factory.createIdentifier(locals.name);
  const fields = ts.factory.createIdentifier(locals.fields);
  const dataRecord = dataRecordType(prelude.dataBoundary);
  const decoders: ts.Statement[] = [];
  for (const [leanName, emitted] of [...prelude.decoders].sort(([left], [right]) => compareCodePoints(left, right))) {
    if (!context.used.has(emitted)) continue;
    decoders.push(emitStructuralDecoder(leanName, emitted, context));
  }
  const requireBooleanDeclaration: ts.Statement[] = [];
  if (context.used.has(prelude.requireBoolean)) {
    requireBooleanDeclaration.push(
      ts.factory.createFunctionDeclaration(
        undefined,
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
  const dataFieldsDeclaration: ts.Statement[] = [];
  if (context.used.has(prelude.dataFields)) {
    dataFieldsDeclaration.push(
      ts.factory.createFunctionDeclaration(
        undefined,
        undefined,
        prelude.dataFields,
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
  const isDataObjectDeclaration: ts.Statement[] = [];
  if (context.used.has(prelude.isDataObject)) {
    isDataObjectDeclaration.push(
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
              ts.factory.createBinaryExpression(
                ts.factory.createTypeOfExpression(value),
                ts.SyntaxKind.EqualsEqualsEqualsToken,
                ts.factory.createStringLiteral('object'),
              ),
              ts.factory.createBinaryExpression(
                value,
                ts.SyntaxKind.ExclamationEqualsEqualsToken,
                ts.factory.createNull(),
              ),
              ts.factory.createPrefixUnaryExpression(
                ts.SyntaxKind.ExclamationToken,
                ts.factory.createCallExpression(
                  ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier('Array'), 'isArray'),
                  undefined,
                  [value],
                ),
              ),
            ]),
          ),
        ),
      ),
    );
  }
  // Built last: the alias is emitted only once some validator above has actually referenced it.
  const boundaryDeclaration: ts.Statement[] = context.used.has(prelude.dataBoundary)
    ? [emitDataBoundaryAlias(prelude.dataBoundary)]
    : [];
  return [
    ...boundaryDeclaration,
    ...isDataObjectDeclaration,
    ...dataFieldsDeclaration,
    ...requireBooleanDeclaration,
    ...decoders,
  ];
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
  return ts.factory.createFunctionDeclaration(
    undefined,
    undefined,
    emitted,
    undefined,
    [dataParameter(context.locals.value, context), stringParameter(context.locals.name)],
    ts.factory.createTypeReferenceNode(plan.typeName),
    block(...statements),
  );
}

function methodParameters(
  method: MethodPlan,
  allocator: IdentifierAllocator,
  context: EmitContext,
): readonly ts.ParameterDeclaration[] {
  return method.declaration.parameters
    .slice(1)
    .map((parameter) =>
      ts.factory.createParameterDeclaration(
        undefined,
        undefined,
        allocator.allocate(parameter.name),
        undefined,
        emitType(parameter.type, context),
      ),
    );
}

/** de Bruijn scope for a method body: the receiver is `this`, the rest are its parameters. */
function methodScope(parameters: readonly ts.ParameterDeclaration[]): readonly Binding[] {
  const names = parameters.map((parameter): Binding => {
    if (!ts.isIdentifier(parameter.name)) throw new TypeError('emitted parameter is not an identifier');
    return { kind: 'identifier', name: parameter.name.text };
  });
  return [...names].reverse().concat({ kind: 'receiver' });
}

/** A dispatched arm reads its constructor's fields off the receiver, innermost binder last. */
function armBindings(constructor: LeanEnumConstructor): readonly Binding[] {
  return [...constructor.fields].reverse().map((field) => ({ kind: 'receiverField', field: field.name }) as const);
}

/**
 * How many leading declared parameters an override has to keep: TypeScript admits an
 * override that ignores a trailing suffix, and the handwritten idiom drops it.
 */
function usedParameterCount(expression: LeanExpression, scope: readonly Binding[], fieldCount: number): number {
  const receiverIndex = scope.length - 1;
  let highest = 0;
  const visit = (node: LeanExpression, depth: number): void => {
    switch (node.kind) {
      case 'variable': {
        const index = node.index - depth;
        if (index < fieldCount || index >= receiverIndex) return;
        highest = Math.max(highest, receiverIndex - index);
        return;
      }
      case 'let':
        visit(node.value, depth);
        visit(node.body, depth + 1);
        return;
      case 'field':
        visit(node.target, depth);
        return;
      case 'if':
        visit(node.condition, depth);
        visit(node.consequent, depth);
        visit(node.alternate, depth);
        return;
      case 'equals':
      case 'and':
      case 'or':
        visit(node.left, depth);
        visit(node.right, depth);
        return;
      case 'not':
        visit(node.operand, depth);
        return;
      case 'some':
        visit(node.value, depth);
        return;
      case 'record':
        node.fields.forEach((field) => visit(field.value, depth));
        return;
      case 'match':
        visit(node.scrutinee, depth);
        node.cases.forEach((entry) => visit(entry.value, depth));
        return;
      case 'variant':
      case 'call':
        node.arguments.forEach((argument) => visit(argument, depth));
        return;
      case 'boolean':
      case 'none':
        return;
    }
  };
  visit(expression, 0);
  return highest;
}

function emitType(type: LeanType, context: EmitContext): ts.TypeNode {
  switch (type.kind) {
    case 'boolean':
      return ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword);
    case 'named':
      return ts.factory.createTypeReferenceNode(requiredDeclarationName(context.declarationNames, type.name));
    case 'option':
      return ts.factory.createUnionTypeNode([
        emitType(type.inner, context),
        ts.factory.createKeywordTypeNode(ts.SyntaxKind.UndefinedKeyword),
      ]);
  }
}

function emitFunctionBody(
  expression: LeanExpression,
  scope: readonly Binding[],
  allocator: IdentifierAllocator,
  context: EmitContext,
): ts.Block {
  const statements: ts.Statement[] = [];
  let current = expression;
  let currentScope = scope;
  while (current.kind === 'let') {
    const emittedName = allocator.allocate(current.name);
    statements.push(constantStatement(emittedName, emitExpression(current.value, currentScope, context)));
    currentScope = [{ kind: 'identifier', name: emittedName }, ...currentScope];
    current = current.body;
  }
  statements.push(ts.factory.createReturnStatement(emitExpression(current, currentScope, context)));
  return ts.factory.createBlock(statements, true);
}

function emitExpression(expression: LeanExpression, scope: readonly Binding[], context: EmitContext): ts.Expression {
  switch (expression.kind) {
    case 'variable': {
      const binding = scope[expression.index];
      if (binding === undefined) throw new TypeError(`unbound de Bruijn index ${expression.index}`);
      return emitBinding(binding);
    }
    case 'boolean':
      return expression.value ? ts.factory.createTrue() : ts.factory.createFalse();
    case 'let':
      throw new TypeError('nested let expressions must be normalized before emission');
    case 'field':
      return fieldAccess(emitExpression(expression.target, scope, context), expression.field);
    case 'if':
      return ts.factory.createConditionalExpression(
        emitExpression(expression.condition, scope, context),
        undefined,
        emitExpression(expression.consequent, scope, context),
        undefined,
        emitExpression(expression.alternate, scope, context),
      );
    case 'equals':
      if (expression.right.kind === 'boolean' && expression.right.value) {
        return emitExpression(expression.left, scope, context);
      }
      if (expression.left.kind === 'boolean' && expression.left.value) {
        return emitExpression(expression.right, scope, context);
      }
      return ts.factory.createBinaryExpression(
        emitExpression(expression.left, scope, context),
        ts.SyntaxKind.EqualsEqualsEqualsToken,
        emitExpression(expression.right, scope, context),
      );
    case 'and':
    case 'or':
      return ts.factory.createBinaryExpression(
        emitExpression(expression.left, scope, context),
        expression.kind === 'and' ? ts.SyntaxKind.AmpersandAmpersandToken : ts.SyntaxKind.BarBarToken,
        emitExpression(expression.right, scope, context),
      );
    case 'not':
      return ts.factory.createPrefixUnaryExpression(
        ts.SyntaxKind.ExclamationToken,
        emitExpression(expression.operand, scope, context),
      );
    case 'some':
      return emitExpression(expression.value, scope, context);
    case 'none':
      return ts.factory.createIdentifier('undefined');
    case 'variant': {
      const plan = requiredTypePlan(context, expression.type);
      const values = expression.arguments.map((argument) => emitExpression(argument, scope, context));
      const constructor =
        plan.declaration.kind === 'enum'
          ? plan.declaration.constructors.find((candidate) => candidate.name === expression.name)
          : undefined;
      if (constructor === undefined) throw new TypeError(`unknown constructor ${expression.type}.${expression.name}`);
      if (!plan.nominal) {
        if (constructor.fields.length === 0 && plan.declaration.kind === 'enum') {
          const carriesData = plan.declaration.constructors.some((candidate) => candidate.fields.length > 0);
          if (!carriesData) return ts.factory.createStringLiteral(expression.name);
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
      const member = ts.factory.createPropertyAccessExpression(
        ts.factory.createIdentifier(plan.typeName),
        expression.name,
      );
      return constructor.fields.length === 0 ? member : ts.factory.createCallExpression(member, undefined, values);
    }
    case 'match':
      return emitTagMatch(expression, scope, context);
    case 'record': {
      const plan = requiredTypePlan(context, expression.type);
      const literal = ts.factory.createObjectLiteralExpression(
        expression.fields.map((field) =>
          ts.factory.createPropertyAssignment(propertyName(field.name), emitExpression(field.value, scope, context)),
        ),
        true,
      );
      return plan.nominal
        ? ts.factory.createNewExpression(ts.factory.createIdentifier(plan.typeName), undefined, [literal])
        : literal;
    }
    case 'call': {
      const method = context.methods.get(expression.function);
      if (method === undefined) {
        return ts.factory.createCallExpression(
          ts.factory.createIdentifier(requiredDeclarationName(context.declarationNames, expression.function)),
          undefined,
          expression.arguments.map((argument) => emitExpression(argument, scope, context)),
        );
      }
      const [receiver, ...rest] = expression.arguments;
      if (receiver === undefined) throw new TypeError(`method call ${expression.function} has no receiver`);
      return ts.factory.createCallExpression(
        ts.factory.createPropertyAccessExpression(emitExpression(receiver, scope, context), method.name),
        undefined,
        rest.map((argument) => emitExpression(argument, scope, context)),
      );
    }
  }
}

/**
 * A `match` on a tag union, in any expression position: the representation of a nullary-only
 * structural enum is its own tag, so the alternatives lower to strict-equality conditionals in
 * declaration order. The IR has already proved the match decides every constructor exactly once,
 * which is what makes the final alternative an unconditional fallback rather than a guess.
 *
 * The scrutinee is read once per test, so only a binding or a field read is admitted: anything
 * that computes has to be named by a `let` first rather than be silently re-evaluated per arm.
 * A value object keeps its dot-notation dispatch, and a payload-carrying union still needs one,
 * because neither can be decided by comparing the scrutinee against a tag.
 */
function emitTagMatch(
  expression: Extract<LeanExpression, { kind: 'match' }>,
  scope: readonly Binding[],
  context: EmitContext,
): ts.Expression {
  const plan = requiredTypePlan(context, expression.type);
  if (plan.declaration.kind !== 'enum') {
    throw new TypeError(`match scrutinee ${plan.typeName} is not an inductive`);
  }
  if (plan.nominal) {
    throw new TypeError(
      `a match on the value object ${plan.typeName} outside dot-notation dispatch position is outside this fragment version`,
    );
  }
  if (plan.declaration.constructors.some((constructor) => constructor.fields.length > 0)) {
    throw new TypeError(
      `a match on the payload-carrying union ${plan.typeName} outside dot-notation dispatch position is outside this fragment version`,
    );
  }
  if (expression.scrutinee.kind !== 'variable' && expression.scrutinee.kind !== 'field') {
    throw new TypeError(
      `a match on a computed ${plan.typeName} is outside this fragment version: bind the scrutinee with let first`,
    );
  }
  const scrutinee = emitExpression(expression.scrutinee, scope, context);
  const arms = expression.cases.map((entry) => ({
    tag: entry.constructor,
    value: emitExpression(entry.value, scope, context),
  }));
  const fallback = arms.at(-1);
  if (fallback === undefined) throw new TypeError(`match on ${plan.typeName} decides no alternative`);
  return arms
    .slice(0, -1)
    .reduceRight(
      (alternate, arm) =>
        ts.factory.createConditionalExpression(
          ts.factory.createBinaryExpression(
            scrutinee,
            ts.SyntaxKind.EqualsEqualsEqualsToken,
            ts.factory.createStringLiteral(arm.tag),
          ),
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
    case 'receiver':
      return ts.factory.createThis();
    case 'receiverField':
      return receiverField(binding.field);
  }
}

function orderedDeclarations(program: LeanSemanticProgram): readonly LeanDeclaration[] {
  const types = program.declarations
    .filter((declaration) => declaration.kind !== 'function')
    .sort((left, right) => {
      const kindOrder = Number(left.kind === 'record') - Number(right.kind === 'record');
      return kindOrder || compareCodePoints(left.name, right.name);
    });
  const functions = new Map(
    program.declarations
      .filter((declaration): declaration is LeanFunction => declaration.kind === 'function')
      .map((declaration) => [declaration.name, declaration]),
  );
  const orderedFunctions: LeanFunction[] = [];
  const visiting = new Set<string>();
  const visited = new Set<string>();
  const visit = (name: string): void => {
    if (visited.has(name)) return;
    // Direct self-recursion is admitted where Lean proved it structural; a cycle through another
    // declaration has no such proof and no ordering.
    if (visiting.has(name)) throw new TypeError(`mutual recursion is outside the fragment: ${name}`);
    const declaration = functions.get(name);
    if (declaration === undefined) return;
    visiting.add(name);
    for (const dependency of calledFunctions(declaration.body)) {
      if (dependency !== name) visit(dependency);
    }
    visiting.delete(name);
    visited.add(name);
    orderedFunctions.push(declaration);
  };
  for (const root of program.roots) visit(root);
  for (const name of [...functions.keys()].sort(compareCodePoints)) visit(name);
  return [...types, ...orderedFunctions];
}

function calledFunctions(expression: LeanExpression): readonly string[] {
  const names = new Set<string>();
  const visit = (node: LeanExpression): void => {
    switch (node.kind) {
      case 'call':
        names.add(node.function);
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
      case 'equals':
      case 'and':
      case 'or':
        visit(node.left);
        visit(node.right);
        return;
      case 'not':
        visit(node.operand);
        return;
      case 'some':
        visit(node.value);
        return;
      case 'record':
        node.fields.forEach((field) => visit(field.value));
        return;
      case 'match':
        visit(node.scrutinee);
        node.cases.forEach((entry) => visit(entry.value));
        return;
      case 'variant':
        node.arguments.forEach(visit);
        return;
      case 'variable':
      case 'boolean':
      case 'none':
        return;
    }
  };
  visit(expression);
  return [...names].sort(compareCodePoints);
}

function newAllocator(context: EmitContext): IdentifierAllocator {
  return new IdentifierAllocator(context.reserved);
}

function requiredTypePlan(context: EmitContext, name: string): TypePlan {
  const plan = context.types.get(name);
  if (plan === undefined) throw new TypeError(`missing emitted representation for data type ${name}`);
  return plan;
}

function callPrelude(context: EmitContext, name: string, argumentsList: readonly ts.Expression[]): ts.CallExpression {
  context.used.add(name);
  return ts.factory.createCallExpression(ts.factory.createIdentifier(name), undefined, argumentsList);
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

function constantStatement(name: string, initializer: ts.Expression): ts.Statement {
  return ts.factory.createVariableStatement(
    undefined,
    ts.factory.createVariableDeclarationList(
      [ts.factory.createVariableDeclaration(name, undefined, undefined, initializer)],
      ts.NodeFlags.Const,
    ),
  );
}

function block(...statements: readonly ts.Statement[]): ts.Block {
  return ts.factory.createBlock(statements, true);
}

function freezeThis(): ts.Statement {
  return ts.factory.createExpressionStatement(
    ts.factory.createCallExpression(
      ts.factory.createPropertyAccessExpression(ts.factory.createIdentifier('Object'), 'freeze'),
      undefined,
      [ts.factory.createThis()],
    ),
  );
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
