import { describe, expect, test } from 'vitest';
import {
  decodeLeanSemanticProgram,
  LEAN_HOST_OPCODES,
  LEAN_RUNTIME_ASSUMPTIONS,
  LEAN_RUNTIME_HELPER_ROLES,
  LEAN_RUNTIME_OPCODES,
  LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
  referencedRuntimeOpcodes,
  runtimeHelperRole,
  type LeanOpcode,
} from '../src/lean-to-typescript/ir.js';
import { createHash } from 'node:crypto';
import ts from 'typescript';
import { loadRuntimeCertificateRegistry, loadRuntimeProbeCorpus } from '../src/lean-to-typescript/certificates.js';
import { emitTypeScriptPackage, leanToTypeScriptHelperBindings } from '../src/lean-to-typescript/emitter.js';
import { declaredNames, moduleImports } from '../src/lean-to-typescript/package-layout.js';

const identitySpan = { startLine: 2, startColumn: 0, endLine: 2, endColumn: 46 };

const identityDeclaration = {
  kind: 'function',
  name: 'Example.identity',
  module: 'Example',
  namespace: 'Example',
  typeParameters: [],
  span: identitySpan,
  parameters: [{ name: 'value', type: { kind: 'boolean' } }],
  result: { kind: 'boolean' },
  // Every v6 function carries the recursion descriptor explicitly. A non-recursive declaration
  // spells it as a literal null, so a document that forgot the field is refused rather than read
  // as "Lean proved nothing to record".
  recursion: null,
  body: { kind: 'variable', index: 0 },
};

const identityClosure = { declaration: 'Example.identity', module: 'Example', role: 'emitted', reason: '' };

const otherDeclaration = {
  kind: 'record',
  name: 'Other.identity',
  module: 'Other',
  namespace: 'Other',
  typeParameters: [],
  span: identitySpan,
  constructor: 'mk',
  fields: [],
};

const otherClosure = { declaration: 'Other.identity', module: 'Other', role: 'emitted', reason: '' };

function program(
  declarations: readonly object[] = [identityDeclaration],
  closure: readonly object[] = [identityClosure],
  roots: readonly string[] = ['Example.identity'],
): object {
  return {
    schemaVersion: 1,
    fragmentVersion: LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
    roots,
    closure,
    declarations,
  };
}

/** A `Tree` inductive plus a declaration that walks it, which is the shape recursion tests need. */
const treeDeclaration = {
  kind: 'enum',
  name: 'Example.Tree',
  module: 'Example',
  namespace: 'Example',
  typeParameters: [],
  span: identitySpan,
  constructors: [
    { name: 'leaf', fields: [] },
    { name: 'branch', fields: [{ name: 'inner', type: { kind: 'named', name: 'Example.Tree', arguments: [] } }] },
  ],
};

const treeClosure = { declaration: 'Example.Tree', module: 'Example', role: 'emitted', reason: '' };
const treeType = { kind: 'named', name: 'Example.Tree', arguments: [] };

/** `Example.depth : Tree -> Nat`, structurally recursive on its only parameter. */
const depthDeclaration = {
  kind: 'function',
  name: 'Example.depth',
  module: 'Example',
  namespace: 'Example',
  typeParameters: [],
  span: identitySpan,
  parameters: [{ name: 'tree', type: treeType }],
  result: { kind: 'nat' },
  recursion: { kind: 'structural', parameter: 0 },
  body: {
    kind: 'match',
    type: treeType,
    scrutinee: { kind: 'variable', index: 0 },
    cases: [
      { constructor: 'leaf', value: { kind: 'nat', value: '0' } },
      {
        constructor: 'branch',
        value: {
          kind: 'operation',
          opcode: 'nat.successor',
          typeArguments: [],
          arguments: [
            { kind: 'call', function: 'Example.depth', typeArguments: [], arguments: [{ kind: 'variable', index: 0 }] },
          ],
        },
      },
    ],
  },
};

const depthClosure = { declaration: 'Example.depth', module: 'Example', role: 'emitted', reason: '' };

/** The same declaration with no recorded recursion, which is what a guessed recursion looks like. */
function withoutRecursion(declaration: typeof depthDeclaration): object {
  return { ...declaration, recursion: null };
}

function recursionProgram(declaration: object = depthDeclaration): object {
  return program([treeDeclaration, declaration], [treeClosure, depthClosure], ['Example.depth']);
}

/** Provenance is not under test in the emitter cases below; only the emitted names are. */
const inputClosure = (inputs: readonly { kind: string; identity: string; sha256: string }[]): string =>
  `sha256:${createHash('sha256').update(JSON.stringify(inputs)).digest('hex')}`;
// A package that spends a certified opcode must carry the probe corpus it rests on and the engine
// binary that ran it, and every input list is read in canonical identity order.
const semanticInputs = [
  {
    kind: 'compiler-source' as const,
    identity: 'compiler:spec:semantics/probes.json',
    sha256: loadRuntimeProbeCorpus().sha256,
  },
  { kind: 'lean-source' as const, identity: 'source:Example', sha256: `sha256:${'0'.repeat(64)}` },
];
const environmentInputs = [
  { kind: 'compiler-runtime' as const, identity: 'compiler:runtime', sha256: `sha256:${'1'.repeat(64)}` },
  { kind: 'lean-module' as const, identity: 'module:Example', sha256: `sha256:${'0'.repeat(64)}` },
];
const provenance = {
  certificates: loadRuntimeCertificateRegistry().catalog,
  semantic: {
    fragmentVersion: LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
    entryModule: 'Example',
    declarations: ['Example.doubled'],
    leanToolchain: {
      identity: 'leanprover/lean4:v4.33.1',
      leanVersion: 'Lean (version 4.33.1)',
      lakeVersion: 'Lake version 5.0.0',
    },
    inputs: semanticInputs,
    inputClosureSha256: inputClosure(semanticInputs),
    semanticIrSha256: `sha256:${'0'.repeat(64)}`,
  },
  environment: {
    runtime: 'node:test',
    typescriptVersion: ts.version,
    platform: 'test',
    inputs: environmentInputs,
    inputClosureSha256: inputClosure(environmentInputs),
  },
  sources: new Map([['Example', 'Example.lean']]),
  leanProjectPath: 'lean',
};

describe('Lean semantic IR runtime opcode registry', () => {
  test('is total, closed, and names one Lean symbol and one operand list per opcode', () => {
    const opcodes = Object.keys(LEAN_RUNTIME_OPCODES) as readonly LeanOpcode[];
    expect(opcodes.length).toBe(54);
    for (const opcode of opcodes) {
      const row = LEAN_RUNTIME_OPCODES[opcode];
      expect(row.opcode).toBe(opcode);
      expect(row.leanSymbol.length).toBeGreaterThan(0);
      // One name per operand, positionally: the row's form is written over exactly these.
      expect(row.operands.length).toBe(
        row.parameters(Array.from({ length: row.typeParameters }, () => ({ kind: 'nat' }) as const)).length,
      );
      expect(row.modelTheorem).toMatch(/^TSLean\.LeanToTypeScript\.Semantics\.Opcode\.[A-Za-z]+$/u);
      // A row stands on an engine assumption, or — where its form is an identity on an image two
      // Lean types share — on the ordered model composition that makes it one. Neither would be a
      // lowering nothing accounts for, which is exactly what the certificate gate refuses.
      expect(row.assumptions.length + (row.components?.length ?? 0)).toBeGreaterThan(0);
      for (const assumption of row.assumptions) {
        expect(LEAN_RUNTIME_ASSUMPTIONS[assumption]).toBeTypeOf('string');
      }
    }
    // The seven guarded roles, in the fixed print order the emitter allocates them in. A helper
    // opcode binds its role rather than an inline form, so this is the whole guarded set.
    expect(opcodes.filter((opcode) => LEAN_RUNTIME_OPCODES[opcode].runtimeSymbol.startsWith('helper:'))).toEqual([
      'nat.subtract',
      'list.head',
      'int.tdiv',
      'int.tmod',
      'int.toNat',
      'char.ofNat',
      'char.less',
    ]);
    expect(
      opcodes
        .map((opcode) => runtimeHelperRole(LEAN_RUNTIME_OPCODES[opcode].runtimeSymbol))
        .filter((role): role is NonNullable<typeof role> => role !== undefined)
        .sort(),
    ).toEqual([...LEAN_RUNTIME_HELPER_ROLES].sort());
    expect(LEAN_RUNTIME_OPCODES['nat.subtract'].runtimeSymbol).toBe('helper:nat-truncated-subtraction');
    expect(LEAN_RUNTIME_OPCODES['nat.subtract'].components).toEqual([
      'inline:nat.less',
      'conditional:select',
      'primitive:bigint.subtract',
    ]);
    // The closure order mirrors the composition order, so a reordered row fails here.
    expect(LEAN_RUNTIME_OPCODES['nat.subtract'].assumptions).toEqual([
      'bigint.relational',
      'conditional.truthy-selection',
      'bigint.exact-arithmetic',
    ]);
    expect(LEAN_RUNTIME_OPCODES['list.head'].runtimeSymbol).toBe('helper:list-head-option');
    expect(LEAN_RUNTIME_OPCODES['list.head'].components).toEqual([
      'inline:list.isEmpty',
      'inline:list.first',
      'conditional:select',
      'representation:option.tagged-option',
    ]);
    expect(LEAN_RUNTIME_OPCODES['list.head'].assumptions).toEqual([
      'array.dense-element-sequence',
      'conditional.truthy-selection',
      'option.tagged-object',
    ]);
    // The truncating Int division helpers guard the zero divisor Lean's `tdiv`/`tmod` define, and
    // the clamp guards the negative `Int` that has no `Nat` image.
    expect(LEAN_RUNTIME_OPCODES['int.tdiv'].components).toEqual([
      'inline:int.equals',
      'conditional:select',
      'primitive:bigint.divide',
    ]);
    expect(LEAN_RUNTIME_OPCODES['int.toNat'].components).toEqual([
      'inline:int.less',
      'conditional:select',
      'representation:nat.nonnegative-bigint',
    ]);
    // A representation identity carries no engine assumption: it stands on the shared image alone.
    for (const opcode of ['int.ofNat', 'array.toList', 'array.ofList', 'string.singleton'] as const) {
      expect(LEAN_RUNTIME_OPCODES[opcode].assumptions).toEqual([]);
      expect(LEAN_RUNTIME_OPCODES[opcode].components?.length).toBeGreaterThan(0);
    }
    expect(LEAN_RUNTIME_OPCODES['bool.and'].runtimeSymbol).toBe('inline:bool.and');
    expect(LEAN_RUNTIME_OPCODES['bool.and'].components).toBeUndefined();
    // Every model theorem is distinct, so two opcodes can never share one proof obligation.
    expect(new Set(opcodes.map((opcode) => LEAN_RUNTIME_OPCODES[opcode].modelTheorem)).size).toBe(opcodes.length);
    expect(new Set(Object.keys(LEAN_RUNTIME_ASSUMPTIONS)).size).toBe(16);
  });

  test('closes the host-operation registry the substrate publishes', () => {
    const hosts = Object.keys(LEAN_HOST_OPCODES);
    expect(hosts.length).toBe(19);
    // Every host identity is a dotted wire name under `host.`, and each row states what the
    // substrate owes it, so a foreign declaration cannot acquire an unowned boundary.
    for (const host of hosts) {
      expect(host).toMatch(/^host\.[a-z]+\.[a-zA-Z]+$/u);
      expect(LEAN_HOST_OPCODES[host as keyof typeof LEAN_HOST_OPCODES].length).toBeGreaterThan(0);
    }
    expect([...new Set(hosts.map((host) => host.split('.')[1]))]).toEqual([
      'store',
      'alarm',
      'content',
      'queue',
      'isolate',
      'rpc',
    ]);
  });

  test('reports exactly the opcodes a program names, including a match destructuring cost', () => {
    expect(referencedRuntimeOpcodes(decodeLeanSemanticProgram(recursionProgram()))).toEqual(['nat.successor']);
    const listType = { kind: 'list', element: { kind: 'nat' } };
    const listWalk = {
      kind: 'function',
      name: 'Example.total',
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      parameters: [{ name: 'values', type: listType }],
      result: { kind: 'nat' },
      recursion: { kind: 'structural', parameter: 0 },
      body: {
        kind: 'match',
        type: listType,
        scrutinee: { kind: 'variable', index: 0 },
        cases: [
          { constructor: 'nil', value: { kind: 'nat', value: '0' } },
          {
            constructor: 'cons',
            value: {
              kind: 'operation',
              opcode: 'nat.add',
              typeArguments: [],
              arguments: [
                { kind: 'variable', index: 1 },
                {
                  kind: 'call',
                  function: 'Example.total',
                  typeArguments: [],
                  arguments: [{ kind: 'variable', index: 0 }],
                },
              ],
            },
          },
        ],
      },
    };
    const decoded = decodeLeanSemanticProgram(
      program(
        [listWalk],
        [{ declaration: 'Example.total', module: 'Example', role: 'emitted', reason: '' }],
        ['Example.total'],
      ),
    );
    expect(referencedRuntimeOpcodes(decoded)).toEqual(['list.first', 'list.isEmpty', 'list.rest', 'nat.add']);
  });
});

describe('emitted binder names survive a hostile semantic program', () => {
  test('an eta-wrapped callback never takes the name of the binding it applies', () => {
    const nat = { kind: 'nat' } as const;
    const listNat = { kind: 'list', element: nat } as const;
    const step = { kind: 'function', parameters: [nat], result: nat } as const;
    // The callback operand is a binding, not an abstraction, so the emitter has to wrap it. Its
    // Lean name is the one the wrapper would otherwise take.
    const mapWith = {
      kind: 'function',
      name: 'Example.mapWith',
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      parameters: [
        { name: 'element', type: step },
        { name: 'values', type: listNat },
      ],
      result: listNat,
      recursion: null,
      body: {
        kind: 'operation',
        opcode: 'list.map',
        typeArguments: [nat, nat],
        arguments: [
          { kind: 'variable', index: 1 },
          { kind: 'variable', index: 0 },
        ],
      },
    };
    const doubled = {
      kind: 'function',
      name: 'Example.doubled',
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      parameters: [{ name: 'values', type: listNat }],
      result: listNat,
      recursion: null,
      body: {
        kind: 'call',
        function: 'Example.mapWith',
        typeArguments: [],
        arguments: [
          {
            kind: 'lambda',
            parameters: [{ name: 'value', type: nat }],
            body: {
              kind: 'operation',
              opcode: 'nat.add',
              typeArguments: [],
              arguments: [
                { kind: 'variable', index: 0 },
                { kind: 'variable', index: 0 },
              ],
            },
          },
          { kind: 'variable', index: 0 },
        ],
      },
    };
    const decoded = decodeLeanSemanticProgram(
      program(
        [doubled, mapWith],
        [
          { declaration: 'Example.doubled', module: 'Example', role: 'emitted', reason: '' },
          { declaration: 'Example.mapWith', module: 'Example', role: 'emitted', reason: '' },
        ],
        ['Example.doubled'],
      ),
    );
    const emitted = emitTypeScriptPackage(decoded, provenance);
    const [module] = emitted.modules;
    if (module === undefined) throw new TypeError('the emitter produced no module');
    expect(module.code).toContain('return values.map(element$2 => element(element$2));');
    expect(module.code).not.toContain('element => element(element)');
    expect(module.code).toContain('return mapWith((value: bigint) => value + value, values);');
  });

  test.each([
    // Each generated member is its own scope, so one suffix per member, not a module-wide count.
    ['Object', 'Object$2', 'Object$2'],
    ['BarFoo', 'BarFoo$2', 'BarFoo$2'],
  ])('a nominal case field named %s never shadows its generated binder', (fieldName, factoryName, constructorName) => {
    const foo = {
      kind: 'enum',
      name: 'Example.Foo',
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      constructors: [{ name: 'bar', fields: [{ name: fieldName, type: { kind: 'boolean' } }] }],
    };
    const fooType = { kind: 'named', name: 'Example.Foo', arguments: [] };
    const read = {
      kind: 'function',
      name: 'Example.Foo.read',
      module: 'Example',
      namespace: 'Example.Foo',
      typeParameters: [],
      span: identitySpan,
      receiver: { type: 'Example.Foo', parameter: 0 },
      parameters: [{ name: 'foo', type: fooType }],
      result: { kind: 'boolean' },
      recursion: null,
      body: {
        kind: 'match',
        type: fooType,
        scrutinee: { kind: 'variable', index: 0 },
        cases: [{ constructor: 'bar', value: { kind: 'variable', index: 0 } }],
      },
    };
    const decoded = decodeLeanSemanticProgram(
      program(
        [foo, read],
        [
          { declaration: 'Example.Foo', module: 'Example', role: 'emitted', reason: '' },
          { declaration: 'Example.Foo.read', module: 'Example', role: 'emitted', reason: '' },
        ],
        ['Example.Foo.read'],
      ),
    );
    const emitted = emitTypeScriptPackage(decoded, {
      certificates: provenance.certificates,
      ...provenance,
      semantic: { ...provenance.semantic, declarations: ['Example.Foo.read'] },
    });
    const [module] = emitted.modules;
    if (module === undefined) throw new TypeError('the emitter produced no module');
    expect(module.code).toContain(`public static bar(${factoryName}: boolean): Foo {`);
    expect(module.code).toContain(`return new BarFoo(${factoryName});`);
    expect(module.code).toContain(`public constructor(${constructorName}: boolean) {`);
    expect(module.code).toContain(`this.${fieldName} = ${constructorName};`);
    expect(module.code).toContain(`public readonly ${fieldName}: boolean;`);
    if (fieldName === 'Object') expect(module.code).toContain('Object.freeze(this);');
  });

  test.each(['Object', 'BigInt', 'Array', 'TypeError'] as const)(
    'a top-level declaration named %s never shadows an emitted global',
    (localName) => {
      const recordName = `Example.${localName}`;
      const recordType = { kind: 'named', name: recordName, arguments: [] };
      const record = {
        kind: 'record',
        name: recordName,
        module: 'Example',
        namespace: 'Example',
        typeParameters: [],
        span: identitySpan,
        constructor: 'mk',
        fields: [{ name: 'flag', type: { kind: 'boolean' } }],
      };
      const method = {
        kind: 'function',
        name: `${recordName}.read`,
        module: 'Example',
        namespace: recordName,
        typeParameters: [],
        span: identitySpan,
        receiver: { type: recordName, parameter: 0 },
        parameters: [{ name: 'record', type: recordType }],
        result: { kind: 'boolean' },
        recursion: null,
        body: { kind: 'field', target: { kind: 'variable', index: 0 }, field: 'flag' },
      };
      const decoded = decodeLeanSemanticProgram(
        program(
          [record, method],
          [
            { declaration: recordName, module: 'Example', role: 'emitted', reason: '' },
            { declaration: `${recordName}.read`, module: 'Example', role: 'emitted', reason: '' },
          ],
          [`${recordName}.read`],
        ),
      );
      const emitted = emitTypeScriptPackage(decoded, {
        certificates: provenance.certificates,
        ...provenance,
        semantic: { ...provenance.semantic, declarations: [`${recordName}.read`] },
      });
      const [module] = emitted.modules;
      if (module === undefined) throw new TypeError('the emitter produced no module');
      expect(module.code).toContain(`export class ${localName}$2 {`);
      expect(
        emitted.manifest.semantic.modules[0]?.declarations.find((entry) => entry.declaration === recordName)?.emitted,
      ).toBe(`${localName}$2`);
      expect(
        emitted.manifest.semantic.modules[0]?.declarations.find((entry) => entry.declaration === `${recordName}.read`)
          ?.emitted,
      ).toBe('read');
      if (localName === 'Object') expect(module.code).toContain('Object.freeze(this);');
    },
  );

  test('allocates the tag-constructor local when a nullary nominal type is named kind', () => {
    const kindType = { kind: 'named', name: 'Example.kind', arguments: [] };
    const kind = {
      kind: 'enum',
      name: 'Example.kind',
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      constructors: [
        { name: 'first', fields: [] },
        { name: 'second', fields: [] },
      ],
    };
    const read = {
      kind: 'function',
      name: 'Example.kind.read',
      module: 'Example',
      namespace: 'Example.kind',
      typeParameters: [],
      span: identitySpan,
      receiver: { type: 'Example.kind', parameter: 0 },
      parameters: [{ name: 'value', type: kindType }],
      result: { kind: 'boolean' },
      recursion: null,
      body: {
        kind: 'match',
        type: kindType,
        scrutinee: { kind: 'variable', index: 0 },
        cases: [
          { constructor: 'first', value: { kind: 'boolean', value: true } },
          { constructor: 'second', value: { kind: 'boolean', value: false } },
        ],
      },
    };
    const decoded = decodeLeanSemanticProgram(
      program(
        [kind, read],
        [
          { declaration: 'Example.kind', module: 'Example', role: 'emitted', reason: '' },
          { declaration: 'Example.kind.read', module: 'Example', role: 'emitted', reason: '' },
        ],
        ['Example.kind.read'],
      ),
    );
    const emitted = emitTypeScriptPackage(decoded, {
      certificates: provenance.certificates,
      ...provenance,
      semantic: { ...provenance.semantic, declarations: ['Example.kind.read'] },
    });
    const [module] = emitted.modules;
    if (module === undefined) throw new TypeError('the emitter produced no module');
    expect(module.code).toContain('public static from(kind$2: kind["kind"]): kind {');
    expect(module.code).toContain('switch (kind$2) {');
    expect(
      emitted.manifest.semantic.modules[0]?.declarations.find((entry) => entry.declaration === 'Example.kind')?.emitted,
    ).toBe('kind');
    expect(
      emitted.manifest.semantic.modules[0]?.declarations.find((entry) => entry.declaration === 'Example.kind.read')
        ?.emitted,
    ).toBe('read');
  });
});

describe('lexical module reference discovery', () => {
  test('does not import hostile exports that helper scopes bind locally', () => {
    const exportedConst = (name: string): ts.Statement =>
      ts.factory.createVariableStatement(
        [ts.factory.createModifier(ts.SyntaxKind.ExportKeyword)],
        ts.factory.createVariableDeclarationList(
          [ts.factory.createVariableDeclaration(name, undefined, undefined, ts.factory.createNumericLiteral(0))],
          ts.NodeFlags.Const,
        ),
      );
    const ownerStatements = [
      exportedConst('left'),
      exportedConst('right'),
      ts.factory.createClassDeclaration(
        [ts.factory.createModifier(ts.SyntaxKind.ExportKeyword)],
        'A',
        undefined,
        undefined,
        [],
      ),
      exportedConst('codeUnit'),
    ];
    const owners = new Map(declaredNames(ownerStatements).map((name) => [name, 'Owner.ts']));
    // The runtime helper binds all four spellings: A in type space; left and right as parameters;
    // codeUnit as a nested local. None is a free reference, despite the other module exporting all.
    const helper = ts.factory.createFunctionDeclaration(
      undefined,
      undefined,
      'equalList',
      [ts.factory.createTypeParameterDeclaration(undefined, 'A')],
      [
        ts.factory.createParameterDeclaration(
          undefined,
          undefined,
          'left',
          undefined,
          ts.factory.createTypeReferenceNode('A'),
        ),
        ts.factory.createParameterDeclaration(
          undefined,
          undefined,
          'right',
          undefined,
          ts.factory.createTypeReferenceNode('A'),
        ),
      ],
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
      ts.factory.createBlock(
        [
          ts.factory.createVariableStatement(
            undefined,
            ts.factory.createVariableDeclarationList(
              [
                ts.factory.createVariableDeclaration(
                  'codeUnit',
                  undefined,
                  undefined,
                  ts.factory.createNumericLiteral(0),
                ),
              ],
              ts.NodeFlags.Const,
            ),
          ),
          ts.factory.createReturnStatement(
            ts.factory.createBinaryExpression(
              ts.factory.createIdentifier('left'),
              ts.SyntaxKind.EqualsEqualsEqualsToken,
              ts.factory.createIdentifier('right'),
            ),
          ),
        ],
        true,
      ),
    );
    const predicate = ts.factory.createFunctionDeclaration(
      undefined,
      undefined,
      'isDataObject',
      undefined,
      [
        ts.factory.createParameterDeclaration(
          undefined,
          undefined,
          'value',
          undefined,
          ts.factory.createKeywordTypeNode(ts.SyntaxKind.UnknownKeyword),
        ),
      ],
      ts.factory.createTypePredicateNode(
        undefined,
        ts.factory.createIdentifier('value'),
        ts.factory.createTypeLiteralNode([]),
      ),
      ts.factory.createBlock([ts.factory.createReturnStatement(ts.factory.createTrue())], true),
    );
    // The owner module also exports a type named value. The predicate parameter is a value binder,
    // not a type reference to that export, so neither helper needs an import.
    const valueOwner = ts.factory.createTypeAliasDeclaration(
      [ts.factory.createModifier(ts.SyntaxKind.ExportKeyword)],
      'value',
      undefined,
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
    );
    const allOwners = new Map([...owners, ...declaredNames([valueOwner]).map((name) => [name, 'Owner.ts'])]);
    expect(moduleImports('tslean-runtime.ts', [helper, predicate], allOwners)).toEqual([]);
  });
});

describe('Lean semantic IR generated helper bindings', () => {
  test('names only the roles a program reaches, with the identifier the emitter allocated', () => {
    const listType = { kind: 'list', element: { kind: 'nat' } };
    const head = {
      kind: 'function',
      name: 'Example.first',
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      parameters: [{ name: 'values', type: listType }],
      result: { kind: 'option', value: { kind: 'nat' } },
      recursion: null,
      body: {
        kind: 'operation',
        opcode: 'list.head',
        typeArguments: [{ kind: 'nat' }],
        arguments: [{ kind: 'variable', index: 0 }],
      },
    };
    const decoded = decodeLeanSemanticProgram(
      program(
        [head],
        [{ declaration: 'Example.first', module: 'Example', role: 'emitted', reason: '' }],
        ['Example.first'],
      ),
    );
    expect(leanToTypeScriptHelperBindings(decoded)).toEqual([
      { opcode: 'list.head', role: 'list-head-option', declaration: 'listHead' },
    ]);

    const subtract = {
      ...head,
      name: 'Example.drop',
      result: { kind: 'nat' },
      parameters: [
        { name: 'left', type: { kind: 'nat' } },
        { name: 'right', type: { kind: 'nat' } },
      ],
      body: {
        kind: 'operation',
        opcode: 'nat.subtract',
        typeArguments: [],
        arguments: [
          { kind: 'variable', index: 1 },
          { kind: 'variable', index: 0 },
        ],
      },
    };
    expect(
      leanToTypeScriptHelperBindings(
        decodeLeanSemanticProgram(
          program(
            [subtract],
            [{ declaration: 'Example.drop', module: 'Example', role: 'emitted', reason: '' }],
            ['Example.drop'],
          ),
        ),
      ),
    ).toEqual([{ opcode: 'nat.subtract', role: 'nat-truncated-subtraction', declaration: 'natSubtract' }]);

    // A program that spends no guarded opcode names no helper, because none is printed for it.
    expect(leanToTypeScriptHelperBindings(decodeLeanSemanticProgram(program()))).toEqual([]);
  });

  test('does not advertise an opcode that a dead let value never emits', () => {
    const ignored = {
      kind: 'function',
      name: 'Example.ignoredSubtraction',
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      parameters: [
        { name: 'left', type: { kind: 'nat' } },
        { name: 'right', type: { kind: 'nat' } },
      ],
      result: { kind: 'boolean' },
      recursion: null,
      body: {
        kind: 'let',
        name: 'x',
        value: {
          kind: 'operation',
          opcode: 'nat.subtract',
          typeArguments: [],
          arguments: [
            { kind: 'variable', index: 1 },
            { kind: 'variable', index: 0 },
          ],
        },
        // The inner value reads x, but z is dead too. Backward liveness must drop both lets, not
        // keep x alive merely because its value appears in an erased inner value.
        body: {
          kind: 'let',
          name: 'y',
          value: { kind: 'variable', index: 0 },
          body: { kind: 'boolean', value: true },
        },
      },
    };
    const decoded = decodeLeanSemanticProgram(
      program(
        [ignored],
        [{ declaration: 'Example.ignoredSubtraction', module: 'Example', role: 'emitted', reason: '' }],
        ['Example.ignoredSubtraction'],
      ),
    );
    expect(referencedRuntimeOpcodes(decoded)).toEqual([]);
    expect(leanToTypeScriptHelperBindings(decoded)).toEqual([]);
    const emitted = emitTypeScriptPackage(decoded, {
      certificates: provenance.certificates,
      ...provenance,
      semantic: { ...provenance.semantic, declarations: ['Example.ignoredSubtraction'] },
    });
    const [module] = emitted.modules;
    if (module === undefined) throw new TypeError('the emitter produced no module');
    expect(module.code).not.toContain('natSubtract');
    expect(module.code).toContain('return true;');
  });

  test('eliminates a deep dead-let chain with one bottom-up liveness pass', () => {
    let body: object = { kind: 'boolean', value: true };
    // Each value would spend natSubtract if emitted. Its two parameter indices shift under every
    // outer let; all 64 are dead, so the liveness set stays empty as it walks back out.
    for (let depth = 63; depth >= 0; depth -= 1) {
      body = {
        kind: 'let',
        name: `dead${depth}`,
        value: {
          kind: 'operation',
          opcode: 'nat.subtract',
          typeArguments: [],
          arguments: [
            { kind: 'variable', index: depth + 1 },
            { kind: 'variable', index: depth },
          ],
        },
        body,
      };
    }
    const ignored = {
      kind: 'function',
      name: 'Example.deepIgnoredSubtraction',
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      parameters: [
        { name: 'left', type: { kind: 'nat' } },
        { name: 'right', type: { kind: 'nat' } },
      ],
      result: { kind: 'boolean' },
      recursion: null,
      body,
    };
    const decoded = decodeLeanSemanticProgram(
      program(
        [ignored],
        [{ declaration: 'Example.deepIgnoredSubtraction', module: 'Example', role: 'emitted', reason: '' }],
        ['Example.deepIgnoredSubtraction'],
      ),
    );
    expect(referencedRuntimeOpcodes(decoded)).toEqual([]);
    expect(leanToTypeScriptHelperBindings(decoded)).toEqual([]);
    const emitted = emitTypeScriptPackage(decoded, {
      certificates: provenance.certificates,
      ...provenance,
      semantic: { ...provenance.semantic, declarations: ['Example.deepIgnoredSubtraction'] },
    });
    const [module] = emitted.modules;
    if (module === undefined) throw new TypeError('the emitter produced no module');
    expect(module.code).not.toContain('natSubtract');
    expect(module.code).not.toContain('const dead');
    expect(module.code).toContain('return true;');
  });

  test('renames a helper the program itself already declares, and reports the new name', () => {
    const listType = { kind: 'list', element: { kind: 'nat' } };
    const collision = {
      kind: 'function',
      name: 'Example.listHead',
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      parameters: [{ name: 'values', type: listType }],
      result: { kind: 'option', value: { kind: 'nat' } },
      recursion: null,
      body: {
        kind: 'operation',
        opcode: 'list.head',
        typeArguments: [{ kind: 'nat' }],
        arguments: [{ kind: 'variable', index: 0 }],
      },
    };
    const decoded = decodeLeanSemanticProgram(
      program(
        [collision],
        [{ declaration: 'Example.listHead', module: 'Example', role: 'emitted', reason: '' }],
        ['Example.listHead'],
      ),
    );
    expect(leanToTypeScriptHelperBindings(decoded)).toEqual([
      { opcode: 'list.head', role: 'list-head-option', declaration: 'listHead$2' },
    ]);
  });
});

describe('Lean semantic IR trust boundary', () => {
  test('accepts its exact serialized schema, and reads a null descriptor as no recursion at all', () => {
    const serialized = JSON.stringify(program());
    // The wire document spells "Lean proved no recursion here" as a literal `null`; the decoded
    // program carries no descriptor, so nothing downstream can confuse an absent discipline with
    // a recorded one.
    const { recursion: _recursion, ...withoutDescriptor } = identityDeclaration;
    expect(decodeLeanSemanticProgram(JSON.parse(serialized))).toEqual(program([withoutDescriptor]));
  });

  test('accepts a structural recursion whose decrease it can restate', () => {
    expect(() => decodeLeanSemanticProgram(recursionProgram())).not.toThrow();
  });

  test('rejects the retired v5 fragment by name rather than reading its termination evidence', () => {
    expect(() => decodeLeanSemanticProgram({ ...program(), fragmentVersion: 'tslean-semantic-typed-v5' })).toThrowError(
      /Lean fragment tslean-semantic-typed-v5 is retired/u,
    );
  });

  test.each([
    ['unknown program field', { ...program(), extra: true }, /semantic program fields must be exactly/u],
    [
      'unknown fragment',
      { ...program(), fragmentVersion: 'tslean-unchecked-v0' },
      /unsupported Lean fragment tslean-unchecked-v0/u,
    ],
    [
      'unbound variable',
      program([{ ...identityDeclaration, body: { kind: 'variable', index: 1 } }]),
      /unbound de Bruijn index 1/u,
    ],
    [
      'unknown call target',
      program([
        {
          ...identityDeclaration,
          body: {
            kind: 'call',
            function: 'Example.missing',
            typeArguments: [],
            arguments: [{ kind: 'variable', index: 0 }],
          },
        },
      ]),
      /references unknown function Example\.missing/u,
    ],
    [
      'expression type mismatch',
      program([
        {
          ...identityDeclaration,
          body: {
            kind: 'variant',
            type: { kind: 'option', value: { kind: 'boolean' } },
            name: 'some',
            arguments: [{ kind: 'variable', index: 0 }],
          },
        },
      ]),
      /has type Option \(Bool\); expected Bool/u,
    ],
    [
      'operation outside the closed opcode registry',
      program([
        {
          ...identityDeclaration,
          body: { kind: 'operation', opcode: 'bool.xor', typeArguments: [], arguments: [] },
        },
      ]),
      /is not a registered runtime opcode: bool\.xor/u,
    ],
    [
      'a free-standing list.first',
      program([
        {
          ...identityDeclaration,
          parameters: [{ name: 'values', type: { kind: 'list', element: { kind: 'boolean' } } }],
          body: {
            kind: 'operation',
            opcode: 'list.first',
            typeArguments: [{ kind: 'boolean' }],
            arguments: [{ kind: 'variable', index: 0 }],
          },
        },
      ]),
      /list\.first is spent by a list match, never named by an operation/u,
    ],
    [
      'a free-standing list.rest',
      program([
        {
          ...identityDeclaration,
          parameters: [{ name: 'values', type: { kind: 'list', element: { kind: 'boolean' } } }],
          result: { kind: 'list', element: { kind: 'boolean' } },
          body: {
            kind: 'operation',
            opcode: 'list.rest',
            typeArguments: [{ kind: 'boolean' }],
            arguments: [{ kind: 'variable', index: 0 }],
          },
        },
      ]),
      /list\.rest is spent by a list match, never named by an operation/u,
    ],
    [
      'operation applied at the wrong operand count',
      program([
        {
          ...identityDeclaration,
          body: {
            kind: 'operation',
            opcode: 'bool.and',
            typeArguments: [],
            arguments: [{ kind: 'variable', index: 0 }],
          },
        },
      ]),
      /passes 1 operands to bool\.and; expected 2/u,
    ],
    [
      'operation at the wrong operand type',
      program([
        {
          ...identityDeclaration,
          body: {
            kind: 'operation',
            opcode: 'nat.add',
            typeArguments: [],
            arguments: [
              { kind: 'variable', index: 0 },
              { kind: 'variable', index: 0 },
            ],
          },
        },
      ]),
      /has type Bool; expected Nat/u,
    ],
    [
      'reserved emitted name',
      program(
        [{ ...identityDeclaration, name: 'Example.default', namespace: 'Example' }],
        [{ ...identityClosure, declaration: 'Example.default' }],
      ),
      /is not a safe TypeScript binding name: default/u,
    ],
    [
      'namespace its own name does not spell',
      program([{ ...identityDeclaration, namespace: 'Elsewhere' }]),
      /claims Lean namespace Elsewhere, which its own name does not spell/u,
    ],
    [
      'colliding emitted names',
      program([identityDeclaration, otherDeclaration], [identityClosure, otherClosure]),
      /Example\.identity.*Other\.identity.*both emit identity/u,
    ],
    [
      'colliding emitted names attributed to the same module',
      program(
        [identityDeclaration, { ...otherDeclaration, module: 'Example' }],
        [identityClosure, { ...otherClosure, module: 'Example' }],
      ),
      /Example\.identity.*Other\.identity.*both emit identity.*both are attributed to Lean module Example/u,
    ],
    [
      'declaration without a declaring module',
      program([
        {
          kind: 'function',
          name: 'Example.identity',
          namespace: 'Example',
          typeParameters: [],
          span: identitySpan,
          parameters: [{ name: 'value', type: { kind: 'boolean' } }],
          result: { kind: 'boolean' },
          recursion: null,
          body: { kind: 'variable', index: 0 },
        },
      ]),
      /declarations\[0\]\.module must be a nonempty string/u,
    ],
    [
      'declaring module outside the Lean module grammar',
      program([{ ...identityDeclaration, module: '1Example' }]),
      /declarations\[0\]\.module is not a Lean module name: 1Example/u,
    ],
    [
      'declaration without a source span',
      program([
        {
          kind: 'function',
          name: 'Example.identity',
          module: 'Example',
          namespace: 'Example',
          typeParameters: [],
          parameters: [{ name: 'value', type: { kind: 'boolean' } }],
          result: { kind: 'boolean' },
          recursion: null,
          body: { kind: 'variable', index: 0 },
        },
      ]),
      /declarations\[0\]\.span must be an object/u,
    ],
    [
      'source span that ends before it starts',
      program([{ ...identityDeclaration, span: { startLine: 9, startColumn: 4, endLine: 8, endColumn: 4 } }]),
      /declarations\[0\]\.span ends before it starts/u,
    ],
    [
      'program without a reachability closure',
      {
        schemaVersion: 1,
        fragmentVersion: LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
        roots: ['Example.identity'],
        declarations: [identityDeclaration],
      },
      /semantic program fields must be exactly closure, declarations, fragmentVersion, roots, schemaVersion/u,
    ],
    [
      'closure out of canonical order',
      program([identityDeclaration, otherDeclaration], [otherClosure, identityClosure]),
      /semantic program closure must be strictly ordered and unique/u,
    ],
    [
      'closure omitting an emitted declaration',
      program([identityDeclaration, otherDeclaration], [identityClosure]),
      /semantic program closure does not record Other\.identity as emitted/u,
    ],
    [
      'emitted closure entry carrying a reason',
      program([identityDeclaration], [{ ...identityClosure, reason: 'emitted through the runtime boundary' }]),
      /closure\[0\]\.reason must be empty exactly for an emitted declaration/u,
    ],
    [
      'erased closure entry without a reason',
      program(
        [identityDeclaration],
        [identityClosure, { declaration: 'Example.proof', module: 'Example', role: 'erased', reason: '' }],
      ),
      /closure\[1\]\.reason must be empty exactly for an emitted declaration/u,
    ],
    [
      'closure disagreeing with the declaring module',
      program([identityDeclaration], [{ ...identityClosure, module: 'Other' }]),
      /semantic program closure disagrees on the module of Example\.identity/u,
    ],
  ])('rejects mutation: %s', (_label, mutation, diagnostic) => {
    expect(() => decodeLeanSemanticProgram(mutation)).toThrowError(diagnostic);
  });
});

describe('Lean semantic IR recursion policy', () => {
  /** A mutual pair over `Example.Tree`, which is the only shape a group descriptor admits. */
  const mutualMember = (name: string, peer: string, recursion: object): object => ({
    kind: 'function',
    name,
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    parameters: [{ name: 'tree', type: treeType }],
    result: { kind: 'nat' },
    recursion,
    body: {
      kind: 'match',
      type: treeType,
      scrutinee: { kind: 'variable', index: 0 },
      cases: [
        { constructor: 'leaf', value: { kind: 'nat', value: '0' } },
        {
          constructor: 'branch',
          value: { kind: 'call', function: peer, typeArguments: [], arguments: [{ kind: 'variable', index: 0 }] },
        },
      ],
    },
  });

  const mutualProgram = (left: object, right: object): object =>
    program(
      [treeDeclaration, left, right],
      [
        treeClosure,
        { declaration: 'Example.even', module: 'Example', role: 'emitted', reason: '' },
        { declaration: 'Example.odd', module: 'Example', role: 'emitted', reason: '' },
      ],
      ['Example.even'],
    );

  test('admits a well-founded recursion on Lean-s own proof, with no restated decrease', () => {
    // A measure the emitted program cannot restate is carried as Lean's evidence: the descriptor
    // names the discipline and nothing else, and the self-call needs no constructor field.
    expect(() =>
      decodeLeanSemanticProgram(
        recursionProgram({
          ...depthDeclaration,
          recursion: { kind: 'wellFounded' },
          body: {
            kind: 'match',
            type: treeType,
            scrutinee: { kind: 'variable', index: 0 },
            cases: [
              { constructor: 'leaf', value: { kind: 'nat', value: '0' } },
              {
                constructor: 'branch',
                value: {
                  kind: 'call',
                  function: 'Example.depth',
                  typeArguments: [],
                  // The parameter itself, which only a well-founded measure can justify.
                  arguments: [{ kind: 'variable', index: 1 }],
                },
              },
            ],
          },
        }),
      ),
    ).not.toThrow();
  });

  test('admits a mutual group both members record identically', () => {
    const group = { kind: 'mutual', group: ['Example.even', 'Example.odd'] };
    expect(() =>
      decodeLeanSemanticProgram(
        mutualProgram(
          mutualMember('Example.even', 'Example.odd', group),
          mutualMember('Example.odd', 'Example.even', group),
        ),
      ),
    ).not.toThrow();
  });

  test.each([
    [
      'a self-call with no recorded recursion',
      recursionProgram(withoutRecursion(depthDeclaration)),
      /Example\.depth calls itself but records no recursion discipline/u,
    ],
    [
      'a structural recursion that does not decrease',
      recursionProgram({
        ...depthDeclaration,
        body: {
          kind: 'match',
          type: treeType,
          scrutinee: { kind: 'variable', index: 0 },
          cases: [
            { constructor: 'leaf', value: { kind: 'nat', value: '0' } },
            {
              constructor: 'branch',
              value: {
                kind: 'call',
                function: 'Example.depth',
                typeArguments: [],
                // Index 1 is the parameter itself, not the constructor field bound at index 0.
                arguments: [{ kind: 'variable', index: 1 }],
              },
            },
          ],
        },
      }),
      /recurses on a value that is not a constructor field of its Example\.Tree argument/u,
    ],
    [
      'a structural recursion on a parameter with no constructors',
      recursionProgram({
        ...depthDeclaration,
        parameters: [{ name: 'tree', type: { kind: 'nat' } }],
        body: { kind: 'nat', value: '0' },
      }),
      /recurses on Nat, which carries no constructors to decrease on/u,
    ],
    [
      'recorded structural recursion with no recursion at all',
      recursionProgram({
        ...depthDeclaration,
        body: {
          kind: 'match',
          type: treeType,
          scrutinee: { kind: 'variable', index: 0 },
          cases: [
            { constructor: 'leaf', value: { kind: 'nat', value: '0' } },
            { constructor: 'branch', value: { kind: 'nat', value: '1' } },
          ],
        },
      }),
      /declares a structural recursion argument but never recurses/u,
    ],
    [
      'a well-founded descriptor over a body that never recurses',
      recursionProgram({
        ...depthDeclaration,
        recursion: { kind: 'wellFounded' },
        body: {
          kind: 'match',
          type: treeType,
          scrutinee: { kind: 'variable', index: 0 },
          cases: [
            { constructor: 'leaf', value: { kind: 'nat', value: '0' } },
            { constructor: 'branch', value: { kind: 'nat', value: '1' } },
          ],
        },
      }),
      /records a wellFounded recursion discipline but never recurses/u,
    ],
    [
      'a structural descriptor naming a parameter the declaration does not declare',
      recursionProgram({ ...depthDeclaration, recursion: { kind: 'structural', parameter: 1 } }),
      /declarations\[1\]\.recursion\.parameter is not one of the declared parameters/u,
    ],
    [
      'a well-founded descriptor carrying a decreasing parameter',
      recursionProgram({ ...depthDeclaration, recursion: { kind: 'wellFounded', parameter: 0 } }),
      /declarations\[1\]\.recursion fields must be exactly kind/u,
    ],
    [
      'a structural descriptor with no decreasing parameter',
      recursionProgram({ ...depthDeclaration, recursion: { kind: 'structural' } }),
      /declarations\[1\]\.recursion fields must be exactly kind, parameter/u,
    ],
    [
      'a v5 termination record where v6 carries a recursion descriptor',
      recursionProgram({
        ...withoutRecursion(depthDeclaration),
        termination: { kind: 'structural', argument: 0, group: ['Example.depth'], equation: 'Example.depth.eq_def' },
      }),
      /declarations\[1\] fields must be exactly .*recursion/u,
    ],
    [
      'an omitted recursion descriptor, which is not the same as a recorded null',
      recursionProgram(Object.fromEntries(Object.entries(depthDeclaration).filter(([key]) => key !== 'recursion'))),
      /declarations\[1\] fields must be exactly .*recursion/u,
    ],
    [
      'a mutual descriptor naming one member',
      recursionProgram({ ...depthDeclaration, recursion: { kind: 'mutual', group: ['Example.depth'] } }),
      /names 1 declaration\(s\); a mutual block has at least two members/u,
    ],
    [
      'a mutual group naming a declaration that was not exported',
      recursionProgram({
        ...depthDeclaration,
        recursion: { kind: 'mutual', group: ['Example.depth', 'Example.height'] },
      }),
      /names Example\.height in its mutual group, which the program does not declare as a function/u,
    ],
    [
      'a mutual pair whose members disagree on the group',
      mutualProgram(
        mutualMember('Example.even', 'Example.odd', { kind: 'mutual', group: ['Example.even', 'Example.odd'] }),
        mutualMember('Example.odd', 'Example.even', { kind: 'mutual', group: ['Example.odd', 'Example.even'] }),
      ),
      /disagree on their mutual group/u,
    ],
    [
      'a recursion that leaves the recorded group',
      mutualProgram(
        mutualMember('Example.even', 'Example.odd', { kind: 'structural', parameter: 0 }),
        mutualMember('Example.odd', 'Example.even', { kind: 'structural', parameter: 0 }),
      ),
      /recurses through Example\.odd, which Lean did not record in its mutual group/u,
    ],
  ])('refuses %s', (_label, mutation, diagnostic) => {
    expect(() => decodeLeanSemanticProgram(mutation)).toThrowError(diagnostic);
  });
});

describe('Lean semantic IR dot-notation evidence', () => {
  const valueType = { kind: 'named', name: 'Example.Config', arguments: [] };
  const configDeclaration = {
    kind: 'record',
    name: 'Example.Config',
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    constructor: 'mk',
    fields: [{ name: 'enabled', type: { kind: 'boolean' } }],
  };
  const methodDeclaration = {
    kind: 'function',
    name: 'Example.Config.read',
    module: 'Example',
    namespace: 'Example.Config',
    typeParameters: [],
    span: identitySpan,
    receiver: { type: 'Example.Config', parameter: 0 },
    parameters: [{ name: 'config', type: valueType }],
    result: { kind: 'boolean' },
    recursion: null,
    body: { kind: 'field', target: { kind: 'variable', index: 0 }, field: 'enabled' },
  };
  const closure = [
    { declaration: 'Example.Config', module: 'Example', role: 'emitted', reason: '' },
    { declaration: 'Example.Config.read', module: 'Example', role: 'emitted', reason: '' },
  ];

  test('accepts a receiver whose namespace, module and parameter type all agree', () => {
    expect(() =>
      decodeLeanSemanticProgram(program([configDeclaration, methodDeclaration], closure, ['Example.Config.read'])),
    ).not.toThrow();
  });

  test.each([
    [
      'a receiver the declaration does not live under',
      { ...methodDeclaration, name: 'Example.read', namespace: 'Example' },
      [
        { declaration: 'Example.Config', module: 'Example', role: 'emitted', reason: '' },
        { declaration: 'Example.read', module: 'Example', role: 'emitted', reason: '' },
      ],
      /claims Example\.Config as its receiver but is owned by namespace Example/u,
    ],
    [
      'a receiver parameter that carries another type',
      {
        ...methodDeclaration,
        parameters: [{ name: 'config', type: { kind: 'boolean' } }],
        body: { kind: 'variable', index: 0 },
      },
      closure,
      /receiver parameter has type Bool; dot notation requires Example\.Config/u,
    ],
    [
      'a receiver declared by another Lean module',
      { ...methodDeclaration, module: 'Elsewhere' },
      [
        { declaration: 'Example.Config', module: 'Example', role: 'emitted', reason: '' },
        { declaration: 'Example.Config.read', module: 'Elsewhere', role: 'emitted', reason: '' },
      ],
      /declared by Elsewhere but its receiver Example\.Config is declared by Example/u,
    ],
    [
      'a receiver that is not an exported data type',
      { ...methodDeclaration, receiver: { type: 'Example.Missing', parameter: 0 } },
      closure,
      /claims a receiver Example\.Missing that is not an exported data type/u,
    ],
  ])('refuses %s', (_label, declaration, entries, diagnostic) => {
    expect(() => decodeLeanSemanticProgram(program([configDeclaration, declaration], entries, []))).toThrowError(
      diagnostic,
    );
  });
});

describe('Lean semantic IR boundary', () => {
  const boxDeclaration = {
    kind: 'record',
    name: 'Example.Box',
    module: 'Example',
    namespace: 'Example',
    typeParameters: ['payload'],
    span: identitySpan,
    constructor: 'mk',
    fields: [{ name: 'held', type: { kind: 'parameter', index: 0 } }],
  };
  const boxClosure = { declaration: 'Example.Box', module: 'Example', role: 'emitted', reason: '' };

  test.each([
    [
      'a polymorphic root',
      program(
        [
          {
            ...identityDeclaration,
            typeParameters: ['value'],
            parameters: [{ name: 'value', type: { kind: 'parameter', index: 0 } }],
            result: { kind: 'parameter', index: 0 },
          },
        ],
        [identityClosure],
      ),
      /is polymorphic in 1 type parameter\(s\); a root's boundary is monomorphic/u,
    ],
    [
      'a root taking an arrow',
      program([
        {
          ...identityDeclaration,
          parameters: [
            {
              name: 'step',
              type: { kind: 'function', parameters: [{ kind: 'boolean' }], result: { kind: 'boolean' } },
            },
          ],
          body: {
            kind: 'apply',
            target: { kind: 'variable', index: 0 },
            arguments: [{ kind: 'boolean', value: true }],
          },
        },
      ]),
      /parameter 0: an arrow has no serialized form/u,
    ],
    [
      'a root returning a generic instantiation',
      program(
        [
          boxDeclaration,
          {
            ...identityDeclaration,
            result: { kind: 'named', name: 'Example.Box', arguments: [{ kind: 'boolean' }] },
            body: {
              kind: 'record',
              type: { kind: 'named', name: 'Example.Box', arguments: [{ kind: 'boolean' }] },
              fields: [{ name: 'held', value: { kind: 'variable', index: 0 } }],
            },
          },
        ],
        [boxClosure, identityClosure],
      ),
      /result: Example\.Box \(Bool\) has no data image; wrap it in a monomorphic structure/u,
    ],
  ])('refuses %s', (_label, mutation, diagnostic) => {
    expect(() => decodeLeanSemanticProgram(mutation)).toThrowError(diagnostic);
  });
});

describe('Lean semantic IR refusals with no representation', () => {
  test.each([
    [
      'a match on Nat',
      program([
        {
          ...identityDeclaration,
          parameters: [{ name: 'value', type: { kind: 'nat' } }],
          body: {
            kind: 'match',
            type: { kind: 'nat' },
            scrutinee: { kind: 'variable', index: 0 },
            cases: [{ constructor: 'zero', value: { kind: 'boolean', value: true } }],
          },
        },
      ]),
      /matches a Nat; decide it with nat\.equals, nat\.less or nat\.lessOrEqual/u,
    ],
    [
      'a Nat built as a constructor',
      program([
        {
          ...identityDeclaration,
          result: { kind: 'nat' },
          body: { kind: 'variant', type: { kind: 'nat' }, name: 'succ', arguments: [] },
        },
      ]),
      /constructs a Nat; a Nat arrives as a literal or through nat\.successor/u,
    ],
    [
      'an arrow returning an arrow',
      program([
        {
          ...identityDeclaration,
          parameters: [
            {
              name: 'step',
              type: {
                kind: 'function',
                parameters: [{ kind: 'boolean' }],
                result: { kind: 'function', parameters: [{ kind: 'boolean' }], result: { kind: 'boolean' } },
              },
            },
          ],
        },
      ]),
      /returns an arrow; a function value is admitted at its full Lean arity/u,
    ],
    [
      'a generic type applied at the wrong arity',
      program(
        [
          {
            kind: 'record',
            name: 'Example.Box',
            module: 'Example',
            namespace: 'Example',
            typeParameters: ['payload'],
            span: identitySpan,
            constructor: 'mk',
            fields: [{ name: 'held', type: { kind: 'parameter', index: 0 } }],
          },
          {
            ...identityDeclaration,
            parameters: [{ name: 'box', type: { kind: 'named', name: 'Example.Box', arguments: [] } }],
            body: { kind: 'boolean', value: true },
          },
        ],
        [{ declaration: 'Example.Box', module: 'Example', role: 'emitted', reason: '' }, identityClosure],
      ),
      /applies Example\.Box to 0 type arguments; it declares 1/u,
    ],
    [
      'a type parameter no declaration binds',
      program([{ ...identityDeclaration, result: { kind: 'parameter', index: 0 } }]),
      /references type parameter 0, which is not declared/u,
    ],
    [
      'a match that does not decide every constructor in declaration order',
      program(
        [
          treeDeclaration,
          {
            ...identityDeclaration,
            parameters: [{ name: 'tree', type: treeType }],
            body: {
              kind: 'match',
              type: treeType,
              scrutinee: { kind: 'variable', index: 0 },
              cases: [
                { constructor: 'branch', value: { kind: 'boolean', value: true } },
                { constructor: 'leaf', value: { kind: 'boolean', value: false } },
              ],
            },
          },
        ],
        [treeClosure, identityClosure],
      ),
      /does not decide every constructor of Example\.Tree exactly once in declaration order/u,
    ],
  ])('refuses %s', (_label, mutation, diagnostic) => {
    expect(() => decodeLeanSemanticProgram(mutation)).toThrowError(diagnostic);
  });
});

describe('emission is the rooted export closure', () => {
  // `storeGet` is a host boundary: the substrate implements it, so its reference body is never
  // printed. `shape` is reachable only by walking that body, which makes it dead in the emitted
  // tree while it stays declared for the model to prove the reference against.
  const shape = {
    kind: 'function',
    name: 'Example.shape',
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    parameters: [{ name: 'value', type: { kind: 'nat' } }],
    result: { kind: 'nat' },
    recursion: null,
    body: { kind: 'variable', index: 0 },
  };
  const storeGet = {
    kind: 'foreign',
    name: 'Example.storeGet',
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    host: 'host.store.get',
    parameters: [{ name: 'store', type: { kind: 'nat' } }],
    result: { kind: 'nat' },
    reference: {
      kind: 'call',
      function: 'Example.shape',
      typeArguments: [],
      arguments: [{ kind: 'variable', index: 0 }],
    },
  };
  const caller = {
    kind: 'function',
    name: 'Example.caller',
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    parameters: [{ name: 'value', type: { kind: 'nat' } }],
    result: { kind: 'nat' },
    recursion: null,
    body: { kind: 'call', function: 'Example.shape', typeArguments: [], arguments: [{ kind: 'variable', index: 0 }] },
  };
  const entry = (name: string) => ({ declaration: name, module: 'Example', role: 'emitted', reason: '' });
  const emit = (declarations: readonly object[], roots: readonly string[]) =>
    emitTypeScriptPackage(
      decodeLeanSemanticProgram(
        program(
          declarations,
          declarations
            .map((declaration) => entry((declaration as { name: string }).name))
            .sort((left, right) => (left.declaration < right.declaration ? -1 : 1)),
          roots,
        ),
      ),
      { ...provenance, semantic: { ...provenance.semantic, declarations: [...roots].sort() } },
    );

  test('a helper only a host reference body reaches is declared but not printed', () => {
    const emitted = emit([shape, storeGet], ['Example.storeGet']);
    const code = emitted.modules.map((module) => module.code).join('\n');
    // The boundary itself is reachable, so it is imported and re-exported.
    expect(code).toContain('export { storeGet };');
    // The helper is not: nothing printed can reach it, so printing it would be dead code the
    // generated package's own type check rejects.
    expect(code).not.toContain('function shape');
  });

  test('the same helper is printed when printed code also reaches it', () => {
    const emitted = emit([shape, storeGet, caller], ['Example.storeGet', 'Example.caller']);
    const code = emitted.modules.map((module) => module.code).join('\n');
    expect(code).toContain('export { storeGet };');
    // Reached through `caller`, which is printed, so the prune must not take it: the closure is
    // over the emitted tree, not over the host boundary alone.
    expect(code).toContain('function shape');
    expect(code).toContain('export function caller');
  });
});

/**
 * The statement form a payload-carrying `match` reaches the target as, byte for byte, beside the
 * documents that shape is refused for. `Compile.returnBody` lowers this shape to
 * `Target.Body.branch` and `Preservation.branchBody` proves it refines the source match, so what is
 * pinned here is the correspondence between those bytes and the term the theorem is about.
 */
describe('a payload-carrying match in return position emits the modeled statement form', () => {
  const jsonType = { kind: 'json' } as const;
  const leaseType = { kind: 'named', name: 'Example.Lease', arguments: [] } as const;
  const optionType = { kind: 'option', value: { kind: 'boolean' } } as const;

  const leaseEnum = {
    kind: 'enum',
    name: 'Example.Lease',
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    constructors: [
      { name: 'unheld', fields: [] },
      {
        name: 'held',
        fields: [
          { name: 'owner', type: { kind: 'string' } },
          { name: 'exclusive', type: { kind: 'boolean' } },
        ],
      },
    ],
  };

  /** Every `JsonValue` constructor decided once, in declaration order; `bool` reads its payload. */
  const describeJson = {
    kind: 'function',
    name: 'Example.describeJson',
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    parameters: [{ name: 'value', type: jsonType }],
    result: { kind: 'boolean' },
    recursion: null,
    body: {
      kind: 'match',
      type: jsonType,
      scrutinee: { kind: 'variable', index: 0 },
      cases: [
        { constructor: 'null', value: { kind: 'boolean', value: false } },
        { constructor: 'bool', value: { kind: 'variable', index: 0 } },
        { constructor: 'int', value: { kind: 'boolean', value: false } },
        { constructor: 'string', value: { kind: 'boolean', value: false } },
        { constructor: 'array', value: { kind: 'boolean', value: false } },
        { constructor: 'object', value: { kind: 'boolean', value: false } },
      ],
    },
  };

  /** A two-field alternative that reads both fields. */
  const readsBoth = {
    kind: 'function',
    name: 'Example.readsBoth',
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    parameters: [{ name: 'lease', type: leaseType }],
    result: { kind: 'boolean' },
    recursion: null,
    body: {
      kind: 'match',
      type: leaseType,
      scrutinee: { kind: 'variable', index: 0 },
      cases: [
        { constructor: 'unheld', value: { kind: 'boolean', value: false } },
        {
          constructor: 'held',
          value: {
            kind: 'operation',
            opcode: 'bool.and',
            typeArguments: [],
            arguments: [
              { kind: 'variable', index: 0 },
              {
                kind: 'operation',
                opcode: 'string.isEmpty',
                typeArguments: [],
                arguments: [{ kind: 'variable', index: 1 }],
              },
            ],
          },
        },
      ],
    },
  };

  /** A two-field alternative that reads neither field, and an enclosing binder above it. */
  const capture = {
    kind: 'function',
    name: 'Example.capture',
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    parameters: [
      { name: 'lease', type: leaseType },
      { name: 'fallback', type: { kind: 'boolean' } },
    ],
    result: { kind: 'boolean' },
    recursion: null,
    body: {
      kind: 'match',
      type: leaseType,
      scrutinee: { kind: 'variable', index: 1 },
      cases: [
        { constructor: 'unheld', value: { kind: 'variable', index: 0 } },
        { constructor: 'held', value: { kind: 'variable', index: 2 } },
      ],
    },
  };

  /** A match inside an alternative of another match. */
  const nested = {
    kind: 'function',
    name: 'Example.nested',
    module: 'Example',
    namespace: 'Example',
    typeParameters: [],
    span: identitySpan,
    parameters: [
      { name: 'flag', type: optionType },
      { name: 'value', type: jsonType },
    ],
    result: { kind: 'boolean' },
    recursion: null,
    body: {
      kind: 'match',
      type: jsonType,
      scrutinee: { kind: 'variable', index: 0 },
      cases: [
        {
          constructor: 'null',
          value: {
            kind: 'match',
            type: optionType,
            scrutinee: { kind: 'variable', index: 1 },
            cases: [
              { constructor: 'none', value: { kind: 'boolean', value: false } },
              { constructor: 'some', value: { kind: 'variable', index: 0 } },
            ],
          },
        },
        { constructor: 'bool', value: { kind: 'variable', index: 0 } },
        { constructor: 'int', value: { kind: 'boolean', value: false } },
        { constructor: 'string', value: { kind: 'boolean', value: false } },
        { constructor: 'array', value: { kind: 'boolean', value: false } },
        { constructor: 'object', value: { kind: 'boolean', value: false } },
      ],
    },
  };

  const decode = (declarations: readonly { readonly name: string }[], roots: readonly string[]) =>
    decodeLeanSemanticProgram(
      program(
        declarations,
        declarations
          .map((declaration) => ({
            declaration: declaration.name,
            module: 'Example',
            role: 'emitted',
            reason: '',
          }))
          .sort((left, right) => (left.declaration < right.declaration ? -1 : 1)),
        roots,
      ),
    );
  const emit = (declarations: readonly { readonly name: string }[], roots: readonly string[]) =>
    emitTypeScriptPackage(decode(declarations, roots), {
      ...provenance,
      semantic: { ...provenance.semantic, declarations: [...roots].sort() },
    })
      .modules.map((module) => module.code)
      .join('\n');

  test('a JsonValue match emits one test per alternative in declaration order, the last unconditional', () => {
    // Byte for byte the statements `Compile.returnBody` lowers to
    // `.branch (.binding 0) .tagged [("null", [], …), ("bool", ["value"], …), …]`: one `kind` test
    // per alternative, the payload named by a `const` inside the branch that decided it, and no test
    // for `object`, whose statements are the narrowed remainder.
    expect(emit([describeJson], ['Example.describeJson'])).toContain(
      [
        'export function describeJson(value: JsonValue): boolean {',
        '    if (value.kind === "null") {',
        '        return false;',
        '    }',
        '    if (value.kind === "bool") {',
        '        const value$2 = value.value;',
        '        return value$2;',
        '    }',
        '    if (value.kind === "int") {',
        '        return false;',
        '    }',
        '    if (value.kind === "string") {',
        '        return false;',
        '    }',
        '    if (value.kind === "array") {',
        '        return false;',
        '    }',
        '    return false;',
        '}',
      ].join('\n'),
    );
  });

  test('a two-field alternative names its fields in declaration order', () => {
    // The `const` run is `owner` then `exclusive`, so the innermost binding is the *last* field:
    // de Bruijn index 0 is `exclusive` and index 1 is `owner`, which is the scope
    // `Source.evalCases` binds and the one `Target.readPayload` reverses onto.
    expect(emit([leaseEnum, readsBoth], ['Example.readsBoth'])).toContain(
      [
        'export function readsBoth(lease: Lease): boolean {',
        '    if (lease.kind === "unheld") {',
        '        return false;',
        '    }',
        '    const owner = lease.owner;',
        '    const exclusive = lease.exclusive;',
        '    return exclusive && owner.length === 0;',
        '}',
      ].join('\n'),
    );
  });

  test('an alternative reading neither field names none, and the enclosing binder keeps its slot', () => {
    // The liveness prune drops a `const` no alternative reads, and the binder it would have named
    // keeps its de Bruijn position, so index 2 still resolves to `fallback` rather than to the
    // scrutinee. The model names every declared field instead; the difference is unobservable,
    // because the initializer it drops is an own data-property read, which
    // `Tests.readPayload_changes_no_state` states.
    expect(emit([leaseEnum, capture], ['Example.capture'])).toContain(
      [
        'export function capture(lease: Lease, fallback: boolean): boolean {',
        '    if (lease.kind === "unheld") {',
        '        return fallback;',
        '    }',
        '    return fallback;',
        '}',
      ].join('\n'),
    );
  });

  test('a match inside an alternative emits the nested statement form', () => {
    // The inner match is statements inside the branch that decided the outer one, which is the
    // nested `.branch` inside an arm body that `Tests.nested_match_lowers` pins.
    expect(emit([nested], ['Example.nested'])).toContain(
      [
        'export function nested(flag: Option<boolean>, value: JsonValue): boolean {',
        '    if (value.kind === "null") {',
        '        if (flag.kind === "none") {',
        '            return false;',
        '        }',
        '        const value$2 = flag.value;',
        '        return value$2;',
        '    }',
        '    if (value.kind === "bool") {',
        '        const value$3 = value.value;',
        '        return value$3;',
        '    }',
      ].join('\n'),
    );
  });

  test('arms out of declaration order are refused', () => {
    // The emitted chain reads each arm's payload field list positionally out of the declaration, so
    // a drifted order would bind `held`'s payload under `unheld`'s branch. `Compile.decidesInOrder`
    // refuses the same document, and `semantics-drifted-arm-order.lean` refuses the refinement.
    const drifted = {
      ...readsBoth,
      body: { ...readsBoth.body, cases: [readsBoth.body.cases[1], readsBoth.body.cases[0]] },
    };
    expect(() => decode([leaseEnum, drifted], ['Example.readsBoth'])).toThrow(
      'does not decide every constructor of Example.Lease exactly once in declaration order',
    );
  });

  test('a missing alternative is refused', () => {
    const partial = { ...readsBoth, body: { ...readsBoth.body, cases: [readsBoth.body.cases[0]] } };
    expect(() => decode([leaseEnum, partial], ['Example.readsBoth'])).toThrow(
      'does not decide every constructor of Example.Lease exactly once in declaration order',
    );
  });

  test('two arms deciding one constructor are refused', () => {
    const repeated = {
      ...readsBoth,
      body: { ...readsBoth.body, cases: [readsBoth.body.cases[0], readsBoth.body.cases[0]] },
    };
    expect(() => decode([leaseEnum, repeated], ['Example.readsBoth'])).toThrow(
      'body.cases contains duplicates',
    );
  });
});
