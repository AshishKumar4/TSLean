import { describe, expect, test } from 'vitest';
import {
  decodeLeanSemanticProgram,
  LEAN_RUNTIME_ASSUMPTIONS,
  LEAN_RUNTIME_OPCODES,
  LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
  referencedRuntimeOpcodes,
  type LeanOpcode,
} from '../src/lean-to-typescript/ir.js';
import { createHash } from 'node:crypto';
import ts from 'typescript';
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
  termination: { kind: 'structural', argument: 0, group: ['Example.depth'], equation: 'Example.depth.eq_def' },
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

/** The same declaration with no recorded termination, which is what a guessed recursion looks like. */
function withoutTermination(declaration: typeof depthDeclaration): object {
  const { termination: _termination, ...rest } = declaration;
  return rest;
}

function recursionProgram(declaration: object = depthDeclaration): object {
  return program([treeDeclaration, declaration], [treeClosure, depthClosure], ['Example.depth']);
}

/** Provenance is not under test in the emitter cases below; only the emitted names are. */
const inputClosure = (inputs: readonly { kind: string; identity: string; sha256: string }[]): string =>
  `sha256:${createHash('sha256').update(JSON.stringify(inputs)).digest('hex')}`;
const semanticInputs = [
  { kind: 'lean-source' as const, identity: 'source:Example', sha256: `sha256:${'0'.repeat(64)}` },
];
const environmentInputs = [
  { kind: 'lean-module' as const, identity: 'module:Example', sha256: `sha256:${'0'.repeat(64)}` },
];
const provenance = {
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
  test('is total, closed, and names one Lean symbol and one emitted form per opcode', () => {
    const opcodes = Object.keys(LEAN_RUNTIME_OPCODES) as readonly LeanOpcode[];
    expect(opcodes.length).toBe(26);
    for (const opcode of opcodes) {
      const row = LEAN_RUNTIME_OPCODES[opcode];
      expect(row.opcode).toBe(opcode);
      expect(row.leanSymbol.length).toBeGreaterThan(0);
      expect(row.runtimeForm.length).toBeGreaterThan(0);
      expect(row.modelTheorem).toMatch(/^TSLean\.LeanToTypeScript\.Semantics\.Opcode\.[A-Za-z]+$/u);
      expect(row.assumptions.length).toBeGreaterThan(0);
      for (const assumption of row.assumptions) {
        expect(LEAN_RUNTIME_ASSUMPTIONS[assumption]).toBeTypeOf('string');
      }
    }
    expect(LEAN_RUNTIME_OPCODES['nat.subtract'].runtimeSymbol).toBe('helper:nat-truncated-subtraction');
    expect(LEAN_RUNTIME_OPCODES['nat.subtract'].components).toEqual([
      'inline:nat.less',
      'conditional:select',
      'primitive:bigint.subtract',
    ]);
    expect(LEAN_RUNTIME_OPCODES['list.head'].runtimeSymbol).toBe('helper:list-head-option');
    expect(LEAN_RUNTIME_OPCODES['list.head'].components).toEqual([
      'inline:list.isEmpty',
      'inline:list.first',
      'conditional:select',
      'representation:option.tagged-option',
    ]);
    expect(LEAN_RUNTIME_OPCODES['bool.and'].runtimeSymbol).toBe('inline:bool.and');
    expect(LEAN_RUNTIME_OPCODES['bool.and'].components).toBeUndefined();
    // Every model theorem is distinct, so two opcodes can never share one proof obligation.
    expect(new Set(opcodes.map((opcode) => LEAN_RUNTIME_OPCODES[opcode].modelTheorem)).size).toBe(opcodes.length);
    expect(new Set(Object.keys(LEAN_RUNTIME_ASSUMPTIONS)).size).toBe(9);
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
      termination: { kind: 'structural', argument: 0, group: ['Example.total'], equation: 'Example.total.eq_def' },
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
      ts.factory.createClassDeclaration([ts.factory.createModifier(ts.SyntaxKind.ExportKeyword)], 'A', undefined, undefined, []),
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
        ts.factory.createParameterDeclaration(undefined, undefined, 'left', undefined, ts.factory.createTypeReferenceNode('A')),
        ts.factory.createParameterDeclaration(undefined, undefined, 'right', undefined, ts.factory.createTypeReferenceNode('A')),
      ],
      ts.factory.createKeywordTypeNode(ts.SyntaxKind.BooleanKeyword),
      ts.factory.createBlock(
        [
          ts.factory.createVariableStatement(
            undefined,
            ts.factory.createVariableDeclarationList(
              [ts.factory.createVariableDeclaration('codeUnit', undefined, undefined, ts.factory.createNumericLiteral(0))],
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
  test('accepts its exact serialized schema', () => {
    const serialized = JSON.stringify(program());
    expect(decodeLeanSemanticProgram(JSON.parse(serialized))).toEqual(program());
  });

  test('accepts a structural recursion whose decrease it can restate', () => {
    expect(() => decodeLeanSemanticProgram(recursionProgram())).not.toThrow();
  });

  test('accepts a recursive group both members record identically', () => {
    const member = (name: string, peer: string): object => ({
      kind: 'function',
      name,
      module: 'Example',
      namespace: 'Example',
      typeParameters: [],
      span: identitySpan,
      parameters: [{ name: 'tree', type: treeType }],
      result: { kind: 'nat' },
      termination: {
        kind: 'structural',
        argument: 0,
        group: ['Example.even', 'Example.odd'],
        equation: `${name}.eq_def`,
      },
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
    const declarations = [treeDeclaration, member('Example.even', 'Example.odd'), member('Example.odd', 'Example.even')];
    const closure = [
      { declaration: 'Example.Tree', module: 'Example', role: 'emitted', reason: '' },
      { declaration: 'Example.even', module: 'Example', role: 'emitted', reason: '' },
      { declaration: 'Example.odd', module: 'Example', role: 'emitted', reason: '' },
    ];
    expect(() => decodeLeanSemanticProgram(program(declarations, closure, ['Example.even']))).not.toThrow();
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

describe('Lean semantic IR termination policy', () => {
  test.each([
    [
      'a self-call with no recorded termination',
      recursionProgram(withoutTermination(depthDeclaration)),
      /Example\.depth calls itself without recorded termination evidence/u,
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
      'recorded termination with no recursion at all',
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
      'a group naming a declaration that was not exported',
      recursionProgram({
        ...depthDeclaration,
        termination: {
          kind: 'structural',
          argument: 0,
          group: ['Example.depth', 'Example.height'],
          equation: 'Example.depth.eq_def',
        },
      }),
      /names Example\.height in its recursive group, which is not an exported function/u,
    ],
    [
      'well-founded recursion carrying a decreasing argument',
      recursionProgram({
        ...depthDeclaration,
        termination: {
          kind: 'wellFounded',
          argument: 0,
          group: ['Example.depth'],
          equation: 'Example.depth.eq_def',
        },
      }),
      /records a decreasing argument for well-founded recursion/u,
    ],
    [
      'structural recursion with no decreasing argument',
      recursionProgram({
        ...depthDeclaration,
        termination: { kind: 'structural', group: ['Example.depth'], equation: 'Example.depth.eq_def' },
      }),
      /records structural recursion without a decreasing argument/u,
    ],
    [
      'a termination record with no unfolding equation',
      recursionProgram({
        ...depthDeclaration,
        termination: { kind: 'structural', argument: 0, group: ['Example.depth'] },
      }),
      /termination fields must be exactly equation, group, kind with optional argument/u,
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
    body: { kind: 'field', target: { kind: 'variable', index: 0 }, field: 'enabled' },
  };
  const closure = [
    { declaration: 'Example.Config', module: 'Example', role: 'emitted', reason: '' },
    { declaration: 'Example.Config.read', module: 'Example', role: 'emitted', reason: '' },
  ];

  test('accepts a receiver whose namespace, module and parameter type all agree', () => {
    expect(() =>
      decodeLeanSemanticProgram(
        program([configDeclaration, methodDeclaration], closure, ['Example.Config.read']),
      ),
    ).not.toThrow();
  });

  test.each([
    [
      'a receiver the declaration does not live under',
      { ...methodDeclaration, name: 'Example.read', namespace: 'Example' },
      [{ declaration: 'Example.Config', module: 'Example', role: 'emitted', reason: '' }, { declaration: 'Example.read', module: 'Example', role: 'emitted', reason: '' }],
      /claims Example\.Config as its receiver but is owned by namespace Example/u,
    ],
    [
      'a receiver parameter that carries another type',
      { ...methodDeclaration, parameters: [{ name: 'config', type: { kind: 'boolean' } }], body: { kind: 'variable', index: 0 } },
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
    expect(() =>
      decodeLeanSemanticProgram(program([configDeclaration, declaration], entries, [])),
    ).toThrowError(diagnostic);
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
          parameters: [{ name: 'step', type: { kind: 'function', parameters: [{ kind: 'boolean' }], result: { kind: 'boolean' } } }],
          body: { kind: 'apply', target: { kind: 'variable', index: 0 }, arguments: [{ kind: 'boolean', value: true }] },
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
      program([
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
      ], [{ declaration: 'Example.Box', module: 'Example', role: 'emitted', reason: '' }, identityClosure]),
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
