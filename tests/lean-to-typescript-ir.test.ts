import { describe, expect, test } from 'vitest';
import { decodeLeanSemanticProgram, LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION } from '../src/lean-to-typescript/ir.js';

const identitySpan = { startLine: 2, startColumn: 0, endLine: 2, endColumn: 46 };

const identityDeclaration = {
  kind: 'function',
  name: 'Example.identity',
  module: 'Example',
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
  span: identitySpan,
  fields: [],
};

const otherClosure = { declaration: 'Other.identity', module: 'Other', role: 'emitted', reason: '' };

function program(
  declarations: readonly object[] = [identityDeclaration],
  closure: readonly object[] = [identityClosure],
): object {
  return {
    schemaVersion: 1,
    fragmentVersion: LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
    roots: ['Example.identity'],
    closure,
    declarations,
  };
}

describe('Lean semantic IR trust boundary', () => {
  test('accepts its exact serialized schema', () => {
    const serialized = JSON.stringify(program());
    expect(decodeLeanSemanticProgram(JSON.parse(serialized))).toEqual(program());
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
          body: { kind: 'call', function: 'Example.missing', arguments: [{ kind: 'variable', index: 0 }] },
        },
      ]),
      /references unknown function Example\.missing/u,
    ],
    [
      'expression type mismatch',
      program([{ ...identityDeclaration, body: { kind: 'some', value: { kind: 'variable', index: 0 } } }]),
      /has type Option \(Bool\); expected Bool/u,
    ],
    [
      'reserved emitted name',
      program(
        [{ ...identityDeclaration, name: 'Example.default' }],
        [{ ...identityClosure, declaration: 'Example.default' }],
      ),
      /is not a safe TypeScript binding name: default/u,
    ],
    [
      'colliding emitted names',
      program([identityDeclaration, otherDeclaration], [identityClosure, otherClosure]),
      /Example\.identity.*Other\.identity.*both emit identity/u,
    ],
    [
      'declaration without a declaring module',
      program([
        {
          kind: 'function',
          name: 'Example.identity',
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
