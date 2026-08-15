import { describe, expect, test } from 'vitest';
import { decodeLeanSemanticProgram, LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION } from '../src/lean-to-typescript/ir.js';

const identityDeclaration = {
  kind: 'function',
  name: 'Example.identity',
  parameters: [{ name: 'value', type: { kind: 'boolean' } }],
  result: { kind: 'boolean' },
  body: { kind: 'variable', index: 0 },
};

function program(declarations: readonly object[] = [identityDeclaration]): object {
  return {
    schemaVersion: 1,
    fragmentVersion: LEAN_TO_TYPESCRIPT_FRAGMENT_VERSION,
    roots: ['Example.identity'],
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
      program([{ ...identityDeclaration, name: 'Example.default' }]),
      /is not a safe TypeScript binding name: default/u,
    ],
    [
      'colliding emitted names',
      program([
        identityDeclaration,
        {
          kind: 'record',
          name: 'Other.identity',
          fields: [],
        },
      ]),
      /TypeScript declaration names contains duplicates/u,
    ],
  ])('rejects mutation: %s', (_label, mutation, diagnostic) => {
    expect(() => decodeLeanSemanticProgram(mutation)).toThrowError(diagnostic);
  });
});
