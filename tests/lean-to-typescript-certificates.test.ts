import { describe, expect, test } from 'vitest';
import {
  assertRuntimeCertificateBindings,
  assertRuntimeOpcodeCertificates,
  bindRuntimeSymbol,
  certificateForOpcode,
  loadRuntimeCertificateRegistry,
  runtimeBodyDigest,
  runtimeDeclarationDigest,
  RuntimeCertificateUnresolvedError,
  type RuntimeCertificateCatalog,
} from '../src/lean-to-typescript/certificates.js';
import { inlineOperationForms } from '../src/lean-to-typescript/emitter.js';

const { catalog, sha256: registrySha256 } = loadRuntimeCertificateRegistry();

describe('Lean-to-TypeScript runtime certificates', () => {
  test('reads the landed registry as the only declaration source', () => {
    expect(registrySha256).toMatch(/^sha256:[0-9a-f]{64}$/u);
    expect(catalog.certificates.length).toBeGreaterThan(0);
    expect(catalog.assumptions.length).toBeGreaterThan(0);

    for (const certificate of catalog.certificates) {
      expect(certificate.relation).toBe('source = model');
      expect(certificate.runtimeSymbol).toMatch(/^(?:inline|helper):/u);
      expect(certificate.assumptions.length).toBeGreaterThan(0);
      for (const id of certificate.assumptions) {
        expect(catalog.assumptions.some((assumption) => assumption.id === id)).toBe(true);
      }
    }
    for (const assumption of catalog.assumptions) {
      expect(assumption.sourceArtifact).toBe('spec/semantics/ecma262-2025.html');
      expect(assumption.clauses.every((clause) => clause.startsWith('sec-'))).toBe(true);
      expect(assumption.coverage.length).toBeGreaterThan(0);
    }
  });

  test('refuses an opcode with no certificate, no assumption, or an unregistered assumption', () => {
    const [certified] = catalog.certificates;
    if (certified === undefined) throw new TypeError('the registry certifies no opcode');

    expect(() => assertRuntimeOpcodeCertificates([certified.opcode], catalog)).not.toThrow();
    expect(() => assertRuntimeOpcodeCertificates(['nat.uncertified'], catalog)).toThrowError(
      RuntimeCertificateUnresolvedError,
    );
    expect(() => assertRuntimeOpcodeCertificates(['nat.uncertified'], catalog)).toThrowError(
      'runtime-certificate-unresolved: nat.uncertified: no Lean certificate names this opcode',
    );

    const withoutAssumptions: RuntimeCertificateCatalog = {
      ...catalog,
      certificates: catalog.certificates.map((certificate) => ({ ...certificate, assumptions: [] })),
    };
    expect(() => assertRuntimeOpcodeCertificates([certified.opcode], withoutAssumptions)).toThrowError(
      `runtime-certificate-unresolved: ${certified.opcode}: certificate names no external assumption`,
    );

    const withoutRecords: RuntimeCertificateCatalog = { ...catalog, assumptions: [] };
    expect(() => assertRuntimeOpcodeCertificates([certified.opcode], withoutRecords)).toThrowError(
      /has no catalog record/u,
    );
  });

  test('binds an inline form, an allocated helper declaration, and refuses anything unemitted', () => {
    const body =
      'export function natSubtract$2(left: bigint, right: bigint): bigint {\n  return left < right ? 0n : left - right;\n}\n';
    const context = {
      helperDeclarations: new Map([['nat-truncated-subtraction', 'natSubtract$2']]),
      inlineForms: new Map([['nat.add', 'left + right']]),
      bodies: [body],
    };

    expect(bindRuntimeSymbol('inline:nat.add', context)).toEqual({
      kind: 'inline',
      form: 'left + right',
      digest: runtimeBodyDigest('left + right'),
    });
    expect(bindRuntimeSymbol('helper:nat-truncated-subtraction', context)).toEqual({
      kind: 'declaration',
      declaration: 'natSubtract$2',
      digest: runtimeDeclarationDigest('natSubtract$2', body),
    });
    expect(() => bindRuntimeSymbol('inline:list.map', context)).toThrowError(
      'runtime certificate names an unemitted inline form: list.map',
    );
    expect(() => bindRuntimeSymbol('helper:list-head-option', context)).toThrowError(
      'runtime certificate names an unprinted helper role: list-head-option',
    );
    expect(() => bindRuntimeSymbol('macro:whatever', context)).toThrowError(
      'runtime certificate names an unknown symbol kind: macro',
    );
  });

  test('refuses a recorded binding that drifts from the registry or from emitted bytes', () => {
    const inline = catalog.certificates.find((certificate) => certificate.runtimeSymbol.startsWith('inline:'));
    if (inline === undefined) throw new TypeError('the registry certifies no inline opcode');
    const honest = {
      opcode: inline.opcode,
      runtimeSymbol: inline.runtimeSymbol,
      declaration: '',
      runtimeBodySha256: runtimeBodyDigest(inline.emittedForm),
    };

    expect(() => assertRuntimeCertificateBindings(catalog, [honest], [])).not.toThrow();
    expect(() =>
      assertRuntimeCertificateBindings(catalog, [{ ...honest, runtimeSymbol: 'inline:nat.uncertified' }], []),
    ).toThrowError(`runtime certificate binding does not match the registry: ${inline.opcode}`);
    expect(() =>
      assertRuntimeCertificateBindings(catalog, [{ ...honest, runtimeBodySha256: `sha256:${'0'.repeat(64)}` }], []),
    ).toThrowError(`inline runtime form digest does not match the registry: ${inline.opcode}`);

    const helper = catalog.certificates.find((certificate) => certificate.runtimeSymbol.startsWith('helper:'));
    if (helper === undefined) throw new TypeError('the registry certifies no helper opcode');
    expect(() =>
      assertRuntimeCertificateBindings(
        catalog,
        [
          {
            opcode: helper.opcode,
            runtimeSymbol: helper.runtimeSymbol,
            declaration: 'listHead',
            runtimeBodySha256: `sha256:${'0'.repeat(64)}`,
          },
        ],
        [],
      ),
    ).toThrowError(/must resolve exactly once/u);
  });

  test('prints every inline opcode in exactly the form the registry certifies', () => {
    const forms = inlineOperationForms();
    const inline = catalog.certificates.filter((certificate) => certificate.runtimeSymbol.startsWith('inline:'));
    expect(inline.length).toBeGreaterThan(0);
    // The certificate an emitted package records digests this print, so an inline opcode's binding is
    // a claim about emitted structure rather than a digest of the registry row it is compared with.
    for (const certificate of inline) {
      expect(forms.get(certificate.opcode)).toBe(certificate.emittedForm);
      expect(runtimeBodyDigest(forms.get(certificate.opcode) ?? '')).toBe(runtimeBodyDigest(certificate.emittedForm));
    }
    // A helper reaches the target as a declaration, so it has no inline form to print.
    for (const certificate of catalog.certificates) {
      if (certificate.runtimeSymbol.startsWith('helper:')) expect(forms.get(certificate.opcode)).toBeUndefined();
    }
    expect(forms.size).toBe(inline.length);
    // One drifted form is one refused package: the binding a drifted emitter records no longer
    // digests the form Lean states.
    const [first] = inline;
    if (first === undefined) throw new TypeError('the registry certifies no inline opcode');
    expect(() =>
      assertRuntimeCertificateBindings(
        catalog,
        [
          {
            opcode: first.opcode,
            runtimeSymbol: first.runtimeSymbol,
            declaration: '',
            runtimeBodySha256: runtimeBodyDigest(`(${first.emittedForm})`),
          },
        ],
        [],
      ),
    ).toThrowError(`inline runtime form digest does not match the registry: ${first.opcode}`);
  });

  test('resolves every certified opcode to a registry row with a proved theorem', () => {
    for (const certificate of catalog.certificates) {
      const resolved = certificateForOpcode(catalog, certificate.opcode);
      expect(resolved.theorem).toMatch(/^TSLean\.LeanToTypeScript\.Semantics\.Opcode\./u);
      expect(resolved.model).toMatch(/^TSLean\.LeanToTypeScript\.Semantics\.Runtime\./u);
    }
    expect(() => certificateForOpcode(catalog, 'nat.uncertified')).toThrowError(
      'runtime opcode has no Lean certificate: nat.uncertified',
    );
  });
});
