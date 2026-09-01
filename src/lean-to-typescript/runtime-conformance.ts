import type { LeanToTypeScriptInput } from './artifact.js';
import {
  loadRuntimeProbeCorpus,
  RUNTIME_BINARY_INPUT,
  RUNTIME_EVIDENCE_INPUT,
  type RuntimeCertificateBinding,
  type RuntimeCertificateCatalog,
  type RuntimeConformanceAttestation,
} from './certificates.js';
import { compareCodePoints } from './ordering.js';

/**
 * Records, per used certificate and named assumption, which engine ran and which probe corpus
 * witnessed it. The corpus itself is executed and compared against the Lean model by the registry
 * gate; this binds that evidence to the artifact rather than re-running or re-deciding it.
 */
export function attestRuntimeConformance(
  catalog: RuntimeCertificateCatalog,
  certificates: readonly RuntimeCertificateBinding[],
  semanticInputs: readonly LeanToTypeScriptInput[],
  environmentInputs: readonly LeanToTypeScriptInput[],
): readonly RuntimeConformanceAttestation[] {
  if (certificates.length === 0) return [];
  const binary = environmentInputs.find((input) => input.identity === RUNTIME_BINARY_INPUT);
  if (binary === undefined) throw new TypeError(`runtime certificate requires ${RUNTIME_BINARY_INPUT} provenance`);
  const evidence = semanticInputs.find((input) => input.identity === RUNTIME_EVIDENCE_INPUT);
  if (evidence === undefined) throw new TypeError(`runtime certificate requires ${RUNTIME_EVIDENCE_INPUT} provenance`);
  if (evidence.sha256 !== loadRuntimeProbeCorpus().sha256) {
    throw new TypeError('recorded probe corpus digest does not match the corpus on disk');
  }
  const assumptions = new Map(catalog.assumptions.map((assumption) => [assumption.id, assumption]));
  const attestations: RuntimeConformanceAttestation[] = [];
  for (const binding of certificates) {
    const certificate = catalog.certificates.find((entry) => entry.opcode === binding.opcode);
    if (certificate === undefined) {
      throw new TypeError(`recorded certificate names an opcode the registry does not certify: ${binding.opcode}`);
    }
    for (const id of certificate.assumptions) {
      const assumption = assumptions.get(id);
      if (assumption === undefined) {
        throw new TypeError(`certificate ${binding.opcode} references unknown assumption ${id}`);
      }
      attestations.push({
        certificate: binding.opcode,
        assumption: assumption.id,
        oracle: assumption.oracle,
        binaryInput: RUNTIME_BINARY_INPUT,
        binarySha256: binary.sha256,
        evidenceInput: RUNTIME_EVIDENCE_INPUT,
        oracleSha256: evidence.sha256,
        runtimeSymbol: binding.runtimeSymbol,
        runtimeBodySha256: binding.runtimeBodySha256,
      });
    }
  }
  return attestations.sort((left, right) =>
    compareCodePoints(`${left.certificate}:${left.assumption}`, `${right.certificate}:${right.assumption}`),
  );
}
