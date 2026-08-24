import { generateLeanTracked, type GenerateResult } from '../codegen/index.js';
import { parseFile, type ParseOptions } from '../parser/index.js';
import { rewriteModule } from '../rewrite/index.js';

/** Compile one typed TypeScript source into Lean and report every emitted degradation. */
export function compileTypeScriptToLean(options: ParseOptions): GenerateResult {
  return generateLeanTracked(rewriteModule(parseFile(options)));
}

export { generateLean, generateLeanTracked } from '../codegen/index.js';
export type { DegradationMarker, GenerateResult } from '../codegen/index.js';
export { parseFile } from '../parser/index.js';
export type { ParseOptions } from '../parser/index.js';
export { rewriteModule } from '../rewrite/index.js';
export {
  transpileProject as compileTypeScriptProjectToLean,
  writeProjectOutputs as writeTypeScriptProjectOutputs,
} from '../project/index.js';
export type { ProjectOpts, ProjectResult } from '../project/index.js';
export { generateVerification } from '../verification/index.js';
export type { ObligationKind, ProofObligation, VerificationResult } from '../verification/index.js';
