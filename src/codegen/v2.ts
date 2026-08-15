/**
 * @module codegen/v2
 *
 * V2 codegen entry point: IR → LeanAST → Text.
 * Replaces the string-building approach of V1 with a typed AST intermediate.
 */

import type { IRModule } from '../ir/types.js';
import { lowerModule } from './lower.js';
import { printFile } from './printer.js';
import type { LeanFile } from './lean-ast.js';

/**
 * Build the LeanAST for a module — the exact tree `generateLeanV2` prints.
 *
 * Exposed so callers that need to inspect the artifact (the degradation scan)
 * work on the printed tree rather than on the printed text.
 */
export function buildLeanFile(mod: IRModule): LeanFile {
  return lowerModule(mod);
}

/**
 * Generate Lean 4 source code from an IR module using the V2 pipeline.
 */
export function generateLeanV2(mod: IRModule): string {
  return printFile(buildLeanFile(mod));
}
