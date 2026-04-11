/**
 * @module codegen/v2
 *
 * V2 codegen entry point: IR → LeanAST → Text.
 * Replaces the string-building approach of V1 with a typed AST intermediate.
 */

import type { IRModule } from '../ir/types.js';
import { lowerModule } from './lower.js';
import { printFile } from './printer.js';

/**
 * Generate Lean 4 source code from an IR module using the V2 pipeline.
 *
 * V2 pipeline: IR → LeanAST (lower.ts) → Text (printer.ts)
 * V1 pipeline: IR → Text (index.ts, string builder)
 *
 * During migration, both pipelines coexist. Once V2 produces identical
 * output to V1 on all fixtures, V1 and the post-processor are deleted.
 */
export function generateLeanV2(mod: IRModule): string {
  const leanFile = lowerModule(mod);
  return printFile(leanFile);
}
