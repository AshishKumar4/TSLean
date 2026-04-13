/**
 * @module codegen
 *
 * Code generator: IR → valid Lean 4 syntax.
 *
 * V2 pipeline: IR → LeanAST (lower.ts) → Text (printer.ts)
 *
 * The LeanAST intermediate representation ensures all Lean syntax is
 * structurally valid before printing. No post-processing needed.
 *
 * Pipeline position:  IR → Rewrite → **Codegen** → Lean 4 source text
 */

import type { IRModule } from '../ir/types.js';
import { generateLeanV2 } from './v2.js';
import { resetTracker, currentTracker, type SorryTracker } from '../sorry-tracker.js';
export type { CodegenOptions } from './v2.js';
export type { SorryTracker, SorryEntry } from '../sorry-tracker.js';

export interface GenerateResult {
  code: string;
  tracker: SorryTracker;
}

/**
 * Generate Lean 4 source code from an IR module.
 *
 * @param mod - A fully-typed, effect-annotated IR module.
 * @returns A string containing valid Lean 4 source code.
 */
export function generateLean(mod: IRModule): string {
  return generateLeanV2(mod);
}

/**
 * Generate Lean 4 source code with sorry tracking.
 * Returns both the code and a tracker with all sorry entries.
 */
export function generateLeanTracked(mod: IRModule): GenerateResult {
  const tracker = resetTracker();
  const code = generateLeanV2(mod);
  const summary = tracker.summary();
  return {
    code: summary ? code + '\n' + summary : code,
    tracker,
  };
}
