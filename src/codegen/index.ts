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
import { buildLeanFile, type CodegenOptions } from './v2.js';
import { printFile } from './printer.js';
import { scanDegradation, type DegradationMarker } from './degradation.js';
import { resetTracker, type SorryTracker } from '../sorry-tracker.js';
export type { CodegenOptions } from './v2.js';
export type { SorryTracker, SorryEntry } from '../sorry-tracker.js';
export type { DegradationMarker } from './degradation.js';

export interface GenerateResult {
  code: string;
  /** Why the lowerer degraded, for the sites that record a reason. */
  tracker: SorryTracker;
  /** Every `sorry`/`default` placeholder present in `code`. */
  degradations: DegradationMarker[];
}

/**
 * Generate Lean 4 source code from an IR module.
 *
 * @param mod - A fully-typed, effect-annotated IR module.
 * @returns A string containing valid Lean 4 source code.
 */
export function generateLean(mod: IRModule): string {
  return generateLeanTracked(mod).code;
}

/**
 * Generate Lean 4 source code together with the degradation it carries.
 *
 * The single code path: `generateLean` returns this function's `code`, so
 * every caller emits the same bytes and every caller can see the same
 * degradation.
 */
export function generateLeanTracked(mod: IRModule, opts?: CodegenOptions): GenerateResult {
  const tracker = resetTracker();
  const file = buildLeanFile(mod, opts);
  return { code: printFile(file), tracker, degradations: scanDegradation(file) };
}
