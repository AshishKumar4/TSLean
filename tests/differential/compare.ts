import { isDeepStrictEqual } from 'node:util';
import type { Observation } from './types.js';

export function observationMismatch(id: string, node: Observation, lean: Observation): string | undefined {
  if (isDeepStrictEqual(node, lean)) return undefined;
  return `${id}: Node ${JSON.stringify(node)} != Lean ${JSON.stringify(lean)}`;
}
