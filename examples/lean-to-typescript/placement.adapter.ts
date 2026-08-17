import { choosePlacement, PlacementSet, type Placement } from './placement.generated.js';

/**
 * The boundary between untrusted input and the generated decision. `PlacementSet` carries
 * behaviour in Lean, so the compiler emits it as an immutable value object with its own codec;
 * the adapter therefore validates through that codec instead of restating the field contract.
 */
export function choosePlacementFromUnknown(
  manifest: unknown,
  policy: unknown,
  substrate: unknown,
  trust: unknown,
): Placement | undefined {
  return choosePlacement(
    PlacementSet.fromData(manifest),
    PlacementSet.fromData(policy),
    PlacementSet.fromData(substrate),
    PlacementSet.fromData(trust),
  );
}
