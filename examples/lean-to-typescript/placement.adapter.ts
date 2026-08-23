import { choosePlacement, PlacementSet, type GeneratedData, type Placement } from './generated/TSLean/Examples/Placement.js';

/**
 * The boundary between untrusted input and the generated decision. `PlacementSet` carries
 * behaviour in Lean, so the compiler emits it as an immutable value object with its own codec;
 * the adapter therefore validates through that codec instead of restating the field contract.
 *
 * The parameters are `GeneratedData` rather than `unknown` because that is what the generated
 * codec accepts: a named union of everything a JSON document can deliver. A caller holding
 * `unknown` parses it at its own I/O boundary first, which is the narrowing this type exists to
 * force rather than to skip.
 */
export function choosePlacementFromData(
  manifest: GeneratedData,
  policy: GeneratedData,
  substrate: GeneratedData,
  trust: GeneratedData,
): Placement | undefined {
  return choosePlacement(
    PlacementSet.fromData(manifest),
    PlacementSet.fromData(policy),
    PlacementSet.fromData(substrate),
    PlacementSet.fromData(trust),
  );
}
