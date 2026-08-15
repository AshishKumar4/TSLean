import { choosePlacement, type Placement, type PlacementSet } from './placement.generated.js';

export function choosePlacementFromUnknown(
  manifest: unknown,
  policy: unknown,
  substrate: unknown,
  trust: unknown,
): Placement | undefined {
  return choosePlacement(
    decodePlacementSet(manifest, 'manifest'),
    decodePlacementSet(policy, 'policy'),
    decodePlacementSet(substrate, 'substrate'),
    decodePlacementSet(trust, 'trust'),
  );
}

function decodePlacementSet(value: unknown, name: string): PlacementSet {
  if (!isRecord(value) || !hasOnlyPlacementFields(value)) {
    throw new TypeError(`${name} must be a plain PlacementSet`);
  }
  const { bundled, dynamic, provider } = value;
  if (typeof bundled !== 'boolean' || typeof dynamic !== 'boolean' || typeof provider !== 'boolean') {
    throw new TypeError(`${name} must contain boolean bundled, dynamic, and provider fields`);
  }
  return { bundled, dynamic, provider };
}

function isRecord(value: unknown): value is Record<string, unknown> {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) return false;
  const prototype: unknown = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
}

function hasOnlyPlacementFields(value: Record<string, unknown>): boolean {
  const names = Object.keys(value).sort();
  return names.length === 3 && names[0] === 'bundled' && names[1] === 'dynamic' && names[2] === 'provider';
}
