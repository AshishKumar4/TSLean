// Shared utilities used across the transpiler pipeline.

/** Capitalize the first character of a string. */
export function capitalize(s: string): string {
  return s ? s[0].toUpperCase() + s.slice(1) : s;
}

/**
 * Field names that serve as discriminants in TypeScript discriminated unions.
 * Checked in order — the first matching field wins.
 */
export const DISCRIMINANT_FIELDS = ['kind', 'type', 'tag', 'ok', 'hasValue', '_type', '__type'];
