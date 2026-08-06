// Shared utilities used across the transpiler pipeline.

/** Capitalize the first character of a string. */
export function capitalize(s: string): string {
  return s ? s[0].toUpperCase() + s.slice(1) : s;
}

/** Prevent generated text from opening or closing a Lean block comment. */
export function escapeLeanComment(s: string): string {
  return s.replaceAll('/-', '/ -').replaceAll('-/', '- /');
}

/**
 * Field names that serve as discriminants in TypeScript discriminated unions.
 * Checked in order — the first matching field wins.
 */
export const DISCRIMINANT_FIELDS = ['kind', 'type', 'tag', 'ok', 'hasValue', '_type', '__type'];
