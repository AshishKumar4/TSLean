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
 * Names a generated Lean identifier must not take: Lean 4 keywords, and the
 * pervasive types and classes a generated declaration would otherwise shadow.
 * Module naming and constructor naming read the same set.
 */
export const LEAN_RESERVED = new Set([
  'String', 'Nat', 'Int', 'Float', 'Bool', 'Unit', 'IO', 'Type', 'Prop',
  'Array', 'List', 'Option', 'Except', 'True', 'False', 'And', 'Or', 'Not',
  'Set', 'Map', 'Monad', 'Functor', 'Pure', 'Bind',
  'abbrev', 'at', 'attribute', 'by', 'catch', 'class', 'deriving', 'do', 'def',
  'else', 'end', 'example', 'finally', 'for', 'from', 'fun', 'have', 'if',
  'import', 'in', 'inductive', 'instance', 'let', 'macro', 'match', 'mutual',
  'namespace', 'notation', 'open', 'partial', 'private', 'protected', 'return',
  'section', 'show', 'sorry', 'structure', 'syntax', 'then', 'theorem', 'this',
  'try', 'universe', 'unless', 'variable', 'where', 'while', 'with',
]);

/** Characters Lean accepts in a plain identifier atom, anchored to the whole name. */
const LEAN_IDENTIFIER = /^[A-Za-z_][A-Za-z0-9_'!?]*$/u;

/**
 * Whether a name can stand alone as a Lean identifier atom.
 *
 * A name that fails here cannot become a Lean declaration or constructor without a
 * rename, and a rename breaks the correspondence a caller relies on. Callers that
 * need the correspondence therefore refuse the construct instead of renaming it.
 */
export function isLeanIdentifier(name: string): boolean {
  return LEAN_IDENTIFIER.test(name) && !LEAN_RESERVED.has(name);
}

/**
 * Field names that serve as discriminants in TypeScript discriminated unions.
 * Checked in order — the first matching field wins.
 */
export const DISCRIMINANT_FIELDS = ['kind', 'type', 'tag', 'ok', 'hasValue', '_type', '__type'];
