import { identity } from './core.js';

export type Result<T, E> = { ok: true; value: T } | { ok: false; error: E };

export function ok<T>(value: T): Result<T, never> {
  return { ok: true, value };
}

export function err<E>(error: E): Result<never, E> {
  return { ok: false, error };
}

export function map<T, U, E>(result: Result<T, E>, fn: (t: T) => U): Result<U, E> {
  if (result.ok) return ok(fn(result.value));
  return result;
}

export function flatMap<T, U, E>(result: Result<T, E>, fn: (t: T) => Result<U, E>): Result<U, E> {
  if (result.ok) return fn(result.value);
  return result;
}

export function unwrap<T, E>(result: Result<T, E>): T {
  if (result.ok) return result.value;
  throw new Error('Unwrap failed on Err');
}

export function unwrapOr<T, E>(result: Result<T, E>, defaultValue: T): T {
  if (result.ok) return result.value;
  return defaultValue;
}

export function tryCatch<T>(fn: () => T): Result<T, string> {
  try {
    return ok(fn());
  } catch (e) {
    return err(String(e));
  }
}

// Use identity from core to test cross-file imports
export function mapIdentity<T, E>(result: Result<T, E>): Result<T, E> {
  return map(result, identity);
}
