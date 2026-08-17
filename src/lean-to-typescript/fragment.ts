/**
 * The one refusal every stage raises: the Lean exporter when a declaration leaves the admitted
 * fragment, and the emitter when an admitted declaration has no representation. Both carry the
 * declaration they were working on, so a refusal is attributable without reading a stack trace.
 */
export class UnsupportedLeanFragmentError extends TypeError {
  public readonly code = 'UNSUPPORTED_LEAN_FRAGMENT';

  public constructor(
    public readonly declaration: string,
    public readonly diagnostic: string,
  ) {
    super(`${declaration}: ${diagnostic}`);
    this.name = 'UnsupportedLeanFragmentError';
  }
}

export function attributeUnsupportedFragment(error: unknown, declaration: string): unknown {
  if (error instanceof UnsupportedLeanFragmentError) return error;
  if (error instanceof TypeError) return new UnsupportedLeanFragmentError(declaration, error.message);
  return error;
}
