// Anonymous object types in parameter and return position.
// Known broken: the build gate is red on this fixture — `{ width, height }`
// maps to `AssocMap String TSAny`, `TSAny` is `String`, and the fields are then
// multiplied as if they were `Float`, so the generated Lean does not typecheck.

export function area(rect: { width: number; height: number }): number {
  return rect.width * rect.height;
}

export function scale(rect: { width: number; height: number }, factor: number): { width: number; height: number } {
  return { width: rect.width * factor, height: rect.height * factor };
}
