// A Durable Object namespace one struct deep.
//
// `DurableObjectNamespace` is an opaque stub with no `Inhabited` instance, so `Rooms` has none
// either, and neither does `Registry`, which only holds a `Rooms`. The compiler used to see the
// carrier only in a struct's own field list, so `Registry` got `deriving ... Inhabited` and a
// `default` value for a type Lean cannot instantiate: the artifact did not elaborate and no
// degradation marker recorded that it would not. Both sites now ask the same transitive question, so
// this file degrades visibly — one `sorry` that `--strict` rejects — and the Lean it emits
// elaborates, which is what the build gate checks by elaborating it.

export interface Rooms {
  namespace: DurableObjectNamespace<unknown>;
}

export interface Registry {
  rooms: Rooms;
  label: string;
}

// Every constructor carries a carrier, so the union has no inhabitant either. Lean builds the
// instance from one constructor, so this is the one shape the inductive `deriving` site gets wrong:
// it never asked the question at all, and `deriving ... Inhabited` here does not elaborate.
export type Binding =
  | { kind: 'namespace'; namespace: DurableObjectNamespace<unknown> }
  | { kind: 'stub'; stub: DurableObjectStub<unknown> };

export function labelOf(registry: Registry): string {
  return registry.label;
}

export function chosen(useFallback: boolean, primary: Registry, fallback: Registry): Registry {
  let selected: Registry;
  if (useFallback) {
    selected = fallback;
  } else {
    selected = primary;
  }
  return selected;
}
