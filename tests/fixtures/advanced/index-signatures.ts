// Index signatures and mapped types

interface StringMap {
  [key: string]: string;
}

interface NumberDict {
  [key: string]: number;
  readonly size: number;
}

interface Env {
  [key: string]: string | undefined;
  readonly NODE_ENV: string;
}

function getFromMap(m: StringMap, key: string): string | undefined {
  return m[key];
}

function setInMap(m: StringMap, key: string, value: string): StringMap {
  return { ...m, [key]: value };
}

type Nullable<T> = { [K in keyof T]: T[K] | null };
type Optional<T> = { [K in keyof T]?: T[K] };
type Readonly_<T> = { readonly [K in keyof T]: T[K] };
