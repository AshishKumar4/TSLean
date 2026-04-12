export function mapArray<T, U>(arr: T[], fn: (x: T) => U): U[] {
  return arr.map(fn);
}

export function filterArray<T>(arr: T[], pred: (x: T) => boolean): T[] {
  return arr.filter(pred);
}

export function reduceArray<T, U>(arr: T[], fn: (acc: U, x: T) => U, init: U): U {
  return arr.reduce(fn, init);
}

export function flatten<T>(nested: T[][]): T[] {
  return nested.flat();
}

export function unique<T>(arr: T[]): T[] {
  return [...new Set(arr)];
}

export function groupBy<T>(arr: T[], key: (item: T) => string): Map<string, T[]> {
  const map = new Map<string, T[]>();
  for (const item of arr) {
    const k = key(item);
    const existing = map.get(k) ?? [];
    existing.push(item);
    map.set(k, existing);
  }
  return map;
}
