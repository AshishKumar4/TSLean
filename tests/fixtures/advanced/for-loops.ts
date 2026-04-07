// For loops, for-of, for-in, while, destructuring in loops

function rangeSum(n: number): number {
  let total = 0;
  for (let i = 0; i < n; i++) {
    total += i;
  }
  return total;
}

function countDown(n: number): number[] {
  const result: number[] = [];
  for (let i = n; i > 0; i--) {
    result.push(i);
  }
  return result;
}

function processItems(items: string[]): string[] {
  const out: string[] = [];
  for (const item of items) {
    out.push(item.toUpperCase());
  }
  return out;
}

function objectKeys(obj: Record<string, number>): string[] {
  const keys: string[] = [];
  for (const key in obj) {
    keys.push(key);
  }
  return keys;
}

function fibonacci(n: number): number {
  let a = 0, b = 1;
  while (n-- > 0) {
    const tmp = b;
    b = a + b;
    a = tmp;
  }
  return a;
}

function findFirst<T>(items: T[], pred: (x: T) => boolean): T | undefined {
  for (const item of items) {
    if (pred(item)) return item;
  }
  return undefined;
}
