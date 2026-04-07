// Optional chaining, nullish coalescing, destructuring, rest params

interface Config {
  host?: string;
  port?: number;
  db?: { name: string; url?: string };
}

function getHost(config?: Config): string {
  return config?.host ?? 'localhost';
}

function getDbUrl(config?: Config): string {
  return config?.db?.url ?? 'default-url';
}

function withDefaults(config?: Config): Config {
  const host = config?.host ?? 'localhost';
  const port = config?.port ?? 5432;
  const dbName = config?.db?.name ?? 'mydb';
  return { host, port, db: { name: dbName } };
}

// Destructuring
function describePoint({ x, y }: { x: number; y: number }): string {
  return `Point(${x}, ${y})`;
}

function sumArray([first, ...rest]: number[]): number {
  if (rest.length === 0) return first;
  return first + sumArray(rest);
}

// Rest parameters
function sum(...nums: number[]): number {
  return nums.reduce((acc, n) => acc + n, 0);
}

function max(...nums: number[]): number {
  return Math.max(...nums);
}
