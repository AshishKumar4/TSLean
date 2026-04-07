// Basic: functions, variables, primitives

function greet(name: string): string {
  return `Hello, ${name}!`;
}

function add(a: number, b: number): number {
  return a + b;
}

function isPositive(n: number): boolean {
  return n > 0;
}

function factorial(n: number): number {
  if (n <= 0) return 1;
  return n * factorial(n - 1);
}

const PI = 3.14159;
const greeting = greet("World");
