// 05-error-handling/errors.ts
// try/catch/finally and throw → Lean tryCatch/ExceptT/Except.
//
// Run: npx tsx src/cli.ts examples/05-error-handling/errors.ts -o output.lean

// Throwing functions use ExceptT in the monad stack
function divide(a: number, b: number): number {
  if (b === 0) {
    throw new Error("Division by zero");
  }
  return a / b;
}

// try/catch → tryCatch
function safeDivide(a: number, b: number): number {
  try {
    return divide(a, b);
  } catch (e) {
    return 0;
  }
}

// try/catch/finally → tryCatch + let-bind cleanup
function withCleanup(x: number): number {
  try {
    if (x < 0) throw new Error("negative");
    return x * 2;
  } catch {
    return 0;
  } finally {
    console.log("cleanup done");
  }
}

// Multiple catch patterns (re-throw)
function processValue(input: string): string {
  try {
    if (input.length === 0) throw new Error("empty input");
    return input.toUpperCase();
  } catch (e) {
    throw e;  // re-throw
  }
}
