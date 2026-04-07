// Exceptions → ExceptT

class ValidationError extends Error {
  constructor(public readonly field: string, public readonly reason: string) {
    super(`Validation failed for ${field}: ${reason}`);
  }
}

function parseAge(input: string): number {
  const n = parseInt(input, 10);
  if (isNaN(n)) throw new ValidationError("age", "must be a number");
  if (n < 0 || n > 150) throw new ValidationError("age", "must be between 0 and 150");
  return n;
}

function divide(a: number, b: number): number {
  if (b === 0) throw new Error("Division by zero");
  return a / b;
}

function safeDivide(a: number, b: number): number | null {
  try { return divide(a, b); } catch { return null; }
}

function validateEmail(email: string): string {
  if (!email.includes("@")) throw new ValidationError("email", "must contain @");
  if (email.length < 5)     throw new ValidationError("email", "too short");
  return email.toLowerCase().trim();
}
