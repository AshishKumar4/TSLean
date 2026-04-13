export interface ValidationResult { valid: boolean; errors: string[] }

export function validateEmail(email: string): ValidationResult {
  const errors: string[] = [];
  if (!email.includes("@")) errors.push("must contain @");
  if (email.length < 5)    errors.push("too short");
  if (email.length > 254)  errors.push("too long");
  return { valid: errors.length === 0, errors };
}

export function validateDisplayName(name: string): ValidationResult {
  const errors: string[] = [];
  if (name.length < 2)  errors.push("too short");
  if (name.length > 50) errors.push("too long");
  return { valid: errors.length === 0, errors };
}

export function validateRoomName(name: string): ValidationResult {
  const errors: string[] = [];
  if (name.length < 3)   errors.push("too short");
  if (name.length > 100) errors.push("too long");
  return { valid: errors.length === 0, errors };
}
