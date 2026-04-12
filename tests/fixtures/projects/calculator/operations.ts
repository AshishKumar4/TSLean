import { Expression, Result, CalcError } from './types.js';

export function evaluate(expr: Expression): Result {
  const { left, right, op } = expr;
  let value: number;
  switch (op) {
    case 'add': value = left + right; break;
    case 'sub': value = left - right; break;
    case 'mul': value = left * right; break;
    case 'div':
      if (right === 0) throw new CalcError('DIV_ZERO', 'Division by zero');
      value = left / right;
      break;
    default: throw new CalcError('UNKNOWN_OP', `Unknown operator`);
  }
  return { value, expression: `${left} ${op} ${right} = ${value}` };
}

export function evaluateSafe(expr: Expression): Result | null {
  try {
    return evaluate(expr);
  } catch {
    return null;
  }
}

export function batch(expressions: Expression[]): Result[] {
  return expressions.map(e => evaluate(e));
}
