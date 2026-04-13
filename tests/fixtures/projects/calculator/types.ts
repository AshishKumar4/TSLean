export type Operator = 'add' | 'sub' | 'mul' | 'div';

export interface Expression {
  left: number;
  right: number;
  op: Operator;
}

export interface Result {
  value: number;
  expression: string;
}

export class CalcError extends Error {
  constructor(public code: string, message: string) {
    super(message);
  }
}
