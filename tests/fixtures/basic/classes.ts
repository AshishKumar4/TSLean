// Classes → Lean state structs + methods

class Counter {
  private count: number = 0;
  private step: number;
  constructor(step: number = 1) { this.step = step; }
  increment(): void { this.count += this.step; }
  decrement(): void { this.count -= this.step; }
  reset(): void { this.count = 0; }
  getCount(): number { return this.count; }
}

class Stack<T> {
  private items: T[] = [];
  push(item: T): void { this.items.push(item); }
  pop(): T | undefined { return this.items.pop(); }
  peek(): T | undefined { return this.items[this.items.length - 1]; }
  isEmpty(): boolean { return this.items.length === 0; }
  size(): number { return this.items.length; }
}

class BankAccount {
  private balance: number;
  readonly owner: string;
  constructor(owner: string, initial: number = 0) { this.owner = owner; this.balance = initial; }
  deposit(amount: number): void { if (amount <= 0) throw new Error("must be positive"); this.balance += amount; }
  withdraw(amount: number): boolean { if (amount > this.balance) return false; this.balance -= amount; return true; }
  getBalance(): number { return this.balance; }
}
