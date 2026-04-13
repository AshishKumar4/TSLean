import { Result } from './types.js';

export class History {
  private entries: Result[] = [];

  add(result: Result): void {
    this.entries.push(result);
  }

  getAll(): Result[] {
    return this.entries;
  }

  getLast(): Result | undefined {
    return this.entries[this.entries.length - 1];
  }

  clear(): void {
    this.entries = [];
  }

  size(): number {
    return this.entries.length;
  }
}
