// 03-classes/counter.ts
// Classes become structures (state) + namespaced methods.
//
// Run: npx tsx src/cli.ts examples/03-classes/counter.ts -o output.lean

class Counter {
  private count: number = 0;

  increment(): void {
    this.count++;
  }

  decrement(): void {
    if (this.count > 0) {
      this.count--;
    }
  }

  getCount(): number {
    return this.count;
  }

  reset(): void {
    this.count = 0;
  }
}

// Lean output:
// structure CounterState where count : Float := 0
// def Counter.increment (self : CounterState) : CounterState := ...
// def Counter.getCount (self : CounterState) : Float := self.count
