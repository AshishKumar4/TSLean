# 03 — Classes

TypeScript classes become Lean structures (for state) and namespaced functions (for methods).

## Key pattern

```typescript
class Counter {
  private count: number = 0;
  increment(): void { this.count++; }
  getCount(): number { return this.count; }
}
```

becomes:

```lean
structure CounterState where
  count : Float := 0

def Counter.increment (self : CounterState) : CounterState :=
  { self with count := self.count + 1 }

def Counter.getCount (self : CounterState) : Float := self.count
```

Mutation is modeled as pure state transformation — the method returns a new state.
