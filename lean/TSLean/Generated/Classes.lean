-- TSLean.Generated.Classes
-- TypeScript class patterns transpiled to Lean 4 structures + functions
-- Demonstrates: class hierarchies, generics, method chaining

import TSLean.Runtime.Basic
import TSLean.Runtime.Monad

namespace TSLean.Generated.Classes
open TSLean

-- TypeScript: class Counter { constructor(private step: number = 1) {} }
structure Counter where
  value : Nat
  step  : Nat
  deriving Repr

def Counter.new (step : Nat := 1) : Counter := { value := 0, step }
def Counter.increment (c : Counter) : Counter := { c with value := c.value + c.step }
def Counter.decrement (c : Counter) : Counter :=
  { c with value := if c.value ≥ c.step then c.value - c.step else 0 }
def Counter.reset (c : Counter) : Counter := { c with value := 0 }
def Counter.withStep (c : Counter) (s : Nat) : Counter := { c with step := s }
def Counter.getValue (c : Counter) : Nat := c.value

-- TypeScript: class Stack<T> { private items: T[] = [] }
structure Stack (α : Type) where
  items : List α
  deriving Repr

def Stack.empty : Stack α := { items := [] }
def Stack.push (s : Stack α) (x : α) : Stack α := { items := x :: s.items }
def Stack.pop (s : Stack α) : Option α × Stack α :=
  match s.items with
  | [] => (none, s)
  | x :: rest => (some x, { items := rest })
def Stack.peek (s : Stack α) : Option α := s.items.head?
def Stack.size (s : Stack α) : Nat := s.items.length
def Stack.isEmpty (s : Stack α) : Bool := s.items.isEmpty

-- TypeScript: class Builder<T> { build(): T }
structure Builder (α : Type) where
  fields : List (String × String)
  deriving Repr

def Builder.empty : Builder α := { fields := [] }
def Builder.set (b : Builder α) (k v : String) : Builder α :=
  { fields := (k, v) :: b.fields }
def Builder.get (b : Builder α) (k : String) : Option String :=
  (b.fields.find? (fun (key, _) => key == k)).map Prod.snd

-- Theorems about Counter

theorem counter_monotone (c : Counter) : c.value ≤ c.increment.value := by
  simp [Counter.increment]

theorem counter_reset_zero (c : Counter) : c.reset.value = 0 := rfl

theorem counter_increment_step (c : Counter) :
    c.increment.value = c.value + c.step := rfl

theorem counter_new_zero (step : Nat) : (Counter.new step).value = 0 := rfl

-- After 2 increments, value = initial + 2 * step
theorem counter_two_increments (c : Counter) :
    c.increment.increment.value = c.value + 2 * c.step := by
  simp [Counter.increment]; omega

theorem counter_reset_then_increment (c : Counter) :
    c.reset.increment.value = c.step := by
  simp [Counter.reset, Counter.increment]

-- Theorems about Stack

theorem stack_push_size (s : Stack α) (x : α) :
    (s.push x).size = s.size + 1 := by
  simp [Stack.push, Stack.size]

theorem stack_pop_size (s : Stack α) (h : ¬s.isEmpty = true) :
    (s.pop.2).size = s.size - 1 := by
  cases hs : s.items with
  | nil => simp [Stack.isEmpty, hs] at h
  | cons x rest =>
    simp [Stack.pop, Stack.size, hs]

theorem stack_empty_size : (Stack.empty : Stack α).size = 0 := by
  simp [Stack.empty, Stack.size]

theorem stack_push_peek (s : Stack α) (x : α) :
    (s.push x).peek = some x := by
  simp [Stack.push, Stack.peek]

theorem stack_empty_isEmpty : (Stack.empty : Stack α).isEmpty = true := by
  simp [Stack.empty, Stack.isEmpty]

theorem stack_push_nonempty (s : Stack α) (x : α) :
    (s.push x).isEmpty = false := by
  simp [Stack.push, Stack.isEmpty]

-- Theorems about Builder

theorem builder_set_get (b : Builder α) (k v : String) :
    (b.set k v).get k = some v := by
  simp [Builder.set, Builder.get, beq_self_eq_true]

theorem builder_get_empty (k : String) :
    (Builder.empty : Builder α).get k = none := by
  simp [Builder.empty, Builder.get]

end TSLean.Generated.Classes
