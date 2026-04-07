-- TSLean.Generated.Interfaces
-- TypeScript interfaces and type aliases transpiled to Lean 4
-- Demonstrates: interface → structure, generics → type parameters

import TSLean.Runtime.Basic
import TSLean.Runtime.BrandedTypes

namespace TSLean.Generated.Interfaces
open TSLean

-- TypeScript: interface User { id: string; name: string; email: string; age: number }
structure User where
  id    : String
  name  : String
  email : String
  age   : Nat
  deriving Repr, BEq, DecidableEq

-- TypeScript: interface Point { x: number; y: number }
structure Point where
  x : Float
  y : Float
  deriving Repr, BEq

-- TypeScript: interface Rectangle { topLeft: Point; width: number; height: number }
structure Rectangle where
  topLeft : Point
  width   : Float
  height  : Float
  deriving Repr

-- TypeScript: function area(r: Rectangle): number
def Rectangle.area (r : Rectangle) : Float := r.width * r.height
def Rectangle.perimeter (r : Rectangle) : Float := 2 * (r.width + r.height)

-- TypeScript: interface Comparable<T> { compareTo(other: T): number }
class Comparable (α : Type) where
  compareTo : α → α → Int

instance : Comparable Nat where
  compareTo a b := (a : Int) - (b : Int)

instance : Comparable String where
  compareTo a b := if a < b then -1 else if a > b then 1 else 0

-- TypeScript: interface Serializable { serialize(): string; deserialize(s: string): this }
class Serializable (α : Type) where
  serialize   : α → String
  deserialize : String → Option α

-- TypeScript: type Pair<A, B> = { fst: A; snd: B }
structure Pair (α β : Type) where
  fst : α
  snd : β
  deriving Repr

-- TypeScript: type Option<T> = T | null  (already in Lean as Option)
-- TypeScript: type Either<L, R> = { tag: 'left', value: L } | { tag: 'right', value: R }
abbrev Either (α β : Type) := Sum α β

-- TypeScript: interface KeyValue<K, V> { key: K; value: V }
structure KeyValue (α β : Type) where
  key   : α
  value : β
  deriving Repr

-- Theorems about the generated interfaces

theorem rect_area_def (r : Rectangle) : r.area = r.width * r.height := rfl
theorem rect_perimeter_def (r : Rectangle) : r.perimeter = 2 * (r.width + r.height) := rfl

theorem user_eq_iff (u v : User) :
    u = v ↔ u.id = v.id ∧ u.name = v.name ∧ u.email = v.email ∧ u.age = v.age := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · intro ⟨h1, h2, h3, h4⟩; cases u; cases v; simp_all

theorem pair_eq_iff (p q : Pair α β) : p = q ↔ p.fst = q.fst ∧ p.snd = q.snd := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩; cases p; cases q; simp_all

theorem keyvalue_eq_iff (kv1 kv2 : KeyValue α β) [BEq α] [BEq β] :
    kv1.key = kv2.key → kv1.value = kv2.value → kv1 = kv2 := by
  intro hk hv; cases kv1; cases kv2; simp_all

theorem comparable_nat_reflexive (n : Nat) :
    Comparable.compareTo (α := Nat) n n = 0 := by simp [Comparable.compareTo]

theorem comparable_nat_antisymm (a b : Nat) :
    Comparable.compareTo (α := Nat) a b = 0 ↔ a = b := by
  simp [Comparable.compareTo]; omega

end TSLean.Generated.Interfaces
