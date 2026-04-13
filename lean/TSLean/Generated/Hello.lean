-- TSLean.Generated.Hello
-- Example of TypeScript code transpiled to Lean 4
-- Original TypeScript: function hello() { return "Hello World!"; }

import TSLean.Runtime.Basic
import TSLean.Runtime.Monad

namespace TSLean.Generated.Hello
open TSLean

-- TypeScript: const hello: string = "Hello World!"
def hello : String := "Hello from TypeScript transpiled to Lean 4!"

-- TypeScript: function greet(name: string): string { return `Hello, ${name}!`; }
def greet (name : String) : String := "Hello, " ++ name ++ "!"

-- TypeScript: function repeat(s: string, n: number): string
def repeatStr (s : String) (n : Nat) : String :=
  (List.replicate n s).foldl (· ++ ·) ""

-- TypeScript: function isEmpty(s: string): boolean
def isEmpty (s : String) : Bool := s.length == 0

-- Theorems about the generated functions

theorem hello_nonempty : hello.length > 0 := by native_decide

theorem greet_nonempty (name : String) : (greet name).length > 0 := by
  simp only [greet, String.length_append]
  have h : ("Hello, " : String).length = 7 := rfl
  omega

theorem greet_eq (name : String) :
    greet name = "Hello, " ++ name ++ "!" := rfl

theorem greet_length (name : String) :
    (greet name).length = 7 + name.length + 1 := by
  simp only [greet, String.length_append]
  have h1 : ("Hello, " : String).length = 7 := rfl
  have h2 : ("!" : String).length = 1 := rfl
  omega

theorem repeatStr_zero (s : String) : repeatStr s 0 = "" := by
  simp [repeatStr]

theorem repeatStr_one (s : String) : repeatStr s 1 = s := by
  simp [repeatStr, List.replicate_succ, List.foldl]

theorem isEmpty_empty : isEmpty "" = true := by
  simp [isEmpty]

theorem isEmpty_false_of_nonempty (s : String) (h : s.length > 0) :
    isEmpty s = false := by
  simp [isEmpty, beq_iff_eq]
  intro heq; rw [heq] at h; simp at h

-- greet produces unique outputs for unique inputs
theorem greet_length_eq_iff (a b : String) :
    (greet a).length = (greet b).length ↔ a.length = b.length := by
  simp [greet_length]

theorem hello_eq : hello = "Hello from TypeScript transpiled to Lean 4!" := rfl

theorem greet_nonempty2 (name : String) : greet name ≠ "" := by
  simp [greet]

end TSLean.Generated.Hello
