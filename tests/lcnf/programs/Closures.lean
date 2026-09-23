import TSLean.Lcnf.Driver

/-! Closures under Lean's `pap` semantics: partial applications of code declarations, lambdas and
`@[extern]` primitives; closure calls that under-apply, saturate exactly and over-apply. -/

def curry3 (a b c : Nat) : Nat := a * 100 + b * 10 + c

/-- Not specialized, so callers pass real closures. -/
@[noinline] def twice (f : Nat → Nat) : Nat → Nat := fun x => f (f x)

/-- A partial application of a lambda (`stepper._lam_0 n`), saturated by `twice`. -/
def stepper (n : Nat) : Nat → Nat := twice (· + n)

@[noinline] def konst {α : Type} (a : α) (_n : Nat) : α := a

/-- Closures of arity 3 and 1 in one list; `f 1 x y` saturates the first exactly and over-applies
`konst Nat.add`, whose result is applied to the remaining two arguments. -/
@[noinline] def fns (k : Nat) : List (Nat → Nat → Nat → Nat) :=
  [konst Nat.add, konst (curry3 k), curry3, fun a b c => a + b + c + k]

def overApp (k x y : Nat) : List Nat := (fns k).map (fun f => f 1 x y)

/-- Over-application of a constant: `konst._redArg` has arity 1 and receives 3 arguments. -/
def constOver (x y : Nat) : Nat := konst Nat.mul 0 x y

/-- Under-application of a closure: `g 2` is a closure again, then saturated. -/
@[noinline] def partial2 (f : Nat → Nat → Nat → Nat) (a : Nat) : Nat → Nat := f a 2
def underApp (x : Nat) : Nat := partial2 curry3 x 7

structure Box where
  f : Nat → Nat → Nat

@[noinline] def boxes (k : Nat) : List Box :=
  [⟨Nat.add⟩, ⟨Nat.mul⟩, ⟨curry3 k⟩, ⟨fun a => if a == 0 then Nat.sub 100 else Nat.add a⟩]

def runBoxes (k x y : Nat) : List Nat := (boxes k).map (fun b => b.f x y)

open Lean TSLean.Lcnf.Driver

def case3 (label : String) (root : Name) (f : Nat → Nat → Nat → List Nat) (a b c : Nat) : Case :=
  { label, root, args := #[toSem a, toSem b, toSem c], expect := toSem (f a b c) }

#eval show CoreM Unit from do
  runSuite "Closures" #[``stepper, ``overApp, ``underApp, ``runBoxes, ``constOver] <|
    #[{ label := "stepper/3/4", root := ``stepper, args := #[toSem 3, toSem 4], expect := toSem (stepper 3 4) },
      { label := "stepper/big", root := ``stepper, args := #[toSem (2 ^ 90), toSem 1], expect := toSem (stepper (2 ^ 90) 1) },
      case3 "overApp/5/2/3" ``overApp overApp 5 2 3,
      case3 "overApp/0/9/9" ``overApp overApp 0 9 9,
      { label := "underApp/4", root := ``underApp, args := #[toSem 4], expect := toSem (underApp 4) },
      case3 "runBoxes/5/2/3" ``runBoxes runBoxes 5 2 3,
      case3 "runBoxes/1/0/30" ``runBoxes runBoxes 1 0 30,
      case3 "runBoxes/1/0/300" ``runBoxes runBoxes 1 0 300,
      { label := "constOver/4/5", root := ``constOver, args := #[toSem 4, toSem 5], expect := toSem (constOver 4 5) },
      { label := "constOver/big", root := ``constOver, args := #[toSem (2 ^ 70), toSem 3], expect := toSem (constOver (2 ^ 70) 3) }]
