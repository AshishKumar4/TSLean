import TSLean.Lcnf.Driver

/-! Control and representation shapes around the explicit stack: a non-tail call whose continuation
jumps to a join point declared outside it, a mutual component mixing tail and non-tail calls, an
enumeration type and a mixed nullary/non-nullary type. -/

/-- The continuation of each recursive call jumps to the join point `r + 1`. -/
def jpAfter : List Nat → Nat
  | [] => 0
  | x :: xs =>
    let r := if x > 3 then jpAfter xs + x else jpAfter xs * 2
    r + 1

mutual
/-- `evens` calls `odds` in non-tail position; `odds` calls `evens` in tail position. -/
def evens : List Nat → List Nat
  | [] => []
  | x :: xs => x :: odds xs
def odds : List Nat → List Nat
  | [] => []
  | _ :: xs => evens xs
end

inductive Color where
  | red | green | blue

def Color.next : Color → Color
  | .red => .green
  | .green => .blue
  | .blue => .red

def cycle : Nat → Color → Color
  | 0, c => c
  | n + 1, c => cycle n c.next

def colorAt (n : Nat) : Color := cycle n .red

def sumOpts : List (Option Nat) → Nat
  | [] => 0
  | none :: xs => sumOpts xs
  | some x :: xs => x + sumOpts xs

open Lean TSLean.Lcnf.Driver

instance : ToSem Color := ⟨fun
  | .red => .ctor ``Color.red #[] | .green => .ctor ``Color.green #[] | .blue => .ctor ``Color.blue #[]⟩

def opts (seed n : Nat) : List (Option Nat) :=
  (gen seed n 1000).map fun x => if x % 3 == 0 then none else some x

def case1 {α β} [ToSem α] [ToSem β] (label : String) (root : Name) (f : α → β) (a : α)
    (sem := true) : Case :=
  { label, root, args := #[toSem a], expect := toSem (f a), sem }

#eval show CoreM Unit from do
  runSuite "Shapes" #[``jpAfter, ``evens, ``odds, ``colorAt, ``sumOpts] <|
    ([0, 1, 6, 200].map fun n => case1 s!"jpAfter/gen{n}" ``jpAfter jpAfter (gen n n 8)).toArray ++
    #[case1 "jpAfter/200000" ``jpAfter jpAfter (gen 11 200000 8) (sem := false)] ++
    ([0, 1, 7, 300].map fun n => case1 s!"evens/gen{n}" ``evens evens (gen n n 50)).toArray ++
    #[case1 "odds/gen9" ``odds odds (gen 9 9 50),
      case1 "evens/1000000" ``evens evens (gen 12 1000000 50) (sem := false)] ++
    ([0, 1, 2, 3, 100].map fun n => case1 s!"colorAt/{n}" ``colorAt colorAt n).toArray ++
    #[case1 "colorAt/1000000" ``colorAt colorAt 1000000 (sem := false)] ++
    ([0, 1, 10, 300].map fun n => case1 s!"sumOpts/gen{n}" ``sumOpts sumOpts (opts n n)).toArray ++
    #[case1 "sumOpts/500000" ``sumOpts sumOpts (opts 13 500000) (sem := false)]
