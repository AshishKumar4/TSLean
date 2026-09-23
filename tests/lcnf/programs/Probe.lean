import TSLean.Lcnf.Driver

/-! The probe program of the plan (`total`/`firstBig`/`countdown`). -/

structure Order where
  id : Nat
  qty : Nat
  price : Nat

def total (os : List Order) : Nat :=
  os.foldl (fun acc o => acc + o.qty * o.price) 0

def firstBig (os : List Order) : Nat :=
  match os.find? (fun o => o.qty > 10) with
  | some o => o.id
  | none => 0

def countdown : Nat → List Nat
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n

open Lean TSLean.Lcnf.Driver

instance : ToSem Order := ⟨fun o => .ctor ``Order.mk #[toSem o.id, toSem o.qty, toSem o.price]⟩

def orders (seed n : Nat) : List Order :=
  let xs := (gen seed (3 * n) (2 ^ 70)).toArray
  (List.range n).map fun i => ⟨xs[3 * i]!, xs[3 * i + 1]! % 20, xs[3 * i + 2]!⟩

def orderCase (label : String) (os : List Order) (sem := true) : Array Case :=
  #[{ label := s!"total/{label}", root := ``total, args := #[toSem os], expect := toSem (total os), sem },
    { label := s!"firstBig/{label}", root := ``firstBig, args := #[toSem os], expect := toSem (firstBig os), sem }]

def countdownCase (n : Nat) (sem := true) : Case :=
  { label := s!"countdown/{n}", root := ``countdown, args := #[toSem n], expect := toSem (countdown n), sem }

#eval show CoreM Unit from do
  runSuite "Probe" #[``total, ``firstBig, ``countdown] <|
    orderCase "0" [] ++ orderCase "3" [⟨1, 2, 3⟩, ⟨2, 11, 5⟩, ⟨3, 4, 5⟩] ++
    orderCase "gen100" (orders 1 100) ++ orderCase "gen100000" (orders 2 100000) (sem := false) ++
    #[countdownCase 0, countdownCase 3, countdownCase 1000, countdownCase 1000000 (sem := false)]
