import TSLean.Refinement

open TSLean.Refinement

def positiveGuard : Guard Nat (fun value => 0 < value) :=
  Guard.create "positive" (by decide) (fun value => decide (0 < value))
    (fun value accepted => of_decide_eq_true accepted)

def invalidReceipt : GuardReceipt positiveGuard 0 := ⟨rfl⟩
