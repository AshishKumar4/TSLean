import TSLean.Lcnf.Tests.Extract.Harness

/-!
# Canonicalization plant: before

The baseline program of the canonicalization plant (p2).

`CanonBefore`, `CanonAfter` and `CanonControl` are never imported together. Each one pins its own
output, so the three `#guard_msgs` blocks side by side are the comparison.
-/

open Lean TSLean.Lcnf.Tests.Extract

namespace CanonPlant
structure Order where
  id : Nat
  qty : Nat
  price : Nat

def total (os : List Order) : Nat := os.foldl (fun acc o => acc + o.qty * o.price) 0

def firstBig (os : List Order) : Nat :=
  match os.find? (fun o => o.qty > 10) with
  | some o => o.id
  | none => 0

def countdown : Nat → List Nat
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
end CanonPlant

/--
info: aux List.foldl._at_.CanonPlant.total.spec_0 => List.foldl._lcnf_43daaaec8a74ff04
aux List.find?._at_.CanonPlant.firstBig.spec_0 => List.find?._lcnf_ab779f6236c87a1a
raw digest CanonPlant.total: a2a8b43a3a400846b5d46222a07ce00f37906befe6c2103152cd8f53b3799d04
raw digest CanonPlant.firstBig: 416a3c191c58c8bb71982bdcb3cdbba2775103ec99fc74ce2b526418e29453b3
raw digest CanonPlant.countdown: e3d728017783cfe9e52dcfe028ffe3c2367963451b2800abbc6a4b9a2efb58a7
canonical digest CanonPlant.total: 8b3223e0212ca5846fdcf1f63aed04624bf7707a40f70811f9448cc2fd88c572
canonical digest CanonPlant.firstBig: 8181d918acae1c0628116174fc05e0b59a9720f1690f5a4da25f858167da94bf
canonical digest CanonPlant.countdown: e3d728017783cfe9e52dcfe028ffe3c2367963451b2800abbc6a4b9a2efb58a7
-/
#guard_msgs in
#eval canonReport #[``CanonPlant.total, ``CanonPlant.firstBig, ``CanonPlant.countdown]
