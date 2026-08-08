import TSLean.Refinement

namespace TSLean.Refinement.Tests

open TSLean.JS

/-- Type-level inventory of every append-only JS heap allocator covered by exact extension. -/
theorem allocation_exactExtension_inventory : True := by
  let _ordinary := @Refinement.Heap.allocate_exactExtension
  let _wrapper := @Refinement.Heap.allocatePrimitiveWrapper_exactExtension
  let _arrayList := @Refinement.Heap.allocateArray_exactExtension
  let _array := @Refinement.Heap.allocateArrayFromArray_exactExtension
  let _function := @Refinement.Heap.allocateFunction_exactExtension
  let _constructor := @Refinement.Heap.allocateConstructorPair_exactExtension
  let _iterator := @Refinement.Heap.allocateArrayIterator_exactExtension
  trivial

private def referenceRefinement : Refinement RefId where
  Rel heap native value := value = .object native ∧ heap.valueValid value = true
  valueValid related := related.2
  stable extension related := ⟨related.1, extension.preserves_valueValid _ related.2⟩

/-- A dangling object reference cannot inhabit the reference refinement. -/
theorem dangling_reference_rejected :
    ¬referenceRefinement.Rel Heap.empty ⟨0⟩ (.object ⟨0⟩) := by
  simp [referenceRefinement, Heap.valueValid, Heap.size, Heap.empty]

/-- A primitive cannot inhabit the object-reference refinement. -/
theorem primitive_reference_rejected :
    ¬referenceRefinement.Rel Heap.empty ⟨0⟩ (.primitive .undefined) := by
  simp [referenceRefinement]

/-- Successful allocation from the empty heap is exact. -/
theorem empty_allocation_is_exact (ref : RefId) (next : Heap)
    (allocated : Heap.empty.allocate none true = .ok (ref, next)) :
    Refinement.Heap.ExactExtension Heap.empty next :=
  Refinement.Heap.allocate_exactExtension Heap.empty next none true ref Heap.empty_wellFormed allocated

/-- Exact allocation frames own-property reads of every old object. -/
theorem allocation_frames_getOwnProperty (heap next : Heap) (allocatedRef oldRef : RefId)
    (object : ObjectRecord) (key : PropertyKey) (valid : heap.WellFormed)
    (found : heap.get? oldRef = .ok object)
    (allocated : heap.allocate none true = .ok (allocatedRef, next)) :
    next.getOwnProperty oldRef key = heap.getOwnProperty oldRef key :=
  (Refinement.Heap.allocate_exactExtension heap next none true allocatedRef valid allocated).preserves_getOwnProperty
    oldRef object found key

/-- Constructor-pair allocation preserves old records despite fresh descriptor cross-references. -/
theorem constructor_pair_is_exact (heap next : Heap) (environment : EnvId)
    (constructor prototype : RefId) (valid : heap.WellFormed)
    (allocated : heap.allocateConstructorPair environment none none false .base =
      .ok (constructor, prototype, next)) :
    Refinement.Heap.ExactExtension heap next :=
  Refinement.Heap.allocateConstructorPair_exactExtension heap next environment none none false .base
    constructor prototype valid allocated

private def firstAssumption : Assumption :=
  (Assumption.create "native number representation" "enabled by test profile").get (by decide)

private def secondAssumption : Assumption :=
  (Assumption.create "native string representation" "enabled by test profile").get (by decide)

private def validAssumptions : ValidAssumptions :=
  (ValidAssumptions.create [firstAssumption, secondAssumption]).get (by decide)

private def firstOnly : ValidAssumptions :=
  (ValidAssumptions.create [firstAssumption]).get (by decide)

private def secondOnly : ValidAssumptions :=
  (ValidAssumptions.create [secondAssumption]).get (by decide)

private def assumedFalse : Evidence False := Evidence.assumed validAssumptions

/-- Assumed false evidence exposes no proof. -/
theorem assumed_false_has_no_proof :
    assumedFalse.proof? = @ProofStatus.none False := rfl

/-- Direct proofs remain extractable through the public constructor. -/
theorem proved_true_has_proof :
    (Evidence.proved True.intro).proof? = @ProofStatus.some True True.intro := rfl

private def positiveGuard : Guard Nat (fun value => 0 < value) :=
  Guard.create "positive natural" (by decide) (fun value => decide (0 < value))
    (fun value accepted => of_decide_eq_true accepted)

private def guardedPositive : Evidence (0 < 1) :=
  Evidence.ofGuard positiveGuard 1 (by decide)

/-- Guarded evidence exposes the proof derived by the guard's soundness law. -/
theorem guarded_positive_has_proof : ∃ proof, guardedPositive.proof? = .some proof := by
  exact ⟨of_decide_eq_true (by decide), rfl⟩

private def unitRefinement : Refinement Unit where
  Rel heap _ value := value = .primitive .undefined ∧ heap.valueValid value = true
  valueValid related := related.2
  stable extension related := ⟨related.1, extension.preserves_valueValid _ related.2⟩

private def alwaysErrorCodec : Codec Unit Unit Unit unitRefinement where
  encode _ _ := .error ()
  decode _ _ := .error ()
  encode_sound := by simp
  decode_sound := by simp

/-- Encode totality rules out a vacuous always-error lawful codec. -/
theorem always_error_codec_not_lawful : ¬LawfulCodec alwaysErrorCodec :=
  LawfulCodec.not_of_encode_always_errors alwaysErrorCodec () (by
    intro heap value
    exact ⟨(), rfl⟩)

private def totalUnitCodec : Codec Unit Unit Unit unitRefinement where
  encode heap _ := .ok (.primitive .undefined, heap)
  decode _ value := if value = .primitive .undefined then .ok () else .error ()
  encode_sound := by
    intro old native value next valid encoded
    simp only [Except.ok.injEq, Prod.mk.injEq] at encoded
    rcases encoded with ⟨rfl, rfl⟩
    exact ⟨Refinement.Heap.ExactExtension.refl old valid, ⟨rfl, rfl⟩⟩
  decode_sound := by
    intro heap value native decoded
    split at decoded
    · rename_i equal
      cases decoded
      exact ⟨equal, by cases equal; rfl⟩
    · contradiction

private theorem totalUnitCodec_lawful : LawfulCodec totalUnitCodec where
  encode_total heap native valid := ⟨.primitive .undefined, heap, rfl⟩
  complete := by
    intro heap native value related
    rcases related with ⟨rfl, valid⟩
    rfl

/-- The derived roundtrip theorem applies to a genuinely total codec. -/
theorem total_codec_roundtrip :
    totalUnitCodec.decode Heap.empty (.primitive .undefined) = .ok () :=
  totalUnitCodec_lawful.roundtrip Heap.empty_wellFormed rfl

private def testEvidenceApi : IO Unit := do
  assert! (Assumption.create "" "reason").isNone
  assert! (Assumption.create "statement" "").isNone
  assert! (ValidAssumptions.create []).isNone
  assert! (ValidAssumptions.create [firstAssumption, firstAssumption]).isNone
  assert! assumedFalse.metadata.assumptions.length == 2
  assert! assumedFalse.metadata.guards.isEmpty
  assert! guardedPositive.metadata.assumptions.isEmpty
  assert! guardedPositive.metadata.guards.length == 1
  let composed := (assumedFalse.and guardedPositive).and (assumedFalse.and guardedPositive)
  let reversed := guardedPositive.and assumedFalse
  assert! composed.kind == .assumed
  assert! composed.metadata.assumptions.length == 2
  assert! composed.metadata.guards.length == 1
  assert! composed.metadata.assumptions.map (·.id) |>.Nodup
  assert! composed.metadata.guards.map (·.id) |>.Nodup
  assert! decide ((assumedFalse.and guardedPositive).metadata = reversed.metadata)
  let firstEvidence : Evidence True := Evidence.assumed firstOnly
  let secondEvidence : Evidence True := Evidence.assumed secondOnly
  assert! decide ((firstEvidence.and secondEvidence).metadata =
    (secondEvidence.and firstEvidence).metadata)
  assert! decide (((assumedFalse.map (fun proof => False.elim proof) : Evidence True).metadata) =
    assumedFalse.metadata)

#eval testEvidenceApi

end TSLean.Refinement.Tests
