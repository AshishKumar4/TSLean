import TSLean.Refinement.Heap

namespace TSLean.Refinement

open TSLean.JS

/-- A native Lean carrier related to valid values in the executable JS heap model. -/
structure Refinement (α : Type u) where
  Rel : Heap → α → Value → Prop
  valueValid : ∀ {heap native value}, Rel heap native value → heap.valueValid value = true
  stable : ∀ {old next native value}, Heap.ExactExtension old next →
    Rel old native value → Rel next native value

/-- Optional injectivity law for refinements whose JS values decode uniquely. -/
def Refinement.UniqueDecode (refinement : Refinement α) : Prop :=
  ∀ {heap left right value}, refinement.Rel heap left value →
    refinement.Rel heap right value → left = right

/-- Typed failures produced by a codec operation. -/
structure Codec (α : Type u) (EncodeFault : Type v) (DecodeFault : Type w)
    (refinement : Refinement α) where
  encode : Heap → α → Except EncodeFault (Value × Heap)
  decode : Heap → Value → Except DecodeFault α
  encode_sound : ∀ {old native value next}, old.WellFormed →
    encode old native = .ok (value, next) →
    Heap.ExactExtension old next ∧ refinement.Rel next native value
  decode_sound : ∀ {heap value native}, decode heap value = .ok native →
    refinement.Rel heap native value

/-- A lawful codec encodes every native value from a well-formed heap and completely decodes its
refinement relation. -/
structure LawfulCodec {α : Type u} {EncodeFault : Type v} {DecodeFault : Type w}
    {refinement : Refinement α} (codec : Codec α EncodeFault DecodeFault refinement) : Prop where
  encode_total : ∀ (heap : Heap) (native : α), heap.WellFormed →
    ∃ value next, codec.encode heap native = .ok (value, next)
  complete : ∀ {heap native value}, refinement.Rel heap native value →
    codec.decode heap value = .ok native

/-- Codec roundtrip follows from encode soundness and decode completeness. -/
theorem LawfulCodec.roundtrip {codec : Codec α EncodeFault DecodeFault refinement}
    (lawful : LawfulCodec codec) {old : Heap} {native : α} {value : Value} {next : Heap}
    (valid : old.WellFormed) (encoded : codec.encode old native = .ok (value, next)) :
    codec.decode next value = .ok native :=
  lawful.complete (codec.encode_sound valid encoded).2

/-- A codec that always returns an encode fault cannot satisfy encode totality. -/
theorem LawfulCodec.not_of_encode_always_errors
    (codec : Codec α EncodeFault DecodeFault refinement) (native : α)
    (alwaysErrors : ∀ heap value, ∃ fault, codec.encode heap value = .error fault) :
    ¬LawfulCodec codec := by
  intro lawful
  obtain ⟨value, next, encoded⟩ := lawful.encode_total Heap.empty native Heap.empty_wellFormed
  obtain ⟨fault, failed⟩ := alwaysErrors Heap.empty native
  rw [failed] at encoded
  contradiction

end TSLean.Refinement
