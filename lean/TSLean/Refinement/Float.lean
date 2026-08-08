import TSLean.Refinement.Core
import TSLean.Refinement.Evidence
import TSLean.JS.Equality
import TSLean.JS.PrimitiveOperators

namespace TSLean.Refinement

open TSLean.JS

namespace Float

/-- A Float codec rejects every JavaScript value outside the Number primitive domain. -/
inductive DecodeFault where
  | expectedNumber
  deriving DecidableEq, Repr

/-- The executable native remainder bridge corresponding to the committed JS Number operation. -/
def remainder (left right : _root_.Float) : _root_.Float :=
  (JSNumber.remainder (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right)).toFloat

/-- Runtime law for canonical re-encoding after `Float.ofBits`. -/
def BridgeSameValueRoundtrip : Prop := ∀ number,
    JSNumber.sameValue (JSNumber.ofFloatCanonical number.toFloat) number = true

/-- Runtime law relating `Float.add` to committed Number addition. -/
def Add : Prop := ∀ left right,
    JSNumber.sameValue (JSNumber.ofFloatCanonical (_root_.Float.add left right))
      (JSNumber.add (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right)) = true

/-- Runtime law relating `Float.sub` to committed Number subtraction. -/
def Subtract : Prop := ∀ left right,
    JSNumber.sameValue (JSNumber.ofFloatCanonical (_root_.Float.sub left right))
      (JSNumber.subtract (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right)) = true

/-- Runtime law relating `Float.mul` to committed Number multiplication. -/
def Multiply : Prop := ∀ left right,
    JSNumber.sameValue (JSNumber.ofFloatCanonical (_root_.Float.mul left right))
      (JSNumber.multiply (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right)) = true

/-- Runtime law relating `Float.div` to committed Number division. -/
def Divide : Prop := ∀ left right,
    JSNumber.sameValue (JSNumber.ofFloatCanonical (_root_.Float.div left right))
      (JSNumber.divide (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right)) = true

/-- Runtime law relating native strict ordering to committed Number less-than. -/
def LessThan : Prop := ∀ left right,
    decide (left < right) =
      JSNumber.lessThan (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right)

/-- Runtime law relating native non-strict ordering to ordered Number not-greater-than. -/
def LessThanOrEqual : Prop := ∀ left right,
    decide (left ≤ right) =
      (!JSNumber.lessThan (JSNumber.ofFloatCanonical right) (JSNumber.ofFloatCanonical left) &&
        !(JSNumber.ofFloatCanonical left).isNaN && !(JSNumber.ofFloatCanonical right).isNaN)

/-- Runtime law relating `Float.beq` to committed strict Number equality. -/
def StrictEqual : Prop := ∀ left right,
    _root_.Float.beq left right =
      JSNumber.strictEqual (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right)

/-- Lean Floats refine Number primitives that are observationally identical under SameValue. -/
def refinement : Refinement _root_.Float where
  Rel _ native value := match value with
    | .primitive (.number number) =>
        JSNumber.sameValue (JSNumber.ofFloatCanonical native) number = true
    | _ => False
  valueValid := by
    intro heap native value related
    cases value with
    | object ref => contradiction
    | primitive primitive => cases primitive <;> rfl
  stable _ related := related

/-- The Float relation is heap-independent and observes Number values through SameValue. -/
theorem refinement_rel_iff (heap : Heap) (native : _root_.Float) (value : Value) :
    refinement.Rel heap native value ↔ ∃ number,
      value = .primitive (.number number) ∧
        JSNumber.sameValue (JSNumber.ofFloatCanonical native) number = true := by
  cases value with
  | object ref => simp [refinement]
  | primitive primitive =>
      cases primitive <;> simp [refinement]

/-- Encodes a Float as a canonical Number primitive without changing the heap. -/
def encode (heap : Heap) (native : _root_.Float) : Except Empty (Value × Heap) :=
  .ok (.primitive (.number (JSNumber.ofFloatCanonical native)), heap)

/-- Decodes only Number primitives through the executable `Float.ofBits` bridge. -/
def decode (_ : Heap) (value : Value) : Except DecodeFault _root_.Float :=
  match value with
  | .primitive (.number number) => .ok number.toFloat
  | _ => .error .expectedNumber

/-- Total Float encoding and Number-only decoding, justified by the executable bridge law. -/
def codec (bridge : BridgeSameValueRoundtrip) :
    Codec _root_.Float Empty DecodeFault refinement where
  encode := encode
  decode := decode
  encode_sound := by
    intro old native value next valid encoded
    simp only [encode, Except.ok.injEq, Prod.mk.injEq] at encoded
    rcases encoded with ⟨rfl, rfl⟩
    exact ⟨Heap.ExactExtension.refl old valid, by
      simp [refinement, JSNumber.sameValue, JSNumber.ofFloatCanonical]⟩
  decode_sound := by
    intro heap value native decoded
    cases value with
    | object ref => simp [decode] at decoded
    | primitive primitive =>
        cases primitive <;> simp [decode] at decoded
        rename_i number
        cases decoded
        exact bridge number

/-- Float encoding returns the canonical Number primitive and leaves the heap unchanged. -/
theorem encode_exact (bridge : BridgeSameValueRoundtrip) (heap : Heap) (native : _root_.Float) :
    (codec bridge).encode heap native =
      .ok (.primitive (.number (JSNumber.ofFloatCanonical native)), heap) := rfl

/-- Number decoding executes `Float.ofBits` on the represented binary64 bits. -/
theorem decode_exact (bridge : BridgeSameValueRoundtrip) (heap : Heap) (number : JSNumber) :
    (codec bridge).decode heap (.primitive (.number number)) = .ok number.toFloat := rfl

/-- Float decoding rejects every non-Number primitive with its typed fault. -/
theorem decode_nonnumber (bridge : BridgeSameValueRoundtrip) (heap : Heap)
    (primitive : JS.Primitive) (notNumber : ∀ number, primitive ≠ .number number) :
    (codec bridge).decode heap (.primitive primitive) = .error .expectedNumber := by
  cases primitive <;> simp_all [codec, decode]

/-- Float decoding rejects object references with its typed fault. -/
theorem decode_object (bridge : BridgeSameValueRoundtrip) (heap : Heap) (ref : RefId) :
    (codec bridge).decode heap (.object ref) = .error .expectedNumber := rfl

/-- Encoding and decoding preserve one shared SameValue observation without asserting Float equality. -/
theorem codec_observational_roundtrip (bridge : BridgeSameValueRoundtrip) (heap : Heap)
    (native : _root_.Float) (valid : heap.WellFormed) :
    ∃ value next decoded,
      (codec bridge).encode heap native = .ok (value, next) ∧
      value = .primitive (.number (JSNumber.ofFloatCanonical native)) ∧
      next = heap ∧
      (codec bridge).decode next value = .ok decoded ∧
      refinement.Rel next native value ∧ refinement.Rel next decoded value := by
  let value := Value.primitive (.number (JSNumber.ofFloatCanonical native))
  let decoded := (JSNumber.ofFloatCanonical native).toFloat
  refine ⟨value, heap, decoded, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact ((codec bridge).encode_sound valid rfl).2
  · exact (codec bridge).decode_sound rfl

/-- Number truthiness commutes with the canonical Float encoding. -/
theorem toBoolean_commutes (native : _root_.Float) :
    (Value.primitive (.number (JSNumber.ofFloatCanonical native))).toBoolean =
      !((JSNumber.ofFloatCanonical native).isZero ||
        (JSNumber.ofFloatCanonical native).isNaN) := rfl

/-- Float addition commutes with the committed JS Number addition under the runtime contract. -/
theorem add_commutes (law : Add) (left right : _root_.Float) :
    refinement.Rel Heap.empty (_root_.Float.add left right)
      (.primitive (.number (JSNumber.add (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right)))) := law left right

/-- Float subtraction commutes with the committed JS Number subtraction under the runtime contract. -/
theorem subtract_commutes (law : Subtract) (left right : _root_.Float) :
    refinement.Rel Heap.empty (_root_.Float.sub left right)
      (.primitive (.number (JSNumber.subtract (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right)))) := law left right

/-- Float multiplication commutes with the committed JS Number multiplication under the runtime contract. -/
theorem multiply_commutes (law : Multiply) (left right : _root_.Float) :
    refinement.Rel Heap.empty (_root_.Float.mul left right)
      (.primitive (.number (JSNumber.multiply (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right)))) := law left right

/-- Float division commutes with the committed JS Number division under the runtime contract. -/
theorem divide_commutes (law : Divide) (left right : _root_.Float) :
    refinement.Rel Heap.empty (_root_.Float.div left right)
      (.primitive (.number (JSNumber.divide (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right)))) := law left right

/-- The native remainder bridge commutes with committed Number remainder under the bridge law. -/
theorem remainder_commutes (bridge : BridgeSameValueRoundtrip) (left right : _root_.Float) :
    refinement.Rel Heap.empty (Float.remainder left right)
      (.primitive (.number (JSNumber.remainder (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right)))) :=
  bridge (JSNumber.remainder (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right))

/-- Native Float strict ordering commutes with committed JS Number less-than. -/
theorem lessThan_commutes (law : LessThan) (left right : _root_.Float) :
    JSNumber.lessThan (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right) =
      decide (left < right) := (law left right).symm

/-- Native Float non-strict ordering commutes with committed JS Number less-than-or-equal. -/
theorem lessThanOrEqual_commutes (law : LessThanOrEqual)
    (left right : _root_.Float) :
    (!JSNumber.lessThan (JSNumber.ofFloatCanonical right) (JSNumber.ofFloatCanonical left) &&
      !(JSNumber.ofFloatCanonical left).isNaN &&
      !(JSNumber.ofFloatCanonical right).isNaN) = decide (left ≤ right) :=
  (law left right).symm

/-- Native Float greater-than commutes by reversing committed JS Number less-than. -/
theorem greaterThan_commutes (law : LessThan) (left right : _root_.Float) :
    JSNumber.lessThan (JSNumber.ofFloatCanonical right) (JSNumber.ofFloatCanonical left) =
      decide (right < left) := (law right left).symm

/-- Native Float greater-than-or-equal commutes by reversing non-strict ordering. -/
theorem greaterThanOrEqual_commutes (law : LessThanOrEqual)
    (left right : _root_.Float) :
    (!JSNumber.lessThan (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right) &&
      !(JSNumber.ofFloatCanonical right).isNaN &&
      !(JSNumber.ofFloatCanonical left).isNaN) = decide (right ≤ left) :=
  (law right left).symm

/-- Native Float IEEE equality commutes with JavaScript strict numeric equality. -/
theorem strictEqual_commutes (law : StrictEqual) (left right : _root_.Float) :
    strictEqual (.primitive (.number (JSNumber.ofFloatCanonical left)))
      (.primitive (.number (JSNumber.ofFloatCanonical right))) =
        _root_.Float.beq left right := (law left right).symm

/-- JavaScript SameValue on refined Floats is exactly SameValue on their canonical encodings. -/
theorem sameValue_commutes (left right : _root_.Float) :
    sameValue (.primitive (.number (JSNumber.ofFloatCanonical left)))
      (.primitive (.number (JSNumber.ofFloatCanonical right))) =
        JSNumber.sameValue (JSNumber.ofFloatCanonical left)
          (JSNumber.ofFloatCanonical right) := rfl

/-- JavaScript SameValueZero on refined Floats is exactly SameValueZero on canonical encodings. -/
theorem sameValueZero_commutes (left right : _root_.Float) :
    sameValueZero (.primitive (.number (JSNumber.ofFloatCanonical left)))
      (.primitive (.number (JSNumber.ofFloatCanonical right))) =
        JSNumber.sameValueZero (JSNumber.ofFloatCanonical left)
          (JSNumber.ofFloatCanonical right) := rfl

/-- Assumption metadata for `bridgeSameValueRoundtrip`. -/
def bridgeSameValueRoundtripAssumption : Assumption :=
  (Assumption.create
    "Canonical re-encoding of Float.ofBits is JSNumber.sameValue to the source JSNumber."
    "Lean Float primitives are executable runtime bridges, not kernel definitions.").get (by decide)

/-- Assumption metadata for Float addition. -/
def addAssumption : Assumption :=
  (Assumption.create "Canonical Float.add encoding is SameValue to JSNumber.add on canonical operands."
    "Float.add is an executable runtime primitive.").get (by decide)

/-- Assumption metadata for Float subtraction. -/
def subtractAssumption : Assumption :=
  (Assumption.create
    "Canonical Float.sub encoding is SameValue to JSNumber.subtract on canonical operands."
    "Float.sub is an executable runtime primitive.").get (by decide)

/-- Assumption metadata for Float multiplication. -/
def multiplyAssumption : Assumption :=
  (Assumption.create
    "Canonical Float.mul encoding is SameValue to JSNumber.multiply on canonical operands."
    "Float.mul is an executable runtime primitive.").get (by decide)

/-- Assumption metadata for Float division. -/
def divideAssumption : Assumption :=
  (Assumption.create
    "Canonical Float.div encoding is SameValue to JSNumber.divide on canonical operands."
    "Float.div is an executable runtime primitive.").get (by decide)

/-- Assumption metadata for native strict Float ordering. -/
def lessThanAssumption : Assumption :=
  (Assumption.create "Native Float strict ordering equals JSNumber.lessThan on canonical operands."
    "Float.decLt is an executable runtime primitive.").get (by decide)

/-- Assumption metadata for native non-strict Float ordering. -/
def lessThanOrEqualAssumption : Assumption :=
  (Assumption.create
    "Native Float non-strict ordering equals ordered JSNumber not-greater-than on canonical operands."
    "Float.decLe is an executable runtime primitive.").get (by decide)

/-- Assumption metadata for native IEEE Float equality. -/
def strictEqualAssumption : Assumption :=
  (Assumption.create "Float.beq equals JSNumber.strictEqual on canonical operands."
    "Float.beq is an executable runtime primitive.").get (by decide)

/-- Ledger-ready assumption metadata in runtime-contract field order. -/
def runtimeAssumptionRegistry : List Assumption :=
  [bridgeSameValueRoundtripAssumption, addAssumption, subtractAssumption, multiplyAssumption,
    divideAssumption, lessThanAssumption, lessThanOrEqualAssumption, strictEqualAssumption]

/-- Valid requirements for the bridge SameValue roundtrip field. -/
def bridgeSameValueRoundtripRequirements : ValidAssumptions :=
  ValidAssumptions.singleton bridgeSameValueRoundtripAssumption (by
    unfold bridgeSameValueRoundtripAssumption
    apply Assumption.valid_get_create)

/-- Valid requirements for the addition field. -/
def addRequirements : ValidAssumptions :=
  ValidAssumptions.singleton addAssumption (by
    unfold addAssumption
    apply Assumption.valid_get_create)

/-- Valid requirements for the subtraction field. -/
def subtractRequirements : ValidAssumptions :=
  ValidAssumptions.singleton subtractAssumption (by
    unfold subtractAssumption
    apply Assumption.valid_get_create)

/-- Valid requirements for the multiplication field. -/
def multiplyRequirements : ValidAssumptions :=
  ValidAssumptions.singleton multiplyAssumption (by
    unfold multiplyAssumption
    apply Assumption.valid_get_create)

/-- Valid requirements for the division field. -/
def divideRequirements : ValidAssumptions :=
  ValidAssumptions.singleton divideAssumption (by
    unfold divideAssumption
    apply Assumption.valid_get_create)

/-- Valid requirements for the strict-ordering field. -/
def lessThanRequirements : ValidAssumptions :=
  ValidAssumptions.singleton lessThanAssumption (by
    unfold lessThanAssumption
    apply Assumption.valid_get_create)

/-- Valid requirements for the non-strict-ordering field. -/
def lessThanOrEqualRequirements : ValidAssumptions :=
  ValidAssumptions.singleton lessThanOrEqualAssumption (by
    unfold lessThanOrEqualAssumption
    apply Assumption.valid_get_create)

/-- Valid requirements for the strict-equality field. -/
def strictEqualRequirements : ValidAssumptions :=
  ValidAssumptions.singleton strictEqualAssumption (by
    unfold strictEqualAssumption
    apply Assumption.valid_get_create)

/-- Assumed evidence exposing the bridge SameValue roundtrip requirement without proving it. -/
def bridgeSameValueRoundtripEvidence : Evidence BridgeSameValueRoundtrip :=
  Evidence.assumed bridgeSameValueRoundtripRequirements

/-- Assumed evidence exposing the Float addition requirement without proving it. -/
def addEvidence : Evidence Add := Evidence.assumed addRequirements

/-- Assumed evidence exposing the Float subtraction requirement without proving it. -/
def subtractEvidence : Evidence Subtract :=
  Evidence.assumed subtractRequirements

/-- Assumed evidence exposing the Float multiplication requirement without proving it. -/
def multiplyEvidence : Evidence Multiply :=
  Evidence.assumed multiplyRequirements

/-- Assumed evidence exposing the Float division requirement without proving it. -/
def divideEvidence : Evidence Divide := Evidence.assumed divideRequirements

/-- Assumed evidence exposing the Float strict-ordering requirement without proving it. -/
def lessThanEvidence : Evidence LessThan :=
  Evidence.assumed lessThanRequirements

/-- Assumed evidence exposing the Float non-strict-ordering requirement without proving it. -/
def lessThanOrEqualEvidence : Evidence LessThanOrEqual :=
  Evidence.assumed lessThanOrEqualRequirements

/-- Assumed evidence exposing the Float strict-equality requirement without proving it. -/
def strictEqualEvidence : Evidence StrictEqual :=
  Evidence.assumed strictEqualRequirements

/-- Proof-backed evidence for a supplied bridge law. -/
def provedBridgeSameValueRoundtrip (law : BridgeSameValueRoundtrip) :
    Evidence BridgeSameValueRoundtrip :=
  Evidence.proved law

/-- Proof-backed evidence for a supplied addition law. -/
def provedAdd (law : Add) : Evidence Add := Evidence.proved law

/-- Proof-backed evidence for a supplied subtraction law. -/
def provedSubtract (law : Subtract) : Evidence Subtract := Evidence.proved law

/-- Proof-backed evidence for a supplied multiplication law. -/
def provedMultiply (law : Multiply) : Evidence Multiply := Evidence.proved law

/-- Proof-backed evidence for a supplied division law. -/
def provedDivide (law : Divide) : Evidence Divide := Evidence.proved law

/-- Proof-backed evidence for a supplied strict-ordering law. -/
def provedLessThan (law : LessThan) : Evidence LessThan := Evidence.proved law

/-- Proof-backed evidence for a supplied non-strict-ordering law. -/
def provedLessThanOrEqual (law : LessThanOrEqual) :
    Evidence LessThanOrEqual := Evidence.proved law

/-- Proof-backed evidence for a supplied strict-equality law. -/
def provedStrictEqual (law : StrictEqual) : Evidence StrictEqual := Evidence.proved law

end Float

end TSLean.Refinement
