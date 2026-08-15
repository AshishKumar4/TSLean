import TSLean.Refinement.Float

namespace TSLean.Refinement

open TSLean.JS

/-!
# The ECMAScript `Math` object, in three tiers

* **Tier 1 — proved, no assumption of its own.** `abs`, `sign`, `trunc`, `floor`, `ceil`,
  `round`, `max`, `min`, and the six constants are computed from the binary64 encoding by
  exact integer arithmetic in `JSNumber.Math`, so what they return is a theorem of this
  development rather than a property of a runtime primitive. The native carriers below
  reach those results through `Float.ofBits`, so they carry the
  `Float.BridgeSameValueRoundtrip` law every native Float carrier already carries and add
  nothing to the ledger.
* **Tier 2 — assumed, exactly one law.** IEEE-754 mandates a correctly rounded square
  root, so `Sqrt` says that Lean's `Float.sqrt` is the platform's and says nothing else.
* **Tier 3 — absent.** ECMA-262 permits implementation-approximated results for `exp`,
  `log`, `log2`, `log10`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `pow`,
  `cbrt`, and `hypot`, so no carrier for them can claim bit equality with a host and none
  is offered here.
-/

namespace Math

/-- Node's exact binary64 encoding of `Math.PI`, as a native carrier. -/
def PI : _root_.Float := JSNumber.Math.PI.toFloat

/-- Node's exact binary64 encoding of `Math.E`, as a native carrier. -/
def E : _root_.Float := JSNumber.Math.E.toFloat

/-- Node's exact binary64 encoding of `Math.LN2`, as a native carrier. -/
def LN2 : _root_.Float := JSNumber.Math.LN2.toFloat

/-- Node's exact binary64 encoding of `Math.LN10`, as a native carrier. -/
def LN10 : _root_.Float := JSNumber.Math.LN10.toFloat

/-- Node's exact binary64 encoding of `Math.SQRT2`, as a native carrier. -/
def SQRT2 : _root_.Float := JSNumber.Math.SQRT2.toFloat

/-- Node's exact binary64 encoding of `Math.SQRT1_2`, as a native carrier. -/
def SQRT1_2 : _root_.Float := JSNumber.Math.SQRT1_2.toFloat

/-- The executable native `Math.abs` bridge over the committed Number operation. -/
def abs (value : _root_.Float) : _root_.Float :=
  (JSNumber.Math.abs (JSNumber.ofFloatCanonical value)).toFloat

/-- The executable native `Math.sign` bridge over the committed Number operation. -/
def sign (value : _root_.Float) : _root_.Float :=
  (JSNumber.Math.sign (JSNumber.ofFloatCanonical value)).toFloat

/-- The executable native `Math.trunc` bridge over the committed Number operation. -/
def trunc (value : _root_.Float) : _root_.Float :=
  (JSNumber.Math.trunc (JSNumber.ofFloatCanonical value)).toFloat

/-- The executable native `Math.floor` bridge over the committed Number operation. -/
def floor (value : _root_.Float) : _root_.Float :=
  (JSNumber.Math.floor (JSNumber.ofFloatCanonical value)).toFloat

/-- The executable native `Math.ceil` bridge over the committed Number operation. -/
def ceil (value : _root_.Float) : _root_.Float :=
  (JSNumber.Math.ceil (JSNumber.ofFloatCanonical value)).toFloat

/-- The executable native `Math.round` bridge over the committed Number operation. -/
def round (value : _root_.Float) : _root_.Float :=
  (JSNumber.Math.round (JSNumber.ofFloatCanonical value)).toFloat

/-- The executable native `Math.max` bridge over the committed Number operation. -/
def max (left right : _root_.Float) : _root_.Float :=
  (JSNumber.Math.max (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right)).toFloat

/-- The executable native `Math.min` bridge over the committed Number operation. -/
def min (left right : _root_.Float) : _root_.Float :=
  (JSNumber.Math.min (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right)).toFloat

/-- Runtime law relating `Float.sqrt` to the committed Number square root. -/
def Sqrt : Prop := ∀ value,
    JSNumber.sameValue (JSNumber.ofFloatCanonical (_root_.Float.sqrt value))
      (JSNumber.Math.sqrt (JSNumber.ofFloatCanonical value)) = true

/-- Two Numbers whose encodings neither precede the other as unsigned integers agree. -/
private theorem eq_of_not_lt {left right : JSNumber}
    (leftNotLess : ¬ left.bits.toNat < right.bits.toNat)
    (rightNotLess : ¬ right.bits.toNat < left.bits.toNat) : left = right := by
  have same : left.bits.toNat = right.bits.toNat := by omega
  cases left
  cases right
  simpa using UInt64.toNat_inj.mp same

/-- The six Math constants carry the exact binary64 encodings Node reports. -/
theorem constants_exact :
    JSNumber.Math.PI.bits = 0x400921fb54442d18 ∧
    JSNumber.Math.E.bits = 0x4005bf0a8b145769 ∧
    JSNumber.Math.LN2.bits = 0x3fe62e42fefa39ef ∧
    JSNumber.Math.LN10.bits = 0x40026bb1bbb55516 ∧
    JSNumber.Math.SQRT2.bits = 0x3ff6a09e667f3bcd ∧
    JSNumber.Math.SQRT1_2.bits = 0x3fe6a09e667f3bcd := by decide

/-- `Math.max` is NaN-poisoning in either argument position. -/
theorem max_nan (left right : JSNumber) (nan : (left.isNaN || right.isNaN) = true) :
    JSNumber.Math.max left right = JSNumber.canonicalNaN := by
  simp [JSNumber.Math.max, nan]

/-- `Math.min` is NaN-poisoning in either argument position. -/
theorem min_nan (left right : JSNumber) (nan : (left.isNaN || right.isNaN) = true) :
    JSNumber.Math.min left right = JSNumber.canonicalNaN := by
  simp [JSNumber.Math.min, nan]

/-- `Math.max` does not depend on the order of its arguments. -/
theorem max_comm (left right : JSNumber) :
    JSNumber.Math.max left right = JSNumber.Math.max right left := by
  unfold JSNumber.Math.max JSNumber.Math.orderedLess
  cases leftNaN : left.isNaN <;> cases rightNaN : right.isNaN <;>
    cases leftZero : left.isZero <;> cases rightZero : right.isZero <;>
      cases leftSign : left.sign <;> cases rightSign : right.sign <;>
        simp_all <;> split <;> split <;>
        first
          | rfl
          | omega
          | exact eq_of_not_lt (by omega) (by omega)
          | exact (eq_of_not_lt (by omega) (by omega)).symm

/-- `Math.min` does not depend on the order of its arguments. -/
theorem min_comm (left right : JSNumber) :
    JSNumber.Math.min left right = JSNumber.Math.min right left := by
  unfold JSNumber.Math.min JSNumber.Math.orderedLess
  cases leftNaN : left.isNaN <;> cases rightNaN : right.isNaN <;>
    cases leftZero : left.isZero <;> cases rightZero : right.isZero <;>
      cases leftSign : left.sign <;> cases rightSign : right.sign <;>
        simp_all <;> split <;> split <;>
        first
          | rfl
          | omega
          | exact eq_of_not_lt (by omega) (by omega)
          | exact (eq_of_not_lt (by omega) (by omega)).symm

/-- `Math.max` over the four ordered pairs of zeros prefers `+0`. -/
theorem max_signedZero :
    JSNumber.Math.max JSNumber.positiveZero JSNumber.negativeZero = JSNumber.positiveZero ∧
    JSNumber.Math.max JSNumber.negativeZero JSNumber.positiveZero = JSNumber.positiveZero ∧
    JSNumber.Math.max JSNumber.positiveZero JSNumber.positiveZero = JSNumber.positiveZero ∧
    JSNumber.Math.max JSNumber.negativeZero JSNumber.negativeZero = JSNumber.negativeZero := by
  decide

/-- `Math.min` over the four ordered pairs of zeros prefers `-0`. -/
theorem min_signedZero :
    JSNumber.Math.min JSNumber.positiveZero JSNumber.negativeZero = JSNumber.negativeZero ∧
    JSNumber.Math.min JSNumber.negativeZero JSNumber.positiveZero = JSNumber.negativeZero ∧
    JSNumber.Math.min JSNumber.positiveZero JSNumber.positiveZero = JSNumber.positiveZero ∧
    JSNumber.Math.min JSNumber.negativeZero JSNumber.negativeZero = JSNumber.negativeZero := by
  decide

/-- `Math.sign` of a nonzero Number is one of the two units, chosen by the sign bit. -/
theorem sign_nonzero (value : JSNumber) (notNaN : value.isNaN = false)
    (nonzero : value.isZero = false) :
    JSNumber.Math.sign value = if value.sign then JSNumber.negativeOne else JSNumber.one := by
  simp [JSNumber.Math.sign, notNaN, nonzero]

/-- `Math.sign` returns each zero unchanged, so `-0` does not become `+0`. -/
theorem sign_signedZero :
    JSNumber.Math.sign JSNumber.positiveZero = JSNumber.positiveZero ∧
    JSNumber.Math.sign JSNumber.negativeZero = JSNumber.negativeZero := by decide

/-- `Math.abs` maps both zeros to `+0`. -/
theorem abs_signedZero :
    JSNumber.Math.abs JSNumber.positiveZero = JSNumber.positiveZero ∧
    JSNumber.Math.abs JSNumber.negativeZero = JSNumber.positiveZero := by decide

/--
`Math.round` rounds halves towards `+∞`: `round (-0.5)` is `-0`, `round 0.5` is `1`,
`round (-1.5)` is `-1`, and `round 2.5` is `3`.
-/
theorem round_halves :
    JSNumber.Math.round ⟨0xbfe0000000000000⟩ = JSNumber.negativeZero ∧
    JSNumber.Math.round ⟨0x3fe0000000000000⟩ = ⟨0x3ff0000000000000⟩ ∧
    JSNumber.Math.round ⟨0xbff8000000000000⟩ = JSNumber.negativeOne ∧
    JSNumber.Math.round ⟨0x4004000000000000⟩ = ⟨0x4008000000000000⟩ := by decide

/--
`Math.trunc`, `Math.floor`, and `Math.ceil` at `±0.5`: only `floor` leaves the unit
interval, and the three results that stay inside it keep the sign of their argument.
-/
theorem integral_halves :
    JSNumber.Math.trunc ⟨0x3fe0000000000000⟩ = JSNumber.positiveZero ∧
    JSNumber.Math.trunc ⟨0xbfe0000000000000⟩ = JSNumber.negativeZero ∧
    JSNumber.Math.floor ⟨0x3fe0000000000000⟩ = JSNumber.positiveZero ∧
    JSNumber.Math.floor ⟨0xbfe0000000000000⟩ = JSNumber.negativeOne ∧
    JSNumber.Math.ceil ⟨0x3fe0000000000000⟩ = JSNumber.one ∧
    JSNumber.Math.ceil ⟨0xbfe0000000000000⟩ = JSNumber.negativeZero := by decide

/-- The integral operations and `Math.abs` fix the infinities, and `Math.sign` maps them to units. -/
theorem infinities :
    JSNumber.Math.trunc JSNumber.positiveInfinity = JSNumber.positiveInfinity ∧
    JSNumber.Math.floor JSNumber.negativeInfinity = JSNumber.negativeInfinity ∧
    JSNumber.Math.ceil JSNumber.negativeInfinity = JSNumber.negativeInfinity ∧
    JSNumber.Math.round JSNumber.positiveInfinity = JSNumber.positiveInfinity ∧
    JSNumber.Math.abs JSNumber.negativeInfinity = JSNumber.positiveInfinity ∧
    JSNumber.Math.sign JSNumber.negativeInfinity = JSNumber.negativeOne ∧
    JSNumber.Math.max JSNumber.positiveInfinity JSNumber.negativeInfinity =
      JSNumber.positiveInfinity ∧
    JSNumber.Math.min JSNumber.positiveInfinity JSNumber.negativeInfinity =
      JSNumber.negativeInfinity := by decide

/-- The native Math constants commute with their committed Number encodings under the bridge law. -/
theorem constants_commute (bridge : Float.BridgeSameValueRoundtrip) :
    Float.refinement.Rel Heap.empty PI (.primitive (.number JSNumber.Math.PI)) ∧
    Float.refinement.Rel Heap.empty E (.primitive (.number JSNumber.Math.E)) ∧
    Float.refinement.Rel Heap.empty LN2 (.primitive (.number JSNumber.Math.LN2)) ∧
    Float.refinement.Rel Heap.empty LN10 (.primitive (.number JSNumber.Math.LN10)) ∧
    Float.refinement.Rel Heap.empty SQRT2 (.primitive (.number JSNumber.Math.SQRT2)) ∧
    Float.refinement.Rel Heap.empty SQRT1_2 (.primitive (.number JSNumber.Math.SQRT1_2)) :=
  ⟨bridge JSNumber.Math.PI, bridge JSNumber.Math.E, bridge JSNumber.Math.LN2,
    bridge JSNumber.Math.LN10, bridge JSNumber.Math.SQRT2, bridge JSNumber.Math.SQRT1_2⟩

/-- The native absolute-value bridge commutes with committed `Math.abs` under the bridge law. -/
theorem abs_commutes (bridge : Float.BridgeSameValueRoundtrip) (value : _root_.Float) :
    Float.refinement.Rel Heap.empty (abs value)
      (.primitive (.number (JSNumber.Math.abs (JSNumber.ofFloatCanonical value)))) :=
  bridge (JSNumber.Math.abs (JSNumber.ofFloatCanonical value))

/-- The native sign bridge commutes with committed `Math.sign` under the bridge law. -/
theorem sign_commutes (bridge : Float.BridgeSameValueRoundtrip) (value : _root_.Float) :
    Float.refinement.Rel Heap.empty (sign value)
      (.primitive (.number (JSNumber.Math.sign (JSNumber.ofFloatCanonical value)))) :=
  bridge (JSNumber.Math.sign (JSNumber.ofFloatCanonical value))

/-- The native truncation bridge commutes with committed `Math.trunc` under the bridge law. -/
theorem trunc_commutes (bridge : Float.BridgeSameValueRoundtrip) (value : _root_.Float) :
    Float.refinement.Rel Heap.empty (trunc value)
      (.primitive (.number (JSNumber.Math.trunc (JSNumber.ofFloatCanonical value)))) :=
  bridge (JSNumber.Math.trunc (JSNumber.ofFloatCanonical value))

/-- The native floor bridge commutes with committed `Math.floor` under the bridge law. -/
theorem floor_commutes (bridge : Float.BridgeSameValueRoundtrip) (value : _root_.Float) :
    Float.refinement.Rel Heap.empty (floor value)
      (.primitive (.number (JSNumber.Math.floor (JSNumber.ofFloatCanonical value)))) :=
  bridge (JSNumber.Math.floor (JSNumber.ofFloatCanonical value))

/-- The native ceiling bridge commutes with committed `Math.ceil` under the bridge law. -/
theorem ceil_commutes (bridge : Float.BridgeSameValueRoundtrip) (value : _root_.Float) :
    Float.refinement.Rel Heap.empty (ceil value)
      (.primitive (.number (JSNumber.Math.ceil (JSNumber.ofFloatCanonical value)))) :=
  bridge (JSNumber.Math.ceil (JSNumber.ofFloatCanonical value))

/-- The native rounding bridge commutes with committed `Math.round` under the bridge law. -/
theorem round_commutes (bridge : Float.BridgeSameValueRoundtrip) (value : _root_.Float) :
    Float.refinement.Rel Heap.empty (round value)
      (.primitive (.number (JSNumber.Math.round (JSNumber.ofFloatCanonical value)))) :=
  bridge (JSNumber.Math.round (JSNumber.ofFloatCanonical value))

/-- The native maximum bridge commutes with committed `Math.max` under the bridge law. -/
theorem max_commutes (bridge : Float.BridgeSameValueRoundtrip) (left right : _root_.Float) :
    Float.refinement.Rel Heap.empty (max left right)
      (.primitive (.number (JSNumber.Math.max (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right)))) :=
  bridge (JSNumber.Math.max (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right))

/-- The native minimum bridge commutes with committed `Math.min` under the bridge law. -/
theorem min_commutes (bridge : Float.BridgeSameValueRoundtrip) (left right : _root_.Float) :
    Float.refinement.Rel Heap.empty (min left right)
      (.primitive (.number (JSNumber.Math.min (JSNumber.ofFloatCanonical left)
        (JSNumber.ofFloatCanonical right)))) :=
  bridge (JSNumber.Math.min (JSNumber.ofFloatCanonical left) (JSNumber.ofFloatCanonical right))

/-- Native `Float.sqrt` commutes with committed `Math.sqrt` under the runtime contract. -/
theorem sqrt_commutes (law : Sqrt) (value : _root_.Float) :
    Float.refinement.Rel Heap.empty (_root_.Float.sqrt value)
      (.primitive (.number (JSNumber.Math.sqrt (JSNumber.ofFloatCanonical value)))) := law value

/-- Assumption metadata for the IEEE square root. -/
def sqrtAssumption : Assumption :=
  (Assumption.create
    "Canonical Float.sqrt encoding is SameValue to JSNumber.Math.sqrt on canonical operands."
    ("Float.sqrt is an executable runtime primitive, and IEEE-754 fixes its correctly " ++
      "rounded result.")).get (by decide)

/-- Ledger-ready assumption metadata for the one Math law that is not proved. -/
def runtimeAssumptionRegistry : List Assumption := [sqrtAssumption]

/-- Valid requirements for the square-root field. -/
def sqrtRequirements : ValidAssumptions :=
  ValidAssumptions.singleton sqrtAssumption (by
    unfold sqrtAssumption
    apply Assumption.valid_get_create)

/-- Assumed evidence exposing the square-root requirement without proving it. -/
def sqrtEvidence : Evidence Sqrt := Evidence.assumed sqrtRequirements

/-- Proof-backed evidence for a supplied square-root law. -/
def provedSqrt (law : Sqrt) : Evidence Sqrt := Evidence.proved law

end Math

end TSLean.Refinement
