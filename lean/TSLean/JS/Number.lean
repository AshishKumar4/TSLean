import Init.Data.Float
import Init.Data.UInt

namespace TSLean.JS

/-- An ECMAScript Number represented by its exact IEEE-754 binary64 encoding. -/
structure JSNumber where
  bits : UInt64
  deriving DecidableEq

namespace JSNumber

private def exponentMask : UInt64 := 0x7ff0000000000000
private def fractionMask : UInt64 := 0x000fffffffffffff
private def signMask : UInt64 := 0x8000000000000000

/-- Positive zero. -/
def positiveZero : JSNumber := ⟨0x0000000000000000⟩

/-- Negative zero. -/
def negativeZero : JSNumber := ⟨0x8000000000000000⟩

/-- Positive infinity. -/
def positiveInfinity : JSNumber := ⟨0x7ff0000000000000⟩

/-- Negative infinity. -/
def negativeInfinity : JSNumber := ⟨0xfff0000000000000⟩

/-- The canonical quiet NaN used when this model must produce a NaN. -/
def canonicalNaN : JSNumber := ⟨0x7ff8000000000000⟩

/-- Reports whether the encoding is any positive or negative zero. -/
def isZero (value : JSNumber) : Bool :=
  (value.bits &&& ~~~signMask) == 0

/-- Reports whether the encoding is positive or negative infinity. -/
def isInfinite (value : JSNumber) : Bool :=
  (value.bits &&& exponentMask) == exponentMask &&
    (value.bits &&& fractionMask) == 0

/-- Reports whether the encoding is any quiet or signaling NaN. -/
def isNaN (value : JSNumber) : Bool :=
  (value.bits &&& exponentMask) == exponentMask &&
    (value.bits &&& fractionMask) != 0

/-- Returns the IEEE-754 sign bit, including for zero and NaN encodings. -/
def sign (value : JSNumber) : Bool := (value.bits &&& signMask) != 0

/-- ECMAScript strict numeric equality. NaN differs from everything and the two zeros agree. -/
def strictEqual (left right : JSNumber) : Bool :=
  if left.isNaN || right.isNaN then false
  else if left.isZero && right.isZero then true
  else left.bits == right.bits

/-- ECMAScript SameValue numeric equality. NaNs agree and signed zeros differ. -/
def sameValue (left right : JSNumber) : Bool :=
  if left.isNaN && right.isNaN then true else left.bits == right.bits

/-- ECMAScript SameValueZero numeric equality. NaNs and signed zeros each agree. -/
def sameValueZero (left right : JSNumber) : Bool :=
  if left.isNaN && right.isNaN then true
  else if left.isZero && right.isZero then true
  else left.bits == right.bits

/-!
`Float.toBits`, `Float.ofBits`, and `Float.add` are trusted executable runtime
primitives. `Float.ofBits` canonicalizes every NaN encoding, so this is not an exact
bridge for NaN payloads, signs, or signaling bits. No theorem in this model assigns
ECMAScript semantics or roundtrip laws to these runtime primitives.
-/

private def ofFloat (value : Float) : JSNumber := ⟨value.toBits⟩

private def toFloat (value : JSNumber) : Float := Float.ofBits value.bits

/--
Passes a number through Lean's executable Float representation. NaNs are
deterministically replaced by `canonicalNaN`; non-NaN preservation is a trusted
runtime property checked by executable boundary tests, not a theorem.
-/
def executableRoundtripCanonicalizingNaN (value : JSNumber) : JSNumber :=
  if value.isNaN then canonicalNaN else ofFloat value.toFloat

/--
Executes addition through Lean's Float primitive. Any NaN input or result is
deterministically replaced by `canonicalNaN`.
-/
def add (left right : JSNumber) : JSNumber :=
  if left.isNaN || right.isNaN then
    canonicalNaN
  else
    let result := ofFloat (Float.add left.toFloat right.toFloat)
    if result.isNaN then canonicalNaN else result

end JSNumber
end TSLean.JS
