import TSLean.Refinement.Core
import TSLean.JS.Equality
import TSLean.JS.Monad
import TSLean.JS.PrimitiveTheorems

namespace TSLean.Refinement

open TSLean.JS

namespace Primitive

/-- Lifting a pure result into `JSM` leaves the complete machine, including heap and trace,
unchanged. -/
theorem jsm_pure_neutral (result : α) (machine : Machine P) :
    JSM.pure result machine = .done (.normal result) machine := rfl

end Primitive

namespace Bool

/-- A Boolean codec rejects every JavaScript value outside the Boolean primitive domain. -/
inductive DecodeFault where
  | expectedBoolean
  deriving DecidableEq, Repr

/-- Lean Booleans refine exactly their corresponding JavaScript Boolean primitives. -/
def refinement : Refinement _root_.Bool where
  Rel _ native value := value = .primitive (.boolean native)
  valueValid related := by cases related; rfl
  stable _ related := related

/-- The Boolean refinement relation is exactly primitive Boolean equality and is heap-independent. -/
theorem refinement_rel_iff (heap : Heap) (native : _root_.Bool) (value : Value) :
    refinement.Rel heap native value ↔ value = .primitive (.boolean native) := Iff.rfl

/-- The Boolean refinement has a unique native decoding. -/
theorem refinement_uniqueDecode : refinement.UniqueDecode := by
  intro heap left right value leftRelated rightRelated
  simp only [refinement] at leftRelated rightRelated
  rw [leftRelated] at rightRelated
  exact Primitive.boolean.inj (Value.primitive.inj rightRelated)

/-- Encodes a Lean Boolean as its exact primitive without changing the heap. -/
def encode (heap : Heap) (native : _root_.Bool) : Except Empty (Value × Heap) :=
  .ok (.primitive (.boolean native), heap)

/-- Decodes only JavaScript Boolean primitives. -/
def decode (_ : Heap) (value : Value) : Except DecodeFault _root_.Bool :=
  match value with
    | .primitive (.boolean native) => .ok native
    | _ => .error .expectedBoolean

/-- Total, heap-neutral encoding and typed decoding for JavaScript Boolean primitives. -/
def codec : Codec _root_.Bool Empty DecodeFault refinement where
  encode := encode
  decode := decode
  encode_sound := by
    intro old native value next valid encoded
    simp only [encode, Except.ok.injEq, Prod.mk.injEq] at encoded
    rcases encoded with ⟨rfl, rfl⟩
    exact ⟨Heap.ExactExtension.refl old valid, rfl⟩
  decode_sound := by
    intro heap value native decoded
    cases value with
    | object ref => simp [decode] at decoded
    | primitive primitive =>
        cases primitive <;> simp [decode] at decoded
        rename_i actual
        cases decoded
        rfl

/-- Boolean encoding returns the exact primitive without changing the heap. -/
theorem encode_exact (heap : Heap) (native : _root_.Bool) :
    codec.encode heap native = .ok (.primitive (.boolean native), heap) := rfl

/-- Boolean decoding accepts the exact corresponding primitive. -/
theorem decode_exact (heap : Heap) (native : _root_.Bool) :
    codec.decode heap (.primitive (.boolean native)) = .ok native := rfl

/-- Boolean decoding rejects every non-Boolean primitive with its typed fault. -/
theorem decode_nonboolean (heap : Heap) (primitive : JS.Primitive)
    (notBoolean : ∀ value, primitive ≠ .boolean value) :
    codec.decode heap (.primitive primitive) = .error .expectedBoolean := by
  cases primitive <;> simp_all [codec, decode]

/-- Boolean decoding rejects object references with its typed fault. -/
theorem decode_object (heap : Heap) (ref : RefId) :
    codec.decode heap (.object ref) = .error .expectedBoolean := rfl

/-- The Boolean codec is total and complete for the exact primitive relation. -/
theorem codec_lawful : LawfulCodec codec where
  encode_total heap native valid := ⟨.primitive (.boolean native), heap, rfl⟩
  complete := by
    intro heap native value related
    cases related
    rfl

/-- Boolean codec roundtrip is exact and heap-neutral. -/
theorem codec_roundtrip (heap : Heap) (native : _root_.Bool) (valid : heap.WellFormed) :
    ∃ value next,
      codec.encode heap native = .ok (value, next) ∧
      value = .primitive (.boolean native) ∧
      next = heap ∧
      codec.decode next value = .ok native := by
  refine ⟨.primitive (.boolean native), heap, encode_exact heap native, rfl, rfl, ?_⟩
  exact codec_lawful.roundtrip valid (encode_exact heap native)

/-- JavaScript ToBoolean commutes with exact Boolean refinement. -/
theorem toBoolean_commutes (native : _root_.Bool) :
    (Value.primitive (.boolean native)).toBoolean = native := rfl

/-- JavaScript strict equality on refined Booleans is Lean Boolean equality. -/
theorem strictEqual_commutes (left right : _root_.Bool) :
    strictEqual (.primitive (.boolean left)) (.primitive (.boolean right)) = (left == right) := rfl

/-- JavaScript SameValue on refined Booleans is Lean Boolean equality. -/
theorem sameValue_commutes (left right : _root_.Bool) :
    sameValue (.primitive (.boolean left)) (.primitive (.boolean right)) = (left == right) := rfl

/-- JavaScript SameValueZero on refined Booleans is Lean Boolean equality. -/
theorem sameValueZero_commutes (left right : _root_.Bool) :
    sameValueZero (.primitive (.boolean left)) (.primitive (.boolean right)) = (left == right) := rfl

/-- JavaScript loose equality on refined Booleans is Lean Boolean equality. -/
theorem looseEqual_commutes (left right : _root_.Bool) :
    (JS.Primitive.boolean left).looseEqual (.boolean right) = (left == right) := rfl

/-- JavaScript logical negation commutes with Lean Boolean negation. -/
theorem not_commutes (native : _root_.Bool) :
    _root_.Bool.not (Value.primitive (.boolean native)).toBoolean = !native := rfl

/-- Boolean-only conditional selection chooses the same branch in JavaScript and Lean. -/
theorem select_commutes (condition : _root_.Bool) (whenTrue whenFalse : α) :
    (if (Value.primitive (.boolean condition)).toBoolean then whenTrue else whenFalse) =
      if condition then whenTrue else whenFalse := rfl

end Bool

namespace BigInt

/-- A BigInt codec rejects every JavaScript value outside the BigInt primitive domain. -/
inductive DecodeFault where
  | expectedBigInt
  deriving DecidableEq, Repr

/-- Lean integers refine exactly JavaScript BigInt primitives, never Number values. -/
def refinement : Refinement Int where
  Rel _ native value := value = .primitive (.bigint native)
  valueValid related := by cases related; rfl
  stable _ related := related

/-- The BigInt refinement relation is exactly primitive BigInt equality and is heap-independent. -/
theorem refinement_rel_iff (heap : Heap) (native : Int) (value : Value) :
    refinement.Rel heap native value ↔ value = .primitive (.bigint native) := Iff.rfl

/-- The BigInt refinement has a unique native decoding. -/
theorem refinement_uniqueDecode : refinement.UniqueDecode := by
  intro heap left right value leftRelated rightRelated
  simp only [refinement] at leftRelated rightRelated
  rw [leftRelated] at rightRelated
  exact JS.Primitive.bigint.inj (Value.primitive.inj rightRelated)

/-- Encodes a Lean integer as its exact BigInt primitive without changing the heap. -/
def encode (heap : Heap) (native : Int) : Except Empty (Value × Heap) :=
  .ok (.primitive (.bigint native), heap)

/-- Decodes only JavaScript BigInt primitives. -/
def decode (_ : Heap) (value : Value) : Except DecodeFault Int :=
  match value with
    | .primitive (.bigint native) => .ok native
    | _ => .error .expectedBigInt

/-- Total, heap-neutral encoding and typed decoding for JavaScript BigInt primitives. -/
def codec : Codec Int Empty DecodeFault refinement where
  encode := encode
  decode := decode
  encode_sound := by
    intro old native value next valid encoded
    simp only [encode, Except.ok.injEq, Prod.mk.injEq] at encoded
    rcases encoded with ⟨rfl, rfl⟩
    exact ⟨Heap.ExactExtension.refl old valid, rfl⟩
  decode_sound := by
    intro heap value native decoded
    cases value with
    | object ref => simp [decode] at decoded
    | primitive primitive =>
        cases primitive <;> simp [decode] at decoded
        rename_i actual
        cases decoded
        rfl

/-- BigInt encoding returns the exact primitive without changing the heap. -/
theorem encode_exact (heap : Heap) (native : Int) :
    codec.encode heap native = .ok (.primitive (.bigint native), heap) := rfl

/-- BigInt decoding accepts the exact corresponding primitive. -/
theorem decode_exact (heap : Heap) (native : Int) :
    codec.decode heap (.primitive (.bigint native)) = .ok native := rfl

/-- BigInt decoding rejects every non-BigInt primitive with its typed fault. -/
theorem decode_nonbigint (heap : Heap) (primitive : JS.Primitive)
    (notBigInt : ∀ value, primitive ≠ .bigint value) :
    codec.decode heap (.primitive primitive) = .error .expectedBigInt := by
  cases primitive <;> simp_all [codec, decode]

/-- BigInt decoding rejects object references with its typed fault. -/
theorem decode_object (heap : Heap) (ref : RefId) :
    codec.decode heap (.object ref) = .error .expectedBigInt := rfl

/-- The BigInt codec is total and complete for the exact primitive relation. -/
theorem codec_lawful : LawfulCodec codec where
  encode_total heap native valid := ⟨.primitive (.bigint native), heap, rfl⟩
  complete := by
    intro heap native value related
    cases related
    rfl

/-- BigInt codec roundtrip is exact and heap-neutral. -/
theorem codec_roundtrip (heap : Heap) (native : Int) (valid : heap.WellFormed) :
    ∃ value next,
      codec.encode heap native = .ok (value, next) ∧
      value = .primitive (.bigint native) ∧
      next = heap ∧
      codec.decode next value = .ok native := by
  refine ⟨.primitive (.bigint native), heap, encode_exact heap native, rfl, rfl, ?_⟩
  exact codec_lawful.roundtrip valid (encode_exact heap native)

/-- JavaScript BigInt truthiness is exact nonzero testing on Lean integers. -/
theorem toBoolean_commutes (native : Int) :
    (Value.primitive (.bigint native)).toBoolean = (native != 0) := rfl

/-- JavaScript strict equality on refined BigInts is Lean integer equality. -/
theorem strictEqual_commutes (left right : Int) :
    strictEqual (.primitive (.bigint left)) (.primitive (.bigint right)) = (left == right) := rfl

/-- JavaScript SameValue on refined BigInts is Lean integer equality. -/
theorem sameValue_commutes (left right : Int) :
    sameValue (.primitive (.bigint left)) (.primitive (.bigint right)) = (left == right) := rfl

/-- JavaScript SameValueZero on refined BigInts is Lean integer equality. -/
theorem sameValueZero_commutes (left right : Int) :
    sameValueZero (.primitive (.bigint left)) (.primitive (.bigint right)) = (left == right) := rfl

/-- JavaScript loose equality on refined BigInts is Lean integer equality. -/
theorem looseEqual_commutes (left right : Int) :
    (JS.Primitive.bigint left).looseEqual (.bigint right) = (left == right) := rfl

/-- JavaScript BigInt ToString is Lean signed decimal rendering encoded as UTF-16. -/
theorem toString_commutes (native : Int) :
    (JS.Primitive.bigint native).toString = .ok (JSString.ofLeanString native.repr) := rfl

/-- JavaScript BigInt addition is exact Lean integer addition. -/
theorem add_commutes (left right : Int) :
    JS.Primitive.add (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left + right))) := rfl

/-- JavaScript BigInt subtraction is exact Lean integer subtraction. -/
theorem subtract_commutes (left right : Int) :
    JS.Primitive.subtract (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left - right))) := rfl

/-- JavaScript BigInt multiplication is exact Lean integer multiplication. -/
theorem multiply_commutes (left right : Int) :
    JS.Primitive.multiply (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left * right))) := rfl

/-- JavaScript BigInt `<` is exact Lean integer ordering. -/
theorem lessThan_commutes (left right : Int) :
    JS.Primitive.lessThan (.bigint left) (.bigint right) = .ok (decide (left < right)) := rfl

/-- JavaScript BigInt `>` is exact Lean integer ordering. -/
theorem greaterThan_commutes (left right : Int) :
    JS.Primitive.greaterThan (.bigint left) (.bigint right) = .ok (decide (left > right)) := rfl

/-- JavaScript BigInt `<=` is exact Lean integer ordering. -/
theorem lessThanOrEqual_commutes (left right : Int) :
    JS.Primitive.lessThanOrEqual (.bigint left) (.bigint right) = .ok (decide (left ≤ right)) := by
  have compared : JS.Primitive.abstractRelationalComparison (.bigint right) (.bigint left) false =
      .ok (some (decide (right < left))) := rfl
  unfold JS.Primitive.lessThanOrEqual
  rw [compared]
  by_cases ordered : right < left
  · have nativeOrder : ¬left ≤ right := Int.not_le_of_gt ordered
    simp [ordered, nativeOrder, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have nativeOrder : left ≤ right := Int.not_lt.mp ordered
    simp [ordered, nativeOrder, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- JavaScript BigInt `>=` is exact Lean integer ordering. -/
theorem greaterThanOrEqual_commutes (left right : Int) :
    JS.Primitive.greaterThanOrEqual (.bigint left) (.bigint right) = .ok (decide (left ≥ right)) := by
  have compared : JS.Primitive.abstractRelationalComparison (.bigint left) (.bigint right) =
      .ok (some (decide (left < right))) := rfl
  unfold JS.Primitive.greaterThanOrEqual
  rw [compared]
  by_cases ordered : left < right
  · have nativeOrder : ¬right ≤ left := Int.not_le_of_gt ordered
    simp [ordered, nativeOrder, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have nativeOrder : right ≤ left := Int.not_lt.mp ordered
    simp [ordered, nativeOrder, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Nonzero JavaScript BigInt division is exactly Lean truncating division. -/
theorem divide_commutes (left right : Int) (nonzero : right ≠ 0) :
    JS.Primitive.divide (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left.tdiv right))) := by
  cases right <;> simp_all [JS.Primitive.divide, JS.Primitive.toNumeric, JS.Numeric.divide,
    JS.Numeric.toValue, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- JavaScript BigInt division by zero returns the committed coercion fault. -/
theorem divide_zero (left : Int) :
    JS.Primitive.divide (.bigint left) (.bigint 0) = .error .bigintDivisionByZero := rfl

/-- Nonzero JavaScript BigInt remainder is exactly Lean truncating remainder. -/
theorem remainder_commutes (left right : Int) (nonzero : right ≠ 0) :
    JS.Primitive.remainder (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left.tmod right))) := by
  cases right <;> simp_all [JS.Primitive.remainder, JS.Primitive.toNumeric, JS.Numeric.remainder,
    JS.Numeric.toValue, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- JavaScript BigInt remainder by zero returns the committed coercion fault. -/
theorem remainder_zero (left : Int) :
    JS.Primitive.remainder (.bigint left) (.bigint 0) = .error .bigintDivisionByZero := rfl

end BigInt

end TSLean.Refinement
