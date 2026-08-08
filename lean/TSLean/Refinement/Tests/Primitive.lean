import TSLean.Refinement

namespace TSLean.Refinement.Tests

open TSLean.JS

example (result : α) (machine : Machine P) :
    JSM.pure result machine = .done (.normal result) machine :=
  Primitive.jsm_pure_neutral result machine

example (heap : Heap) (native : _root_.Bool) (value : Value) :
    Bool.refinement.Rel heap native value ↔ value = .primitive (.boolean native) :=
  Bool.refinement_rel_iff heap native value

example : Bool.refinement.UniqueDecode := Bool.refinement_uniqueDecode

example (heap : Heap) (native : _root_.Bool) :
    Bool.codec.encode heap native = .ok (.primitive (.boolean native), heap) :=
  Bool.encode_exact heap native

example (heap : Heap) (native : _root_.Bool) :
    Bool.codec.decode heap (.primitive (.boolean native)) = .ok native :=
  Bool.decode_exact heap native

example (heap : Heap) (primitive : JS.Primitive)
    (notBoolean : ∀ value, primitive ≠ .boolean value) :
    Bool.codec.decode heap (.primitive primitive) = .error .expectedBoolean :=
  Bool.decode_nonboolean heap primitive notBoolean

example (heap : Heap) (ref : RefId) :
    Bool.codec.decode heap (.object ref) = .error .expectedBoolean :=
  Bool.decode_object heap ref

example : LawfulCodec Bool.codec := Bool.codec_lawful

example (heap : Heap) (native : _root_.Bool) (valid : heap.WellFormed) :
    ∃ value next,
      Bool.codec.encode heap native = .ok (value, next) ∧
      value = .primitive (.boolean native) ∧
      next = heap ∧
      Bool.codec.decode next value = .ok native :=
  Bool.codec_roundtrip heap native valid

example (native : _root_.Bool) :
    (Value.primitive (.boolean native)).toBoolean = native :=
  Bool.toBoolean_commutes native

example (left right : _root_.Bool) :
    strictEqual (.primitive (.boolean left)) (.primitive (.boolean right)) = (left == right) :=
  Bool.strictEqual_commutes left right

example (left right : _root_.Bool) :
    sameValue (.primitive (.boolean left)) (.primitive (.boolean right)) = (left == right) :=
  Bool.sameValue_commutes left right

example (left right : _root_.Bool) :
    sameValueZero (.primitive (.boolean left)) (.primitive (.boolean right)) = (left == right) :=
  Bool.sameValueZero_commutes left right

example (left right : _root_.Bool) :
    (JS.Primitive.boolean left).looseEqual (.boolean right) = (left == right) :=
  Bool.looseEqual_commutes left right

example (native : _root_.Bool) :
    _root_.Bool.not (Value.primitive (.boolean native)).toBoolean = !native :=
  Bool.not_commutes native

example (condition : _root_.Bool) (whenTrue whenFalse : α) :
    (if (Value.primitive (.boolean condition)).toBoolean then whenTrue else whenFalse) =
      if condition then whenTrue else whenFalse :=
  Bool.select_commutes condition whenTrue whenFalse

example (heap : Heap) (native : Int) (value : Value) :
    BigInt.refinement.Rel heap native value ↔ value = .primitive (.bigint native) :=
  BigInt.refinement_rel_iff heap native value

example : BigInt.refinement.UniqueDecode := BigInt.refinement_uniqueDecode

example (heap : Heap) (native : Int) :
    BigInt.codec.encode heap native = .ok (.primitive (.bigint native), heap) :=
  BigInt.encode_exact heap native

example (heap : Heap) (native : Int) :
    BigInt.codec.decode heap (.primitive (.bigint native)) = .ok native :=
  BigInt.decode_exact heap native

example (heap : Heap) (primitive : JS.Primitive)
    (notBigInt : ∀ value, primitive ≠ .bigint value) :
    BigInt.codec.decode heap (.primitive primitive) = .error .expectedBigInt :=
  BigInt.decode_nonbigint heap primitive notBigInt

example (heap : Heap) (ref : RefId) :
    BigInt.codec.decode heap (.object ref) = .error .expectedBigInt :=
  BigInt.decode_object heap ref

example : LawfulCodec BigInt.codec := BigInt.codec_lawful

example (heap : Heap) (native : Int) (valid : heap.WellFormed) :
    ∃ value next,
      BigInt.codec.encode heap native = .ok (value, next) ∧
      value = .primitive (.bigint native) ∧
      next = heap ∧
      BigInt.codec.decode next value = .ok native :=
  BigInt.codec_roundtrip heap native valid

example (native : Int) :
    (Value.primitive (.bigint native)).toBoolean = (native != 0) :=
  BigInt.toBoolean_commutes native

example (left right : Int) :
    strictEqual (.primitive (.bigint left)) (.primitive (.bigint right)) = (left == right) :=
  BigInt.strictEqual_commutes left right

example (left right : Int) :
    sameValue (.primitive (.bigint left)) (.primitive (.bigint right)) = (left == right) :=
  BigInt.sameValue_commutes left right

example (left right : Int) :
    sameValueZero (.primitive (.bigint left)) (.primitive (.bigint right)) = (left == right) :=
  BigInt.sameValueZero_commutes left right

example (left right : Int) :
    (JS.Primitive.bigint left).looseEqual (.bigint right) = (left == right) :=
  BigInt.looseEqual_commutes left right

example (native : Int) :
    (JS.Primitive.bigint native).toString = .ok (JSString.ofLeanString native.repr) :=
  BigInt.toString_commutes native

example (left right : Int) :
    JS.Primitive.add (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left + right))) :=
  BigInt.add_commutes left right

example (left right : Int) :
    JS.Primitive.subtract (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left - right))) :=
  BigInt.subtract_commutes left right

example (left right : Int) :
    JS.Primitive.multiply (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left * right))) :=
  BigInt.multiply_commutes left right

example (left right : Int) :
    JS.Primitive.lessThan (.bigint left) (.bigint right) = .ok (decide (left < right)) :=
  BigInt.lessThan_commutes left right

example (left right : Int) :
    JS.Primitive.greaterThan (.bigint left) (.bigint right) = .ok (decide (left > right)) :=
  BigInt.greaterThan_commutes left right

example (left right : Int) :
    JS.Primitive.lessThanOrEqual (.bigint left) (.bigint right) = .ok (decide (left ≤ right)) :=
  BigInt.lessThanOrEqual_commutes left right

example (left right : Int) :
    JS.Primitive.greaterThanOrEqual (.bigint left) (.bigint right) = .ok (decide (left ≥ right)) :=
  BigInt.greaterThanOrEqual_commutes left right

example (left right : Int) (nonzero : right ≠ 0) :
    JS.Primitive.divide (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left.tdiv right))) :=
  BigInt.divide_commutes left right nonzero

example (left : Int) :
    JS.Primitive.divide (.bigint left) (.bigint 0) = .error .bigintDivisionByZero :=
  BigInt.divide_zero left

example (left right : Int) (nonzero : right ≠ 0) :
    JS.Primitive.remainder (.bigint left) (.bigint right) =
      .ok (.primitive (.bigint (left.tmod right))) :=
  BigInt.remainder_commutes left right nonzero

example (left : Int) :
    JS.Primitive.remainder (.bigint left) (.bigint 0) = .error .bigintDivisionByZero :=
  BigInt.remainder_zero left

private def boolDecodeIs (value : Value) (expected : Except Bool.DecodeFault _root_.Bool) : Bool :=
  match Bool.decode Heap.empty value, expected with
  | .ok actual, .ok wanted => decide (actual = wanted)
  | .error actual, .error wanted => decide (actual = wanted)
  | _, _ => false

private def bigintDecodeIs (value : Value) (expected : Except BigInt.DecodeFault Int) : Bool :=
  match BigInt.decode Heap.empty value, expected with
  | .ok actual, .ok wanted => decide (actual = wanted)
  | .error actual, .error wanted => decide (actual = wanted)
  | _, _ => false

private def operationResultIs (actual expected : Except CoercionFault Value) : Bool :=
  match actual, expected with
  | .ok actual, .ok wanted => decide (actual = wanted)
  | .error actual, .error wanted => decide (actual = wanted)
  | _, _ => false

private def testPrimitiveCodecs : IO Unit := do
  assert! boolDecodeIs (.primitive .undefined) (.error .expectedBoolean)
  assert! boolDecodeIs (.primitive (.bigint 1)) (.error .expectedBoolean)
  assert! bigintDecodeIs (.primitive (.number JSNumber.one)) (.error .expectedBigInt)
  assert! bigintDecodeIs (.primitive (.boolean true)) (.error .expectedBigInt)
  for value in [0, -1, 2 ^ 100, -(2 ^ 100)] do
    match BigInt.encode Heap.empty value with
    | .error fault => nomatch fault
    | .ok (encoded, next) =>
        assert! decide (encoded = Value.primitive (.bigint value))
        assert! next.size == Heap.empty.size
    assert! bigintDecodeIs (.primitive (.bigint value)) (.ok value)

private def testBigIntDivision : IO Unit := do
  assert! operationResultIs (JS.Primitive.divide (.bigint 7) (.bigint 3))
    (.ok (.primitive (.bigint 2)))
  assert! operationResultIs (JS.Primitive.divide (.bigint (-7)) (.bigint 3))
    (.ok (.primitive (.bigint (-2))))
  assert! operationResultIs (JS.Primitive.divide (.bigint 7) (.bigint (-3)))
    (.ok (.primitive (.bigint (-2))))
  assert! operationResultIs (JS.Primitive.divide (.bigint (-7)) (.bigint (-3)))
    (.ok (.primitive (.bigint 2)))
  assert! operationResultIs (JS.Primitive.remainder (.bigint (-7)) (.bigint 3))
    (.ok (.primitive (.bigint (-1))))
  assert! operationResultIs (JS.Primitive.remainder (.bigint 7) (.bigint (-3)))
    (.ok (.primitive (.bigint 1)))
  assert! operationResultIs (JS.Primitive.divide (.bigint (2 ^ 100)) (.bigint 0))
    (.error .bigintDivisionByZero)
  assert! operationResultIs (JS.Primitive.remainder (.bigint (-(2 ^ 100))) (.bigint 0))
    (.error .bigintDivisionByZero)

#eval testPrimitiveCodecs
#eval testBigIntDivision

end TSLean.Refinement.Tests
