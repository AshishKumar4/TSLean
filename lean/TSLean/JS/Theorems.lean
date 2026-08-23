import TSLean.JS.Conversion
import TSLean.JS.Equality
import TSLean.JS.PropertyKey

namespace TSLean.JS

theorem undefined_toBoolean : (Value.primitive .undefined).toBoolean = false := rfl

theorem null_toBoolean : (Value.primitive .null).toBoolean = false := rfl

theorem boolean_toBoolean (value : Bool) :
    (Value.primitive (.boolean value)).toBoolean = value := rfl

theorem number_toBoolean (value : JSNumber) :
    (Value.primitive (.number value)).toBoolean = !(value.isZero || value.isNaN) := rfl

theorem string_toBoolean (value : JSString) :
    (Value.primitive (.string value)).toBoolean = !value.isEmpty := rfl

theorem bigint_toBoolean (value : Int) :
    (Value.primitive (.bigint value)).toBoolean = (value != 0) := rfl

theorem symbol_toBoolean (id : SymbolId) :
    (Value.primitive (.symbol id)).toBoolean = true := rfl

theorem object_toBoolean (ref : RefId) : (Value.object ref).toBoolean = true := rfl

theorem typeof_undefined : Primitive.typeof .undefined = .undefined := rfl

theorem typeof_null : Primitive.typeof .null = .object := rfl

theorem typeof_boolean (value : Bool) : Primitive.typeof (.boolean value) = .boolean := rfl

theorem typeof_number (value : JSNumber) : Primitive.typeof (.number value) = .number := rfl

theorem typeof_string (value : JSString) : Primitive.typeof (.string value) = .string := rfl

theorem typeof_bigint (value : Int) : Primitive.typeof (.bigint value) = .bigint := rfl

theorem typeof_symbol (id : SymbolId) : Primitive.typeof (.symbol id) = .symbol := rfl

theorem strictEqual_undefined :
    strictEqual (.primitive .undefined) (.primitive .undefined) = true := rfl

theorem strictEqual_null_undefined :
    strictEqual (.primitive .null) (.primitive .undefined) = false := rfl

theorem strictEqual_object (left right : RefId) :
    strictEqual (.object left) (.object right) = decide (left = right) := rfl

theorem sameValue_object (left right : RefId) :
    sameValue (.object left) (.object right) = decide (left = right) := rfl

theorem sameValueZero_object (left right : RefId) :
    sameValueZero (.object left) (.object right) = decide (left = right) := rfl

theorem strictEqual_symbol (left right : SymbolId) :
    strictEqual (.primitive (.symbol left)) (.primitive (.symbol right)) =
      decide (left = right) := rfl

theorem sameValue_symbol (left right : SymbolId) :
    sameValue (.primitive (.symbol left)) (.primitive (.symbol right)) =
      decide (left = right) := rfl

theorem sameValueZero_symbol (left right : SymbolId) :
    sameValueZero (.primitive (.symbol left)) (.primitive (.symbol right)) =
      decide (left = right) := rfl

theorem positiveZero_isZero : JSNumber.positiveZero.isZero = true := rfl

theorem negativeZero_isZero : JSNumber.negativeZero.isZero = true := rfl

theorem positiveInfinity_isInfinite : JSNumber.positiveInfinity.isInfinite = true := rfl

theorem negativeInfinity_isInfinite : JSNumber.negativeInfinity.isInfinite = true := rfl

theorem canonicalNaN_isNaN : JSNumber.canonicalNaN.isNaN = true := rfl

theorem strictEqual_signedZero :
    JSNumber.strictEqual JSNumber.positiveZero JSNumber.negativeZero = true := rfl

theorem sameValue_signedZero :
    JSNumber.sameValue JSNumber.positiveZero JSNumber.negativeZero = false := rfl

theorem sameValueZero_signedZero :
    JSNumber.sameValueZero JSNumber.positiveZero JSNumber.negativeZero = true := rfl

theorem strictEqual_canonicalNaN :
    JSNumber.strictEqual JSNumber.canonicalNaN JSNumber.canonicalNaN = false := rfl

theorem sameValue_canonicalNaN :
    JSNumber.sameValue JSNumber.canonicalNaN JSNumber.canonicalNaN = true := rfl

theorem sameValueZero_canonicalNaN :
    JSNumber.sameValueZero JSNumber.canonicalNaN JSNumber.canonicalNaN = true := rfl

theorem jsString_append_codeUnits (left right : JSString) :
    (left.append right).codeUnits = left.codeUnits ++ right.codeUnits := rfl

theorem jsString_length_append (left right : JSString) :
    (left.append right).length = left.length + right.length := by
  simp [JSString.append, JSString.length]

theorem jsString_equal_iff (left right : JSString) :
    left.equal right = true ↔ left = right := by
  cases left
  cases right
  simp [JSString.equal]

theorem jsString_equal_refl (value : JSString) : value.equal value = true := by
  exact jsString_equal_iff value value |>.2 rfl

theorem jsString_toLeanString_empty : (JSString.mk []).toLeanString? = some "" := rfl

theorem jsString_bmp_decode :
    (JSString.mk [UInt16.ofNat 0x41]).toLeanString? =
      some (String.mk [Char.ofNat 0x41]) := rfl

theorem jsString_astralMin_decode :
    (JSString.mk [UInt16.ofNat 0xd800, UInt16.ofNat 0xdc00]).toLeanString? =
      some (String.mk [Char.ofNat 0x10000]) := rfl

theorem propertyKey_equal_refl (key : PropertyKey) : PropertyKey.equal key key = true := by
  cases key with
  | string value => simp [PropertyKey.equal, JSString.equal]
  | symbol id => simp [PropertyKey.equal]

theorem propertyKey_equal_iff (left right : PropertyKey) :
    PropertyKey.equal left right = true ↔ left = right := by
  cases left with
  | string left =>
      cases right with
      | string right =>
          cases left
          cases right
          simp [PropertyKey.equal, JSString.equal]
      | symbol _ => simp [PropertyKey.equal]
  | symbol left =>
      cases right with
      | string _ => simp [PropertyKey.equal]
      | symbol right => simp [PropertyKey.equal]

end TSLean.JS
