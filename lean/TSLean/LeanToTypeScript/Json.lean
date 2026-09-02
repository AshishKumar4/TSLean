/-!
# `JsonValue`, the compiler's own admitted JSON type

The Lean type the `json` type form is the image of. It is owned here rather than taken from a
library because the fragment's `json` form fixes its constructor set: `Ir.Program.constructorsOf`
answers exactly these six constructors, with exactly these field names, and the emitter builds the
discriminated union from that answer. A second JSON type with a different constructor set would
compile to a different union, so there is one.

The numeric constructor is `Int`, not a float: `Int` reaches the target as a bigint and is exact at
every magnitude, while a JSON number lowered to `number` would be exact only below `2 ^ 53`. A
document that needs the full IEEE range is not this type's business, and saying it were would be a
claim this compiler cannot keep.

An object is a `List (String × JsonValue)`, so key order is part of the value. That is deliberate:
own-key order is observable in the target, so a representation that reordered keys would not be the
identity on documents, and a `Std.TreeMap` image would need the map representation this compiler does
not yet model.
-/

namespace TSLean.LeanToTypeScript

/-- A JSON document, in the six shapes the `json` type form admits. Each payload field is named
`value`, which is the field name the emitted tagged object carries. -/
inductive JsonValue where
  /-- `null`. -/
  | null
  /-- `true` or `false`. -/
  | bool (value : Bool)
  /-- An exact integer, which reaches the target as a bigint. -/
  | int (value : Int)
  /-- A string, in UTF-16 code units. -/
  | string (value : String)
  /-- An array, in element order. -/
  | array (value : List JsonValue)
  /-- An object, in key order, because own-key order is observable. -/
  | object (value : List (String × JsonValue))
  deriving Repr, Inhabited

namespace JsonValue

/-- The constructor tag a value carries, which is the `kind` the emitted object carries. -/
def tag : JsonValue → String
  | .null => "null"
  | .bool _ => "bool"
  | .int _ => "int"
  | .string _ => "string"
  | .array _ => "array"
  | .object _ => "object"

/-- Every admitted tag, in the order `constructorsOf` answers them. -/
def tags : List String := ["null", "bool", "int", "string", "array", "object"]

/-- Every value's tag is one the fragment admits. -/
theorem tag_mem_tags (value : JsonValue) : value.tag ∈ tags := by
  cases value <;> simp [tag, tags]

/-- The tags are distinct, so the emitted `kind` decides the constructor. -/
theorem tags_nodup : tags.Nodup := by decide

end JsonValue

end TSLean.LeanToTypeScript
