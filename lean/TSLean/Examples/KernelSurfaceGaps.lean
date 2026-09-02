import Std.Data.TreeMap
import TSLean.LeanToTypeScript.Json

/-!
# What the v6 surface refuses, written as the Lean that reaches it

Every declaration here elaborates in Lean and is refused by
`TSLean/LeanToTypeScript/Export.lean`. The point of the file is the refusal message: a shape the
surface excludes has a semantic reason, and this fixture is what proves the exporter states it
rather than emitting a placeholder or guessing a neighbouring row.

Nothing here is a work item. Each one is either a semantics that disagrees with the target's
(§10) or a registry row that does not exist in v6, and the message names which.
-/

namespace TSLean.Examples.KernelSurfaceGaps

/-! ## Division and modulo -/

/-- `/` on `Int` is `Int.ediv`, whose remainder is non-negative, while BigInt `/` truncates. -/
def euclidean (dividend divisor : Int) : Int := dividend / divisor

/-- The same disagreement named directly. -/
def euclideanRemainder (dividend divisor : Int) : Int := dividend.emod divisor

/-- `Nat` division, which has no registry row at all. -/
def halved (value : Nat) : Nat := value / 2

/-! ## String positions and ordering -/

/-- Lean compares code-point lists; JavaScript `<` compares UTF-16 code units. -/
def before (left right : String) : Bool := left < right

/-- A string position is a UTF-8 byte offset; a JavaScript index is a UTF-16 code unit. -/
def firstLetter (text : String) : Char := String.Pos.Raw.get text ⟨0⟩

/-- The position type itself. -/
def start (_text : String) : String.Pos.Raw := ⟨0⟩

/-! ## Fixed-width integers -/

/-- `UInt8` arithmetic wraps, which needs a modular-arithmetic opcode family. -/
def wrapped (byte : UInt8) : UInt8 := byte + 1

/-- A `Char`'s raw code unit, which is a `UInt32`. -/
def rawCode (letter : Char) : UInt32 := letter.val

/-! ## Type forms with no opcodes -/

/-- `bytes` is a type form with no opcode, so a computation over one has no emitted form. -/
def payloadSize (payload : ByteArray) : Nat := payload.size

/-- The map forms carry no opcode either. -/
def inserted (table : Std.TreeMap Nat String) : Std.TreeMap Nat String := table.insert 1 "first"

/-- An indexed read, which the absent `array.get` row would have carried. -/
def firstValue (values : Array Nat) : Option Nat := values[0]?

/-! ## Map comparators -/

/-- A `Std.TreeMap` at a comparator that is not the key type's own `compare` orders its entries
differently from the emitted `Map`, whose entry sequence `compareKey` decides. -/
def descendingLookup (_table : Std.TreeMap Nat String (fun left right => compare right left))
    (fallback : String) : String :=
  fallback

/-! ## Records that carry no data -/

/-- A structure with a proof field: the codec's `fromData` would have to rebuild the proof. -/
structure NonEmptyRun where
  values : List Nat
  populated : 0 < values.length

/-! ## Classes the elaborator resolves and the emitted program cannot -/

/-- A class that dispatches on an output parameter. -/
class Widens (source : Type) (target : outParam Type) where
  widen : source → target

end TSLean.Examples.KernelSurfaceGaps

namespace TSLean.LeanToTypeScript.Host

/-- A declaration in the host namespace that names none of the nineteen host operations, so no
wire spelling identifies it. -/
def storeScan (limit : Nat) : Nat := limit

end TSLean.LeanToTypeScript.Host
