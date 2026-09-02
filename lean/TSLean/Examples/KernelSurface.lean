import Std.Data.HashMap
import Std.Data.TreeMap
import TSLean.LeanToTypeScript.Json

/-!
# The v6 kernel surface, written as the Lean the exporter reads

One declaration per surface feature, so `TSLean/LeanToTypeScript/Export.lean` can be run against a
real elaborated environment rather than a constructed one. Every declaration here is inside the
admitted fragment: the type forms are the seventeen the IR carries, the operations are the
fifty-four registry rows, and the recursion is one of the three disciplines the descriptor reports.

What is deliberately absent is as much of the fixture as what is present. There is no `ByteArray`
computation and no `Std.HashMap` or `Std.TreeMap` operation, because the v6 registry carries no
`bytes` and no `map` opcode: those three are type forms whose values cross the boundary unread, and
a fixture that computed with one would be exercising a refusal rather than the surface.
-/

namespace TSLean.Examples.KernelSurface

open TSLean.LeanToTypeScript (JsonValue)

/-! ## Int -/

/-- Subtraction on `Int`, which is `int.subtract` through the `HSub` instance. -/
def netChange (deposits withdrawals : Int) : Int := deposits - withdrawals

/-- Addition and multiplication, reached through their own instances. -/
def compounded (principal rate : Int) : Int := principal + principal * rate

/-- Truncating division, the guarded `int.tdiv` row. Lean's `/` on `Int` is Euclidean and is
outside the surface, so the reference spelling is the truncating one. -/
def share (total parts : Int) : Int := total.tdiv parts

/-- Truncating remainder, the guarded `int.tmod` row. -/
def remainder (total parts : Int) : Int := total.tmod parts

/-- Negation, which is `int.negate`. -/
def owed (amount : Int) : Int := -amount

/-- `int.ofNat`, the identity on the shared bigint image. -/
def credited (count : Nat) : Int := Int.ofNat count

/-- The same row through the `Nat`-to-`Int` coercion. -/
def widened (count : Nat) : Int := (count : Int)

/-- `int.toNat`, which clamps a negative integer to zero. -/
def settled (balance : Int) : Nat := balance.toNat

/-- An `Int` comparison and an `Int` literal, which is `int.ofNat` of a `Nat` literal. -/
def isOverdrawn (balance : Int) : Bool := balance < 0

/-- `Int` equality through `BEq`, and `int.lessOrEqual`. -/
def isSettled (balance : Int) : Bool := balance == 0 || balance ≤ 0

/-! ## Char -/

/-- `char.toNat`, which reads the code point. -/
def codePoint (letter : Char) : Nat := letter.toNat

/-- `char.ofNat`, which answers U+0000 at a value that is not a scalar. -/
def letterAt (code : Nat) : Char := Char.ofNat code

/-- `char.less`, which compares code points. -/
def precedes (left right : Char) : Bool := left < right

/-- `char.equals`. -/
def sameLetter (left right : Char) : Bool := left == right

/-! ## String -/

/-- `string.length`, which counts code points exactly as Lean does. -/
def width (text : String) : Nat := text.length

/-- `string.isEmpty`. -/
def blank (text : String) : Bool := text.isEmpty

/-- `string.push` and `string.singleton`. -/
def extended (text : String) (letter : Char) : String := text.push letter ++ String.singleton letter

/-- `string.toList`, which is the code-point list. -/
def letters (text : String) : List Char := text.toList

/-- `string.ofList`, which joins a code-point list. -/
def assembled (source : List Char) : String := String.ofList source

/-! ## Array -/

/-- `array.push` and `array.reverse`. -/
def appended (values : Array Nat) (value : Nat) : Array Nat := (values.push value).reverse

/-- `array.append`, through the `Array` append instance. -/
def merged (left right : Array Nat) : Array Nat := left ++ right

/-- `array.size` and `array.isEmpty`. -/
def measured (values : Array Nat) : Nat × Bool := (values.size, values.isEmpty)

/-- `array.toList` and `array.ofList`, the two identities on the dense image, which is what makes
the higher-order `list` rows reachable from an `Array`. -/
def roundTripped (values : Array Nat) : Array Nat := values.toList.toArray

/-! ## ByteArray, HashMap and TreeMap: type forms with no opcodes -/

/-- `bytes` reaches the wire as a type form. It has no opcode row, so a payload crosses the
boundary unread and is only ever passed along. -/
def labelled (label : String) (payload : ByteArray) : String × ByteArray := (label, payload)

/-- `treeMap` at a key type whose order the emitted `compareKey` decides. -/
def withFallback (table : Std.TreeMap Nat String) (fallback : String) :
    String × Std.TreeMap Nat String :=
  (fallback, table)

/-- `hashMap` at a `String` key, which is admitted at that type's own instances. -/
def indexed (table : Std.HashMap String Nat) : Std.HashMap String Nat := table

/-! ## Pair -/

/-- The `pair` form, whose own keys are `fst` then `snd`. -/
def swapped (entry : Nat × String) : String × Nat := (entry.snd, entry.fst)

/-- A pair decided by a match, which its single constructor makes a field read. -/
def describedEntry (entry : Nat × String) : String :=
  match entry with
  | (_, label) => label

/-! ## Records, classes, instances and method calls -/

/-- A record. The codec surface generates `equals`, `toData` and `fromData` over exactly these
fields, in declaration order. -/
structure Ticket where
  code : String
  weight : Nat

/-- A type class, which is a record an instance inhabits. -/
class Describable (subject : Type) where
  describe : subject → String

/-- An instance, which is an elaborated record value. -/
instance : Describable Ticket where
  describe := fun ticket => ticket.code

/-- A method call: the class projection applied to a concrete dictionary, which lowers to a field
read of the dictionary applied to the argument. -/
def ticketLabel (ticket : Ticket) : String := Describable.describe ticket

/-- A record built and read back, so the field order the codec depends on is exercised. -/
def reweighed (ticket : Ticket) (weight : Nat) : Ticket :=
  { code := ticket.code, weight := ticket.weight + weight }

/-! ## Erasure -/

/-- A proof binder, which erasure drops from the emitted parameter list. -/
def widthOf (measure : Nat) (_positive : 0 < measure) : Nat := measure

/-- A call site of an erased binder: the proof argument is dropped here too, so the two arities
agree. -/
def widthOfThree : Nat := widthOf 3 (by decide)

/-- A subtype, which erasure replaces by its carrier, and a `.val` read, which is the identity. -/
def carrierOf (bounded : { measure : Nat // 0 < measure }) : Nat := bounded.val

/-- A `Decidable` argument, which erasure drops: the Bool it decides is read from `decide`. -/
def decided (left right : Nat) : Bool := decide (left = right)

/-! ## Recursion -/

/-- Structural recursion, on the parameter Lean proved it decreases on. -/
def total : List Nat → Nat
  | [] => 0
  | value :: rest => value + total rest

/-! A mutual block. The descriptor names every member, so the emitter hoists both and the forward
reference inside the group is legal. -/

mutual
  /-- Whether the list has an even number of entries, decided against its odd counterpart. -/
  def evenCount : List Nat → Bool
    | [] => true
    | _ :: rest => oddCount rest

  /-- Whether the list has an odd number of entries, decided against its even counterpart. -/
  def oddCount : List Nat → Bool
    | [] => false
    | _ :: rest => evenCount rest
end

/-- Well-founded recursion: `value - 1` is not a constructor field, so Lean discharges a measure
and the exporter reads the equational form it proved. -/
def countDown (value : Nat) : Nat :=
  if value = 0 then 0
  else 1 + countDown (value - 1)
termination_by value
decreasing_by omega

/-! ## JsonValue -/

/-- The `json` form is a mapped inductive: its six constructors are fixed by the fragment, so the
type is mapped rather than emitted as a declaration. -/
def numberDocument (value : Int) : JsonValue := JsonValue.int value

/-- A match over the six `json` constructors. -/
def documentTag (document : JsonValue) : String :=
  match document with
  | .null => "null"
  | .bool _ => "bool"
  | .int _ => "int"
  | .string _ => "string"
  | .array _ => "array"
  | .object _ => "object"

end TSLean.Examples.KernelSurface
