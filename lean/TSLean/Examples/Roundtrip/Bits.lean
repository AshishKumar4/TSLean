namespace TSLean.Examples.Roundtrip.Bits

/-- Three independent bits. -/
structure Bits where
  low : Bool
  middle : Bool
  high : Bool
  deriving DecidableEq, Repr

/-- The bitwise exclusive disjunction of two triples. -/
def Bits.exclusive (left right : Bits) : Bits :=
  { low := (left.low || right.low) && (not (left.low && right.low))
    middle := (left.middle || right.middle) && (not (left.middle && right.middle))
    high := (left.high || right.high) && (not (left.high && right.high)) }

/-- Whether at least one bit is set. -/
def Bits.anySet (bits : Bits) : Bool :=
  bits.low || bits.middle || bits.high

/-- A triple exclusive with itself is empty. -/
theorem exclusive_self (bits : Bits) : (Bits.exclusive bits bits).anySet = false := by
  simp [Bits.exclusive, Bits.anySet]

end TSLean.Examples.Roundtrip.Bits
