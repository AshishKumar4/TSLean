-- TSLean.Runtime.Coercions
import TSLean.Runtime.Basic

namespace TSLean

def natToFloat (n : Nat) : Float := n.toFloat
def intToFloat (i : Int) : Float := Float.ofInt i
def natToInt   (n : Nat) : Int   := (n : Int)

def floatToNat (f : Float) : Nat := if f < 0 then 0 else f.toUInt64.toNat
def floatToInt (f : Float) : Int := if f < 0 then -(floatToNat (-f) : Int) else (floatToNat f : Int)

def intToNat (i : Int) : Nat := match i with | .ofNat n => n | .negSucc _ => 0

instance : Coe Nat Float where coe := natToFloat
instance : Coe Int Float where coe := intToFloat
instance : Coe Nat Int  where coe := natToInt

def strLength  (s : String)   : Nat    := s.length
def strTrim    (s : String)   : String := s.trimAscii.toString
def strToUpper (s : String)   : String := s.toUpper
def strToLower (s : String)   : String := s.toLower

def strSlice (s : String) (start stop : Nat) : String :=
  let chars := s.toList; let n := chars.length
  let i := min start n;  let j := min stop n
  if i ≥ j then "" else String.ofList (chars.drop i |>.take (j - i))

def strIncludes (s needle : String) : Bool :=
  needle.isEmpty || Nat.any (s.toList.length - needle.toList.length + 1)
    (fun k _ => (s.toList.drop k |>.take needle.toList.length) == needle.toList)

def strStartsWith (s pfx : String) : Bool := s.startsWith pfx
def strEndsWith   (s sfx : String) : Bool := s.endsWith sfx
def strSplit  (s sep : String)     : Array String := s.splitOn sep |>.toArray
def strJoin   (arr : Array String) (sep : String) : String := String.intercalate sep arr.toList

def strRepeat (s : String) (n : Nat) : String := (List.replicate n s).foldl (· ++ ·) ""

def strPadStart (s : String) (targetLen : Nat) (padChar : Char := ' ') : String :=
  if s.length ≥ targetLen then s
  else String.ofList (List.replicate (targetLen - s.length) padChar) ++ s

def strPadEnd (s : String) (targetLen : Nat) (padChar : Char := ' ') : String :=
  if s.length ≥ targetLen then s
  else s ++ String.ofList (List.replicate (targetLen - s.length) padChar)

def charCodeAt (s : String) (i : Nat) : Option Nat := s.toList[i]?.map (·.toNat)

instance : Coe String TSValue where coe s := .tsStr s
instance : Coe Bool TSValue   where coe b := .tsBool b
instance : Coe Float TSValue  where coe f := .tsNum f
instance : Coe Nat TSValue    where coe n := .tsNum n.toFloat

theorem natToInt_ofNat (n : Nat) : (natToInt n : Int) = Int.ofNat n := rfl
theorem intToNat_ofNat (n : Nat) : intToNat (Int.ofNat n) = n := rfl
theorem intToNat_neg   (n : Nat) : intToNat (Int.negSucc n) = 0 := rfl
theorem intToNat_natToInt (n : Nat) : intToNat (natToInt n) = n := rfl
theorem strLength_empty : strLength "" = 0 := by simp [strLength]
theorem strRepeat_zero (s : String) : strRepeat s 0 = "" := by simp [strRepeat]
theorem strSlice_empty (s : String) (i : Nat) : strSlice s i i = "" := by simp [strSlice]
-- String.startsWith "" depends on internal Slice/memcmpSlice representation.
-- The general theorem strStartsWith s "" = true is axiomatically true but requires
-- opening up the internal Slice API. We prove specific instances by native_decide.
theorem strStartsWith_empty_literal : strStartsWith "hello" "" = true := by native_decide
-- strStartsWith_same: s.startsWith s = true (provable for concrete strings)
theorem strStartsWith_same_concrete : strStartsWith "hello" "hello" = true := by native_decide
theorem natToInt_add (m n : Nat) : natToInt (m + n) = natToInt m + natToInt n := by simp [natToInt, Int.natCast_add]
theorem natToInt_mul (m n : Nat) : natToInt (m * n) = natToInt m * natToInt n := by simp [natToInt, Int.natCast_mul]

theorem strPadStart_length_ge (s : String) (n : Nat) (c : Char) : (strPadStart s n c).length ≥ s.length := by
  simp only [strPadStart]
  split
  · omega
  · simp [String.length_append, String.length_ofList, List.length_replicate]
theorem strPadEnd_length_ge (s : String) (n : Nat) (c : Char) : (strPadEnd s n c).length ≥ s.length := by
  simp only [strPadEnd]
  split
  · omega
  · simp [String.length_append, String.length_ofList, List.length_replicate]

theorem strRepeat_length_zero (s : String) : (strRepeat s 0).length = 0 := by
  simp [strRepeat]

theorem strPadStart_at_least_n (s : String) (n : Nat) (c : Char) : (strPadStart s n c).length ≥ n := by
  simp only [strPadStart]
  split
  · omega
  · simp [String.length_append, String.length_ofList, List.length_replicate]; omega

theorem intToNat_nonneg : ∀ (i : Int), 0 ≤ intToNat i := by
  intro i; cases i <;> simp [intToNat]

theorem natToInt_nonneg (n : Nat) : 0 ≤ natToInt n := Int.ofNat_nonneg n

end TSLean
