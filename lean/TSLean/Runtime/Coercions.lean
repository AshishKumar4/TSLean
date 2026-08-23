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
def strTrim    (s : String)   : String := s.trim
def strToUpper (s : String)   : String := s.toUpper
def strToLower (s : String)   : String := s.toLower

def strSlice (s : String) (start stop : Nat) : String :=
  let chars := s.toList; let n := chars.length
  let i := min start n;  let j := min stop n
  if i ≥ j then "" else String.mk (chars.drop i |>.take (j - i))

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
  else String.mk (List.replicate (targetLen - s.length) padChar) ++ s

def strPadEnd (s : String) (targetLen : Nat) (padChar : Char := ' ') : String :=
  if s.length ≥ targetLen then s
  else s ++ String.mk (List.replicate (targetLen - s.length) padChar)

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
-- Two concrete `strStartsWith` facts were removed here. They were proved `by native_decide`, which
-- injects `Lean.ofReduceBool` into the axiom set, and every non-pure generated module imports this
-- file, so that axiom sat in the trusted base of the compiler's own output. `decide` cannot replace
-- it because `String.startsWith` reduces through an internal slice representation. Nothing consumed
-- either theorem, so they are gone rather than weakened; a general statement belongs in the JS model
-- over `JSString`, where string equality is code-unit equality the kernel can see.
theorem natToInt_add (m n : Nat) : natToInt (m + n) = natToInt m + natToInt n := by simp [natToInt, Int.natCast_add]
theorem natToInt_mul (m n : Nat) : natToInt (m * n) = natToInt m * natToInt n := by simp [natToInt, Int.natCast_mul]

theorem strPadStart_length_ge (s : String) (n : Nat) (c : Char) : (strPadStart s n c).length ≥ s.length := by
  simp only [strPadStart]
  split
  · omega
  · simp [String.length_append, String.length_mk, List.length_replicate]
theorem strPadEnd_length_ge (s : String) (n : Nat) (c : Char) : (strPadEnd s n c).length ≥ s.length := by
  simp only [strPadEnd]
  split
  · omega
  · simp [String.length_append, String.length_mk, List.length_replicate]

theorem strRepeat_length_zero (s : String) : (strRepeat s 0).length = 0 := by
  simp [strRepeat]

theorem strPadStart_at_least_n (s : String) (n : Nat) (c : Char) : (strPadStart s n c).length ≥ n := by
  simp only [strPadStart]
  split
  · omega
  · simp [String.length_append, String.length_mk, List.length_replicate]; omega

theorem intToNat_nonneg : ∀ (i : Int), 0 ≤ intToNat i := by
  intro i; cases i <;> simp [intToNat]

theorem natToInt_nonneg (n : Nat) : 0 ≤ natToInt n := Int.ofNat_nonneg n

end TSLean
