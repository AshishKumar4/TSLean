-- TSLean.Stdlib.Numeric
namespace TSLean.Stdlib.Numeric

def clamp (x lo hi : Int) : Int := max lo (min x hi)
def clampNat (x lo hi : Nat) : Nat := max lo (min x hi)
def gcd' (a b : Nat) : Nat := Nat.gcd a b
def lcm' (a b : Nat) : Nat := Nat.lcm a b
def abs' (x : Int) : Nat := x.natAbs
def sign (x : Int) : Int := if x > 0 then 1 else if x < 0 then -1 else 0
def isPow2 (n : Nat) : Bool := n > 0 && (n &&& (n - 1)) == 0
def ilog2 (n : Nat) : Nat := Nat.log2 n

theorem clamp_ge_lo (x lo hi : Int) : lo ≤ clamp x lo hi := by simp [clamp]; exact Int.le_max_left lo _
theorem clamp_le_hi (x lo hi : Int) (h : lo ≤ hi) : clamp x lo hi ≤ hi := by
  simp [clamp]; exact Int.max_le.mpr ⟨h, Int.min_le_right x hi⟩
theorem clamp_id (x lo hi : Int) (h1 : lo ≤ x) (h2 : x ≤ hi) : clamp x lo hi = x := by
  simp [clamp, Int.max_eq_right h1, Int.min_eq_left h2]
theorem gcd'_dvd_left (a b : Nat) : gcd' a b ∣ a := Nat.gcd_dvd_left a b
theorem gcd'_dvd_right (a b : Nat) : gcd' a b ∣ b := Nat.gcd_dvd_right a b
theorem gcd'_comm (a b : Nat) : gcd' a b = gcd' b a := Nat.gcd_comm a b
theorem lcm'_comm (a b : Nat) : lcm' a b = lcm' b a := Nat.lcm_comm a b
theorem abs'_nonneg (x : Int) : (abs' x : Int) ≥ 0 := by simp [abs']
theorem abs'_neg (x : Int) (h : x ≤ 0) : (abs' x : Int) = -x := by
  simp only [abs']; rw [show x.natAbs = (-x).natAbs from (Int.natAbs_neg x).symm]
  exact Int.natAbs_of_nonneg (Int.neg_nonneg.mpr h)
theorem abs'_pos (x : Int) (h : 0 ≤ x) : (abs' x : Int) = x := by
  simp [abs', Int.natAbs_of_nonneg h]
theorem sign_pos (x : Int) (h : x > 0) : sign x = 1 := by simp [sign, h]
theorem sign_neg (x : Int) (h : x < 0) : sign x = -1 := by simp [sign, Int.not_lt.mpr (Int.le_of_lt h), h]
theorem sign_zero : sign 0 = 0 := by simp [sign]
theorem isPow2_one : isPow2 1 = true := by native_decide
theorem isPow2_two : isPow2 2 = true := by native_decide
theorem isPow2_zero : isPow2 0 = false := by native_decide
-- ilog2 is monotone. For a = 0 it's trivial; for a ≠ 0 we use:
-- if log2 b < log2 a then b < 2^(log2 a) ≤ a ≤ b, contradiction.
theorem ilog2_mono {a b : Nat} (h : a ≤ b) : ilog2 a ≤ ilog2 b := by
  simp only [ilog2]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Nat.zero_le _
  · -- a > 0; use log2_lt and log2_self_le
    apply Nat.le_of_not_lt
    intro hlt
    -- hlt : Nat.log2 b < Nat.log2 a
    have hane : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha
    have hbne : b ≠ 0 := by omega
    have hblt : b < 2^(Nat.log2 a) := (Nat.log2_lt hbne).mp hlt
    have hale : 2^(Nat.log2 a) ≤ a := Nat.log2_self_le hane
    omega


-- Additional numeric theorems
theorem clampNat_ge_lo (x lo hi : Nat) : lo ≤ clampNat x lo hi := by simp [clampNat]; exact Nat.le_max_left lo _
theorem clampNat_le_hi (x lo hi : Nat) (h : lo ≤ hi) : clampNat x lo hi ≤ hi := by
  simp [clampNat]; exact Nat.max_le.mpr ⟨h, Nat.min_le_right x hi⟩
theorem clampNat_id (x lo hi : Nat) (h1 : lo ≤ x) (h2 : x ≤ hi) : clampNat x lo hi = x := by
  simp [clampNat, Nat.max_eq_right h1, Nat.min_eq_left h2]
theorem gcd_mul_lcm (a b : Nat) : gcd' a b * lcm' a b = a * b := Nat.gcd_mul_lcm a b
theorem abs_triangle (a b : Int) : abs' (a + b) ≤ abs' a + abs' b := by
  simp only [abs']; exact Int.natAbs_add_le a b
theorem clamp_in_range (x lo hi : Int) (h : lo ≤ hi) : lo ≤ clamp x lo hi ∧ clamp x lo hi ≤ hi :=
  ⟨clamp_ge_lo x lo hi, clamp_le_hi x lo hi h⟩
theorem isPow2_four : isPow2 4 = true := by native_decide
theorem isPow2_eight : isPow2 8 = true := by native_decide
theorem not_isPow2_three : isPow2 3 = false := by native_decide
theorem ilog2_one : ilog2 1 = 0 := by native_decide
theorem ilog2_two : ilog2 2 = 1 := by native_decide
theorem gcd_le_left (a b : Nat) (h : 0 < a) : gcd' a b ≤ a := Nat.gcd_le_left b h
theorem gcd_le_right (a b : Nat) (h : 0 < b) : gcd' a b ≤ b := Nat.gcd_le_right a h
theorem lcm_dvd_mul_left (a b : Nat) : a ∣ lcm' a b := Nat.dvd_lcm_left a b
theorem lcm_dvd_mul_right (a b : Nat) : b ∣ lcm' a b := Nat.dvd_lcm_right a b

/-! ## Float utilities -/

namespace FloatExt

-- Constants
def pi    : Float := 3.14159265358979323846
def e     : Float := 2.71828182845904523536
def tau   : Float := 2.0 * pi
def ln2   : Float := 0.6931471805599453
def ln10  : Float := 2.302585092994046

-- Arithmetic
def max (a b : Float) : Float := if a ≥ b then a else b
def min (a b : Float) : Float := if a ≤ b then a else b
def abs (x : Float) : Float := if x ≥ 0.0 then x else -x
def clamp (x lo hi : Float) : Float := max lo (min x hi)

-- Rounding
def floor (x : Float) : Float := Float.floor x
def ceil  (x : Float) : Float := Float.ceil x
def round (x : Float) : Float := Float.round x
def trunc (x : Float) : Float := if x ≥ 0.0 then Float.floor x else Float.ceil x

-- Classification
def isNaN      (x : Float) : Bool := Float.isNaN x
def isInfinite (x : Float) : Bool := Float.isInf x
def isFinite   (x : Float) : Bool := !(isNaN x) && !(isInfinite x)

-- Math functions
def sqrt  (x : Float) : Float := Float.sqrt x
def log   (x : Float) : Float := Float.log x
def log2  (x : Float) : Float := Float.log x / ln2
def log10 (x : Float) : Float := Float.log x / ln10
def exp   (x : Float) : Float := Float.exp x
def pow   (base exp_ : Float) : Float := Float.pow base exp_
def sin   (x : Float) : Float := Float.sin x
def cos   (x : Float) : Float := Float.cos x
def tan   (x : Float) : Float := Float.tan x
def atan2 (y x : Float) : Float := Float.atan2 y x

-- Integer conversion
def toInt (x : Float) : Int := x.toUInt64.toNat
def toNat (x : Float) : Nat := x.toUInt64.toNat
def ofInt (n : Int) : Float := Float.ofInt n
def ofNat (n : Nat) : Float := Float.ofNat n

-- Comparison
def approxEq (a b : Float) (eps : Float := 1e-10) : Bool :=
  abs (a - b) < eps

-- Safe division (returns 0 for division by zero)
def safeDiv (a b : Float) : Float :=
  if b == 0.0 then 0.0 else a / b

-- Percentage
def pct (value total : Float) : Float :=
  safeDiv (value * 100.0) total

end FloatExt

-- Concrete tests via native_decide
theorem FloatExt.pi_positive : FloatExt.pi > 0.0 := by native_decide
theorem FloatExt.e_positive  : FloatExt.e > 0.0 := by native_decide
theorem FloatExt.abs_nonneg_concrete : FloatExt.abs (-3.0) == 3.0 := by native_decide
theorem FloatExt.max_comm_concrete : FloatExt.max 1.0 2.0 == FloatExt.max 2.0 1.0 := by native_decide
theorem FloatExt.min_le_max_concrete : FloatExt.min 1.0 2.0 ≤ FloatExt.max 1.0 2.0 := by native_decide
theorem FloatExt.floor_le_concrete : FloatExt.floor 3.7 ≤ 3.7 := by native_decide
theorem FloatExt.ceil_ge_concrete  : FloatExt.ceil 3.2 ≥ 3.2 := by native_decide
theorem FloatExt.round_half_concrete : FloatExt.round 2.5 == 3.0 := by native_decide
theorem FloatExt.safeDiv_zero : FloatExt.safeDiv 1.0 0.0 == 0.0 := by native_decide

end TSLean.Stdlib.Numeric
