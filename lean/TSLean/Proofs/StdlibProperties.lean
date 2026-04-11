-- TSLean.Proofs.StdlibProperties
-- Algebraic laws for Stdlib modules: AssocMap, TSHashSet, Array, Numeric, String, OptionResult.
-- All theorems genuinely proven (zero sorry).

import TSLean.Stdlib.HashMap
import TSLean.Stdlib.HashSet
import TSLean.Stdlib.Array
import TSLean.Stdlib.Numeric
import TSLean.Stdlib.String
import TSLean.Stdlib.OptionResult

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace TSLean.Proofs.StdlibProperties

-- ═══════════════════════════════════════════════════════════════════════
-- §1  AssocMap — additional algebraic laws
-- ═══════════════════════════════════════════════════════════════════════

namespace AssocMapLaws

open TSLean.Stdlib.HashMap
open TSLean.Stdlib.HashMap.AssocMap

variable {α β γ δ : Type} [BEq α] [LawfulBEq α] [DecidableEq α]

-- mapValues commutes with get?
theorem mapValues_get? (m : AssocMap α β) (f : β → γ) (k : α) :
    (m.mapValues f).get? k = (m.get? k).map f := by
  simp only [AssocMap.mapValues, AssocMap.get?]
  induction m.entries with
  | nil => simp [List.findSome?]
  | cons hd tl ih =>
    simp only [List.map_cons, List.findSome?]
    rcases Bool.eq_false_or_eq_true (hd.1 == k) with hc | hc
    · have : hd.1 = k := LawfulBEq.eq_of_beq hc
      simp [hc, this]
    · have hne : hd.1 ≠ k := fun heq => by rw [heq, beq_self_eq_true] at hc; exact absurd hc (by decide)
      simp only [hc, ite_false, hne, ↓reduceIte]
      exact ih

-- mapValues composition
theorem mapValues_comp (m : AssocMap α β) (f : β → γ) (g : γ → δ) :
    (m.mapValues f).mapValues g = m.mapValues (g ∘ f) := by
  simp only [AssocMap.mapValues, AssocMap.mk.injEq]
  simp [List.map_map, Function.comp]

-- mapValues identity
theorem mapValues_id (m : AssocMap α β) : m.mapValues id = m := by
  simp only [AssocMap.mapValues, AssocMap.mk.injEq]
  simp [List.map_id]

-- merge with empty right is identity
theorem merge_empty_right (m : AssocMap α β) :
    m.merge AssocMap.empty = m := by
  simp [AssocMap.merge, AssocMap.empty]

-- erase then insert roundtrip
theorem erase_then_insert_get? (m : AssocMap α β) (k : α) (v : β) :
    ((m.erase k).insert k v).get? k = some v :=
  get?_insert_same (m.erase k) k v

-- getD unfolds correctly
theorem getD_eq (m : AssocMap α β) (k : α) (d : β) :
    m.getD k d = (m.get? k).getD d := rfl

-- contains iff exists value
theorem contains_iff_exists (m : AssocMap α β) (k : α) :
    m.contains k = true ↔ ∃ v, m.get? k = some v := by
  rw [contains_iff_get?_isSome]
  constructor
  · intro h; exact Option.isSome_iff_exists.mp h
  · intro ⟨v, hv⟩; rw [hv]; rfl

-- singleton get? for different key
theorem get?_singleton_diff (k k' : α) (v : β) (h : k ≠ k') :
    (AssocMap.singleton k v).get? k' = none := by
  have hbeq : (k == k') = false := by rw [Bool.eq_false_iff]; intro hb; exact h (LawfulBEq.eq_of_beq hb)
  simp only [AssocMap.singleton, AssocMap.get?, List.findSome?, hbeq, Bool.false_eq_true, ite_false]

-- fromList of empty is empty
theorem fromList_nil : (AssocMap.fromList ([] : List (α × β))) = AssocMap.empty := by
  simp [AssocMap.fromList]

-- fromList of singleton roundtrip
theorem fromList_singleton (k : α) (v : β) :
    (AssocMap.fromList [(k, v)]).get? k = some v := by
  simp [AssocMap.fromList, List.foldl, get?_insert_same]

end AssocMapLaws

-- ═══════════════════════════════════════════════════════════════════════
-- §2  TSHashSet — extensional set algebra
-- ═══════════════════════════════════════════════════════════════════════

namespace HashSetLaws

open TSLean.Stdlib.HashSet
open TSLean.Stdlib.HashSet.TSHashSet

variable {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]

-- diff with empty right is identity (extensional)
theorem diff_empty_right (s : TSHashSet α) (x : α) :
    (TSHashSet.diff s TSHashSet.empty).contains x = s.contains x := by
  simp only [TSHashSet.diff, TSHashSet.empty, TSHashSet.contains]
  congr 1
  apply List.filter_eq_self.mpr
  intro y _
  simp

-- diff with self is empty (extensional)
theorem diff_self (s : TSHashSet α) (x : α) :
    (TSHashSet.diff s s).contains x = false := by
  simp only [TSHashSet.diff, TSHashSet.contains]
  rw [Bool.eq_false_iff]
  intro hmem
  rw [List.contains_iff_mem, List.mem_filter] at hmem
  obtain ⟨hmem_s, hfilt⟩ := hmem
  have hcontains : s.elems.contains x = true := List.contains_iff_mem.mpr hmem_s
  rw [hcontains] at hfilt
  exact absurd hfilt (by decide)

-- inter is idempotent (extensional)
theorem inter_self (s : TSHashSet α) (x : α) :
    (TSHashSet.inter s s).contains x = s.contains x := by
  simp only [TSHashSet.inter, TSHashSet.contains]
  simp [List.mem_filter, List.contains_iff_mem]

-- inter with empty right is empty
theorem inter_empty_right (s : TSHashSet α) (x : α) :
    (TSHashSet.inter s TSHashSet.empty).contains x = false := by
  simp only [TSHashSet.inter, TSHashSet.empty, TSHashSet.contains]
  simp [List.mem_filter, List.contains_iff_mem]

-- union with empty right is identity
theorem union_empty_right (s : TSHashSet α) :
    TSHashSet.union s TSHashSet.empty = s := by
  simp [TSHashSet.union, TSHashSet.empty]

-- insert then erase: does not contain x
theorem insert_erase (s : TSHashSet α) (x : α) :
    ((s.insert x).erase x).contains x = false :=
  erase_not_contains (s.insert x) x

-- erase then insert: contains x
theorem erase_insert (s : TSHashSet α) (x : α) :
    ((s.erase x).insert x).contains x = true :=
  contains_insert_same (s.erase x) x

-- insert preserves existing elements
theorem insert_preserves (s : TSHashSet α) (x y : α) (h : s.contains y = true) :
    (s.insert x).contains y = true :=
  contains_insert_preserved s y x h

-- inter commutativity (extensional)
theorem inter_comm (s t : TSHashSet α) (x : α) :
    (TSHashSet.inter s t).contains x = (TSHashSet.inter t s).contains x := by
  simp only [TSHashSet.inter, TSHashSet.contains]
  simp [List.mem_filter, List.contains_iff_mem, and_comm]

-- size of union is bounded
private theorem foldl_insert_size_le (l : List α) (acc : TSHashSet α) :
    (l.foldl (fun a x => a.insert x) acc).size ≤ acc.size + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    calc (tl.foldl (fun a x => a.insert x) (acc.insert hd)).size
        ≤ (acc.insert hd).size + tl.length := ih _
      _ ≤ (acc.size + 1) + tl.length := by have := size_insert_le acc hd; omega
      _ = acc.size + (tl.length + 1) := by omega

theorem size_union_le (s t : TSHashSet α) :
    (TSHashSet.union s t).size ≤ s.size + t.size := by
  simp only [TSHashSet.union, TSHashSet.size]
  exact foldl_insert_size_le t.elems s

end HashSetLaws

-- ═══════════════════════════════════════════════════════════════════════
-- §3  Array — push/get roundtrip and structural laws
-- ═══════════════════════════════════════════════════════════════════════

namespace ArrayLaws

open TSLean.Stdlib.Array

-- push then getOpt at the pushed index returns the value
theorem push_getOpt_last (a : Array α) (x : α) :
    getOpt (push a x) a.size = some x := by
  simp only [push, getOpt]
  exact Array.getElem?_push_size

-- push then getOpt at an earlier index preserves the old value
theorem push_getOpt_old (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    getOpt (push a x) i = getOpt a i := by
  simp only [push, getOpt]
  have hlt : i < (a.push x).size := by rw [Array.size_push]; omega
  rw [show (a.push x)[i]? = some (a.push x)[i] from Array.getElem?_eq_getElem hlt]
  rw [show a[i]? = some a[i] from Array.getElem?_eq_getElem h]
  congr 1
  exact Array.getElem_push_lt h

-- getOpt out of bounds is none
theorem getOpt_out_of_bounds (a : Array α) (i : Nat) (h : a.size ≤ i) :
    getOpt a i = none := by
  simp [getOpt, Array.getElem?_eq_none_iff.mpr h]

-- Helper: foldl addition shift lemma
private theorem foldl_add_shift (l : List Nat) (init : Nat) :
    l.foldl (· + ·) init = init + l.foldl (· + ·) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + hd), ih hd]; omega

-- sumNat distributes over append
theorem sumNat_append (a b : Array Nat) :
    sumNat (a ++ b) = sumNat a + sumNat b := by
  simp only [sumNat]
  have h1 : Array.foldl (· + ·) 0 (a ++ b) =
    (a ++ b).toList.foldl (· + ·) 0 := (Array.foldl_toList ..).symm
  have h2 : Array.foldl (· + ·) 0 a =
    a.toList.foldl (· + ·) 0 := (Array.foldl_toList ..).symm
  have h3 : Array.foldl (· + ·) 0 b =
    b.toList.foldl (· + ·) 0 := (Array.foldl_toList ..).symm
  rw [h1, h2, h3, Array.toList_append, List.foldl_append]
  exact foldl_add_shift b.toList _

-- flatten of empty
theorem flatten_empty' : flatten (α := α) #[] = #[] := by simp [flatten]

-- flatten of singleton
theorem flatten_singleton' (a : Array α) : flatten #[a] = a := by
  simp [flatten, Array.foldl_push, Array.foldl_empty]

end ArrayLaws

-- ═══════════════════════════════════════════════════════════════════════
-- §4  Numeric — gcd/lcm/clamp/abs algebraic laws
-- ═══════════════════════════════════════════════════════════════════════

namespace NumericLaws

open TSLean.Stdlib.Numeric

-- gcd associativity
theorem gcd_assoc (a b c : Nat) : gcd' (gcd' a b) c = gcd' a (gcd' b c) := by
  simp only [gcd']; exact Nat.gcd_assoc a b c

-- gcd with zero
theorem gcd_zero_left (a : Nat) : gcd' 0 a = a := by simp [gcd']
theorem gcd_zero_right (a : Nat) : gcd' a 0 = a := by simp [gcd']

-- gcd is idempotent
theorem gcd_self (a : Nat) : gcd' a a = a := by simp [gcd']

-- lcm associativity
theorem lcm_assoc (a b c : Nat) : lcm' (lcm' a b) c = lcm' a (lcm' b c) := by
  simp only [lcm']; exact Nat.lcm_assoc a b c

-- lcm with zero
theorem lcm_zero_left (a : Nat) : lcm' 0 a = 0 := by simp [lcm', Nat.lcm]
theorem lcm_zero_right (a : Nat) : lcm' a 0 = 0 := by simp [lcm', Nat.lcm]

-- lcm with one
theorem lcm_one_left (a : Nat) : lcm' 1 a = a := by
  simp [lcm', Nat.lcm]
theorem lcm_one_right (a : Nat) : lcm' a 1 = a := by
  simp [lcm', Nat.lcm]

-- clamp is idempotent
theorem clamp_idempotent (x lo hi : Int) (h : lo ≤ hi) :
    clamp (clamp x lo hi) lo hi = clamp x lo hi :=
  clamp_id _ _ _ (clamp_ge_lo x lo hi) (clamp_le_hi x lo hi h)

-- clampNat is idempotent
theorem clampNat_idempotent (x lo hi : Nat) (h : lo ≤ hi) :
    clampNat (clampNat x lo hi) lo hi = clampNat x lo hi :=
  clampNat_id _ _ _ (clampNat_ge_lo x lo hi) (clampNat_le_hi x lo hi h)

-- sign trichotomy
theorem sign_trichotomy (x : Int) : sign x = -1 ∨ sign x = 0 ∨ sign x = 1 := by
  unfold sign
  by_cases h1 : x > 0
  · simp [h1]
  · by_cases h2 : x < 0
    · simp [h1, h2]
    · simp [h1, h2]

-- sign * abs = id (for positive)
theorem sign_mul_abs_pos (x : Int) (h : x > 0) : sign x * (abs' x : Int) = x := by
  rw [sign_pos x h, abs'_pos x (Int.le_of_lt h)]; simp

-- sign * abs = id (for negative)
theorem sign_mul_abs_neg (x : Int) (h : x < 0) : sign x * (abs' x : Int) = x := by
  rw [sign_neg x h, abs'_neg x (Int.le_of_lt h)]
  omega

-- abs is multiplicative (natAbs level)
theorem abs_mul (a b : Int) : abs' (a * b) = abs' a * abs' b := by
  simp only [abs']; exact Int.natAbs_mul a b

end NumericLaws

-- ═══════════════════════════════════════════════════════════════════════
-- §5  String — structural and algebraic laws
-- ═══════════════════════════════════════════════════════════════════════

namespace StringLaws

open TSLean.Stdlib.String

-- truncate is idempotent
theorem truncate_idempotent (s : String) (n : Nat) :
    truncate (truncate s n) n = truncate s n := by
  simp only [truncate]
  rw [String.toList_ofList, List.take_take, Nat.min_self]

-- truncate 0 gives empty
theorem truncate_zero (s : String) : truncate s 0 = "" := by
  simp [truncate, List.take_zero]

-- charAt of empty string is always none
theorem charAt_empty (i : Nat) : charAt "" i = none := by
  simp [charAt]

-- countChar is monotone under append (left addend)
theorem countChar_le_append (s t : String) (c : Char) :
    countChar s c ≤ countChar (s ++ t) c := by
  rw [countChar_append]; omega

-- reverse is an involution
theorem reverse_involution' (s : String) : reverse (reverse s) = s := reverse_involutive s

-- reverse preserves length
theorem reverse_preserves_length (s : String) : (reverse s).length = s.length := reverse_length s

-- allChars true predicate always true
theorem allChars_true (s : String) : allChars s (fun _ => true) = true := allChars_of_empty_pred s

-- anyChar false predicate always false
theorem anyChar_false (s : String) : anyChar s (fun _ => false) = false := anyChar_false_pred s

-- toCharList preserves length
theorem toCharList_preserves_length (s : String) : (toCharList s).length = s.length :=
  toCharList_length s

-- truncate monotone: smaller n gives shorter result
theorem truncate_mono (s : String) (m n : Nat) (h : m ≤ n) :
    (truncate s m).length ≤ (truncate s n).length := by
  simp only [truncate, String.length_ofList, List.length_take]
  omega

end StringLaws

-- ═══════════════════════════════════════════════════════════════════════
-- §6  OptionResult — additional monad/functor laws
-- ═══════════════════════════════════════════════════════════════════════

namespace OptionResultLaws

open TSLean.Stdlib.OptionResult

-- mapOpt identity law
theorem mapOpt_id' {α : Type} (o : Option α) : mapOpt o id = o := by
  cases o <;> simp [mapOpt]

-- bindOpt left identity
theorem bindOpt_pure {α β : Type} (a : α) (f : α → Option β) :
    bindOpt (some a) f = f a := by
  simp [bindOpt]

-- bindOpt right identity
theorem bindOpt_return {α : Type} (o : Option α) :
    bindOpt o some = o := by
  cases o <;> simp [bindOpt]

-- liftOption then toOption roundtrip
theorem liftOption_toOption_roundtrip {α : Type} (o : Option α) (e : TSError) :
    toOption (liftOption o e) = o := by
  cases o <;> rfl

-- fromOption then toOption roundtrip
theorem fromOption_toOption_roundtrip {α : Type} (o : Option α) (e : TSError) :
    toOption (fromOption o e) = o := by
  cases o <;> rfl

-- recoverResult is idempotent for ok values
theorem recoverResult_ok_id {α : Type} (a : α) (f g : TSError → TSResult α) :
    recoverResult (recoverResult (.ok a) f) g = .ok a := by
  simp [recoverResult]

-- mapResult distributes over bindResult for ok
theorem mapResult_bindResult_ok {α β γ : Type} (a : α) (f : α → TSResult β) (g : β → γ) :
    mapResult (bindResult (.ok a) f) g = bindResult (.ok a) (fun x => mapResult (f x) g) := by
  simp [mapResult, bindResult, Except.bind, Except.map]

-- isOk and isError are complementary
theorem isOk_isError_compl {α : Type} (r : TSResult α) :
    isOk r = !isError r := by
  cases r <;> simp [isOk, isError, Except.isOk, Except.toBool]

-- filterOpt case split
theorem filterOpt_some_iff {α : Type} (a : α) (p : α → Bool) :
    filterOpt (some a) p = if p a then some a else none := by
  cases hp : p a <;> simp [filterOpt, Option.filter, hp]

-- sequenceList of all some gives some
theorem sequenceList_all_some {α : Type} (l : List α) :
    sequenceList (l.map some) = some l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [sequenceList] at *
    simp only [List.map_cons, List.mapM_cons, ih]
    rfl

end OptionResultLaws

end TSLean.Proofs.StdlibProperties
