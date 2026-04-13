-- TSLean.Runtime.Validation
import TSLean.Runtime.Basic
import TSLean.Runtime.BrandedTypes

namespace TSLean.Validation

def validLength (s : String) (minLen maxLen : Nat) : Bool :=
  decide (minLen ≤ s.length ∧ s.length ≤ maxLen)

def nonEmpty (s : String) : Bool := decide (s.length > 0)

def containsChar (s : String) (c : Char) : Bool := s.toList.contains c

def isAlphanumeric (s : String) : Bool := s.toList.all (fun c => c.isAlphanum)

def isValidIdentifier (s : String) : Bool :=
  match s.toList with
  | []     => false
  | c :: cs => (c.isAlpha || c = '_') && cs.all (fun x => x.isAlphanum || x = '_')

def isEmailLike (s : String) : Bool :=
  match s.splitOn "@" with
  | [local_, domain] => nonEmpty local_ && nonEmpty domain && domain.contains '.'
  | _ => false

def isHexColor (s : String) : Bool :=
  match s.toList with
  | '#' :: rest => (rest.length = 6 || rest.length = 3) &&
                   rest.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F'))
  | _ => false

def validateUserId (s : String) : Option UserId := if validLength s 1 128 then some ⟨s⟩ else none
def validateRoomId (s : String) : Option RoomId := if validLength s 1 64 then some ⟨s⟩ else none
def validateSessionToken (s : String) : Option SessionToken := if validLength s 16 512 then some ⟨s⟩ else none
def validateMessageId (s : String) : Option MessageId := if validLength s 1 256 then some ⟨s⟩ else none

-- Theorems

theorem validLength_iff (s : String) (lo hi : Nat) :
    validLength s lo hi = true ↔ lo ≤ s.length ∧ s.length ≤ hi := by
  simp [validLength, decide_eq_true_eq]

theorem validLength_false_iff (s : String) (lo hi : Nat) :
    validLength s lo hi = false ↔ ¬(lo ≤ s.length ∧ s.length ≤ hi) := by
  simp [validLength, Bool.not_eq_true, decide_eq_false_iff_not, decide_eq_true_eq]

theorem nonEmpty_iff (s : String) : nonEmpty s = true ↔ s.length > 0 := by
  simp [nonEmpty, decide_eq_true_eq]

theorem nonEmpty_empty : nonEmpty "" = false := by simp [nonEmpty]

theorem nonEmpty_iff_ne_empty (s : String) : nonEmpty s = true ↔ s ≠ "" := by
  simp [nonEmpty, decide_eq_true_eq]
  constructor
  · intro h heq; rw [heq] at h; simp at h
  · intro h
    cases Nat.eq_zero_or_pos s.length with
    | inl hz => exact absurd (String.length_eq_zero_iff.mp hz) h
    | inr hp => exact hp

theorem containsChar_iff (s : String) (c : Char) : containsChar s c = true ↔ c ∈ s.toList := by
  simp [containsChar, List.contains_iff_mem]

theorem containsChar_false_iff (s : String) (c : Char) : containsChar s c = false ↔ c ∉ s.toList := by
  simp [containsChar, List.contains_iff_mem]

theorem validLength_pos_lo_implies_nonEmpty (s : String) (lo hi : Nat) (hlo : lo > 0)
    (h : validLength s lo hi = true) : nonEmpty s = true := by
  rw [validLength_iff] at h; rw [nonEmpty_iff]; omega

theorem validLength_empty_false (lo hi : Nat) (hlo : lo > 0) : validLength "" lo hi = false := by
  simp [validLength_false_iff, String.length]; omega

theorem validLength_mono (s : String) (lo₁ lo₂ hi₁ hi₂ : Nat) (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂)
    (h : validLength s lo₁ hi₁ = true) : validLength s lo₂ hi₂ = true := by
  rw [validLength_iff] at *; omega

theorem validateUserId_iff (s : String) : (validateUserId s).isSome ↔ 1 ≤ s.length ∧ s.length ≤ 128 := by
  simp [validateUserId, validLength_iff]

theorem validateUserId_val (s : String) (h : 1 ≤ s.length ∧ s.length ≤ 128) :
    ∃ u : UserId, validateUserId s = some u ∧ u.val = s :=
  ⟨⟨s⟩, by simp [validateUserId, validLength_iff, h]⟩

theorem validateRoomId_iff (s : String) : (validateRoomId s).isSome ↔ 1 ≤ s.length ∧ s.length ≤ 64 := by
  simp [validateRoomId, validLength_iff]

theorem validateSessionToken_min_length (s : String) (t : SessionToken)
    (h : validateSessionToken s = some t) : s.length ≥ 16 := by
  simp only [validateSessionToken] at h; split at h
  · next hv => rw [validLength_iff] at hv; exact hv.1
  · simp at h

theorem isAlphanumeric_empty : isAlphanumeric "" = true := by simp [isAlphanumeric]
theorem isValidIdentifier_empty : isValidIdentifier "" = false := by simp [isValidIdentifier]

theorem containsChar_append_left (s t : String) (c : Char) (h : containsChar s c = true) :
    containsChar (s ++ t) c = true := by
  rw [containsChar_iff] at *; simp [String.toList_append, List.mem_append]; exact Or.inl h

theorem containsChar_append_right (s t : String) (c : Char) (h : containsChar t c = true) :
    containsChar (s ++ t) c = true := by
  rw [containsChar_iff] at *; simp [String.toList_append, List.mem_append]; exact Or.inr h

theorem nonEmpty_append_left (s t : String) (h : nonEmpty s = true) : nonEmpty (s ++ t) = true := by
  rw [nonEmpty_iff] at *; simp [String.length_append]; omega

theorem nonEmpty_append_right (s t : String) (h : nonEmpty t = true) : nonEmpty (s ++ t) = true := by
  rw [nonEmpty_iff] at *; simp [String.length_append]; omega

theorem validateMessageId_val (s : String) (h : 1 ≤ s.length ∧ s.length ≤ 256) :
    ∃ m : MessageId, validateMessageId s = some m ∧ m.val = s :=
  ⟨⟨s⟩, by simp [validateMessageId, validLength_iff, h]⟩

theorem validateSessionToken_iff (s : String) : (validateSessionToken s).isSome ↔ 16 ≤ s.length ∧ s.length ≤ 512 := by
  simp [validateSessionToken, validLength_iff]

theorem validateMessageId_iff (s : String) : (validateMessageId s).isSome ↔ 1 ≤ s.length ∧ s.length ≤ 256 := by
  simp [validateMessageId, validLength_iff]

theorem isAlphanumeric_append (s t : String) (hs : isAlphanumeric s = true) (ht : isAlphanumeric t = true) :
    isAlphanumeric (s ++ t) = true := by
  simp only [isAlphanumeric, String.toList_append, List.all_append, Bool.and_eq_true]
  simp only [isAlphanumeric] at hs ht; exact ⟨hs, ht⟩

theorem isValidIdentifier_nonempty (s : String) (h : isValidIdentifier s = true) : s.length > 0 := by
  simp only [isValidIdentifier] at h
  cases hlist : s.toList with
  | nil => rw [hlist] at h; simp at h
  | cons c cs =>
    have : s.toList.length ≥ 1 := by rw [hlist]; simp
    rwa [← String.length_toList]

-- isEmailLike_nonempty: if it validates as email-like, string is nonempty
theorem isEmailLike_nonempty (s : String) (h : isEmailLike s = true) :
    s.length > 0 := by
  simp only [isEmailLike] at h
  cases hsp : s.splitOn "@" with
  | nil => rw [hsp] at h; simp at h
  | cons hd tl =>
    cases tl with
    | nil => rw [hsp] at h; simp at h
    | cons hd2 tl2 =>
      cases tl2 with
      | nil =>
        rw [hsp] at h
        simp only [nonEmpty, Bool.and_eq_true, decide_eq_true_eq] at h
        -- hd.length > 0, and hd is a piece of s, so s.length > 0
        exact Nat.pos_of_ne_zero (fun hz => by
          have hs_empty := String.length_eq_zero_iff.mp hz
          rw [hs_empty] at hsp
          -- "".splitOn "@" = [""] ≠ ["hd", "hd2"]
          have : ("" : String).splitOn "@" = [""] := by native_decide
          rw [this] at hsp
          exact absurd hsp (by simp))
      | cons _ _ => rw [hsp] at h; simp at h

-- isHexColor_starts_hash: if isHexColor s, then s starts with '#'
theorem isHexColor_starts_hash (s : String) (h : isHexColor s = true) :
    s.toList.head? = some '#' := by
  simp only [isHexColor] at h
  cases hlist : s.toList with
  | nil => rw [hlist] at h; simp at h
  | cons c rest =>
    simp only [List.head?_cons]
    rw [hlist] at h
    -- The match in isHexColor is on '#' :: rest vs _
    -- Since h = true, we must be in the '#' :: rest branch
    split at h
    · -- matched '#' :: rest pattern, meaning c = '#'
      next heq =>
        have hc : c = '#' := (List.cons.inj heq).1
        exact congrArg some hc
    · simp at h

theorem validLength_antisymm (s : String) (n : Nat) :
    validLength s n n = true ↔ s.length = n := by
  rw [validLength_iff]; omega

end TSLean.Validation
