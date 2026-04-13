-- TSLean.Runtime.BrandedTypes
import TSLean.Runtime.Basic

namespace TSLean

structure UserId       where val : String deriving Repr, BEq, Hashable
structure RoomId       where val : String deriving Repr, BEq, Hashable
structure MessageId    where val : String deriving Repr, BEq, Hashable
structure SessionToken where val : String deriving Repr, BEq, Hashable

def UserId.mk'       (s : String) : Option UserId       := if s.length > 0 then some ⟨s⟩ else none
def RoomId.mk'       (s : String) : Option RoomId       := if s.length > 0 then some ⟨s⟩ else none
def MessageId.mk'    (s : String) : Option MessageId    := if s.length > 0 then some ⟨s⟩ else none
def SessionToken.mk' (s : String) : Option SessionToken := if s.length > 0 then some ⟨s⟩ else none

instance : Coe UserId      String where coe u := u.val
instance : Coe RoomId      String where coe r := r.val
instance : Coe MessageId   String where coe m := m.val
instance : Coe SessionToken String where coe t := t.val

instance : ToString UserId       where toString u := u.val
instance : ToString RoomId       where toString r := r.val
instance : ToString MessageId    where toString m := m.val
instance : ToString SessionToken where toString t := t.val

instance : DecidableEq UserId :=
  fun a b => if h : a.val = b.val then isTrue (by cases a; cases b; exact congrArg UserId.mk h)
             else isFalse (by intro heq; cases heq; exact h rfl)
instance : DecidableEq RoomId :=
  fun a b => if h : a.val = b.val then isTrue (by cases a; cases b; exact congrArg RoomId.mk h)
             else isFalse (by intro heq; cases heq; exact h rfl)
instance : DecidableEq MessageId :=
  fun a b => if h : a.val = b.val then isTrue (by cases a; cases b; exact congrArg MessageId.mk h)
             else isFalse (by intro heq; cases heq; exact h rfl)
instance : DecidableEq SessionToken :=
  fun a b => if h : a.val = b.val then isTrue (by cases a; cases b; exact congrArg SessionToken.mk h)
             else isFalse (by intro heq; cases heq; exact h rfl)

instance : LawfulBEq UserId where
  eq_of_beq {a b} h := by
    cases a; cases b; simp only [BEq.beq] at h
    exact congrArg UserId.mk (LawfulBEq.eq_of_beq h)
  rfl := by intro a; cases a; simp only [BEq.beq]; exact beq_self_eq_true _
instance : LawfulBEq RoomId where
  eq_of_beq {a b} h := by
    cases a; cases b; simp only [BEq.beq] at h
    exact congrArg RoomId.mk (LawfulBEq.eq_of_beq h)
  rfl := by intro a; cases a; simp only [BEq.beq]; exact beq_self_eq_true _
instance : LawfulBEq MessageId where
  eq_of_beq {a b} h := by
    cases a; cases b; simp only [BEq.beq] at h
    exact congrArg MessageId.mk (LawfulBEq.eq_of_beq h)
  rfl := by intro a; cases a; simp only [BEq.beq]; exact beq_self_eq_true _
instance : LawfulBEq SessionToken where
  eq_of_beq {a b} h := by
    cases a; cases b; simp only [BEq.beq] at h
    exact congrArg SessionToken.mk (LawfulBEq.eq_of_beq h)
  rfl := by intro a; cases a; simp only [BEq.beq]; exact beq_self_eq_true _
instance : Ord UserId       where compare a b := compare a.val b.val
instance : Ord RoomId       where compare a b := compare a.val b.val
instance : Ord MessageId    where compare a b := compare a.val b.val
instance : Ord SessionToken where compare a b := compare a.val b.val

theorem UserId.val_injective      : Function.Injective UserId.val      := fun a b h => by cases a; cases b; exact congrArg UserId.mk h
theorem RoomId.val_injective      : Function.Injective RoomId.val      := fun a b h => by cases a; cases b; exact congrArg RoomId.mk h
theorem MessageId.val_injective   : Function.Injective MessageId.val   := fun a b h => by cases a; cases b; exact congrArg MessageId.mk h
theorem SessionToken.val_injective: Function.Injective SessionToken.val := fun a b h => by cases a; cases b; exact congrArg SessionToken.mk h

theorem UserId.eq_iff_val_eq (a b : UserId) : a = b ↔ a.val = b.val := ⟨fun h => by cases h; rfl, fun h => UserId.val_injective h⟩
theorem RoomId.eq_iff_val_eq (a b : RoomId) : a = b ↔ a.val = b.val := ⟨fun h => by cases h; rfl, fun h => RoomId.val_injective h⟩
theorem MessageId.eq_iff_val_eq (a b : MessageId) : a = b ↔ a.val = b.val := ⟨fun h => by cases h; rfl, fun h => MessageId.val_injective h⟩
theorem SessionToken.eq_iff_val_eq (a b : SessionToken) : a = b ↔ a.val = b.val := ⟨fun h => by cases h; rfl, fun h => SessionToken.val_injective h⟩

theorem UserId.ne_iff_val_ne (a b : UserId) : a ≠ b ↔ a.val ≠ b.val := by rw [ne_eq, UserId.eq_iff_val_eq]
theorem RoomId.ne_iff_val_ne (a b : RoomId) : a ≠ b ↔ a.val ≠ b.val := by rw [ne_eq, RoomId.eq_iff_val_eq]
theorem MessageId.ne_iff_val_ne (a b : MessageId) : a ≠ b ↔ a.val ≠ b.val := by rw [ne_eq, MessageId.eq_iff_val_eq]
theorem SessionToken.ne_iff_val_ne (a b : SessionToken) : a ≠ b ↔ a.val ≠ b.val := by rw [ne_eq, SessionToken.eq_iff_val_eq]

theorem UserId.mk'_some_iff (s : String) : (UserId.mk' s).isSome ↔ s.length > 0 := by simp only [UserId.mk', Option.isSome]; split <;> simp_all
theorem RoomId.mk'_some_iff (s : String) : (RoomId.mk' s).isSome ↔ s.length > 0 := by simp only [RoomId.mk', Option.isSome]; split <;> simp_all
theorem MessageId.mk'_some_iff (s : String) : (MessageId.mk' s).isSome ↔ s.length > 0 := by simp only [MessageId.mk', Option.isSome]; split <;> simp_all
theorem SessionToken.mk'_some_iff (s : String) : (SessionToken.mk' s).isSome ↔ s.length > 0 := by simp only [SessionToken.mk', Option.isSome]; split <;> simp_all

theorem UserId.mk'_val {s : String} {u : UserId} (h : UserId.mk' s = some u) : u.val = s := by
  simp only [UserId.mk'] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h ▸ rfl
  · simp at h
theorem RoomId.mk'_val {s : String} {r : RoomId} (h : RoomId.mk' s = some r) : r.val = s := by
  simp only [RoomId.mk'] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h ▸ rfl
  · simp at h
theorem MessageId.mk'_val {s : String} {m : MessageId} (h : MessageId.mk' s = some m) : m.val = s := by
  simp only [MessageId.mk'] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h ▸ rfl
  · simp at h
theorem SessionToken.mk'_val {s : String} {t : SessionToken} (h : SessionToken.mk' s = some t) : t.val = s := by
  simp only [SessionToken.mk'] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h ▸ rfl
  · simp at h

theorem UserId.coe_eq_val (u : UserId) : (u : String) = u.val := rfl
theorem RoomId.coe_eq_val (r : RoomId) : (r : String) = r.val := rfl
theorem MessageId.coe_eq_val (m : MessageId) : (m : String) = m.val := rfl
theorem SessionToken.coe_eq_val (t : SessionToken) : (t : String) = t.val := rfl

theorem UserId.mk_val (s : String) : (UserId.mk s).val = s := rfl
theorem RoomId.mk_val (s : String) : (RoomId.mk s).val = s := rfl
theorem MessageId.mk_val (s : String) : (MessageId.mk s).val = s := rfl
theorem SessionToken.mk_val (s : String) : (SessionToken.mk s).val = s := rfl

theorem UserId.eq_of_val_eq (a b : UserId) : a.val = b.val → a = b := fun h => UserId.val_injective h
theorem RoomId.eq_of_val_eq (a b : RoomId) : a.val = b.val → a = b := fun h => RoomId.val_injective h
theorem UserId.ne_of_val_ne (a b : UserId) : a.val ≠ b.val → a ≠ b :=
  fun h heq => h (congrArg UserId.val heq)
theorem RoomId.ne_of_val_ne (a b : RoomId) : a.val ≠ b.val → a ≠ b :=
  fun h heq => h (congrArg RoomId.val heq)

end TSLean
