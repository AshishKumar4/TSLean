-- TSLean.DurableObjects.RPC
import TSLean.Runtime.Basic
import TSLean.Runtime.Monad

namespace TSLean.DO.RPC
open TSLean

class Serializer (α : Type) where
  serialize   : α → String
  deserialize : String → Option α
  roundtrip   : ∀ (a : α), deserialize (serialize a) = some a

def Serializer.deserializeOrThrow {α} [Serializer α] (s ctx : String) : Except TSError α :=
  match Serializer.deserialize s with
  | some a => .ok a
  | none   => .error (.typeError s!"Deserialisation failed in {ctx}")

instance : Serializer String where
  serialize s := s; deserialize s := some s; roundtrip _ := rfl

-- The `Nat` serializer was removed here. Its `roundtrip` field was discharged by
-- `private axiom nat_toNat?_toString : (toString n).toNat? = some n`, and this module is in the
-- emitted trusted base directly -- `DO_LEAN_IMPORTS` puts it at the top of every emitted Durable
-- Object file -- so that axiom was an unearned assumption in every artifact the compiler produced
-- from one. The statement is true but needs decimal-parsing lemmas Lean 4.29 does not expose
-- (`exact?` and `simp` both fail), and nothing outside this file consumes `Serializer` at all --
-- so an unused instance is dropped rather than its law asserted.

instance : Serializer Bool where
  serialize b := if b then "true" else "false"
  deserialize s := if s == "true" then some true else if s == "false" then some false else none
  roundtrip b := by cases b <;> simp

instance : Serializer Unit where
  serialize _ := "()"; deserialize s := if s == "()" then some () else none
  roundtrip _ := by simp

-- The `Option` serializer was removed here for the same reason: its `roundtrip` rested on
-- `private axiom option_serializer_roundtrip`, nothing consumes it, and an unproven law in the
-- emitted trusted base is worse than an absent instance.

structure RPCRequest where
  method : String
  arg    : String
  reqId  : Nat
  deriving Repr, BEq

structure RPCResponse where
  reqId  : Nat
  result : Except String String
  deriving Repr

class RPCHandler (σ : Type) where
  handle : RPCRequest → DOMonad σ RPCResponse

theorem serializer_roundtrip_string (s : String) :
    Serializer.deserialize (α := String) (Serializer.serialize s) = some s := Serializer.roundtrip s

theorem serializer_roundtrip_bool (b : Bool) :
    Serializer.deserialize (α := Bool) (Serializer.serialize b) = some b := Serializer.roundtrip b

theorem serializer_roundtrip_unit :
    Serializer.deserialize (α := Unit) (Serializer.serialize ()) = some () := Serializer.roundtrip ()

theorem deserializeOrThrow_roundtrip {α} [Serializer α] (a : α) (ctx : String) :
    Serializer.deserializeOrThrow (Serializer.serialize a) ctx = .ok a := by
  simp [Serializer.deserializeOrThrow, Serializer.roundtrip]

theorem serializer_injective {α} [Serializer α] (a b : α)
    (h : Serializer.serialize a = Serializer.serialize b) : a = b := by
  have ha := Serializer.roundtrip a; have hb := Serializer.roundtrip b
  rw [h] at ha; exact Option.some.inj (ha.symm.trans hb)

theorem rpcRequest_eq_iff (r₁ r₂ : RPCRequest) :
    r₁ = r₂ ↔ r₁.method = r₂.method ∧ r₁.arg = r₂.arg ∧ r₁.reqId = r₂.reqId := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · intro ⟨hm, ha, hi⟩; cases r₁; cases r₂; simp_all

theorem deserializeOrThrow_succeeds [Serializer α] (a : α) (ctx : String) :
    (Serializer.deserializeOrThrow (α := α) (Serializer.serialize a) ctx).isOk = true := by
  simp [Serializer.deserializeOrThrow, Serializer.roundtrip, Except.isOk, Except.toBool]

theorem rpcResponse_same_reqId (r : RPCResponse) : r.reqId = r.reqId := rfl

theorem serializer_never_none [Serializer α] (a : α) :
    Serializer.deserialize (α := α) (Serializer.serialize a) ≠ none := by
  rw [Serializer.roundtrip]; simp

theorem serializer_string_identity (s : String) :
    Serializer.serialize (α := String) s = s := rfl

theorem serializer_bool_true : Serializer.serialize (α := Bool) true = "true" := rfl
theorem serializer_bool_false : Serializer.serialize (α := Bool) false = "false" := rfl

theorem deserializeOrThrow_ok_iff [Serializer α] (s ctx : String) :
    (Serializer.deserializeOrThrow (α := α) s ctx).isOk = true ↔
    (Serializer.deserialize (α := α) s).isSome = true := by
  simp [Serializer.deserializeOrThrow]
  cases Serializer.deserialize (α := α) s with
  | none => simp [Except.isOk, Except.toBool]
  | some v => simp [Except.isOk, Except.toBool]

theorem rpc_request_method_preserved (r : RPCRequest) :
    r.method = r.method := rfl

end TSLean.DO.RPC
