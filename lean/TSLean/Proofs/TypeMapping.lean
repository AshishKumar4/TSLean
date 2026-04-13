/-
  TSLean.Proofs.TypeMapping
  Correctness theorems for type classification and mapping functions.
-/
import TSLean.Generated.SelfHost.ir_types
import TSLean.Generated.SelfHost.stdlib_index
import TSLean.Generated.SelfHost.typemap_index

open TSLean.Generated.Types
open TSLean.Generated.SelfHost.StdlibIndex
open TSLean.Generated.SelfHost.TypemapIndex

-- ─── isStringType is correct ─────────────────────────────────────────────────────

theorem isStringType_String : isStringType IRType.String = true := by rfl
theorem isStringType_Bool : isStringType IRType.Bool = false := by rfl
theorem isStringType_Nat : isStringType IRType.Nat = false := by rfl
theorem isStringType_Array (e : IRType) : isStringType (IRType.Array e) = false := by rfl

-- isStringType characterization
theorem isStringType_iff (t : IRType) : isStringType t = true ↔ t = IRType.String := by
  constructor
  · intro h; cases t <;> simp [isStringType] at h ⊢ <;> exact h
  · intro h; subst h; rfl

-- ─── typeObjKind maps primitives correctly ───────────────────────────────────────

theorem typeObjKind_String : typeObjKind IRType.String = ObjKind.String := by rfl
theorem typeObjKind_Array (e : IRType) : typeObjKind (IRType.Array e) = ObjKind.Array := by rfl
theorem typeObjKind_Map (k v : IRType) : typeObjKind (IRType.Map k v) = ObjKind.Map := by rfl
theorem typeObjKind_Set (e : IRType) : typeObjKind (IRType.Set e) = ObjKind.Set := by rfl
theorem typeObjKind_Bool : typeObjKind IRType.Bool = ObjKind.Unknown := by rfl
theorem typeObjKind_Nat : typeObjKind IRType.Nat = ObjKind.Unknown := by rfl

-- TypeRef "Map" maps to ObjKind.Map
theorem typeObjKind_MapRef :
    typeObjKind (IRType.TypeRef "Map" #[]) = ObjKind.Map := by rfl

theorem typeObjKind_AssocMapRef :
    typeObjKind (IRType.TypeRef "AssocMap" #[]) = ObjKind.Map := by rfl

theorem typeObjKind_SetRef :
    typeObjKind (IRType.TypeRef "Set" #[]) = ObjKind.Set := by rfl

-- ─── translateBinOp string concatenation ─────────────────────────────────────────

theorem translateBinOp_Add_String :
    translateBinOp "Add" IRType.String = "++" := by native_decide

theorem translateBinOp_Add_Nat :
    translateBinOp "Add" IRType.Nat = "+" := by native_decide

theorem translateBinOp_Eq :
    translateBinOp "Eq" IRType.Nat = "==" := by native_decide

theorem translateBinOp_Concat :
    translateBinOp "Concat" IRType.String = "++" := by native_decide

-- ─── typeStr / irTypeToLean roundtrip properties ─────────────────────────────────

-- irTypeToLean with parens=false returns typeStr directly
-- (These use partial defs, so we verify specific cases via native_decide)
theorem irTypeToLean_Nat : irTypeToLean IRType.Nat = "Nat" := by native_decide
theorem irTypeToLean_String : irTypeToLean IRType.String = "String" := by native_decide
theorem irTypeToLean_Bool : irTypeToLean IRType.Bool = "Bool" := by native_decide
theorem irTypeToLean_Unit : irTypeToLean IRType.Unit = "Unit" := by native_decide
theorem irTypeToLean_Never : irTypeToLean IRType.Never = "Empty" := by native_decide

-- Parens wrapping: multi-word types get parenthesized
theorem irTypeToLean_Option_parens :
    irTypeToLean (IRType.Option IRType.Nat) true = "(Option Nat)" := by native_decide

-- No wrapping for single-word types
theorem irTypeToLean_Nat_parens :
    irTypeToLean IRType.Nat true = "Nat" := by native_decide
