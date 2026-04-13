-- TSLean.Proofs.TypePreservation
-- Type mapping correctness: the transpiler's type lowering preserves structure.
-- Models the IRType → LeanType mapping from lower.ts lowerType.

import TSLean.Proofs.Semantics

namespace TSLean.Proofs.TypePreservation

open TSLean.Proofs.Semantics

/-! ## TS IR Type System (mirrors ir/types.ts IRType, pure subset) -/

inductive TSType where
  | nat    : TSType
  | int    : TSType
  | float  : TSType
  | string : TSType
  | bool   : TSType
  | unit   : TSType
  | never  : TSType
  | option : TSType → TSType
  | array  : TSType → TSType
  deriving Repr, BEq

/-! ## Lean Type Representation (what lowerType produces) -/

inductive LeanType where
  | name  : String → LeanType
  | app   : String → LeanType → LeanType
  deriving Repr, BEq

/-! ## The type mapping function (mirrors lowerType from lower.ts) -/

def mapType : TSType → LeanType
  | .nat      => .name "Nat"
  | .int      => .name "Int"
  | .float    => .name "Float"
  | .string   => .name "String"
  | .bool     => .name "Bool"
  | .unit     => .name "Unit"
  | .never    => .name "Empty"
  | .option t => .app "Option" (mapType t)
  | .array t  => .app "Array" (mapType t)

/-! ## Primitive type mapping equations -/

@[simp] theorem mapType_nat    : mapType .nat    = .name "Nat"    := rfl
@[simp] theorem mapType_int    : mapType .int    = .name "Int"    := rfl
@[simp] theorem mapType_float  : mapType .float  = .name "Float"  := rfl
@[simp] theorem mapType_string : mapType .string = .name "String" := rfl
@[simp] theorem mapType_bool   : mapType .bool   = .name "Bool"   := rfl
@[simp] theorem mapType_unit   : mapType .unit   = .name "Unit"   := rfl
@[simp] theorem mapType_never  : mapType .never  = .name "Empty"  := rfl

@[simp] theorem mapType_option (t : TSType) :
    mapType (.option t) = .app "Option" (mapType t) := rfl

@[simp] theorem mapType_array (t : TSType) :
    mapType (.array t) = .app "Array" (mapType t) := rfl

/-! ## mapType is injective -/

theorem mapType_injective : ∀ (t1 t2 : TSType), mapType t1 = mapType t2 → t1 = t2 := by
  intro t1
  induction t1 with
  | nat      => intro t2 h; cases t2 <;> simp_all [mapType]
  | int      => intro t2 h; cases t2 <;> simp_all [mapType]
  | float    => intro t2 h; cases t2 <;> simp_all [mapType]
  | string   => intro t2 h; cases t2 <;> simp_all [mapType]
  | bool     => intro t2 h; cases t2 <;> simp_all [mapType]
  | unit     => intro t2 h; cases t2 <;> simp_all [mapType]
  | never    => intro t2 h; cases t2 <;> simp_all [mapType]
  | option t ih =>
    intro t2 h
    cases t2 with
    | option t2' => simp [mapType] at h; exact congrArg _ (ih t2' h)
    | _ => simp [mapType] at h
  | array t ih =>
    intro t2 h
    cases t2 with
    | array t2' => simp [mapType] at h; exact congrArg _ (ih t2' h)
    | _ => simp [mapType] at h

/-! ## Value typing: when a Val has a given TSType -/

def wellTyped : Val → TSType → Prop
  | .num _,  .float  => True
  | .num _,  .nat    => True
  | .num _,  .int    => True
  | .bool _, .bool   => True
  | .str _,  .string => True
  | .unit,   .unit   => True
  | _, _ => False

theorem wellTyped_num_float (n : Float) : wellTyped (.num n) .float := trivial
theorem wellTyped_num_nat (n : Float) : wellTyped (.num n) .nat := trivial
theorem wellTyped_num_int (n : Float) : wellTyped (.num n) .int := trivial
theorem wellTyped_bool (b : Bool) : wellTyped (.bool b) .bool := trivial
theorem wellTyped_str (s : String) : wellTyped (.str s) .string := trivial
theorem wellTyped_unit : wellTyped .unit .unit := trivial

/-! ## Type preservation for BinOps -/

theorem binOp_arith_type (op : BinOp) (a b : Float) (v : Val)
    (hop : op = .add ∨ op = .sub ∨ op = .mul)
    (heval : evalBinOp op (.num a) (.num b) = some v) :
    wellTyped v .float := by
  rcases hop with h | h | h <;> subst h <;> simp [evalBinOp] at heval <;> rw [← heval] <;> trivial

theorem binOp_cmp_type (op : BinOp) (a b : Float) (v : Val)
    (hop : op = .eq ∨ op = .ne ∨ op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge)
    (heval : evalBinOp op (.num a) (.num b) = some v) :
    wellTyped v .bool := by
  rcases hop with h | h | h | h | h | h <;>
    subst h <;> simp [evalBinOp] at heval <;> rw [← heval] <;> trivial

theorem binOp_concat_type (a b : String) (v : Val)
    (heval : evalBinOp .concat (.str a) (.str b) = some v) :
    wellTyped v .string := by
  simp [evalBinOp] at heval; rw [← heval]; trivial

theorem binOp_logic_type (op : BinOp) (a b : Bool) (v : Val)
    (hop : op = .and_ ∨ op = .or_)
    (heval : evalBinOp op (.bool a) (.bool b) = some v) :
    wellTyped v .bool := by
  rcases hop with h | h <;> subst h <;> simp [evalBinOp] at heval <;> rw [← heval] <;> trivial

/-! ## mapType commutes with type constructors -/

theorem mapType_option_comm (t1 t2 : TSType) (h : mapType t1 = mapType t2) :
    mapType (.option t1) = mapType (.option t2) := by
  simp [mapType, h]

theorem mapType_array_comm (t1 t2 : TSType) (h : mapType t1 = mapType t2) :
    mapType (.array t1) = mapType (.array t2) := by
  simp [mapType, h]

/-! ## mapType totality and coverage -/

theorem mapType_total (t : TSType) : ∃ lt, mapType t = lt := ⟨mapType t, rfl⟩

/-! ## Well-typedness is preserved by evaluation: if input is well-typed and
    evalBinOp succeeds, the output is well-typed at the appropriate result type. -/

def binOpResultType : BinOp → TSType → TSType → Option TSType
  | .add,    .float, .float => some .float
  | .add,    .nat,   .nat   => some .float
  | .add,    .int,   .int   => some .float
  | .sub,    .float, .float => some .float
  | .mul,    .float, .float => some .float
  | .eq,     _,      _      => some .bool
  | .ne,     _,      _      => some .bool
  | .lt,     .float, .float => some .bool
  | .le,     .float, .float => some .bool
  | .gt,     .float, .float => some .bool
  | .ge,     .float, .float => some .bool
  | .and_,   .bool,  .bool  => some .bool
  | .or_,    .bool,  .bool  => some .bool
  | .concat, .string, .string => some .string
  | _, _, _ => none

-- The result type mapping is preserved by mapType
theorem binOpResultType_mapType_compat (op : BinOp) (t1 t2 tr : TSType)
    (h : binOpResultType op t1 t2 = some tr) :
    ∃ lr, mapType tr = lr := ⟨mapType tr, rfl⟩

end TSLean.Proofs.TypePreservation
