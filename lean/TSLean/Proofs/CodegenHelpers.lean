/-
  TSLean.Proofs.CodegenHelpers
  Correctness theorems for codegen helper functions.
-/
import TSLean.Generated.SelfHost.ir_types
import TSLean.Generated.SelfHost.codegen_index

open TSLean.Generated.Types
open TSLean.Generated.SelfHost.CodegenIndex

-- ─── fmtTPs: empty params produces empty string ──────────────────────────────────

theorem fmtTPs_empty : fmtTPs #[] = "" := by native_decide

-- ─── fmtExplicitTPs: empty params produces empty string ──────────────────────────

theorem fmtExplicitTPs_empty : fmtExplicitTPs #[] = "" := by native_decide

-- ─── sanitize: non-keyword passes through ────────────────────────────────────────

theorem sanitize_ordinary : sanitize "myFunc" = "myFunc" := by native_decide
theorem sanitize_keyword_def : sanitize "def" = "«def»" := by native_decide
theorem sanitize_keyword_let : sanitize "let" = "«let»" := by native_decide
theorem sanitize_keyword_match : sanitize "match" = "«match»" := by native_decide

-- sanitize replaces slashes
theorem sanitize_slash : sanitize "a/b" = "a_b" := by native_decide

-- ─── needsParens correctness ─────────────────────────────────────────────────────

theorem needsParens_App : needsParens { tag := "App" } = true := by native_decide
theorem needsParens_BinOp : needsParens { tag := "BinOp" } = true := by native_decide
theorem needsParens_Var : needsParens { tag := "Var" } = false := by native_decide
theorem needsParens_LitString : needsParens { tag := "LitString" } = false := by native_decide
theorem needsParens_Lambda : needsParens { tag := "Lambda" } = true := by native_decide

-- ─── isSimpleValue correctness ───────────────────────────────────────────────────

theorem isSimpleValue_true : isSimpleValue "true" = true := by native_decide
theorem isSimpleValue_false : isSimpleValue "false" = true := by native_decide
theorem isSimpleValue_default : isSimpleValue "default" = true := by native_decide
theorem isSimpleValue_none : isSimpleValue "none" = true := by native_decide
theorem isSimpleValue_empty_array : isSimpleValue "#[]" = true := by native_decide
theorem isSimpleValue_func : isSimpleValue "myFunc x" = false := by native_decide

-- ─── isEmptyElse correctness ─────────────────────────────────────────────────────

theorem isEmptyElse_LitUnit : isEmptyElse { tag := "LitUnit" } = true := by native_decide
theorem isEmptyElse_Var : isEmptyElse { tag := "Var" } = false := by native_decide

-- ─── looksMonadic correctness ────────────────────────────────────────────────────

theorem looksMonadic_do : looksMonadic "do\n  x" = true := by native_decide
theorem looksMonadic_pure : looksMonadic "pure x" = true := by native_decide
theorem looksMonadic_return : looksMonadic "return x" = true := by native_decide
theorem looksMonadic_let : looksMonadic "let x := 5" = true := by native_decide
theorem looksMonadic_expr : looksMonadic "myFunc x" = false := by native_decide

-- ─── sorryForType correctness ────────────────────────────────────────────────────

theorem sorryForType_empty : sorryForType "" = "sorry" := by native_decide
theorem sorryForType_Bool : sorryForType "Bool" = "(sorry : Bool)" := by native_decide
theorem sorryForType_String : sorryForType "String" = "(sorry : String)" := by native_decide
theorem sorryForType_Unit : sorryForType "Unit" = "()" := by native_decide
theorem sorryForType_Option : sorryForType "Option" = "none" := by native_decide
theorem sorryForType_Array : sorryForType "Array" = "#[]" := by native_decide

-- ─── Gen.retSig: Pure effect returns the type directly ───────────────────────────

theorem retSig_Pure (gs : GenState) (ret : String) :
    Gen.retSig gs Effect.Pure ret = ret := by rfl

theorem retSig_IO (gs : GenState) (ret : String) :
    Gen.retSig gs Effect.IO ret = "IO " ++ ret := by rfl

-- ─── Gen.genExpr: empty tag returns "sorry" ──────────────────────────────────────

theorem genExpr_empty_tag (gs : GenState) (ctx : Effect) :
    Gen.genExpr gs { tag := "" } ctx = "sorry" := by
  simp [Gen.genExpr]

-- ─── Gen.resolveType is identity ─────────────────────────────────────────────────

theorem resolveType_id (gs : GenState) (ty : String) :
    Gen.resolveType gs ty = ty := by rfl

-- ─── GENERATED_BANNER is a Lean comment ──────────────────────────────────────────

theorem banner_starts_with_comment :
    GENERATED_BANNER.startsWith "--" = true := by native_decide
