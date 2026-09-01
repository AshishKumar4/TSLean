import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
Negative fixture: an eager `&&`.

`emitter.ts` writes `left && right`, which evaluates its right operand only when the left one does
not decide the answer, so the source semantics is lazy in exactly the same place. This file claims
the right operand runs even at a `false` left operand, which is the shape routing `bool.and` through
the strict operation form would have. The proof offered is the direct reduction the lazy statement
uses, so the model itself must reject it.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

theorem andIsEager (program : Ir.Program) (fuel : Nat) (scope : List Source.Value)
    (trace next : Source.Trace) (typeArguments : List Ir.Ty) (left right : Ir.Expr)
    (leftRun : Source.eval program fuel scope trace left = .value (.boolean false) next) :
    Source.eval program fuel scope trace (.operation .boolAnd typeArguments [left, right])
      = Source.eval program fuel scope next right := by
  rw [Source.eval.eq_def]
  simp only [Ir.Opcode.operator?, leftRun]

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
