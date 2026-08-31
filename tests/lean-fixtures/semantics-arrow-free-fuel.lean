import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
Negative fixture: an inline application that spends no fuel.

Applying an inline closure costs one unit of fuel, exactly as entering a declared function does. This
file claims the stored body runs at the fuel the application started with. The proof offered is the
direct reduction a correct fuel statement uses, so the model itself must reject it.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

theorem applyKeepsFuel (program : Ir.Program) (fuel : Nat) (trace : Source.Trace)
    (captured values : List Source.Value) (parameters : List Ir.Field) (body : Ir.Expr)
    (arity : parameters.length = values.length) :
    Source.applyClosure program (fuel + 1) trace captured parameters body values
      = Source.eval program (fuel + 1) (values.reverse ++ captured)
          (trace ++ [.application ⟨parameters, body⟩ values]) body := by
  simp [Source.applyClosure, arity]

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
