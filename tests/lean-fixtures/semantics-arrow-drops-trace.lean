import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
Negative fixture: an inline application that records no entry.

Applying an inline closure records one `.application` event carrying its exact `LambdaCode`, exactly
as a declared entry records a `.function` event. This file claims the stored body runs on the trace
the application started from, which is the shape a lowering that dropped the event would have. The
proof offered is the direct reduction a correct trace statement uses, so the model itself must reject
it.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

theorem applyRecordsNothing (program : Ir.Program) (fuel : Nat) (trace : Source.Trace)
    (captured values : List Source.Value) (parameters : List Ir.Field) (body : Ir.Expr)
    (arity : parameters.length = values.length) :
    Source.applyClosure program (fuel + 1) trace captured parameters body values
      = Source.eval program fuel (values.reverse ++ captured) trace body := by
  simp [Source.applyClosure, arity]

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
