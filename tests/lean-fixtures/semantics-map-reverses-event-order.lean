import TSLean.LeanToTypeScript.Semantics.Preservation

/-!
Negative fixture: a higher-order opcode entering its callback out of order.

`value.map((element) => transform(element))` enters the callback once per element in element order,
so each entry's application event lands in that order and each spends its fuel in that order. This
file claims the tail is walked before the head, which is what a lowering that reversed the traversal
would have. The proof offered is the direct reduction the in-order statement uses, so the model
itself must reject it.

`scripts/check-semantics-registry.mjs --self-test` requires this file to fail.
-/

namespace TSLean.LeanToTypeScript.Semantics.SemanticsFixture

theorem mapRecordsInReverse (program : Ir.Program) (fuel : Nat) (trace : Source.Trace)
    (captured : List Source.Value) (parameters : List Ir.Field) (body : Ir.Expr)
    (head : Source.Value) (rest : List Source.Value) :
    Source.mapElements program fuel trace captured parameters body (head :: rest)
      = (match Source.mapElements program fuel trace captured parameters body rest with
          | .values images last =>
              (match Source.applyClosure program fuel last captured parameters body [head] with
                | .value produced final => .values (produced :: images) final
                | .fault fault final => .fault fault final
                | .exhausted final => .exhausted final)
          | .fault fault last => .fault fault last
          | .exhausted last => .exhausted last) := by
  simp only [Source.mapElements]

end TSLean.LeanToTypeScript.Semantics.SemanticsFixture
