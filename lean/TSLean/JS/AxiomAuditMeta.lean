import Lean
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace TSLean.Audit

syntax "#audit_proofs " ident : command

elab_rules : command
  | `(#audit_proofs $namespaceId:ident) => do
      let environment ← getEnv
      let prefixName := namespaceId.getId
      let mut records : Array (Name × Array Name) := #[]
      for (name, info) in environment.constants.toList do
        if prefixName.isPrefixOf name && !isPrivateName name && !name.isInternalDetail &&
            (← findDeclarationRangesCore? name).isSome then
          let isProposition ← liftTermElabM do Meta.isProp info.type
          if isProposition then
            let axioms ← collectAxioms name
            records := records.push (name, axioms.qsort Name.lt)
      for (name, axioms) in records.qsort (fun left right => Name.lt left.1 right.1) do
        let dependencies := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"JS_AUDIT\t{name}\t{dependencies}"

end TSLean.Audit
