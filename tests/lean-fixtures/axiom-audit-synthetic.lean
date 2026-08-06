import TSLean.JS.AxiomAuditMeta

namespace TSLean.AuditSynthetic

theorem omittedLemma : True := True.intro

theorem
    multilineTheorem : True := True.intro

instance : Nonempty Unit := ⟨()⟩

axiom customAxiom : True

theorem sorryTheorem : True := by sorry

end TSLean.AuditSynthetic

#audit_proofs TSLean.AuditSynthetic
