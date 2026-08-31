import TSLean.JS.AxiomAuditMeta
import TSLean.LeanToTypeScript.Semantics
import TSLean.LeanToTypeScript.Semantics.Tests.Registry

/-!
# Axiom audit for the Lean-to-TypeScript semantics

Reports the axiom dependencies of every authored declaration of every module under
`TSLean.LeanToTypeScript.Semantics`, private and non-`Prop` declarations included.
`scripts/check-semantics-registry.mjs` reads the records and refuses any axiom outside the three
documented kernel axioms.

The file lives outside `TSLean/` on purpose: it is a query, not a library module, so it must not be
built into the library and must not appear in the module/artifact parity the JS trust gate enforces.
-/

#audit_constants TSLean.LeanToTypeScript.Semantics
