-- TSLean.Verification.Tactics
namespace TSLean.Verification.Tactics

/-- A tactic stub: prove goals using omega, simp, decide as appropriate -/
macro "ts_prove" : tactic => `(tactic| first | omega | simp_all | decide | trivial | rfl | contradiction)

/-- Auto-prove Nat arithmetic goals -/
macro "nat_arith" : tactic => `(tactic| omega)

/-- Auto-prove list membership goals -/
macro "list_mem" : tactic => `(tactic| simp [List.mem_cons, List.mem_append, List.mem_filter])

end TSLean.Verification.Tactics
