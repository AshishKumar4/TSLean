import Lean
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace TSLean.Audit

/-- Emit one tab-separated `JS_AUDIT` record per declaration, ordered by name. -/
private def emitRecords (records : Array (Name × Array Name)) : CommandElabM Unit := do
  for (name, axioms) in records.qsort (fun left right => Name.lt left.1 right.1) do
    let dependencies := String.intercalate "," (axioms.toList.map Name.toString)
    logInfo m!"JS_AUDIT\t{name}\t{dependencies}"

/-- Report the axiom dependencies of every environment declaration `select` accepts. -/
private def auditSelected (select : Environment → Name → ConstantInfo → CommandElabM Bool) :
    CommandElabM Unit := do
  let environment ← getEnv
  let mut records : Array (Name × Array Name) := #[]
  for (name, info) in environment.constants.toList do
    if ← select environment name info then
      records := records.push (name, (← collectAxioms name).qsort Name.lt)
  emitRecords records

/--
The module a declaration was imported from, or `none` when the current file declared it.

`#audit_constants` is therefore a query over imported modules: it reports nothing about
declarations the auditing file makes itself.
-/
private def declaringModule (environment : Environment) (name : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? name
  environment.header.moduleNames[index.toNat]?

/--
Names of declarations the compiler derives from already-elaborated source: compiled-code stages
(`._cstageN`), recursion-specialization placeholders (`._specN`), and `partial def` machinery
(`._unsafe_rec`).

They are never authored, and on this toolchain they carry codegen artifacts — `lcProof` standing in
for erased proofs, specialized-recursion lemmas declared as axioms — that say nothing about the
source the gate judges. Source-level taint stays visible: it sits on the authored declaration the
auxiliary was derived from, which the audit still selects.
-/
private def compilerDerivedName (name : Name) : Bool :=
  match name with
  | .str _ suffix => suffix.startsWith "_cstage" || suffix.startsWith "_spec_" || suffix == "_unsafe_rec"
  | _ => false

/--
Audit the public, proposition-valued declarations of a namespace.

Deliberately partial: it sees neither private declarations, nor compiler-internal ones, nor
declarations whose type is not a `Prop` — so a `sorry`-backed `Inhabited` instance is invisible
to it. `#audit_constants` is the total audit; this command exists for the theorem counts that
name a namespace rather than a module.
-/
syntax "#audit_proofs " ident : command

/--
Audit every *authored* declaration of every imported module whose name starts with the given
module prefix — private and non-`Prop` declarations included; compiler-derived auxiliaries
(`compilerDerivedName`) are excluded.

The prefix selects modules, not namespaces, so a declaration cannot escape the audit by living
in a namespace that does not match the module it was compiled into.
-/
syntax "#audit_constants " ident : command

elab_rules : command
  | `(#audit_proofs $namespaceId:ident) =>
      auditSelected fun _ name info => do
        let prefixName := namespaceId.getId
        unless prefixName.isPrefixOf name && !isPrivateName name && !name.isInternalDetail do
          return false
        unless (← findDeclarationRangesCore? name).isSome do return false
        liftTermElabM do Meta.isProp info.type
  | `(#audit_constants $moduleId:ident) =>
      auditSelected fun environment name _ => do
        if compilerDerivedName name then return false
        match declaringModule environment name with
        | none => return false
        | some module => return moduleId.getId.isPrefixOf module

end TSLean.Audit
