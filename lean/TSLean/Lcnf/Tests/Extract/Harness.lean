import TSLean.Lcnf.Canon

/-!
# Harness for the extractor goldens

Not a `module`: every driver of the extractor must load mono bodies at the private olean level,
and `Extract.closure` asserts it.
-/

open Lean Elab Command Compiler LCNF TSLean.Lcnf

namespace TSLean.Lcnf.Tests.Extract

/-- Round-trip every declaration through JSON, individually and as one versioned document.
Throws on the first failure. Returns the number of declarations checked. -/
def roundTripAll (roots : Array Name) (decls : Array (Decl .pure)) : CoreM Nat := do
  for d in decls do
    match Serialize.roundTrip d with
    | .ok _ => pure ()
    | .error e => throwError e
  let doc ← match Serialize.serializeDocument roots decls with
    | .ok j => pure j
    | .error e => throwError e
  match Json.parse doc.compress >>= Serialize.deserializeDocument with
  | .error e => throwError e
  | .ok (roots', decls') =>
    unless roots' == roots && decls'.size == decls.size && (decls'.zip decls).all (fun (a, b) => a == b) do
      throwError "lcnf.roundtrip.document: the document does not survive JSON ⇄ LCNF.Code"
  return decls.size

/-- Extract, canonicalize, round-trip raw and canonical declarations, and print the golden. -/
def golden (roots : Array Name) : CommandElabM Unit := liftCoreM do
  let c ← Extract.closure roots
  let r ← match Canon.canonicalize c with
    | .ok r => pure r
    | .error e => throwError e
  let raw ← roundTripAll roots c.decls
  let canon ← roundTripAll roots r.decls
  let renames : NameMap Name := r.renames.foldl (fun m (a, b) => m.insert a b) {}
  IO.println (c.render (fun n => (renames.find? n).getD n))
  IO.println s!"round-trip: {raw} raw and {canon} canonical declarations"
  for (root, d) in r.rootDigests do IO.println s!"digest {root}: {d}"

/-- Print raw auxiliary names, raw digests and canonical digests: the canonicalization plant. -/
def canonReport (roots : Array Name) : CommandElabM Unit := liftCoreM do
  let c ← Extract.closure roots
  let r ← match Canon.canonicalize c with
    | .ok r => pure r
    | .error e => throwError e
  let raw ← match Canon.rawDigests c with
    | .ok r => pure r
    | .error e => throwError e
  for (a, b) in r.renames do IO.println s!"aux {a} => {b}"
  for (root, d) in raw do IO.println s!"raw digest {root}: {d}"
  for (root, d) in r.rootDigests do IO.println s!"canonical digest {root}: {d}"

end TSLean.Lcnf.Tests.Extract
