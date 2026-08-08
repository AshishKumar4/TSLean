import TSLean.JS.AbstractOperations

namespace TSLean.JS.CoercionEffectsBenchmark

private def platform : Platform := ScriptedPlatform.make {
  times := #[], randoms := #[], fetches := #[]
}

private def hook : BodyHook platform := fun _ _ _ => pure ()

private def timePublic (iterations : Nat) (machine : Machine platform) : IO Nat := do
  let start ← IO.monoMsNow
  for _ in [0:iterations] do
    match AbstractOperations.toNumber hook (.primitive (.boolean true)) machine with
    | .done (.normal value) _ =>
        if value != JSNumber.one then throw (IO.userError "unexpected public result")
    | _ => throw (IO.userError "unexpected public completion")
  pure ((← IO.monoMsNow) - start)

private def timeGeneric (iterations : Nat) (machine : Machine platform) : IO Nat := do
  let start ← IO.monoMsNow
  for _ in [0:iterations] do
    match AbstractOperations.toNumberWith (CoercionEffects.forJSM hook)
        (.primitive (.boolean true)) machine with
    | .done (.normal value) _ =>
        if value != JSNumber.one then throw (IO.userError "unexpected generic result")
    | _ => throw (IO.userError "unexpected generic completion")
  pure ((← IO.monoMsNow) - start)

def run : IO Unit := do
  let machine := Machine.initial platform 1
  let public100k ← timePublic 100000 machine
  let public1m ← timePublic 1000000 machine
  let generic100k ← timeGeneric 100000 machine
  let generic1m ← timeGeneric 1000000 machine
  IO.println (s!"coercion-specialization public100kMs={public100k} public1mMs={public1m} " ++
    s!"generic100kMs={generic100k} generic1mMs={generic1m}")

end TSLean.JS.CoercionEffectsBenchmark

def main : IO Unit := TSLean.JS.CoercionEffectsBenchmark.run
