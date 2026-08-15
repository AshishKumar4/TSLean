namespace TSLean.Examples.Placement

inductive Placement where
  | bundled
  | provider
  | dynamic
  deriving DecidableEq, Repr

structure PlacementSet where
  bundled : Bool
  provider : Bool
  dynamic : Bool
  deriving DecidableEq, Repr

def PlacementSet.intersect (left right : PlacementSet) : PlacementSet :=
  {
    bundled := left.bundled && right.bundled
    provider := left.provider && right.provider
    dynamic := left.dynamic && right.dynamic
  }

def choosePlacement (manifest policy substrate trust : PlacementSet) : Option Placement :=
  let available := ((manifest.intersect policy).intersect substrate).intersect trust
  if available.dynamic then some .dynamic
  else if available.provider then some .provider
  else if available.bundled then some .bundled
  else none

end TSLean.Examples.Placement
