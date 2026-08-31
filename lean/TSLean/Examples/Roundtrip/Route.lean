namespace TSLean.Examples.Roundtrip.Route

/-- Where a request is sent. -/
inductive Route where
  | cache
  | origin
  | reject
  deriving DecidableEq, Repr

/-- What the router knows about a request. -/
structure Request where
  cacheable : Bool
  fresh : Bool
  allowed : Bool
  deriving DecidableEq, Repr

/-- Where the request goes. A refused request is never served. -/
def routeOf (request : Request) : Route :=
  if !request.allowed then .reject
  else if request.cacheable && request.fresh then .cache
  else .origin

end TSLean.Examples.Roundtrip.Route
