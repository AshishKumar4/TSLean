import TSLean.JS.PrimitiveConversion
import TSLean.JS.Monad
import TSLean.JS.Oracle.Fixture
import TSLean.JS.Oracle.GraphFixture

namespace TSLean.JS.Oracle

private def stringDatum (value : JSString) : Lean.Json :=
  Lean.Json.mkObj [
    ("type", "string"),
    ("units", .arr (value.codeUnits.toArray.map fun unit => unit.toNat))
  ]

private def leanStringDatum (value : String) : Lean.Json :=
  stringDatum (JSString.ofLeanString value)

private def wellKnownName : WellKnownSymbol → String
  | .asyncDispose => "asyncDispose"
  | .asyncIterator => "asyncIterator"
  | .dispose => "dispose"
  | .hasInstance => "hasInstance"
  | .isConcatSpreadable => "isConcatSpreadable"
  | .iterator => "iterator"
  | .match => "match"
  | .matchAll => "matchAll"
  | .replace => "replace"
  | .search => "search"
  | .species => "species"
  | .split => "split"
  | .toPrimitive => "toPrimitive"
  | .toStringTag => "toStringTag"
  | .unscopables => "unscopables"

def primitiveDatum (symbols : Array String) : Primitive → Lean.Json
  | .undefined => Lean.Json.mkObj [("type", "undefined")]
  | .null => Lean.Json.mkObj [("type", "null")]
  | .boolean value => Lean.Json.mkObj [("type", "boolean"), ("value", value)]
  | .number value => Lean.Json.mkObj [("type", "number"), ("bits", value.bits.toNat.repr)]
  | .string value => stringDatum value
  | .bigint value => Lean.Json.mkObj [("type", "bigint"), ("decimal", value.repr)]
  | .symbol (.allocated id) =>
      Lean.Json.mkObj [("type", "symbol"), ("kind", "registered"),
        ("identity", (symbols[id]?).getD s!"allocated-{id}")]
  | .symbol (.wellKnown id) =>
      Lean.Json.mkObj [("type", "symbol"), ("kind", "well-known"), ("identity", wellKnownName id)]

def valueDatum (symbols : Array String) : Value → Lean.Json
  | .primitive value => primitiveDatum symbols value
  | .object ref => Lean.Json.mkObj [("type", "object"), ("identity", s!"object-{ref.value}")]

def graphPrimitiveDatum (symbols : Array (String × String)) : Primitive → Lean.Json
  | .symbol (.allocated id) =>
      let metadata := symbols[id]?.getD ("local", s!"allocated-{id}")
      Lean.Json.mkObj [("type", "symbol"),
        ("kind", if metadata.1 = "registered" then "registered" else "unique"),
        ("identity", metadata.2)]
  | .symbol (.wellKnown id) =>
      Lean.Json.mkObj [("type", "symbol"), ("kind", "well-known"), ("identity", wellKnownName id)]
  | value => primitiveDatum (symbols.map (·.2)) value

def graphValueDatum (symbols : Array (String × String)) : Value → Lean.Json
  | .primitive value => graphPrimitiveDatum symbols value
  | .object ref => Lean.Json.mkObj [("type", "object"), ("identity", s!"object-{ref.value}")]

def propertyKeyDatum (symbols : Array String) : PropertyKey → Lean.Json
  | .string value => stringDatum value
  | .symbol id => primitiveDatum symbols (.symbol id)

private def canonicalErrorDatum (identity : String) (name message : JSString) : Lean.Json :=
  Lean.Json.mkObj [("type", "error"), ("identity", identity),
    ("name", stringDatum name), ("message", stringDatum message)]

private def canonicalError (identity name message : String) : Lean.Json :=
  canonicalErrorDatum identity (JSString.ofLeanString name) (JSString.ofLeanString message)

private def dropUnitsPrefix? : List UInt16 → List UInt16 → Option (List UInt16)
  | [], value => some value
  | _, [] => none
  | expected :: expectedRest, actual :: actualRest =>
      if expected = actual then dropUnitsPrefix? expectedRest actualRest else none

private def fixtureError? (value : JSString) : Option (JSString × JSString) := do
  let marker := (JSString.ofLeanString "OracleFixtureError:").codeUnits
  let rest ← dropUnitsPrefix? marker value.codeUnits
  let (name, suffix) := rest.span (· != UInt16.ofNat 0x3a)
  match suffix with
  | [] => none
  | _ :: message => some (⟨name⟩, ⟨message⟩)

def errorDatum : CoercionFault → Lean.Json
  | .bigintDivisionByZero => canonicalError "ref-0" "RangeError" ""
  | .bigintToNumber | .symbolToNumber | .symbolToString | .mixedNumericTypes =>
      canonicalError "ref-0" "TypeError" ""

def thrownValueDatum (symbols : Array (String × String)) : Value → Lean.Json
  | .primitive (.string value) =>
      let rendered := value.toLeanString?.getD ""
      let name := if rendered.startsWith "TypeError:" then some "TypeError"
        else if rendered.startsWith "RangeError:" then some "RangeError"
        else if rendered.startsWith "ReferenceError:" then some "ReferenceError"
        else if rendered.startsWith "SyntaxError:" then some "SyntaxError"
        else none
      match name with
      | some name => canonicalError "ref-0" name ""
      | none => stringDatum value
  | .primitive value =>
      let names := symbols.map (·.2)
      primitiveDatum names value
  | .object ref => Lean.Json.mkObj [("type", "object"), ("identity", s!"object-{ref.value}")]

def traceJson (machine : Machine P) : Lean.Json :=
  .arr (machine.trace.filterMap (fun
    | .emitted value => some (Lean.Json.mkObj [("event", "emit"), ("detail", stringDatum value)])
    | _ => none) |>.toArray)

def machineObservation (symbols : Array (String × String)) (encode : α → Lean.Json)
    (result : RunResult P α) : Except String Lean.Json :=
  match result with
  | .done (.normal value) machine => pure (Lean.Json.mkObj [
      ("completion", Lean.Json.mkObj [("type", "normal"), ("value", encode value)]),
      ("trace", traceJson machine)])
  | .done (.thrown value) machine => pure (Lean.Json.mkObj [
      ("completion", Lean.Json.mkObj [("type", "throw"), ("value", thrownValueDatum symbols value)]),
      ("trace", traceJson machine)])
  | .done _ _ => throw "control completion escaped operation"
  | .fault _ _ => throw "model fault"
  | .exhausted _ => throw "model exhausted"

private structure GraphEncodeState where
  refs : Array (RefId × Nat) := #[]
  objects : Array Lean.Json := #[]
  nextIdentity : Nat := 0

private def refDatum (index : Nat) : Lean.Json :=
  Lean.Json.mkObj [("type", "object"), ("identity", s!"ref-{index}")]

private def encounterRef (ref : RefId) (state : GraphEncodeState) : Lean.Json × GraphEncodeState :=
  match state.refs.findSome? fun entry => if entry.1 = ref then some entry.2 else none with
  | some identity => (refDatum identity, state)
  | none =>
      let identity := state.nextIdentity
      (refDatum identity, { state with
        refs := state.refs.push (ref, identity)
        nextIdentity := identity + 1 })

private def encounterValue (symbols : Array (String × String)) (value : Value)
    (state : GraphEncodeState) : Lean.Json × GraphEncodeState :=
  match value with
  | .primitive value => (graphPrimitiveDatum symbols value, state)
  | .object ref => encounterRef ref state

private def encounterKey (symbols : Array (String × String)) (key : PropertyKey) : Lean.Json :=
  match key with
  | .string value => stringDatum value
  | .symbol value => graphPrimitiveDatum symbols (.symbol value)

private def selectionKeys (heap : Heap) (selections : List GraphSelection) (ref : RefId) : List PropertyKey :=
  match selections.findSome? (fun selection => if selection.ref = ref then some selection.keys else none) with
  | some keys => keys
  | none => match heap.ownPropertyKeys ref with
      | .ok keys => keys
      | .error _ => []

private def objectKindName : ObjectKind → String
  | .function _ => "function"
  | .array _ => "array"
  | .ordinary | .arrayIterator _ | .primitiveWrapper _ => "object"

private def selectionKind (selections : List GraphSelection) (ref : RefId) (fallback : ObjectKind) : String :=
  selections.findSome? (fun selection => if selection.ref = ref then some selection.kind else none)
    |>.getD (objectKindName fallback)

private def ownStringValue (heap : Heap) (ref : RefId) (name : String) : String :=
  match heap.getOwnProperty ref (.string (JSString.ofLeanString name)) with
  | .ok (some (.data { value := .primitive (.string value), .. })) => value.toLeanString?.getD ""
  | _ => ""

private def encounterGraphValue (heap : Heap) (symbols : Array (String × String))
    (selections : List GraphSelection) (value : Value) (state : GraphEncodeState) :
    Lean.Json × GraphEncodeState :=
  match value with
  | .primitive value => (graphPrimitiveDatum symbols value, state)
  | .object ref =>
      let (datum, state) := encounterRef ref state
      let kind := selections.findSome? fun selection =>
        if selection.ref = ref then some selection.kind else none
      if kind = some "error" then
        let identity := state.refs.findSome? (fun entry => if entry.1 = ref then some entry.2 else none) |>.getD 0
        let name := ownStringValue heap ref "name"
        let message := ownStringValue heap ref "message"
        (canonicalError s!"ref-{identity}" (if name.isEmpty then "Error" else name) message, state)
      else (datum, state)

private def encodeDescriptor (heap : Heap) (symbols : Array (String × String))
    (selections : List GraphSelection) (descriptor : PropertyDescriptor)
    (state : GraphEncodeState) : Lean.Json × GraphEncodeState :=
  match descriptor with
  | .data descriptor =>
      let (value, state) := encounterGraphValue heap symbols selections descriptor.value state
      (Lean.Json.mkObj [("kind", "data"), ("value", value), ("writable", descriptor.writable),
        ("enumerable", descriptor.enumerable), ("configurable", descriptor.configurable)], state)
  | .accessor descriptor =>
      let (getter, state) := match descriptor.get with
        | some ref => encounterRef ref state
        | none => (Lean.Json.mkObj [("type", "undefined")], state)
      let (setter, state) := match descriptor.set with
        | some ref => encounterRef ref state
        | none => (Lean.Json.mkObj [("type", "undefined")], state)
      (Lean.Json.mkObj [("kind", "accessor"), ("get", getter), ("set", setter),
        ("enumerable", descriptor.enumerable), ("configurable", descriptor.configurable)], state)

private def encodeProperties (heap : Heap) (symbols : Array (String × String)) (ref : RefId)
    (selections : List GraphSelection) (keys : List PropertyKey) (state : GraphEncodeState) :
    Array Lean.Json × GraphEncodeState :=
  keys.foldl (fun (properties, state) key =>
    match heap.getOwnProperty ref key with
    | .ok (some descriptor) =>
        let (descriptor, state) := encodeDescriptor heap symbols selections descriptor state
        (properties.push (Lean.Json.mkObj [("key", encounterKey symbols key), ("descriptor", descriptor)]), state)
    | _ => (properties, state)) (#[], state)

private partial def encodeObjects (heap : Heap) (symbols : Array (String × String))
    (selections : List GraphSelection) (cursor : Nat) (state : GraphEncodeState) : GraphEncodeState :=
  if cursor ≥ state.refs.size then state
  else
    match state.refs[cursor]? with
    | none => state
    | some (ref, identity) =>
        match heap.get? ref with
        | .error _ => encodeObjects heap symbols selections (cursor + 1) state
        | .ok object =>
            let (prototype, state) := match object.prototype with
              | some prototype => encounterRef prototype state
              | none => (Lean.Json.mkObj [("type", "null")], state)
            let (properties, state) := encodeProperties heap symbols ref selections (selectionKeys heap selections ref) state
            let record := Lean.Json.mkObj [("identity", s!"ref-{identity}"),
              ("kind", selectionKind selections ref object.kind), ("prototype", prototype),
              ("extensible", object.extensible), ("properties", .arr properties)]
            encodeObjects heap symbols selections (cursor + 1) { state with objects := state.objects.push record }

private def encounterEncoded (graph : MaterializedGraph) (machine : Machine oraclePlatform)
    (value : Lean.Json) (state : GraphEncodeState) : Lean.Json × GraphEncodeState :=
  match value.getObjVal? "type", value.getObjVal? "identity" with
  | .ok (.str "object"), .ok (.str identity) =>
      if identity.startsWith "object-" then
        match (identity.drop 7).toNat? with
        | some ref => encounterGraphValue machine.heap graph.symbols graph.selections (.object ⟨ref⟩) state
        | none => (value, state)
      else (value, state)
  | _, _ => (value, state)

private def encounterThrown (graph : MaterializedGraph) (machine : Machine oraclePlatform)
    (value : Value) (state : GraphEncodeState) : Lean.Json × GraphEncodeState :=
  match value with
  | .primitive (.string text) =>
      match fixtureError? text with
      | some (name, message) =>
        let identity := state.nextIdentity
        (canonicalErrorDatum s!"ref-{identity}" name message, { state with nextIdentity := identity + 1 })
      | none =>
        let rendered := text.toLeanString?.getD ""
        let name := if rendered.startsWith "TypeError:" then some "TypeError"
          else if rendered.startsWith "RangeError:" then some "RangeError"
          else if rendered.startsWith "ReferenceError:" then some "ReferenceError"
          else if rendered.startsWith "SyntaxError:" then some "SyntaxError"
          else none
        match name with
        | some name =>
            let identity := state.nextIdentity
            (canonicalError s!"ref-{identity}" name "", { state with nextIdentity := identity + 1 })
        | none => (stringDatum text, state)
  | value => encounterGraphValue machine.heap graph.symbols graph.selections value state

def graphMachineObservation (graph : MaterializedGraph) (encode : α → Lean.Json)
    (result : RunResult oraclePlatform α) : Except String Lean.Json := do
  let machine := match result with
    | .done _ machine | .fault _ machine | .exhausted machine => machine
  let (completionType, completionValue, state) ← match result with
    | .done (.normal value) _ =>
        let (value, state) := encounterEncoded graph machine (encode value) {}
        pure ("normal", value, state)
    | .done (.thrown value) _ =>
        let (value, state) := encounterThrown graph machine value {}
        pure ("throw", value, state)
    | .done _ _ => throw "control completion escaped operation"
    | .fault _ _ => throw "model fault"
    | .exhausted _ => throw "model exhausted"
  let (trace, state) := machine.trace.foldl (fun (trace, state) event =>
    match event with
    | .emitted value =>
        let (detail, state) := encounterGraphValue machine.heap graph.symbols graph.selections
          (.primitive (.string value)) state
        (trace.push (Lean.Json.mkObj [("event", "emit"), ("detail", detail)]), state)
    | _ => (trace, state)) (#[], state)
  let (roots, state) := graph.observe.foldl (fun (roots, state) value =>
    let (value, state) := encounterGraphValue machine.heap graph.symbols graph.selections value state
    (roots.push value, state)) (#[], state)
  let state := encodeObjects machine.heap graph.symbols graph.selections 0 state
  let observation := Lean.Json.mkObj [
    ("completion", Lean.Json.mkObj [("type", completionType), ("value", completionValue)]),
    ("trace", .arr trace)]
  let observation := if roots.isEmpty then observation else observation.setObjVal! "roots" (.arr roots)
  pure (if state.objects.isEmpty then observation else observation.setObjVal! "objects" (.arr state.objects))

def normalObservation (value : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [
    ("completion", Lean.Json.mkObj [("type", "normal"), ("value", value)]),
    ("trace", .arr #[])
  ]

def throwObservation (fault : CoercionFault) : Lean.Json :=
  Lean.Json.mkObj [
    ("completion", Lean.Json.mkObj [("type", "throw"), ("value", errorDatum fault)]),
    ("trace", .arr #[])
  ]

def exceptObservation (encode : α → Lean.Json) : Except CoercionFault α → Lean.Json
  | .ok value => normalObservation (encode value)
  | .error fault => throwObservation fault

end TSLean.JS.Oracle
