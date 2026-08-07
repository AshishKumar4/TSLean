import TSLean.JS.RealmTestSupportTests
import TSLean.JS.Environment
import TSLean.JS.Oracle.Protocol

namespace TSLean.JS.Oracle

def oraclePlatform : Platform := ScriptedPlatform.make { times := #[], randoms := #[], fetches := #[] }

private def maxGraphNodes : Nat := 1024
private def maxNodeProperties : Nat := 4096
private def maxNodeElements : Nat := 65536
private def maxBindings : Nat := 1024
private def maxScriptEvents : Nat := 1024
private def maxScriptCases : Nat := 1024
private def maxGraphRoots : Nat := 1024
private def maxFixtureArrayIndex : Nat := 65535
private def maxDenseArrayCells : Nat := 65536

inductive ScriptFormat where
  | string
  | number
  | boolean
  | bigint
  | null
  | undefined

inductive ScriptEvent where
  | fixed (value : JSString)
  | argument (text : JSString) (index : Nat) (format : ScriptFormat)

structure ScriptCompletion where
  throws : Bool
  value : Value

structure ScriptCase where
  receiver : RefId
  events : List ScriptEvent
  completion : ScriptCompletion

structure FunctionScript where
  events : List ScriptEvent
  completion : ScriptCompletion
  cases : List ScriptCase

structure ScriptEntry where
  ref : RefId
  script : FunctionScript

structure GraphSelection where
  ref : RefId
  kind : String
  keys : List PropertyKey

structure FixtureIntrinsics where
  objectPrototype : RefId
  functionPrototype : RefId
  arrayPrototype : RefId

structure MaterializedGraph where
  machine : Machine oraclePlatform
  arguments : Array Value
  observe : Array Value
  symbols : Array (String × String)
  scripts : List ScriptEntry
  selections : List GraphSelection
  fixtureIntrinsics : FixtureIntrinsics
  realm : Option (RealmTestSupport.Fixture oraclePlatform)

private structure NodeSpec where
  id : String
  kind : String
  prototype : String
  properties : Array Lean.Json
  elements : Array Lean.Json
  script : Lean.Json
  scriptArity : Nat

private def lookupRef (refs : List (String × RefId)) (id : String) : Except String RefId :=
  match refs.findSome? fun entry => if entry.1 = id then some entry.2 else none with
  | some ref => .ok ref
  | none => .error s!"unknown graph ref: {id}"

private def parseWellKnown? : String → Option WellKnownSymbol
  | "asyncDispose" => some .asyncDispose
  | "asyncIterator" => some .asyncIterator
  | "dispose" => some .dispose
  | "hasInstance" => some .hasInstance
  | "isConcatSpreadable" => some .isConcatSpreadable
  | "iterator" => some .iterator
  | "match" => some .match
  | "matchAll" => some .matchAll
  | "replace" => some .replace
  | "search" => some .search
  | "species" => some .species
  | "split" => some .split
  | "toPrimitive" => some .toPrimitive
  | "toStringTag" => some .toStringTag
  | "unscopables" => some .unscopables
  | _ => none

private def symbolId (symbols : Array (String × String)) (kind identity : String) :
    Except String (SymbolId × Array (String × String)) :=
  if kind = "well-known" then
    match parseWellKnown? identity with
    | some symbol => .ok (.wellKnown symbol, symbols)
    | none => .error s!"unknown well-known symbol: {identity}"
  else if kind = "local" || kind = "registered" then do
    if identity.isEmpty then throw "symbol identity must be nonempty"
    if kind = "registered" && !identity.startsWith "tslean-differential:" then
      throw "registered symbol key is not namespaced"
    match symbols.findIdx? (fun entry => entry.1 = kind && entry.2 = identity) with
    | some index => .ok (.allocated index, symbols)
    | none => .ok (.allocated symbols.size, symbols.push (kind, identity))
  else .error s!"unknown symbol kind: {kind}"

private def parseUnitsJson (value : Lean.Json) : Except String JSString := do
  let units ← value.getArr?
  if units.size > 65536 then throw "string exceeds UTF-16 limit"
  let parsed ← units.mapM fun unit => do
    let number ← unit.getNat?
    if number < 65536 then pure (UInt16.ofNat number) else throw "string code unit exceeds UInt16"
  pure ⟨parsed.toList⟩

private def parseUnits (value : Lean.Json) : Except String JSString :=
  value.getObjVal? "units" >>= parseUnitsJson

private def parseInt? (value : String) : Option Int :=
  match value.toList with
  | '-' :: rest => (String.ofList rest).toNat?.map fun magnitude => -(Int.ofNat magnitude)
  | _ => value.toNat?.map Int.ofNat

private def validErrorName (value : JSString) : Bool :=
  ["Error", "TypeError", "RangeError", "ReferenceError", "SyntaxError"].any
    (value = JSString.ofLeanString ·)

private def parseValue (value : Lean.Json) (refs : List (String × RefId))
    (symbols : Array (String × String)) : Except String (Value × Array (String × String)) := do
  let kind ← stringField value "kind"
  match kind with
  | "undefined" => exactObject value 1; pure (.primitive .undefined, symbols)
  | "null" => exactObject value 1; pure (.primitive .null, symbols)
  | "boolean" => exactObject value 2; pure (.primitive (.boolean (← (← value.getObjVal? "value").getBool?)), symbols)
  | "number" =>
      exactObject value 2
      let bitsText ← stringField value "bits"
      let bits ← match bitsText.toNat? with
        | some bits => pure bits
        | none => throw "invalid binary64 bits"
      if bits.repr != bitsText || bits ≥ 18446744073709551616 then throw "invalid binary64 bits"
      pure (.primitive (.number ⟨UInt64.ofNat bits⟩), symbols)
  | "string" => exactObject value 2; pure (.primitive (.string (← parseUnits value)), symbols)
  | "bigint" =>
      exactObject value 2
      let decimal ← stringField value "decimal"
      let integer ← match parseInt? decimal with
        | some integer => pure integer
        | none => throw "invalid BigInt decimal"
      if integer.repr != decimal then throw "invalid BigInt decimal"
      pure (.primitive (.bigint integer), symbols)
  | "symbol" =>
      exactObject value 3
      let (id, symbols) ← symbolId symbols (← stringField value "symbolKind") (← stringField value "identity")
      pure (.primitive (.symbol id), symbols)
  | "error" =>
      exactObject value 3
      let name ← parseUnitsJson (← value.getObjVal? "name")
      let message ← parseUnitsJson (← value.getObjVal? "message")
      if !validErrorName name then throw "unsupported error name"
      let marker := JSString.ofLeanString "OracleFixtureError:"
      pure (.primitive (.string (marker.append name |>.append (JSString.ofLeanString ":") |>.append message)), symbols)
  | "ref" => exactObject value 2; pure (.object (← lookupRef refs (← stringField value "id")), symbols)
  | _ => throw s!"unknown graph value kind: {kind}"

private def parseKey (value : Lean.Json) (symbols : Array (String × String)) :
    Except String (PropertyKey × Array (String × String)) := do
  let kind ← stringField value "kind"
  if kind = "string" then exactObject value 2; pure (.string (← parseUnits value), symbols)
  else if kind = "symbol" then
    exactObject value 3
    let (id, symbols) ← symbolId symbols (← stringField value "symbolKind") (← stringField value "identity")
    pure (.symbol id, symbols)
  else throw s!"unknown property key kind: {kind}"

private def parseNode (value : Lean.Json) : Except String NodeSpec := do
  exactObject value 7
  pure {
    id := ← stringField value "id"
    kind := ← stringField value "kind"
    prototype := ← stringField value "prototype"
    properties := ← arrayField value "properties"
    elements := ← arrayField value "elements"
    script := ← value.getObjVal? "script"
    scriptArity := ← (← value.getObjVal? "scriptArity").getNat?
  }

private def maxElementLength (elements : Array Lean.Json) : Except String Nat := do
  let indices ← elements.mapM fun element => do
    exactObject element 2
    let index ← (← element.getObjVal? "index").getNat?
    if index ≤ maxFixtureArrayIndex then pure index else throw "array index exceeds fixture maximum"
  if indices.toList.Nodup then pure () else throw "duplicate array index"
  pure (indices.foldl (fun length index => max length (index + 1)) 0)

private def allocateNode (machine : Machine oraclePlatform) (node : NodeSpec) :
    Except String (RefId × Machine oraclePlatform) :=
  match node.kind with
  | "object" | "error" => machine.heap.allocate |>.map (fun (ref, heap) => (ref, machine.setHeap heap))
      |>.mapError (fun _ => "object allocation failed")
  | "function" => machine.heap.allocateFunction machine.globalEnv .ordinary false none
      |>.map (fun (ref, heap) => (ref, machine.setHeap heap))
      |>.mapError (fun _ => "function allocation failed")
  | "array" => do
      let length ← maxElementLength node.elements
      machine.heap.allocateArray (List.replicate length none)
        |>.map (fun (ref, heap) => (ref, machine.setHeap heap))
        |>.mapError (fun _ => "array allocation failed")
  | _ => .error s!"unknown graph node kind: {node.kind}"

private def specialPrototype (intrinsics : FixtureIntrinsics)
    (refs : List (String × RefId)) (name : String) : Except String (Option RefId) := do
  if name = "@null" || name = "" then pure none
  else if name = "@object" then pure (some intrinsics.objectPrototype)
  else if name = "@function" then pure (some intrinsics.functionPrototype)
  else if name = "@array" then pure (some intrinsics.arrayPrototype)
  else pure (some (← lookupRef refs name))

private def buildFixtureIntrinsics (machine : Machine oraclePlatform)
    (realm : Option (RealmTestSupport.Fixture oraclePlatform)) :
    Except String (FixtureIntrinsics × Machine oraclePlatform) := do
  let (objectPrototype, machine) ← match realm with
    | some fixture => pure (fixture.intrinsics.objectPrototype, machine)
    | none => machine.heap.allocate
        |>.map (fun (ref, heap) => (ref, machine.setHeap heap))
        |>.mapError (fun _ => "object intrinsic allocation failed")
  let (functionPrototype, heap) ← machine.heap.allocateFunction machine.globalEnv .ordinary false
      (some objectPrototype) |>.mapError (fun _ => "function intrinsic allocation failed")
  let machine := machine.setHeap heap
  let (arrayPrototype, heap) ← machine.heap.allocateArray [] (some objectPrototype)
      |>.mapError (fun _ => "array intrinsic allocation failed")
  pure (⟨objectPrototype, functionPrototype, arrayPrototype⟩, machine.setHeap heap)

private def defineProperty (heap : Heap) (target : RefId) (key : PropertyKey)
    (descriptor : Lean.Json) (refs : List (String × RefId))
    (symbols : Array (String × String)) : Except String (Heap × Array (String × String)) := do
  let kind ← stringField descriptor "kind"
  let isEnumerable ← (← descriptor.getObjVal? "enumerable").getBool?
  let isConfigurable ← (← descriptor.getObjVal? "configurable").getBool?
  let (update, symbols) ← if kind = "data" then
    exactObject descriptor 5
    let (value, symbols) ← parseValue (← descriptor.getObjVal? "value") refs symbols
    let isWritable ← (← descriptor.getObjVal? "writable").getBool?
    let update : DescriptorUpdate := {
      value := .present value
      writable := .present isWritable
      enumerable := .present isEnumerable
      configurable := .present isConfigurable }
    pure (update, symbols)
  else if kind = "accessor" then
    exactObject descriptor 5
    let getter := ← stringField descriptor "get"
    let setter := ← stringField descriptor "set"
    let getterRef ← if getter.isEmpty then pure none else pure (some (← lookupRef refs getter))
    let setterRef ← if setter.isEmpty then pure none else pure (some (← lookupRef refs setter))
    let update : DescriptorUpdate := {
      get := .present getterRef
      set := .present setterRef
      enumerable := .present isEnumerable
      configurable := .present isConfigurable }
    pure (update, symbols)
  else throw s!"unknown descriptor kind: {kind}"
  match heap.defineOwnProperty target key update with
  | .ok (true, heap) => pure (heap, symbols)
  | .ok (false, _) => throw "property definition rejected"
  | .error _ => throw "property definition failed"

private def parseEvent (arity : Nat) (value : Lean.Json) : Except String ScriptEvent := do
  let kind ← stringField value "kind"
  if kind = "fixed" then exactObject value 2; pure (.fixed (← parseUnits value))
  else if kind = "argument" then
    exactObject value 4
    let index ← (← value.getObjVal? "argument").getNat?
    let format ← match ← stringField value "format" with
      | "string" => pure .string
      | "number" => pure .number
      | "boolean" => pure .boolean
      | "bigint" => pure .bigint
      | "null" => pure .null
      | "undefined" => pure .undefined
      | _ => throw "unsupported script argument format"
    if index < arity then pure (.argument (← parseUnitsJson (← value.getObjVal? "prefixUnits")) index format)
    else throw "script argument is out of bounds"
  else throw s!"unknown script event: {kind}"

private def parseCompletion (value : Lean.Json) (refs : List (String × RefId))
    (symbols : Array (String × String)) : Except String (ScriptCompletion × Array (String × String)) := do
  exactObject value 2
  let kind ← stringField value "type"
  let (result, symbols) ← parseValue (← value.getObjVal? "value") refs symbols
  if kind = "return" then pure (⟨false, result⟩, symbols)
  else if kind = "throw" then pure (⟨true, result⟩, symbols)
  else throw s!"unknown script completion: {kind}"

private def parseScriptParts (arity : Nat) (value : Lean.Json) (refs : List (String × RefId))
    (symbols : Array (String × String)) : Except String (List ScriptEvent × ScriptCompletion × Array (String × String)) := do
  let events ← (← arrayField value "events").toList.mapM (parseEvent arity)
  let (completion, symbols) ← parseCompletion (← value.getObjVal? "completion") refs symbols
  pure (events, completion, symbols)

private def parseScript (arity : Nat) (value : Lean.Json) (refs : List (String × RefId))
    (symbols : Array (String × String)) : Except String (FunctionScript × Array (String × String)) := do
  exactObject value 3
  let eventsJson ← arrayField value "events"
  let casesJson ← arrayField value "cases"
  if eventsJson.size > maxScriptEvents || casesJson.size > maxScriptCases then throw "script exceeds fixture bounds"
  let (events, completion, symbols) ← parseScriptParts arity value refs symbols
  let (cases, symbols) ← casesJson.foldlM (init := ([], symbols)) fun (cases, symbols) item => do
    exactObject item 3
    let (events, completion, symbols) ← parseScriptParts arity item refs symbols
    let receiver ← lookupRef refs (← stringField item "receiver")
    pure (cases ++ [⟨receiver, events, completion⟩], symbols)
  pure (⟨events, completion, cases⟩, symbols)

private def formatScriptArgument (format : ScriptFormat) (value : Value) : Option JSString :=
  match format, value with
  | .string, .primitive (.string value) => some value
  | .number, .primitive (.number value) => some value.format
  | .boolean, .primitive (.boolean value) => some (JSString.ofLeanString (toString value))
  | .bigint, .primitive (.bigint value) => some (JSString.ofLeanString value.repr)
  | .null, .primitive .null => some (JSString.ofLeanString "null")
  | .undefined, .primitive .undefined => some (JSString.ofLeanString "undefined")
  | _, _ => none

private def emitEvents (events : List ScriptEvent) (arguments : Array Value)
    (machine : Machine oraclePlatform) : Machine oraclePlatform :=
  events.foldl (fun machine event =>
    let text := match event with
      | .fixed value => value
      | .argument text index format => text.append <| arguments[index]?.bind (formatScriptArgument format) |>.getD
          (JSString.ofLeanString "<invalid-script-argument>")
    machine.emit (.emitted text)) machine

private def runScript (script : FunctionScript) (receiver : Value) (arguments : Array Value) :
    JSM oraclePlatform Unit := fun machine =>
  let selected := match receiver with
    | .object ref => script.cases.findSome? fun (candidate : ScriptCase) =>
        if candidate.receiver = ref then some candidate else none
    | _ => none
  let events := selected.map (·.events) |>.getD script.events
  let completion := selected.map (·.completion) |>.getD script.completion
  let machine := emitEvents events arguments machine
  if completion.throws then JSM.throwJS completion.value machine else JSM.returnJS completion.value machine

def MaterializedGraph.bodyHook (graph : MaterializedGraph) : BodyHook oraclePlatform := fun ref receiver arguments =>
  match graph.scripts.findSome? fun entry => if entry.ref = ref then some entry.script else none with
  | some script => runScript script receiver arguments
  | none => graph.realm.map (·.bodyHook ref receiver arguments) |>.getD (pure ())

def materializeGraph (value : Lean.Json) : Except String MaterializedGraph := do
  exactObject value 7
  if (← stringField value "kind") != "graph" then throw "expected graph fixture"
  let nodes ← (← arrayField value "nodes").mapM parseNode
  if nodes.size > maxGraphNodes then throw "graph exceeds node bound"
  if nodes.toList.map (·.id) |>.Nodup then pure () else throw "graph node IDs must be unique"
  let _ ← nodes.foldlM (init := 0) fun total node => do
    if node.properties.size > maxNodeProperties || node.elements.size > maxNodeElements then
      throw s!"node exceeds fixture bounds: {node.id}"
    let cells ← maxElementLength node.elements
    if node.kind = "array" then
      if cells > maxDenseArrayCells - total then throw "graph exceeds dense-array materialization budget"
      pure (total + cells)
    else pure total
  for node in nodes do
    let propertyKeys ← node.properties.mapM fun property => do
      exactObject property 2
      pure (← property.getObjVal? "key").compress
    if !propertyKeys.toList.Nodup then throw s!"duplicate property key on {node.id}"
  let wantsRealm ← (← value.getObjVal? "realm").getBool?
  let initial := Machine.initial oraclePlatform 10000
  let (machine, realm) ← if wantsRealm then
    match RealmTestSupport.bootstrap initial with
    | .ok fixture => pure (fixture.machine, some fixture)
    | .error _ => throw "realm bootstrap failed"
  else pure (initial, none)
  let (fixtureIntrinsics, machine) ← buildFixtureIntrinsics machine realm
  let (refs, machine) ← nodes.foldlM (init := ([], machine)) fun (refs, machine) node => do
    let (ref, machine) ← allocateNode machine node
    pure (refs ++ [(node.id, ref)], machine)
  let machine ← nodes.foldlM (init := machine) fun machine node => do
    let ref ← lookupRef refs node.id
    let prototype ← specialPrototype fixtureIntrinsics refs node.prototype
    match machine.heap.setPrototypeOf ref prototype with
    | .ok (true, heap) => pure (machine.setHeap heap)
    | _ => throw "prototype installation failed"
  let intrinsicSelections : List GraphSelection := [
    ⟨fixtureIntrinsics.objectPrototype, "object", []⟩,
    ⟨fixtureIntrinsics.functionPrototype, "function", []⟩,
    ⟨fixtureIntrinsics.arrayPrototype, "array", []⟩] ++ match realm with
      | none => []
      | some fixture => [
          ⟨fixture.intrinsics.booleanPrototype, "object", []⟩,
          ⟨fixture.intrinsics.numberPrototype, "object", []⟩,
          ⟨fixture.intrinsics.stringPrototype, "object", []⟩,
          ⟨fixture.intrinsics.bigintPrototype, "object", []⟩,
          ⟨fixture.intrinsics.symbolPrototype, "object", []⟩]
  let (machine, symbols, selections) ← nodes.foldlM (init := (machine, #[], intrinsicSelections))
      fun (machine, symbols, selections) node => do
    let ref ← lookupRef refs node.id
    let (heap, symbols, keys) ← node.elements.foldlM (init := (machine.heap, symbols, []))
      fun (heap, symbols, keys) element => do
        let index ← (← element.getObjVal? "index").getNat?
        let key : PropertyKey := .string (PropertyKey.arrayIndexString index)
        let descriptor := Lean.Json.mkObj [("kind", "data"), ("value", ← element.getObjVal? "value"),
          ("writable", true), ("enumerable", true), ("configurable", true)]
        let (heap, symbols) ← defineProperty heap ref key descriptor refs symbols
        pure (heap, symbols, keys ++ [key])
    let (heap, symbols, keys) ← node.properties.foldlM (init := (heap, symbols, keys))
      fun (heap, symbols, keys) property => do
        let (key, symbols) ← parseKey (← property.getObjVal? "key") symbols
        let (heap, symbols) ← defineProperty heap ref key (← property.getObjVal? "descriptor") refs symbols
        pure (heap, symbols, keys ++ [key])
    let keys := match heap.ownPropertyKeys ref with
      | .ok keys => keys
      | .error _ => keys
    pure (machine.setHeap heap, symbols, selections ++ [⟨ref, node.kind, keys⟩])
  let (scripts, symbols) ← nodes.foldlM (init := ([], symbols)) fun (scripts, symbols) node => do
    if node.kind != "function" then pure (scripts, symbols)
    else
      let (script, symbols) ← parseScript node.scriptArity node.script refs symbols
      pure (scripts ++ [⟨← lookupRef refs node.id, script⟩], symbols)
  let bindings ← value.getObjVal? "bindings" >>= (·.getArr?)
  if bindings.size > maxBindings then throw "graph exceeds binding bound"
  let (machine, symbols) ← bindings.foldlM
      (init := (machine, symbols)) fun (machine, symbols) binding => do
    let name ← stringField binding "name"
    exactObject binding 3
    let mutable ← (← binding.getObjVal? "mutable").getBool?
    let (initialValue, symbols) ← parseValue (← binding.getObjVal? "value") refs symbols
    let action : JSM oraclePlatform Unit := do
      let cell ← Environment.declare machine.globalEnv (JSString.ofLeanString name) mutable
      Environment.initialize cell initialValue
    match action machine with
    | .done (.normal ()) machine => pure (machine, symbols)
    | _ => throw s!"failed to initialize binding: {name}"
  let argumentsJson ← arrayField value "arguments"
  let observeJson ← arrayField value "observe"
  if argumentsJson.size > maxGraphRoots || observeJson.size > maxGraphRoots then throw "graph exceeds root bound"
  let (arguments, symbols) ← argumentsJson.foldlM (init := (#[], symbols))
    fun (values, symbols) item => do
      let (value, symbols) ← parseValue item refs symbols
      pure (values.push value, symbols)
  let (observe, symbols) ← observeJson.foldlM (init := (#[], symbols))
    fun (values, symbols) item => do
      let (value, symbols) ← parseValue item refs symbols
      pure (values.push value, symbols)
  pure { machine, arguments, observe, symbols, scripts, selections, fixtureIntrinsics, realm }

end TSLean.JS.Oracle
