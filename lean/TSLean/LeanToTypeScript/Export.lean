import Lean

namespace TSLean.LeanToTypeScript

open Lean

private def fragmentVersion := "tslean-semantic-typed-v5"

private def array (items : List Json) : Json := .arr items.toArray

private def object (fields : List (String × Json)) : Json := .mkObj fields

private def node (kind : String) (fields : List (String × Json) := []) : Json :=
  object (("kind", .str kind) :: fields)

private def documentationFields (environment : Environment) (name : Name) : List (String × Json) :=
  match docStringExt.find? environment name with
  | some documentation => [("doc", .str documentation)]
  | none => []

private def nameTextLt (left right : Name) : Bool := left.toString < right.toString

private def asciiLetter (character : Char) : Bool :=
  ('A' ≤ character && character ≤ 'Z') || ('a' ≤ character && character ≤ 'z')

private def asciiIdentifierStart (character : Char) : Bool :=
  asciiLetter character || character == '_' || character == '$'

private def asciiIdentifierContinue (character : Char) : Bool :=
  asciiIdentifierStart character || ('0' ≤ character && character ≤ '9')

private def isAsciiIdentifier (value : String) : Bool :=
  match value.toList with
  | [] => false
  | first :: rest => asciiIdentifierStart first && rest.all asciiIdentifierContinue

private def reservedBindingNames : List String := [
  "abstract", "accessor", "any", "arguments", "as", "assert", "asserts", "async", "await",
  "bigint", "boolean", "break", "case", "catch", "class", "const", "constructor", "continue",
  "debugger", "declare", "default", "defer", "delete", "do", "else", "enum", "eval", "export",
  "extends", "false", "finally", "for", "from", "function", "get", "global", "if", "implements",
  "import", "in", "infer", "instanceof", "interface", "intrinsic", "is", "keyof", "let", "module",
  "namespace", "never", "new", "null", "number", "object", "of", "out", "override", "package",
  "private", "protected", "public", "readonly", "require", "return", "satisfies", "set", "static",
  "string", "super", "switch", "symbol", "this", "throw", "true", "try", "type", "typeof",
  "undefined", "unique", "unknown", "using", "var", "void", "while", "with", "yield"
]

private def ensureAsciiIdentifier (value description : String) : Except String Unit := do
  unless isAsciiIdentifier value do
    throw s!"{description} {value} is outside the TypeScript-safe ASCII identifier subset"

private def ensureBindingIdentifier (value description : String) : Except String Unit := do
  ensureAsciiIdentifier value description
  if reservedBindingNames.contains value then
    throw s!"{description} {value} is reserved by TypeScript"

private def ensureAsciiDeclarationName (name : Name) : Except String Unit := do
  for component in name.components do
    ensureAsciiIdentifier component.toString "declaration name component"

private def ensureDeclarationName (name : Name) : Except String Unit := do
  ensureAsciiDeclarationName name
  ensureBindingIdentifier name.getString! "declaration name"

private def declarationModule? (environment : Environment) (name : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? name
  environment.header.moduleNames[index.toNat]?

private def declaredInModules (environment : Environment) (modules : NameSet) (name : Name) : Bool :=
  (declarationModule? environment name).any modules.contains

/-- The module that declares a constant. A declaration decides which generated file carries it, so
a constant whose defining module the environment cannot name is refused rather than placed. -/
private def declarationModule (environment : Environment) (name : Name) : Except String Name :=
  match declarationModule? environment name with
  | some moduleName => pure moduleName
  | none => throw s!"declaration {name} has no defining Lean module"

private def declarationModuleField (environment : Environment) (name : Name) :
    Except String (String × Json) := do
  pure ("module", .str (← declarationModule environment name).toString)

/-- The namespace that owns a declaration, empty at the Lean root. Method ownership is read from
this and from the receiver record, never from the shape of a name. -/
private def namespaceField (name : Name) : String × Json :=
  let owner := name.getPrefix
  ("namespace", .str (if owner.isAnonymous then "" else owner.toString))

/-- A qualified Lean name becomes its final component in TypeScript, and the generated tree binds
that component at module scope. Two declarations that spell the same component would bind the same
name wherever one module imports the other, so the collision is refused across the whole package
rather than per module. -/
private def ensureDistinctDeclarationNames (names : List Name) : Except String Unit := do
  let mut seen : Std.HashMap String Name := {}
  for name in names do
    let localName := name.getString!
    match seen[localName]? with
    | some existing =>
        throw s!"{name}: emitted declaration name {localName} collides with {existing}"
    | none => seen := seen.insert localName name

private def appView : Expr → Expr × List Expr
  | .app function argument =>
      let (head, arguments) := appView function
      (head, arguments ++ [argument])
  | expression => (expression, [])

private def constHead? (expression : Expr) : Option Name :=
  match (appView expression.consumeMData).1 with
  | .const name _ => some name
  | _ => none

/-- The head constant of an elaborated instance term together with the head constant of each of
its arguments. An admitted operation names its instance exactly, so a different instance for the
same class is refused rather than assumed equivalent. -/
private def instanceShape (expression : Expr) : Option (Name × List Name) :=
  match appView expression.consumeMData with
  | (.const name _, arguments) =>
      some (name, arguments.map fun argument => (constHead? argument).getD Name.anonymous)
  | _ => none

private def isInstance (expression : Expr) (head : Name) (arguments : List Name) : Bool :=
  instanceShape expression == some (head, arguments)

/-- Whether an elaborated decidability proof is exactly `name applied to the two compared terms`. -/
private def isDecisionFor (decision : Expr) (name : Name) (left right : Expr) : Bool :=
  match appView decision.consumeMData with
  | (.const head _, [candidateLeft, candidateRight]) =>
      head == name && candidateLeft == left && candidateRight == right
  | _ => false

private def isTypeSort (expression : Expr) : Bool :=
  expression.consumeMData == .sort (.succ .zero)

private def groundLevels (levels : List Level) : Bool := levels.all (· == Level.zero)

/--
An inductive data type the fragment admits: declared by the frozen target closure, in `Type 0`,
with no indices, no universe parameters, and every parameter a `Type 0`. A parameter is what makes
the generated type generic, so it has to be a type and nothing else.
-/
private def ordinaryDataInfo (environment : Environment) (targetModules : NameSet) (name : Name) :
    Except String InductiveVal := do
  unless declaredInModules environment targetModules name do
    throw s!"data type {name} is outside the frozen target module closure"
  let some (.inductInfo declaration) := environment.find? name
    | throw s!"type {name} is not an inductive data type"
  unless declaration.levelParams.isEmpty do
    throw s!"data type {name} is universe polymorphic, which is outside the checked fragment"
  unless declaration.numIndices = 0 do
    throw s!"indexed data type {name} is outside the checked fragment"
  let mut telescope := declaration.type
  for _ in [0 : declaration.numParams] do
    match telescope.consumeMData with
    | .forallE _ binderType body _ =>
        unless isTypeSort binderType do
          throw s!"data type {name} takes a parameter that is not a Type 0"
        telescope := body
    | _ => throw s!"data type {name} does not expose its declared parameters"
  unless isTypeSort telescope do
    throw s!"data type {name} must be declared in Type 0"
  pure declaration

/-- The binder names a data type gives its parameters, kept for diagnostics only. -/
private def dataTypeParameterNames (declaration : InductiveVal) : List String :=
  let rec collect (remaining : Nat) (expression : Expr) (names : List String) : List String :=
    match remaining, expression.consumeMData with
    | 0, _ => names.reverse
    | (n + 1), .forallE binderName _ body _ => collect n body (binderName.toString :: names)
    | _, _ => names.reverse
  collect declaration.numParams declaration.type []

/--
Where a de Bruijn index points, relative to one declaration's binders. The type parameters are the
outermost binders, so an index at or above the current value depth names a type parameter and its
position is counted from the outside in.
-/
private structure Context where
  environment : Environment
  targetModules : NameSet
  typeParameters : Nat
  valueDepth : Nat

private def Context.push (context : Context) (count : Nat := 1) : Context :=
  { context with valueDepth := context.valueDepth + count }

private def Context.typeParameterIndex? (context : Context) (index : Nat) : Option Nat :=
  if index < context.valueDepth then none
  else if index < context.valueDepth + context.typeParameters then
    some (context.typeParameters - 1 - (index - context.valueDepth))
  else none

/-- The three Lean data types the compiler maps rather than lowers, plus a user data type applied
to exactly its declared parameters. One function builds the type node for both, so a constructor
application and a type annotation can never disagree about a type's image. -/
private def dataTypeNode (name : Name) (arguments : List Json) : Except String Json :=
  if name == ``Option then
    match arguments with
    | [value] => pure (node "option" [("value", value)])
    | _ => throw "Option takes exactly one type argument"
  else if name == ``Except then
    match arguments with
    | [error, value] => pure (node "except" [("error", error), ("value", value)])
    | _ => throw "Except takes exactly two type arguments"
  else if name == ``List then
    match arguments with
    | [element] => pure (node "list" [("element", element)])
    | _ => throw "List takes exactly one type argument"
  else
    pure (node "named" [("name", .str name.toString), ("arguments", array arguments)])

mutual

/-- One admitted Lean type, as the fragment's type node. -/
private partial def typeNode (context : Context) (expression : Expr) : Except String Json := do
  let expression := expression.consumeMData
  if expression.isForall then
    let (parameters, result) ← arrowChain context expression
    return node "function" [("parameters", array parameters), ("result", result)]
  let (head, arguments) := appView expression
  match head with
  | .bvar index =>
      unless arguments.isEmpty do
        throw "a type parameter applied to arguments is outside the checked fragment"
      match context.typeParameterIndex? index with
      | some position => pure (node "parameter" [("index", .num position)])
      | none => throw "a value binder appears in a type; dependent types are outside the checked fragment"
  | .const name levels =>
      unless groundLevels levels do
        throw s!"type {name} is applied at a universe above Type 0, which is outside the checked fragment"
      if name == ``Bool then
        unless arguments.isEmpty do throw "Bool received unexpected type arguments"
        pure (node "boolean")
      else if name == ``Nat then
        unless arguments.isEmpty do throw "Nat received unexpected type arguments"
        pure (node "nat")
      else if name == ``String then
        unless arguments.isEmpty do throw "String received unexpected type arguments"
        pure (node "string")
      else if name == ``Option || name == ``Except || name == ``List then
        dataTypeNode name (← arguments.mapM (typeNode context))
      else
        let declaration ← ordinaryDataInfo context.environment context.targetModules name
        unless arguments.length = declaration.numParams do
          throw s!"data type {name} is applied to {arguments.length} arguments; it declares {declaration.numParams}"
        dataTypeNode name (← arguments.mapM (typeNode context))
  | _ => throw s!"unsupported type expression {expression}"

/--
An arrow chain read as one uncurried arity. A binder the body depends on is refused by `typeNode`,
which sees it as a value binder in a type, so only non-dependent arrows survive.
-/
private partial def arrowChain (context : Context) (expression : Expr) :
    Except String (List Json × Json) := do
  match expression.consumeMData with
  | .forallE _ binderType body binderInfo =>
      unless binderInfo == .default do
        throw "an implicit or instance arrow inside a type is outside the checked fragment"
      let parameter ← typeNode context binderType
      let (parameters, result) ← arrowChain context.push body
      pure (parameter :: parameters, result)
  | result => pure ([], ← typeNode context result)

end

private structure Parameter where
  name : String
  type : Json

private structure Signature where
  typeParameterNames : List String
  parameters : List Parameter
  result : Json

/-- The leading implicit `Type 0` binders, which are what the generated declaration is generic in. -/
private partial def peelTypeParameters (expression : Expr) (names : List String) :
    List String × Expr :=
  match expression.consumeMData with
  | .forallE binderName binderType body binderInfo =>
      if binderInfo == .implicit && isTypeSort binderType then
        peelTypeParameters body (binderName.toString :: names)
      else (names.reverse, expression.consumeMData)
  | other => (names.reverse, other)

private partial def peelValueParameters (context : Context) (expression : Expr) :
    Except String (List Parameter × Json) := do
  match expression.consumeMData with
  | .forallE binderName binderType body binderInfo =>
      unless binderInfo == .default do
        throw "instance parameters, and implicit parameters after the leading type parameters, are outside the checked fragment"
      let parameterType ← typeNode context binderType
      let (parameters, result) ← peelValueParameters context.push body
      pure ({ name := binderName.toString, type := parameterType } :: parameters, result)
  | result => pure ([], ← typeNode context result)

private def declarationSignature (environment : Environment) (targetModules : NameSet)
    (type : Expr) : Except String Signature := do
  let (typeParameterNames, rest) := peelTypeParameters type []
  let context : Context :=
    { environment, targetModules, typeParameters := typeParameterNames.length, valueDepth := 0 }
  let (parameters, result) ← peelValueParameters context rest
  pure { typeParameterNames, parameters, result }

/-- The binder names a value abstracts, peeling exactly the declared arity. -/
private partial def peelBinderNames (count : Nat) (expression : Expr) :
    Except String (List Name × Expr) := do
  match count, expression.consumeMData with
  | 0, body => pure ([], body)
  | (n + 1), .lam binderName _ body _ =>
      let (names, inner) ← peelBinderNames n body
      pure (binderName :: names, inner)
  | _, _ => throw "definition value does not abstract its declared parameters"

/--
A function value at exactly one arity. Lean writes a value of arrow type either as an abstraction
or as a term the caller applies later, and only the first has a TypeScript image, so the second is
eta-expanded to the arity its type declares. The generated binders are the compiler's own, which
is why they are positional rather than borrowed from an anonymous Lean binder.
-/
private partial def etaExpandTo (arity : Nat) (expression : Expr) : List String × Expr :=
  match arity, expression.consumeMData with
  | 0, body => ([], body)
  | (n + 1), .lam binderName _ body _ =>
      let (names, inner) := etaExpandTo n body
      (binderName.toString :: names, inner)
  | missing, body =>
      let lifted := body.liftLooseBVars 0 missing
      let applied := mkAppN lifted
        (((List.range missing).map fun position => Expr.bvar (missing - 1 - position)).toArray)
      ((List.range missing).map fun position => s!"argument{position}", applied)

private def structureFieldNames (environment : Environment) (name : Name) : Except String (List Name) := do
  let fields := getStructureFields environment name
  for field in fields do
    ensureAsciiIdentifier field.getString! "structure field"
  pure fields.toList

mutual

/--
One admitted Lean term, as the fragment's expression node.

`returnPosition` carries the emitter's own lowering policy: a `let` becomes a `const` statement, so
it is admitted exactly where the generated function returns — its own body, and the branches of an
`if` or a `match` in that position. A `let` inside an argument would need an immediately applied
function to keep its statement shape, so it is refused with the remedy named.
-/
private partial def expressionNode (context : Context) (returnPosition : Bool) (expression : Expr) :
    Except String Json := do
  let expression := expression.consumeMData
  match expression with
  | .bvar index =>
      if index < context.valueDepth then pure (node "variable" [("index", .num index)])
      else if (context.typeParameterIndex? index).isSome then
        throw "a type parameter is used as a value, which is outside the checked fragment"
      else throw s!"unbound de Bruijn index {index}"
  | .letE binderName binderType value body _ =>
      unless returnPosition do
        throw "a let inside an argument is outside the checked fragment; bind it before the call"
      ensureBindingIdentifier binderName.toString "let binder"
      let valueNode ←
        if binderType.consumeMData.isForall then functionValueNode context binderType value
        else expressionNode context false value
      pure (node "let" [
        ("name", .str binderName.toString),
        ("value", valueNode),
        ("body", ← expressionNode context.push true body)
      ])
  | .proj typeName index subject =>
      let fields ← structureFieldNames context.environment typeName
      let some field := fields[index]?
        | throw s!"structure {typeName} has no field at index {index}"
      pure (node "field" [
        ("target", ← expressionNode context false subject),
        ("field", .str field.getString!)
      ])
  | .fvar _ => throw "free variables are outside the checked fragment"
  | .mvar _ => throw "metavariables are outside the checked fragment"
  | .sort _ | .forallE _ _ _ _ => throw "type-level expressions are outside the checked fragment"
  | .lam _ _ _ _ =>
      throw "a function value in a position with no declared arrow type is outside the checked fragment"
  | .lit (.natVal value) => pure (node "nat" [("value", .str (toString value))])
  | .lit (.strVal value) => pure (node "string" [("value", .str value)])
  | _ => applicationNode context returnPosition expression

/-- A term of arrow type, normalized to exactly the arity its type declares. -/
private partial def functionValueNode (context : Context) (functionType : Expr) (expression : Expr) :
    Except String Json := do
  let (parameterTypes, _) ← arrowChain context functionType
  if parameterTypes.isEmpty then
    throw "a function value whose type is not an arrow is outside the checked fragment"
  let (names, body) := etaExpandTo parameterTypes.length expression
  for name in names do
    ensureBindingIdentifier name "function binder"
  let parameters := (names.zip parameterTypes).map fun (name, parameterType) =>
    object [("name", .str name), ("type", parameterType)]
  pure (node "lambda" [
    ("parameters", array parameters),
    ("body", ← expressionNode (context.push parameterTypes.length) false body)
  ])

/--
The arguments of one elaborated application, split by the telescope of what is applied. A binder
whose type is `Type 0` carries a type argument; every other binder carries a value argument, read
against its own instantiated binder type so a function-typed argument knows its arity.
-/
private partial def applicationArguments (context : Context) (telescope : Expr)
    (arguments : List Expr) : Except String (List Json × List Json) := do
  match arguments with
  | [] => pure ([], [])
  | argument :: rest =>
      match telescope.consumeMData with
      | .forallE _ binderType body binderInfo =>
          let remaining := body.instantiate1 argument
          if isTypeSort binderType then
            let typeArgument ← typeNode context argument
            let (types, values) ← applicationArguments context remaining rest
            pure (typeArgument :: types, values)
          else if binderInfo == .default then
            let valueArgument ←
              if binderType.consumeMData.isForall then functionValueNode context binderType argument
              else expressionNode context false argument
            let (types, values) ← applicationArguments context remaining rest
            pure (types, valueArgument :: values)
          else
            throw "an instance argument is outside the checked fragment"
      | _ => throw "an application is longer than the telescope of what it applies"

/--
The Bool value of a decidable proposition, admitted only for the exact decision procedures the
runtime opcode registry covers.

Lean's `if (b : Bool) then` elaborates through the coercion `b = true`, decided by
`instDecidableEqBool`. That coercion is inverted here rather than emitted, so the generated
condition is the Bool itself and no equality opcode is spent on it.
-/
private partial def decisionNode (context : Context) (proposition : Expr) (decision : Expr) :
    Except String Json := do
  let (head, arguments) := appView proposition.consumeMData
  let .const name _ := head
    | throw "only a decidable comparison is admitted as a condition in this fragment version"
  if name == ``Eq then
    let [comparedType, left, right] := arguments
      | throw "Eq received an unsupported elaborated shape"
    let compared := comparedType.consumeMData
    if compared.isConstOf ``Bool && isDecisionFor decision ``instDecidableEqBool left right then
      if right.consumeMData.isConstOf ``Bool.true then
        expressionNode context false left
      else if left.consumeMData.isConstOf ``Bool.true then
        expressionNode context false right
      else
        pure (node "operation" [
          ("opcode", .str "bool.equals"),
          ("typeArguments", array []),
          ("arguments", array [← expressionNode context false left, ← expressionNode context false right])
        ])
    else if compared.isConstOf ``Nat && isDecisionFor decision ``instDecidableEqNat left right then
      pure (node "operation" [
        ("opcode", .str "nat.equals"),
        ("typeArguments", array []),
        ("arguments", array [← expressionNode context false left, ← expressionNode context false right])
      ])
    else if compared.isConstOf ``String && isDecisionFor decision ``instDecidableEqString left right then
      pure (node "operation" [
        ("opcode", .str "string.equals"),
        ("typeArguments", array []),
        ("arguments", array [← expressionNode context false left, ← expressionNode context false right])
      ])
    else
      throw s!"equality on {compared} has no admitted decision procedure in this fragment version"
  else if name == ``LT.lt || name == ``LE.le then
    let [comparedType, instanceTerm, left, right] := arguments
      | throw s!"{name} received an unsupported elaborated shape"
    let less := name == ``LT.lt
    let expectedInstance := if less then ``instLTNat else ``instLENat
    let expectedDecision := if less then ``Nat.decLt else ``Nat.decLe
    unless comparedType.consumeMData.isConstOf ``Nat && instanceTerm.consumeMData.isConstOf expectedInstance do
      throw s!"{name} is admitted only on Nat in this fragment version"
    unless isDecisionFor decision expectedDecision left right do
      throw s!"{name} on Nat is decided by an unadmitted procedure"
    pure (node "operation" [
      ("opcode", .str (if less then "nat.less" else "nat.lessOrEqual")),
      ("typeArguments", array []),
      ("arguments", array [← expressionNode context false left, ← expressionNode context false right])
    ])
  else
    throw s!"proposition {name} has no admitted decision procedure in this fragment version"

/-- An operation node over already encoded operands. -/
private partial def operationNode (opcode : String) (typeArguments : List Json)
    (arguments : List Json) : Json :=
  node "operation" [
    ("opcode", .str opcode),
    ("typeArguments", array typeArguments),
    ("arguments", array arguments)
  ]

/-- One elaborated application, dispatched on what it applies. -/
private partial def applicationNode (context : Context) (returnPosition : Bool)
    (expression : Expr) : Except String Json := do
  let (head, arguments) := appView expression
  -- A constant's own universe arguments are not checked here: a matcher is universe polymorphic in
  -- its motive and `ite` in its result, so the admitted universes are decided by `typeNode` on the
  -- types that actually reach the IR, and by refusing a universe polymorphic declaration outright.
  -- They are carried instead, because a polymorphic constant's declared telescope still mentions
  -- its level parameters and has to be instantiated before it can be walked.
  let .const name levels := head
    | match head with
      | .bvar _ =>
          -- A bound variable of arrow type, applied. The IR checks the arity against its type.
          pure (node "apply" [
            ("target", ← expressionNode context false head),
            ("arguments", array (← arguments.mapM (expressionNode context false)))
          ])
      | _ => throw s!"unsupported application head {head}"
  if name == ``Bool.true then pure (node "boolean" [("value", .bool true)])
  else if name == ``Bool.false then pure (node "boolean" [("value", .bool false)])
  else if name == ``ite then
    let [_, condition, decision, consequent, alternate] := arguments
      | throw "ite received an unsupported elaborated shape"
    pure (node "if" [
      ("condition", ← decisionNode context condition decision),
      ("consequent", ← expressionNode context returnPosition consequent),
      ("alternate", ← expressionNode context returnPosition alternate)
    ])
  else if name == ``dite then
    throw "a dependent if binds its own decision proof, which is outside the checked fragment"
  else if name == ``decide then
    let [proposition, decision] := arguments | throw "decide received an unsupported elaborated shape"
    decisionNode context proposition decision
  else if name == ``Bool.and || name == ``Bool.or then
    let [left, right] := arguments | throw s!"{name} received an unsupported elaborated shape"
    pure (operationNode (if name == ``Bool.and then "bool.and" else "bool.or") []
      [← expressionNode context false left, ← expressionNode context false right])
  else if name == ``Bool.not then
    let [operand] := arguments | throw "Bool.not received an unsupported elaborated shape"
    pure (operationNode "bool.not" [] [← expressionNode context false operand])
  else if name == ``Nat.add || name == ``Nat.sub || name == ``Nat.mul then
    let [left, right] := arguments | throw s!"{name} received an unsupported elaborated shape"
    let opcode :=
      if name == ``Nat.add then "nat.add" else if name == ``Nat.sub then "nat.subtract" else "nat.multiply"
    pure (operationNode opcode [] [← expressionNode context false left, ← expressionNode context false right])
  else if name == ``Nat.succ then
    let [operand] := arguments | throw "Nat.succ received an unsupported elaborated shape"
    pure (operationNode "nat.successor" [] [← expressionNode context false operand])
  else if name == ``String.append then
    let [left, right] := arguments | throw "String.append received an unsupported elaborated shape"
    pure (operationNode "string.append" [] [← expressionNode context false left, ← expressionNode context false right])
  else if name == ``OfNat.ofNat then
    let [ofType, literal, instanceTerm] := arguments | throw "OfNat.ofNat received an unsupported elaborated shape"
    unless ofType.consumeMData.isConstOf ``Nat do
      throw "numeric literals are admitted only at type Nat in this fragment version"
    let .lit (.natVal value) := literal.consumeMData
      | throw "a Nat literal that is not a raw natural is outside the checked fragment"
    unless isInstance instanceTerm ``instOfNatNat [Name.anonymous] do
      throw "a Nat literal built by an unadmitted OfNat instance is outside the checked fragment"
    pure (node "nat" [("value", .str (toString value))])
  else if name == ``HAdd.hAdd || name == ``HSub.hSub || name == ``HMul.hMul then
    let [_, _, _, instanceTerm, left, right] := arguments
      | throw s!"{name} received an unsupported elaborated shape"
    let (wrapper, natInstance, opcode) :=
      if name == ``HAdd.hAdd then (``instHAdd, ``instAddNat, "nat.add")
      else if name == ``HSub.hSub then (``instHSub, ``instSubNat, "nat.subtract")
      else (``instHMul, ``instMulNat, "nat.multiply")
    unless isInstance instanceTerm wrapper [``Nat, natInstance] do
      throw s!"{name} is admitted only on Nat in this fragment version"
    pure (operationNode opcode [] [← expressionNode context false left, ← expressionNode context false right])
  else if name == ``HAppend.hAppend then
    let [appendedType, _, _, instanceTerm, left, right] := arguments
      | throw "HAppend.hAppend received an unsupported elaborated shape"
    if isInstance instanceTerm ``instHAppendOfAppend [``String, ``instAppendString] then
      pure (operationNode "string.append" []
        [← expressionNode context false left, ← expressionNode context false right])
    else if isInstance instanceTerm ``instHAppendOfAppend [``List, ``List.instAppend] then
      let (_, elementArguments) := appView appendedType.consumeMData
      let [element] := elementArguments | throw "list append received an unsupported element type"
      pure (operationNode "list.append" [← typeNode context element]
        [← expressionNode context false left, ← expressionNode context false right])
    else
      throw "append is admitted only on String and List in this fragment version"
  else if name == ``BEq.beq then
    let [comparedType, instanceTerm, left, right] := arguments
      | throw "BEq.beq received an unsupported elaborated shape"
    let compared := comparedType.consumeMData
    let opcode ←
      if compared.isConstOf ``Bool && isInstance instanceTerm ``instBEqOfDecidableEq [``Bool, ``instDecidableEqBool] then
        pure "bool.equals"
      else if compared.isConstOf ``Nat && isInstance instanceTerm ``instBEqOfDecidableEq [``Nat, ``instDecidableEqNat] then
        pure "nat.equals"
      else if compared.isConstOf ``String && isInstance instanceTerm ``instBEqOfDecidableEq [``String, ``instDecidableEqString] then
        pure "string.equals"
      else
        throw s!"equality on {compared} has no admitted decision procedure in this fragment version"
    pure (operationNode opcode [] [← expressionNode context false left, ← expressionNode context false right])
  else if let some opcode := listOpcode? name then
    listOperationNode context opcode name levels arguments
  else if let some matcherInfo := Meta.getMatcherInfoCore? context.environment name then
    matchNode context returnPosition name matcherInfo arguments
  else
    constantApplicationNode context name levels arguments

/-- The collection operations the fragment admits, each by its exact Lean constant. -/
private partial def listOpcode? (name : Name) : Option String :=
  if name == ``List.length then some "list.length"
  else if name == ``List.isEmpty then some "list.isEmpty"
  else if name == ``List.append then some "list.append"
  else if name == ``List.reverse then some "list.reverse"
  else if name == ``List.map then some "list.map"
  else if name == ``List.filter then some "list.filter"
  else if name == ``List.foldl then some "list.foldLeft"
  else if name == ``List.foldr then some "list.foldRight"
  else if name == ``List.any then some "list.any"
  else if name == ``List.all then some "list.all"
  else if name == ``List.head? then some "list.head"
  else none

/--
A collection operation, with its type arguments put in the registry's own order. `List.foldl` takes
its accumulator first and `List.foldr` takes its element first, so the two are mapped explicitly
rather than passed through, and the registry keeps one order for both.
-/
private partial def listOperationNode (context : Context) (opcode : String) (name : Name)
    (levels : List Level) (arguments : List Expr) : Except String Json := do
  let some info := context.environment.find? name
    | throw s!"constant {name} is absent from the elaborated environment"
  let (typeArguments, valueArguments) ←
    applicationArguments context (info.instantiateTypeLevelParams levels) arguments
  let ordered ←
    if opcode == "list.foldLeft" then
      match typeArguments with
      | [accumulator, element] => pure [element, accumulator]
      | _ => throw "List.foldl received an unsupported elaborated shape"
    else pure typeArguments
  let expectedTypes := if opcode == "list.foldLeft" || opcode == "list.foldRight" || opcode == "list.map" then 2 else 1
  unless ordered.length = expectedTypes do
    throw s!"{name} received {ordered.length} type arguments; expected {expectedTypes}"
  let expectedValues :=
    if opcode == "list.append" then 2
    else if opcode == "list.map" || opcode == "list.filter" || opcode == "list.any" || opcode == "list.all" then 2
    else if opcode == "list.foldLeft" || opcode == "list.foldRight" then 3
    else 1
  unless valueArguments.length = expectedValues do
    throw s!"{name} received {valueArguments.length} arguments; expected {expectedValues}"
  pure (operationNode opcode ordered valueArguments)

/--
A `match`, read from the elaborated matcher. The discriminant type comes from the motive's own
binder, so a generic discriminant carries its instantiated type arguments, and every alternative
has to decide exactly one constructor and bind exactly its fields.
-/
private partial def matchNode (context : Context) (returnPosition : Bool) (name : Name)
    (matcherInfo : Meta.MatcherInfo) (arguments : List Expr) : Except String Json := do
  unless declaredInModules context.environment context.targetModules name do
    throw s!"matcher {name} is outside the frozen target module closure"
  unless matcherInfo.numDiscrs = 1 do
    throw "a match on more than one discriminant is outside this fragment version; nest the matches"
  unless matcherInfo.getNumDiscrEqs = 0 do
    throw "a match binding discriminant equations is outside the checked fragment"
  unless arguments.length = matcherInfo.arity do
    throw s!"matcher {name} received an unsupported elaborated shape"
  let some motive := arguments[matcherInfo.getMotivePos]?
    | throw s!"matcher {name} received no motive"
  let .lam _ discriminantType motiveBody _ := motive.consumeMData
    | throw s!"matcher {name} motive is not a discriminant abstraction"
  if motiveBody.hasLooseBVar 0 then
    throw "a match whose result type depends on the discriminant is outside the checked fragment"
  let scrutineeType ← typeNode context discriminantType
  let dataName ← discriminantTypeName context discriminantType
  let constructors ← discriminantConstructors context dataName
  let alternatives ← matcherAlternativeConstructors context.environment name matcherInfo
  unless alternatives.length = constructors.length do
    throw s!"a match on {dataName} does not decide every constructor exactly once"
  let some discriminant := arguments[matcherInfo.getFirstDiscrPos]?
    | throw s!"matcher {name} received no discriminant"
  let mut cases := []
  for constructorName in constructors do
    let some alternativeIndex := alternatives.findIdx? (· == constructorName)
      | throw s!"a match on {dataName} does not decide {constructorName}"
    let some (.ctorInfo constructorInfo) := context.environment.find? constructorName
      | throw s!"constructor {constructorName} is absent from the elaborated environment"
    let some alternativeParameters := matcherInfo.altNumParams[alternativeIndex]?
      | throw s!"matcher {name} has no alternative {alternativeIndex}"
    -- A nullary alternative is thunked behind one `Unit` binder; every other alternative abstracts
    -- exactly its constructor's fields. Any other parameter count means the alternative carries
    -- discriminant equations or overlap assumptions.
    let hasUnitThunk := constructorInfo.numFields = 0
    unless alternativeParameters = constructorInfo.numFields + (if hasUnitThunk then 1 else 0) do
      throw s!"matcher {name} alternative {alternativeIndex} carries parameters beyond its constructor fields"
    let some encoded := arguments[matcherInfo.getFirstAltPos + alternativeIndex]?
      | throw s!"matcher {name} received no alternative for {constructorName}"
    let (armContext, value) ← if hasUnitThunk then
        match encoded.consumeMData with
        | .lam _ _ thunkBody _ =>
            if thunkBody.hasLooseBVar 0 then
              throw s!"matcher {name} alternative uses its unit thunk binder"
            pure (context, thunkBody.lowerLooseBVars 1 1)
        | _ => throw s!"matcher {name} thunked alternative is not an abstraction"
      else
        let mut body := encoded
        for _ in [0 : constructorInfo.numFields] do
          match body.consumeMData with
          | .lam _ _ inner _ => body := inner
          | _ => throw s!"matcher {name} alternative does not abstract its constructor fields"
        pure (context.push constructorInfo.numFields, body)
    ensureAsciiIdentifier constructorName.getString! "constructor name"
    cases := object [
      ("constructor", .str constructorName.getString!),
      ("value", ← expressionNode armContext returnPosition value)
    ] :: cases
  pure (node "match" [
    ("type", scrutineeType),
    ("scrutinee", ← expressionNode context false discriminant),
    ("cases", array cases.reverse)
  ])

/-- The head constant of a discriminant type, which is the data type the match decides. -/
private partial def discriminantTypeName (_context : Context) (discriminantType : Expr) :
    Except String Name := do
  match (appView discriminantType.consumeMData).1 with
  | .const name _ => pure name
  | _ => throw "a match on a value whose type is not a data type is outside the checked fragment"

/--
The constructors a match has to decide, in declaration order. The three mapped Lean types keep
their own constructors, because their TypeScript representation carries exactly those cases.
-/
private partial def discriminantConstructors (context : Context) (name : Name) :
    Except String (List Name) := do
  if name == ``Nat then
    throw "a match on Nat is outside this fragment version; decide it with a comparison"
  if name == ``Option || name == ``Except || name == ``List then
    let some (.inductInfo declaration) := context.environment.find? name
      | throw s!"type {name} is not an inductive data type"
    pure declaration.ctors
  else
    let declaration ← ordinaryDataInfo context.environment context.targetModules name
    if declaration.ctors.isEmpty then
      throw s!"inductive data type {name} has no constructors"
    pure declaration.ctors

/--
Which constructor each alternative of a matcher decides, read from the matcher's own declared type.
Alternative `i` is typed `motive (Ctor p… f₀ … fₙ₋₁)` behind its own binders, so the constructor is
recovered structurally instead of assuming the source arm order. The pattern has to apply the
constructor to its own binders in field order: a nested or repeated pattern is refused rather than
flattened, while the inductive's parameters are fixed by the discriminant type and are not checked
against the alternative's binders.
-/
private partial def matcherAlternativeConstructors (environment : Environment) (matcherName : Name)
    (info : Meta.MatcherInfo) : Except String (List Name) := do
  let some constantInfo := environment.find? matcherName
    | throw s!"matcher {matcherName} is absent from the elaborated environment"
  let mut telescope := constantInfo.type
  for _ in [0 : info.numParams + 1 + info.numDiscrs] do
    match telescope.consumeMData with
    | .forallE _ _ body _ => telescope := body
    | _ => throw s!"matcher {matcherName} does not expose the expected discriminant telescope"
  let alternativeParameters := info.altNumParams
  let mut constructors := []
  for index in [0 : info.numAlts] do
    match telescope.consumeMData with
    | .forallE _ binderType body _ =>
        let some parameterCount := alternativeParameters[index]?
          | throw s!"matcher {matcherName} has no parameter count for alternative {index}"
        let mut applied := binderType
        for _ in [0 : parameterCount] do
          match applied.consumeMData with
          | .forallE _ _ inner _ => applied := inner
          | _ => throw s!"matcher {matcherName} alternative {index} has an unexpected telescope"
        let (head, appliedArguments) := appView applied.consumeMData
        let .bvar _ := head
          | throw s!"matcher {matcherName} alternative is not an application of its motive"
        let [pattern] := appliedArguments
          | throw s!"matcher {matcherName} alternative does not decide exactly one discriminant"
        let (patternHead, patternArguments) := appView pattern.consumeMData
        let .const constructorName _ := patternHead
          | throw s!"matcher {matcherName} alternative pattern is not a constructor"
        let some (.ctorInfo constructorInfo) := environment.find? constructorName
          | throw s!"constructor {constructorName} is absent from the elaborated environment"
        unless patternArguments.length = constructorInfo.numParams + constructorInfo.numFields do
          throw s!"matcher {matcherName} alternative {index} does not apply {constructorName} to its own arity"
        let fieldArguments := patternArguments.drop constructorInfo.numParams
        let expected := (List.range constructorInfo.numFields).map fun position =>
          Expr.bvar (constructorInfo.numFields - 1 - position)
        unless fieldArguments.map Expr.consumeMData == expected do
          throw s!"matcher {matcherName} alternative {index} does not bind each constructor field exactly once"
        constructors := constructorName :: constructors
        telescope := body
    | _ => throw s!"matcher {matcherName} does not expose the expected alternative telescope"
  pure constructors.reverse

/-- An application of a constant that is neither an admitted operation nor a matcher. -/
private partial def constantApplicationNode (context : Context) (name : Name) (levels : List Level)
    (arguments : List Expr) : Except String Json := do
  let some info := context.environment.find? name
    | throw s!"constant {name} is absent from the elaborated environment"
  if let some projection := context.environment.getProjectionFnInfo? name then
    unless arguments.length = projection.numParams + 1 do
      throw s!"projection {name} is applied to {arguments.length} arguments; a field read takes exactly {projection.numParams + 1}"
    let some target := arguments[projection.numParams]?
      | throw s!"projection {name} received an unsupported elaborated shape"
    ensureAsciiIdentifier name.getString! "structure field"
    return node "field" [
      ("target", ← expressionNode context false target),
      ("field", .str name.getString!)
    ]
  match info with
  | .ctorInfo constructor =>
      let (typeArguments, valueArguments) ←
        applicationArguments context (info.instantiateTypeLevelParams levels) arguments
      unless typeArguments.length = constructor.numParams do
        throw s!"constructor {name} received {typeArguments.length} type arguments; expected {constructor.numParams}"
      unless valueArguments.length = constructor.numFields do
        throw s!"constructor {name} received {valueArguments.length} fields; expected {constructor.numFields}"
      if isStructure context.environment constructor.induct then
        let fields ← structureFieldNames context.environment constructor.induct
        unless fields.length = valueArguments.length do
          throw s!"structure constructor {name} received an unsupported elaborated shape"
        let encodedFields := (fields.zip valueArguments).map fun (field, value) =>
          object [("name", .str field.getString!), ("value", value)]
        pure (node "record" [
          ("type", ← dataTypeNode constructor.induct typeArguments),
          ("fields", array encodedFields)
        ])
      else
        ensureAsciiIdentifier name.getString! "constructor name"
        pure (node "variant" [
          ("type", ← dataTypeNode constructor.induct typeArguments),
          ("name", .str name.getString!),
          ("arguments", array valueArguments)
        ])
  | .defnInfo _ =>
      unless declaredInModules context.environment context.targetModules name do
        throw s!"function {name} is outside the frozen target module closure"
      let (typeArguments, valueArguments) ←
        applicationArguments context (info.instantiateTypeLevelParams levels) arguments
      pure (node "call" [
        ("function", .str name.toString),
        ("typeArguments", array typeArguments),
        ("arguments", array valueArguments)
      ])
  | _ => throw s!"constant {name} is outside the checked fragment"

end

private def fieldDeclaration (context : Context) (structureName fieldName : Name) :
    Except String Json := do
  let some fieldInfo := getFieldInfo? context.environment structureName fieldName
    | throw s!"structure field {structureName}.{fieldName} has no projection metadata"
  let some info := context.environment.find? fieldInfo.projFn
    | throw s!"structure field projection {fieldInfo.projFn} is absent from the environment"
  ensureAsciiIdentifier fieldName.getString! "structure field"
  -- The projection is `∀ (params) (self), field`, so the field type is read one binder inside the
  -- structure value, with the data type's parameters as the type parameters in scope.
  let mut telescope := info.type
  for _ in [0 : context.typeParameters + 1] do
    match telescope.consumeMData with
    | .forallE _ _ body _ => telescope := body
    | _ => throw s!"structure field projection {fieldInfo.projFn} does not expose its telescope"
  let fieldType ← typeNode { context with valueDepth := 1 } telescope
  pure (object ([("name", .str fieldName.getString!), ("type", fieldType)]
    ++ documentationFields context.environment fieldInfo.projFn))

/-- The fields a constructor carries, read from its own declared type behind its type parameters. -/
private def constructorFields (context : Context) (constructorName : Name) :
    Except String (List Parameter) := do
  let some (.ctorInfo constructor) := context.environment.find? constructorName
    | throw s!"constructor {constructorName} is absent from the elaborated environment"
  unless constructor.numParams = context.typeParameters do
    throw s!"constructor {constructorName} does not expose its data type's parameters"
  let mut telescope := constructor.type
  for _ in [0 : constructor.numParams] do
    match telescope.consumeMData with
    | .forallE _ _ body _ => telescope := body
    | _ => throw s!"constructor {constructorName} does not expose its parameter telescope"
  let (fields, _) ← peelValueParameters context telescope
  unless fields.length = constructor.numFields do
    throw s!"constructor {constructorName} does not expose its fields as first-order parameters"
  let mut seen : Std.HashSet String := {}
  for field in fields do
    ensureBindingIdentifier field.name "constructor field"
    if seen.contains field.name then
      throw s!"constructor {constructorName} declares field {field.name} more than once"
    seen := seen.insert field.name
  pure fields

private def typeParameterField (names : List String) : String × Json :=
  ("typeParameters", array (names.map Json.str))

private def dataDeclaration (environment : Environment) (targetModules : NameSet)
    (name : Name) : Except String Json := do
  let declaration ← ordinaryDataInfo environment targetModules name
  let typeParameterNames := dataTypeParameterNames declaration
  let context : Context :=
    { environment, targetModules, typeParameters := declaration.numParams, valueDepth := 0 }
  if isStructure environment name then
    let fields ← structureFieldNames environment name
    let constructor := getStructureCtor environment name
    ensureAsciiIdentifier constructor.name.getString! "structure constructor"
    pure (node "record" ([
      ("name", .str name.toString),
      ← declarationModuleField environment name,
      namespaceField name,
      typeParameterField typeParameterNames,
      ("constructor", .str constructor.name.getString!),
      ("fields", array (← fields.mapM (fieldDeclaration context name)))
    ] ++ documentationFields environment name))
  else
    if declaration.ctors.isEmpty then
      throw s!"inductive data type {name} has no constructors"
    let mut constructors := []
    for constructorName in declaration.ctors do
      ensureAsciiDeclarationName constructorName
      let fields ← constructorFields context constructorName
      let encodedFields := fields.map fun field =>
        object [("name", .str field.name), ("type", field.type)]
      constructors := object ([
        ("name", .str constructorName.getString!),
        ("fields", array encodedFields)
      ] ++ documentationFields environment constructorName) :: constructors
    pure (node "enum" ([
      ("name", .str name.toString),
      ← declarationModuleField environment name,
      namespaceField name,
      typeParameterField typeParameterNames,
      ("constructors", array constructors.reverse)
    ] ++ documentationFields environment name))

/--
How Lean discharged a definition's termination, read from the elaborator's own record. Structural
recursion names the parameter it decreases on; well-founded recursion names none, because its
measure has no image in the generated call. Both name the whole recursive group, which is what the
generated program is allowed to recurse through.
-/
private structure Recursion where
  kind : String
  argument? : Option Nat
  group : List Name

private def recursionOf? (environment : Environment) (name : Name) : Option Recursion :=
  match Lean.Elab.Structural.eqnInfoExt.find? environment name with
  | some info =>
      some { kind := "structural", argument? := some info.recArgPos, group := info.declNames.toList }
  | none =>
      match Lean.Elab.WF.eqnInfoExt.find? environment name with
      | some info => some { kind := "wellFounded", argument? := none, group := info.declNames.toList }
      | none => none

/-- The pre-compilation body of a recursive definition, which still names itself. -/
private def recursionValue? (environment : Environment) (name : Name) : Option Expr :=
  match Lean.Elab.Structural.eqnInfoExt.find? environment name with
  | some info => some info.value
  | none => (Lean.Elab.WF.eqnInfoExt.find? environment name).map (·.value)

/--
Reads a recursive definition's body out of its kernel-checked unfolding theorem
`f.eq_def : ∀ xs, f xs = body`, rather than out of the `brecOn` or `WellFounded.fix` term the
compiler built. The theorem is proved by the kernel, so the exported body is equal to the
definition by the same authority that accepted the definition.
-/
private def unfoldingEquationBody (name : Name) (binderCount : Nat) (equationType : Expr) :
    Except String (List Name × Expr) := do
  let mut telescope := equationType
  let mut names := []
  for _ in [0 : binderCount] do
    match telescope.consumeMData with
    | .forallE binderName _ body _ =>
        names := binderName :: names
        telescope := body
    | _ => throw s!"unfolding theorem for {name} does not abstract every parameter"
  let (head, arguments) := appView telescope.consumeMData
  unless head.isConstOf ``Eq do
    throw s!"unfolding theorem for {name} is not an equation"
  let [_, left, right] := arguments
    | throw s!"unfolding theorem for {name} has an unsupported equation shape"
  let (leftHead, leftArguments) := appView left.consumeMData
  unless leftHead.isConstOf name do
    throw s!"unfolding theorem for {name} does not unfold {name}"
  let expected := (List.range binderCount).map fun position => Expr.bvar (binderCount - 1 - position)
  unless leftArguments.map Expr.consumeMData == expected do
    throw s!"unfolding theorem for {name} does not apply it to its own parameters"
  pure (names.reverse, right)

/--
Dot-notation evidence, read from the elaborated environment. Lean resolves `value.f` through the
namespace of the head symbol of `value`'s type, so a method is a declaration in a data type's own
namespace whose parameter carries exactly that data type at the declaration's own type parameters.
Both have to be declared by one Lean module: a receiver in another module would move code across
the module boundary the generated tree preserves.
-/
private def receiverField? (environment : Environment) (targetModules : NameSet) (name : Name)
    (typeParameterCount : Nat) (parameters : List Parameter) :
    Except String (Option (String × Json)) := do
  let owner := name.getPrefix
  if owner.isAnonymous then return none
  unless declaredInModules environment targetModules owner do return none
  let some (.inductInfo declaration) := environment.find? owner | return none
  unless declaration.numParams = typeParameterCount do return none
  let expected ← dataTypeNode owner
    ((List.range typeParameterCount).map fun (position : Nat) => node "parameter" [("index", .num position)])
  let some position := parameters.findIdx? (fun parameter => parameter.type == expected)
    | return none
  let methodModule ← declarationModule environment name
  let ownerModule ← declarationModule environment owner
  unless methodModule == ownerModule do
    throw s!"dot-notation method is declared by {methodModule} but its receiver {owner} is declared by {ownerModule}; declare it beside its type"
  pure (some ("receiver", object [("type", .str owner.toString), ("parameter", .num position)]))

private def functionDeclaration (environment : Environment) (targetModules : NameSet) (name : Name)
    (unfoldingEquation? : Option Expr) : Except String Json := do
  let some info := environment.find? name
    | throw s!"declaration {name} is absent from the elaborated environment"
  let .defnInfo declaration := info
    | throw s!"declaration {name} is not a definition"
  match declaration.safety with
  | .safe => pure ()
  | .partial => throw "partial definitions are outside the checked fragment"
  | .unsafe => throw "unsafe definitions are outside the checked fragment"
  unless declaration.levelParams.isEmpty do
    throw "universe polymorphic definitions are outside the checked fragment"
  let signature ← declarationSignature environment targetModules declaration.type
  let typeParameterCount := signature.typeParameterNames.length
  let binderCount := typeParameterCount + signature.parameters.length
  let recursion? := recursionOf? environment name
  let selfReferential := declaration.value.getUsedConstants.contains name
    || (recursionValue? environment name).any (·.getUsedConstants.contains name)
  let (binderNames, body, terminationFields) ←
    match recursion?, unfoldingEquation? with
    | some recursion, some equationType =>
        let argumentFields ← match recursion.argument? with
          | some argument =>
              if argument < typeParameterCount then
                throw s!"{name} recurses on a type parameter, which carries no data"
              let valueArgument := argument - typeParameterCount
              unless valueArgument < signature.parameters.length do
                throw s!"structural recursion argument {argument} is outside {name}'s parameters"
              pure [("argument", Json.num valueArgument)]
          | none => pure []
        let (names, body) ← unfoldingEquationBody name binderCount equationType
        let equationName := name ++ `eq_def
        pure (names, body, [("termination", object ([("kind", .str recursion.kind)]
          ++ argumentFields
          ++ [("group", array (recursion.group.map fun member => .str member.toString)),
              ("equation", .str equationName.toString)]))])
    | some _, none => throw s!"unfolding theorem for {name} is unavailable"
    | none, _ =>
        if selfReferential then
          throw "recursion Lean established by neither structural nor well-founded means is outside the checked fragment"
        let (names, body) ← peelBinderNames binderCount declaration.value
        pure (names, body, [])
  let valueNames := binderNames.drop typeParameterCount
  for binderName in valueNames do
    ensureBindingIdentifier binderName.toString "parameter name"
  let parameters := List.zipWith (fun (parameter : Parameter) (binderName : Name) =>
    object [("name", .str binderName.toString), ("type", parameter.type)])
    signature.parameters valueNames
  let namedParameters := List.zipWith
    (fun (parameter : Parameter) (binderName : Name) => { parameter with name := binderName.toString })
    signature.parameters valueNames
  let receiverFields ←
    match ← receiverField? environment targetModules name typeParameterCount namedParameters with
    | some field => pure [field]
    | none => pure []
  let context : Context :=
    { environment, targetModules, typeParameters := typeParameterCount,
      valueDepth := signature.parameters.length }
  pure (node "function" ([
    ("name", .str name.toString),
    ← declarationModuleField environment name,
    namespaceField name,
    typeParameterField signature.typeParameterNames,
    ("parameters", array parameters),
    ("result", signature.result)
  ] ++ receiverFields ++ terminationFields ++ [
    ("body", ← expressionNode context true body)
  ] ++ documentationFields environment name))

/--
What a declaration's own text depends on. A recursive definition is read through its unfolding
theorem, so its dependencies are the ones its own body names, not the `brecOn` or
`WellFounded.fix` scaffolding the compiler built to justify it.
-/
private def declarationDependencies (environment : Environment) (name : Name) : List Name :=
  match environment.find? name with
  | none => []
  | some info =>
      let expressions := match info with
        | .defnInfo declaration =>
            match recursionValue? environment name with
            | some value => [declaration.type, value]
            | none => [declaration.type, declaration.value]
        | .inductInfo declaration => declaration.type :: declaration.ctors.filterMap fun constructorName =>
            match environment.find? constructorName with
            | some constructor => some constructor.type
            | none => none
        | _ => []
      expressions.flatMap (fun expression => expression.getUsedConstants.toList)
        |>.toArray
        |>.qsort nameTextLt
        |>.toList

private def localDependencies (environment : Environment) (targetModules : NameSet) (name : Name) : List Name :=
  (declarationDependencies environment name).filter (declaredInModules environment targetModules)

/--
Whether the executable form of a constant the compiler READ differs from its definition. The audit
applies to the target module closure, which is the code this compiler lowers: a constant outside it
is a runtime boundary whose TypeScript image is fixed by the compiler's own mapping, so no Lean-side
metadata about its executable form can change what is generated for it.
-/
private def executableMetadataDiagnostic? (environment : Environment) (name : Name) : Option String :=
  if Lean.isNoncomputable environment name then
    some "noncomputable declarations are outside the checked fragment"
  else if let some replacement := Compiler.getImplementedBy? environment name then
    some s!"implemented_by replacement {replacement} is outside the checked fragment"
  else if (Lean.getExternAttrData? environment name).isSome then
    some "extern declarations are outside the checked fragment"
  else if (Compiler.CSimp.ext.getState environment).map.find? name |>.isSome then
    some "compiler simplification replacements are outside the checked fragment"
  else
    none

/--
The only axioms an emitted declaration may rest on. These three are Lean's own logical axioms, which
every proof in the standard library already uses; anything else is an assumption this compiler did
not read, and `sorryAx` is an admitted goal masquerading as one.
-/
private def admittedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/--
Refuses an emitted declaration, or the unfolding proof its body was read from, that depends on an
axiom outside the allowlist. A `sorry` anywhere in a termination proof reaches here as `sorryAx`,
so a recursive definition whose measure was admitted rather than proved is refused by name.
-/
private def ensureAdmittedAxioms (name : Name) (role : String) : CoreM Unit := do
  for axiomName in ← Lean.collectAxioms name do
    if axiomName == ``sorryAx then
      throwError "{name}: its {role} depends on sorry, so its proof was admitted rather than checked"
    unless admittedAxioms.contains axiomName do
      throwError "{name}: its {role} depends on the axiom {axiomName}, which is outside the checked fragment"

private structure ClosureEntry where
  name : Name
  module : String
  role : String
  reason : String

private def closureEntryJson (entry : ClosureEntry) : Json :=
  object [
    ("declaration", .str entry.name.toString),
    ("module", .str entry.module),
    ("role", .str entry.role),
    ("reason", .str entry.reason)
  ]

private def moduleText (environment : Environment) (name : Name) : String :=
  match declarationModule? environment name with
  | some moduleName => moduleName.toString
  | none => ""

/--
What the compiler did with one reachable constant. A constant outside the frozen target closure is
a runtime boundary: its TypeScript image is fixed by the type mapping rather than lowered from its
Lean definition. Inside the closure, a constant is either emitted or erased scaffolding.

`viaScaffolding` records that the walk only reached this constant through something already erased,
which is how Lean's generated eliminators and their helpers are reached: nothing an emitted
declaration names directly can arrive that way. A constant the compiler can neither emit nor
account for is refused by name rather than dropped silently.
-/
private def classifyConstant (environment : Environment) (targetModules : NameSet) (emitted : NameSet)
    (name : Name) (info : ConstantInfo) (viaScaffolding : Bool) : Except String ClosureEntry := do
  let module := moduleText environment name
  unless declaredInModules environment targetModules name do
    return { name, module, role := "runtime-boundary",
             reason := "constant outside the target module closure; its TypeScript image is fixed by the type mapping" }
  if let some diagnostic := executableMetadataDiagnostic? environment name then
    throw s!"{name}: {diagnostic}"
  if emitted.contains name then
    return { name, module, role := "emitted", reason := "" }
  let reason ← match info with
    | .ctorInfo _ => pure "constructor lowered with its inductive type"
    | .recInfo _ => pure "recursor"
    | .thmInfo _ => pure "proof"
    | .axiomInfo _ => throw s!"{name}: axioms are outside the checked fragment"
    | .opaqueInfo _ => throw s!"{name}: opaque or partial definitions are outside the checked fragment"
    | .quotInfo _ => throw s!"{name}: quotient primitives are outside the checked fragment"
    | .defnInfo _ =>
        if (Meta.getMatcherInfoCore? environment name).isSome then
          pure "match auxiliary inlined at its application sites"
        else if (environment.getProjectionStructureName? name).isSome then
          pure "structure projection lowered as field access"
        else if viaScaffolding then
          pure "generated helper reached only through erased scaffolding"
        else
          throw s!"{name}: reachable definition was neither emitted nor erased"
    | .inductInfo _ =>
        if viaScaffolding then
          pure "generated type reached only through erased scaffolding"
        else
          throw s!"{name}: reachable inductive type was neither emitted nor erased"
  pure { name, module, role := "erased", reason }

/--
Every constant the emitted program depends on, transitively and across the boundary of the target
module. The same walk records what happened to each constant, so the closure is accounted for
completely instead of only where it reached a generated file.
-/
private partial def classifyClosureAux (environment : Environment) (targetModules : NameSet)
    (emitted : NameSet) (pending : List (Name × Bool)) (seen : NameSet) (entries : List ClosureEntry) :
    Except String (List ClosureEntry) := do
  match pending with
  | [] => pure entries
  | (name, viaScaffolding) :: rest =>
      if seen.contains name then classifyClosureAux environment targetModules emitted rest seen entries
      else
        let some info := environment.find? name
          | throw s!"{name}: declaration is absent from the elaborated environment"
        let entry ← classifyConstant environment targetModules emitted name info viaScaffolding
        let dependencies := match info with
          | .ctorInfo constructor => constructor.induct :: declarationDependencies environment name
          | .inductInfo declaration => declaration.ctors ++ declarationDependencies environment name
          | .defnInfo _ =>
              match environment.getProjectionStructureName? name with
              | some structureName => structureName :: declarationDependencies environment name
              | none => declarationDependencies environment name
          | _ => declarationDependencies environment name
        let erased := entry.role != "emitted"
        classifyClosureAux environment targetModules emitted
          (dependencies.map (fun dependency => (dependency, erased)) ++ rest) (seen.insert name)
          (entry :: entries)

private def classifyClosure (environment : Environment) (targetModules : NameSet) (emitted : NameSet)
    (roots : List Name) : Except String (List ClosureEntry) := do
  let entries ← classifyClosureAux environment targetModules emitted (roots.map (·, false)) {} []
  pure (entries.toArray.qsort (fun left right => nameTextLt left.name right.name) |>.toList)

private partial def collectDeclarationsAux (environment : Environment) (targetModules : NameSet)
    (pending : List Name) (seen : NameSet) (ordered : List Name) :
    Except String (List Name) := do
  match pending with
  | [] => pure ordered.reverse
  | name :: rest =>
      if seen.contains name || !declaredInModules environment targetModules name then
        collectDeclarationsAux environment targetModules rest seen ordered
      else
        let some info := environment.find? name
          | throw s!"declaration {name} is absent from the elaborated environment"
        let seen := seen.insert name
        match info with
        | .ctorInfo constructor =>
            collectDeclarationsAux environment targetModules (constructor.induct :: rest) seen ordered
        | .defnInfo _ =>
            if (Meta.getMatcherInfoCore? environment name).isSome then
              -- Matchers are inlined at their application sites; the discriminant type and
              -- every value the alternatives use are reached through the enclosing definition.
              collectDeclarationsAux environment targetModules rest seen ordered
            else if let some structureName := environment.getProjectionStructureName? name then
              collectDeclarationsAux environment targetModules (structureName :: rest) seen ordered
            else
              collectDeclarationsAux environment targetModules
                (localDependencies environment targetModules name ++ rest) seen (name :: ordered)
        | .inductInfo _ =>
            collectDeclarationsAux environment targetModules
              (localDependencies environment targetModules name ++ rest) seen (name :: ordered)
        | .recInfo _ => collectDeclarationsAux environment targetModules rest seen ordered
        | .opaqueInfo _ =>
            throw s!"{name}: opaque or partial definitions are outside the checked fragment"
        | _ => throw s!"declaration dependency {name} is outside the checked fragment"

private def collectDeclarations (environment : Environment) (targetModules : NameSet)
    (roots : List Name) : Except String (List Name) :=
  collectDeclarationsAux environment targetModules roots {} []

/--
`entryModule` is the module Lake builds and the driver imports; `targetModules` is that module's
frozen transitive import closure. A root may be declared by any module in the closure, so one
compilation exports a whole Lean package rather than one file's worth of it.
-/
private def exportPackage (entryModule : Name) (targetModules : NameSet) (roots : List Name) : CoreM Json := do
  let environment ← getEnv
  unless targetModules.contains entryModule do
    throwError "entry module {entryModule} is outside the frozen target module closure"
  for root in roots do
    unless declaredInModules environment targetModules root do
      throwError "exported declaration {root} is outside the frozen target module closure"
  let names ← match collectDeclarations environment targetModules roots with
    | .ok value => pure value
    | .error message => throwError message
  let names := names.toArray.qsort nameTextLt |>.toList
  let emitted := names.foldl (fun set name => set.insert name) ({} : NameSet)
  let closure ← match classifyClosure environment targetModules emitted roots with
    | .ok value => pure value
    | .error message => throwError message
  for entry in closure do
    unless entry.role == "emitted" || !emitted.contains entry.name do
      throwError "{entry.name}: emitted declaration was classified as {entry.role}"
  for name in names do
    unless closure.any (fun entry => entry.name == name) do
      throwError "{name}: emitted declaration is absent from the classified closure"
  match ensureDistinctDeclarationNames names with
  | .ok () => pure ()
  | .error message => throwError message
  for name in names do
    match ensureDeclarationName name with
    | .ok () => pure ()
    | .error message => throwError "{name}: {message}"
  -- Realizing the unfolding theorem type-checks it, so a recursive body is exported only behind a
  -- kernel-accepted equation.
  let mut unfoldingEquations : Std.HashMap Name Expr := {}
  for name in names do
    if (recursionOf? environment name).isSome then
      let equation ← Meta.MetaM.run' do
        let some equationName ← Meta.getUnfoldEqnFor? name | pure none
        pure ((← getEnv).find? equationName |>.map (fun info => (equationName, info.type)))
      match equation with
      | some (equationName, equationType) =>
          ensureAdmittedAxioms equationName "unfolding theorem"
          unfoldingEquations := unfoldingEquations.insert name equationType
      | none => throwError "{name}: no unfolding theorem is available for its recursion"
  for name in names do
    ensureAdmittedAxioms name "definition"
  let mut declarations := []
  for name in names do
    let some info := environment.find? name
      | throwError "declaration {name} disappeared from the environment"
    let encoded ← match info with
      | .inductInfo _ => pure (dataDeclaration environment targetModules name)
      | .defnInfo _ =>
          pure (functionDeclaration environment targetModules name unfoldingEquations[name]?)
      | _ => pure (.error s!"declaration {name} has an unsupported kind")
    match encoded with
    | .ok value => declarations := value :: declarations
    | .error message => throwError "{name}: {message}"
  -- Every emitted declaration carries the range Lean recorded for it, so a generated file maps
  -- back to the exact source text the kernel accepted.
  let mut spans : Std.HashMap Name Json := {}
  for name in names do
    let some ranges ← Lean.findDeclarationRanges? name
      | throwError "{name}: no source range is recorded for its declaration"
    spans := spans.insert name (object [
      ("startLine", .num ranges.range.pos.line),
      ("startColumn", .num ranges.range.pos.column),
      ("endLine", .num ranges.range.endPos.line),
      ("endColumn", .num ranges.range.endPos.column)
    ])
  let mut spanned := []
  for (name, declaration) in List.zip names declarations.reverse do
    let some span := spans[name]?
      | throwError "{name}: source range disappeared before encoding"
    spanned := (match declaration with
      | .obj fields => Json.obj (fields.insert "span" span)
      | other => other) :: spanned
  pure (object [
    ("schemaVersion", .num 1),
    ("fragmentVersion", .str fragmentVersion),
    ("roots", array (roots.map (fun name => .str name.toString))),
    ("closure", array (closure.map closureEntryJson)),
    ("declarations", array spanned.reverse)
  ])

open Lean Elab Command in
syntax (name := tsleanExport) "#tslean_export " str str str+ : command

open Lean Elab Command in
elab_rules : command
  | `(#tslean_export $entryModule:str $targetModuleNames:str $roots:str*) => do
      let entryModule := entryModule.raw.isStrLit?.getD ""
      let targetModuleNames := targetModuleNames.raw.isStrLit?.getD ""
      let roots := roots.toList.map (fun root => root.raw.isStrLit?.getD "")
      let targetModules := targetModuleNames.splitOn "\n" |>.filter (!·.isEmpty) |>.map String.toName
        |>.foldl (fun modules name => modules.insert name) {}
      if entryModule.isEmpty || targetModules.isEmpty || roots.isEmpty || roots.any String.isEmpty then
        throwError "#tslean_export requires an entry module, target module closure, and at least one declaration"
      let result ← try
        let package ← liftCoreM (exportPackage entryModule.toName targetModules (roots.map String.toName))
        pure (object [("ok", .bool true), ("package", package)])
      catch error =>
        let message ← error.toMessageData.toString
        pure (object [("ok", .bool false), ("error", .str message)])
      liftIO (IO.println result.compress)

end TSLean.LeanToTypeScript
