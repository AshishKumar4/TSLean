import Lean

namespace TSLean.LeanToTypeScript

open Lean

private def fragmentVersion := "tslean-structural-first-order-v4"

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

/-- Emitted names have to be distinct inside one generated module, not across the package: two
Lean modules may each declare `Config`, and each keeps its own file. -/
private def ensureDistinctDeclarationNames (environment : Environment) (names : List Name) :
    Except String Unit := do
  let mut seen : Std.HashSet String := {}
  for name in names do
    let moduleName ← declarationModule environment name
    let localName := name.getString!
    let key := s!"{moduleName}|{localName}"
    if seen.contains key then
      throw s!"{name}: emitted declaration name {localName} collides with another declaration in module {moduleName}"
    seen := seen.insert key

private def appView : Expr → Expr × List Expr
  | .app function argument =>
      let (head, arguments) := appView function
      (head, arguments ++ [argument])
  | expression => (expression, [])

private def containsBoundVariable : Expr → Bool
  | .bvar _ => true
  | .app function argument => containsBoundVariable function || containsBoundVariable argument
  | .lam _ type body _ | .forallE _ type body _ =>
      containsBoundVariable type || containsBoundVariable body
  | .letE _ type value body _ =>
      containsBoundVariable type || containsBoundVariable value || containsBoundVariable body
  | .mdata _ expression => containsBoundVariable expression
  | .proj _ _ subject => containsBoundVariable subject
  | _ => false

private def ordinaryDataInfo (environment : Environment) (targetModules : NameSet) (name : Name) :
    Except String InductiveVal := do
  unless declaredInModules environment targetModules name do
    throw s!"data type {name} is outside the frozen target module closure"
  let some (.inductInfo declaration) := environment.find? name
    | throw s!"type {name} is not an inductive data type"
  unless declaration.type.consumeMData == .sort (.succ .zero) do
    throw s!"data type {name} must be declared in Type 0"
  pure declaration

private partial def typeNode (environment : Environment) (targetModules : NameSet)
    (expression : Expr) : Except String Json := do
  let expression := expression.consumeMData
  let (head, arguments) := appView expression
  match head with
  | .const ``Bool _ =>
      unless arguments.isEmpty do throw "Bool type received unexpected arguments"
      pure (node "boolean")
  | .const ``Option _ =>
      let [inner] := arguments | throw "Option type must have exactly one argument"
      let (innerHead, _) := appView inner
      if innerHead.isConstOf ``Option then
        throw "nested Option collapses under the v1 TypeScript representation"
      pure (node "option" [("inner", ← typeNode environment targetModules inner)])
  | .const name _ =>
      unless arguments.isEmpty do
        throw s!"generic type {name} is outside {fragmentVersion}"
      let _ ← ordinaryDataInfo environment targetModules name
      pure (node "named" [("name", .str name.toString)])
  | .forallE _ _ _ _ => throw "higher-order values are outside the checked fragment"
  | _ => throw s!"unsupported type expression {expression}"

private structure Parameter where
  name : String
  type : Json

private partial def parametersAndResult (environment : Environment) (targetModules : NameSet)
    (expression : Expr) :
    Except String (List Parameter × Json) := do
  match expression.consumeMData with
  | .forallE binderName binderType body binderInfo =>
      unless binderInfo == .default do
        throw "implicit and instance parameters are outside the checked fragment"
      if binderType.isForall then
        throw "higher-order parameters are outside the checked fragment"
      let parameterType ← typeNode environment targetModules binderType
      let (parameters, result) ← parametersAndResult environment targetModules body
      pure ({ name := binderName.toString, type := parameterType } :: parameters, result)
  | result =>
      if containsBoundVariable result then
        throw "dependent result types are outside the checked fragment"
      pure ([], ← typeNode environment targetModules result)

/--
The fields a constructor carries, read from its own declared type. A field whose type mentions an
earlier field is refused by `typeNode`, so a constructor is admitted only when its fields are
independent first-order data.
-/
private def constructorFields (environment : Environment) (targetModules : NameSet)
    (constructorName : Name) : Except String (List Parameter) := do
  let some (.ctorInfo constructor) := environment.find? constructorName
    | throw s!"constructor {constructorName} is absent from the elaborated environment"
  unless constructor.numParams = 0 do
    throw s!"constructor {constructorName} belongs to a parameterized data type"
  let (fields, _) ← parametersAndResult environment targetModules constructor.type
  unless fields.length = constructor.numFields do
    throw s!"constructor {constructorName} does not expose its fields as first-order parameters"
  let mut seen : Std.HashSet String := {}
  for field in fields do
    ensureBindingIdentifier field.name "constructor field"
    if seen.contains field.name then
      throw s!"constructor {constructorName} declares field {field.name} more than once"
    seen := seen.insert field.name
  pure fields

private partial def lambdaBody (expression : Expr) : List String × Expr :=
  match expression.consumeMData with
  | .lam binderName _ body _ =>
      let (names, body) := lambdaBody body
      (binderName.toString :: names, body)
  | body => ([], body)

private def projectionField (environment : Environment) (typeName : Name) (index : Nat) :
    Except String Name := do
  let fields := getStructureFields environment typeName
  let some field := fields[index]?
    | throw s!"structure {typeName} has no field at index {index}"
  pure field

private def boolEqualityOperands? (expression : Expr) : Option (Expr × Expr) := do
  let (head, arguments) := appView expression.consumeMData
  let .const name _ := head | none
  guard (name == ``Eq)
  let [type, left, right] := arguments | none
  guard (type.isConstOf ``Bool)
  pure (left, right)

private def isMatchingBoolDecision (condition decision : Expr) : Bool :=
  match boolEqualityOperands? condition with
  | none => false
  | some (left, right) =>
      let (head, arguments) := appView decision.consumeMData
      match head with
      | .const name _ =>
          match arguments with
          | [candidateLeft, candidateRight] =>
              name == ``instDecidableEqBool && candidateLeft == left && candidateRight == right
          | _ => false
      | _ => false

/--
Reads which constructor each alternative of a `match` auxiliary matcher decides, from the
matcher's own declared type. Alternative `i` is typed `motive (Ctor f₀ … fₙ₋₁)`, behind its own
declared parameters, so the constructor is recovered structurally instead of assuming the source
arm order. The pattern has to apply the constructor to exactly its own binders in declaration
order: a nested or repeated pattern is refused rather than flattened.
-/
private def matcherAlternativeConstructors (environment : Environment) (matcherName : Name)
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
        let (head, arguments) := appView applied.consumeMData
        let .bvar _ := head
          | throw s!"matcher {matcherName} alternative is not an application of its motive"
        let [pattern] := arguments
          | throw s!"matcher {matcherName} alternative does not decide exactly one discriminant"
        let (patternHead, patternArguments) := appView pattern.consumeMData
        let .const constructorName _ := patternHead
          | throw s!"matcher {matcherName} alternative pattern is not a constructor"
        let expected := (List.range patternArguments.length).map fun position =>
          Expr.bvar (patternArguments.length - 1 - position)
        unless patternArguments.map Expr.consumeMData == expected do
          throw s!"matcher {matcherName} alternative {index} does not bind each constructor field exactly once"
        constructors := constructorName :: constructors
        telescope := body
    | _ => throw s!"matcher {matcherName} does not expose the expected alternative telescope"
  pure constructors.reverse

private def alternativeIndexOf (constructors : List Name) (constructorName : Name) : Option Nat :=
  let rec search (remaining : List Name) (index : Nat) : Option Nat :=
    match remaining with
    | [] => none
    | head :: rest => if head == constructorName then some index else search rest (index + 1)
  search constructors 0

private def enumConstructors (environment : Environment) (targetModules : NameSet) (name : Name) :
    Except String (List Name) := do
  let declaration ← ordinaryDataInfo environment targetModules name
  unless declaration.numParams = 0 && declaration.numIndices = 0 do
    throw s!"generic or indexed data type {name} cannot be matched in this fragment version"
  if isStructure environment name then
    throw s!"structure {name} cannot be matched in this fragment version"
  if declaration.ctors.isEmpty then
    throw s!"inductive data type {name} has no constructors"
  pure declaration.ctors

private partial def expressionNode (environment : Environment) (targetModules : NameSet)
    (expression : Expr) (allowLeadingLet : Bool := false) : Except String Json := do
  let expression := expression.consumeMData
  match expression with
  | .bvar index => pure (node "variable" [("index", .num index)])
  | .letE binderName _ value body _ =>
      unless allowLeadingLet do
        throw "nested let expressions are outside this fragment version"
      ensureAsciiIdentifier binderName.toString "let binder"
      pure (node "let" [
        ("name", .str binderName.toString),
        ("value", ← expressionNode environment targetModules value),
        ("body", ← expressionNode environment targetModules body true)
      ])
  | .proj typeName index subject =>
      let field ← projectionField environment typeName index
      ensureAsciiIdentifier field.getString! "structure field"
      pure (node "field" [
        ("target", ← expressionNode environment targetModules subject),
        ("field", .str field.getString!)
      ])
  | .fvar _ => throw "free variables are outside the checked fragment"
  | .mvar _ => throw "metavariables are outside the checked fragment"
  | .sort _ | .forallE _ _ _ _ | .lam _ _ _ _ =>
      throw "type-level and higher-order expressions are outside the checked fragment"
  | .lit _ => throw "numeric and string literals are outside this fragment version"
  | _ =>
      let (head, arguments) := appView expression
      let .const name _ := head
        | throw s!"unsupported application head {head}"
      if name == ``Bool.true then pure (node "boolean" [("value", .bool true)])
      else if name == ``Bool.false then pure (node "boolean" [("value", .bool false)])
      else if name == ``ite then
        let [_, condition, decision, consequent, alternate] := arguments
          | throw "ite received an unsupported elaborated shape"
        unless isMatchingBoolDecision condition decision do
          throw "only conditions decided by Bool equality are admitted in this fragment version"
        pure (node "if" [
          ("condition", ← expressionNode environment targetModules condition),
          ("consequent", ← expressionNode environment targetModules consequent),
          ("alternate", ← expressionNode environment targetModules alternate)
        ])
      else if name == ``Eq then
        let [type, left, right] := arguments | throw "Eq received an unsupported elaborated shape"
        unless type.isConstOf ``Bool do
          throw "only Bool equality is admitted in this fragment version"
        pure (node "equals" [
          ("left", ← expressionNode environment targetModules left),
          ("right", ← expressionNode environment targetModules right)
        ])
      else if name == ``Bool.and || name == ``Bool.or then
        let [left, right] := arguments | throw s!"{name} received an unsupported elaborated shape"
        pure (node (if name == ``Bool.and then "and" else "or") [
          ("left", ← expressionNode environment targetModules left),
          ("right", ← expressionNode environment targetModules right)
        ])
      else if name == ``Bool.not then
        let [operand] := arguments | throw "Bool.not received an unsupported elaborated shape"
        pure (node "not" [("operand", ← expressionNode environment targetModules operand)])
      else if name == ``Option.some then
        let [_, value] := arguments | throw "Option.some received an unsupported elaborated shape"
        pure (node "some" [("value", ← expressionNode environment targetModules value)])
      else if name == ``Option.none then
        let [_] := arguments | throw "Option.none received an unsupported elaborated shape"
        pure (node "none")
      else if let some matcherInfo := Meta.getMatcherInfoCore? environment name then
        unless declaredInModules environment targetModules name do
          throw s!"matcher {name} is outside the frozen target module closure"
        unless matcherInfo.numParams = 0 do
          throw "matchers over parameterized or indexed discriminants are outside the checked fragment"
        unless matcherInfo.numDiscrs = 1 do
          throw "matches on more than one discriminant are outside this fragment version"
        unless matcherInfo.getNumDiscrEqs = 0 do
          throw "matches binding discriminant equations are outside the checked fragment"
        -- Lean 4.16 has no representation for overlapping match alternatives, so the shape check
        -- below is what refuses an alternative carrying anything beyond its constructor fields.
        unless arguments.length = matcherInfo.arity do
          throw s!"matcher {name} received an unsupported elaborated shape"
        let some motive := arguments[matcherInfo.getMotivePos]?
          | throw s!"matcher {name} received no motive"
        let .lam _ discriminantType motiveBody _ := motive.consumeMData
          | throw s!"matcher {name} motive is not a discriminant abstraction"
        if containsBoundVariable motiveBody then
          throw "dependent match result types are outside the checked fragment"
        let .const dataName _ := discriminantType.consumeMData
          | throw s!"matcher {name} discriminant type is not an inductive data type"
        let constructors ← enumConstructors environment targetModules dataName
        let alternatives ← matcherAlternativeConstructors environment name matcherInfo
        unless alternatives.length = constructors.length do
          throw s!"match on {dataName} does not decide every constructor exactly once"
        let some discriminant := arguments[matcherInfo.getFirstDiscrPos]?
          | throw s!"matcher {name} received no discriminant"
        let mut cases := []
        for constructorName in constructors do
          let some alternativeIndex := alternativeIndexOf alternatives constructorName
            | throw s!"match on {dataName} does not decide {constructorName}"
          let some (.ctorInfo constructorInfo) := environment.find? constructorName
            | throw s!"constructor {constructorName} is absent from the elaborated environment"
          let some alternativeParameters := matcherInfo.altNumParams[alternativeIndex]?
            | throw s!"matcher {name} has no alternative {alternativeIndex}"
          -- A nullary alternative is thunked behind one `Unit` binder; every other alternative
          -- abstracts exactly its constructor's fields. Any other parameter count means the
          -- alternative carries discriminant equations or overlap assumptions.
          let hasUnitThunk := constructorInfo.numFields = 0
          unless alternativeParameters = constructorInfo.numFields + (if hasUnitThunk then 1 else 0) do
            throw s!"matcher {name} alternative {alternativeIndex} carries parameters beyond its constructor fields"
          let some encoded := arguments[matcherInfo.getFirstAltPos + alternativeIndex]?
            | throw s!"matcher {name} received no alternative for {constructorName}"
          -- Lean thunks a nullary alternative behind an unused `Unit` binder; the fragment
          -- admits it only when the alternative genuinely ignores that binder. A
          -- payload-carrying alternative instead abstracts its constructor's fields in
          -- declaration order, so peeling those binders leaves the arm's own de Bruijn indices
          -- pointing at the fields, innermost binder last.
          let value ← if hasUnitThunk then
              match encoded.consumeMData with
              | .lam _ _ thunkBody _ =>
                  if thunkBody.hasLooseBVar 0 then
                    throw s!"matcher {name} alternative uses its unit thunk binder"
                  pure (thunkBody.lowerLooseBVars 1 1)
              | _ => throw s!"matcher {name} thunked alternative is not an abstraction"
            else
              let mut body := encoded
              for _ in [0 : constructorInfo.numFields] do
                match body.consumeMData with
                | .lam _ _ inner _ => body := inner
                | _ => throw s!"matcher {name} alternative does not abstract its constructor fields"
              pure body
          ensureAsciiIdentifier constructorName.getString! "constructor name"
          cases := object [
            ("constructor", .str constructorName.getString!),
            ("value", ← expressionNode environment targetModules value)
          ] :: cases
        pure (node "match" [
          ("type", .str dataName.toString),
          ("scrutinee", ← expressionNode environment targetModules discriminant),
          ("cases", array cases.reverse)
        ])
      else
        let some info := environment.find? name
          | throw s!"constant {name} is absent from the elaborated environment"
        if let some projection := environment.getProjectionFnInfo? name then
          let targetIndex := projection.numParams
          let some target := arguments[targetIndex]?
            | throw s!"projection {name} received an unsupported elaborated shape"
          ensureAsciiIdentifier name.getString! "structure field"
          pure (node "field" [
            ("target", ← expressionNode environment targetModules target),
            ("field", .str name.getString!)
          ])
        else match info with
        | .ctorInfo constructor =>
            if isStructure environment constructor.induct then
              let fields := getStructureFields environment constructor.induct
              unless arguments.length = fields.size do
                throw s!"structure constructor {name} received an unsupported elaborated shape"
              let mut encodedFields := []
              for (field, value) in fields.toList.zip arguments do
                ensureAsciiIdentifier field.getString! "structure field"
                encodedFields := object [
                  ("name", .str field.getString!),
                  ("value", ← expressionNode environment targetModules value)
                ] :: encodedFields
              pure (node "record" [
                ("type", .str constructor.induct.toString),
                ("fields", array encodedFields.reverse)
              ])
            else
              let fields ← constructorFields environment targetModules name
              unless arguments.length = fields.length do
                throw s!"constructor {name} received an unsupported elaborated shape"
              ensureAsciiIdentifier name.getString! "constructor name"
              pure (node "variant" [
                ("type", .str constructor.induct.toString),
                ("name", .str name.getString!),
                ("arguments", array (← arguments.mapM (expressionNode environment targetModules)))
              ])
        | .defnInfo declaration =>
            unless declaredInModules environment targetModules name do
              throw s!"function {name} is outside the frozen target module closure"
            let (parameters, _) ← parametersAndResult environment targetModules declaration.type
            unless arguments.length = parameters.length do
              throw s!"function {name} received an unsupported elaborated shape"
            pure (node "call" [
              ("function", .str name.toString),
              ("arguments", array (← arguments.mapM (expressionNode environment targetModules)))
            ])
        | _ => throw s!"constant {name} is outside the checked fragment"

private def fieldDeclaration (environment : Environment) (targetModules : NameSet)
    (structureName fieldName : Name) :
    Except String Json := do
  let some fieldInfo := getFieldInfo? environment structureName fieldName
    | throw s!"structure field {structureName}.{fieldName} has no projection metadata"
  let some info := environment.find? fieldInfo.projFn
    | throw s!"structure field projection {fieldInfo.projFn} is absent from the environment"
  ensureAsciiIdentifier fieldName.getString! "structure field"
  let (_, fieldType) ← parametersAndResult environment targetModules info.type
  pure (object ([("name", .str fieldName.getString!), ("type", fieldType)]
    ++ documentationFields environment fieldInfo.projFn))

private def dataDeclaration (environment : Environment) (targetModules : NameSet)
    (name : Name) : Except String Json := do
  let declaration ← ordinaryDataInfo environment targetModules name
  unless declaration.numParams = 0 && declaration.numIndices = 0 do
    throw s!"generic or indexed data type {name} is outside this fragment version"
  if isStructure environment name then
    let fields := getStructureFields environment name
    pure (node "record" ([
      ("name", .str name.toString),
      ← declarationModuleField environment name,
      ("fields", array (← fields.toList.mapM (fieldDeclaration environment targetModules name)))
    ] ++ documentationFields environment name))
  else
    unless !declaration.ctors.isEmpty do
      throw s!"inductive data type {name} has no constructors"
    let mut constructors := []
    for constructorName in declaration.ctors do
      ensureAsciiDeclarationName constructorName
      let fields ← constructorFields environment targetModules constructorName
      let encodedFields := fields.map fun field =>
        object [("name", .str field.name), ("type", field.type)]
      constructors := object ([
        ("name", .str constructorName.getString!),
        ("fields", array encodedFields)
      ] ++ documentationFields environment constructorName) :: constructors
    pure (node "enum" ([
      ("name", .str name.toString),
      ← declarationModuleField environment name,
      ("constructors", array constructors.reverse)
    ] ++ documentationFields environment name))

/--
The parameter Lean itself proved a definition recurses structurally on, read from the elaborator's
own record. A recursive definition with no such record used well-founded recursion or none at all,
and is refused: its termination argument does not lower to a TypeScript call.
-/
private def structuralRecursionArgument? (environment : Environment) (name : Name) : Option Nat :=
  (Lean.Elab.Structural.eqnInfoExt.find? environment name).map (·.recArgPos)

/-- Mutual recursion has no single decreasing argument to lower, so it is refused by name. -/
private def isMutuallyRecursive (environment : Environment) (name : Name) : Bool :=
  (Lean.Elab.Structural.eqnInfoExt.find? environment name).any (·.declNames.size > 1)

/-- The pre-compilation body of a structurally recursive definition, which still names itself. -/
private def structuralRecursionValue? (environment : Environment) (name : Name) : Option Expr :=
  (Lean.Elab.Structural.eqnInfoExt.find? environment name).map (·.value)

/--
Reads a structurally recursive definition's body out of its kernel-checked unfolding theorem
`f.eq_def : ∀ xs, f xs = body`, rather than out of the `brecOn` term the compiler built or the
elaborator's own record of the body. The theorem is proved by the kernel, so the exported body is
equal to the definition by the same authority that accepted the definition.
-/
private def unfoldingEquationBody (name : Name) (parameterCount : Nat) (equationType : Expr) :
    Except String (List String × Expr) := do
  let mut telescope := equationType
  let mut names := []
  for _ in [0 : parameterCount] do
    match telescope.consumeMData with
    | .forallE binderName _ body _ =>
        names := binderName.toString :: names
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
  let expected := (List.range parameterCount).map fun position => Expr.bvar (parameterCount - 1 - position)
  unless leftArguments.map Expr.consumeMData == expected do
    throw s!"unfolding theorem for {name} does not apply it to its own parameters"
  pure (names.reverse, right)

private def functionDeclaration (environment : Environment) (targetModules : NameSet) (name : Name)
    (unfoldingEquation? : Option Expr) :
    Except String Json := do
  let some info := environment.find? name
    | throw s!"declaration {name} is absent from the elaborated environment"
  let .defnInfo declaration := info
    | throw s!"declaration {name} is not a definition"
  match declaration.safety with
  | .safe => pure ()
  | .partial => throw "partial definitions are outside the checked fragment"
  | .unsafe => throw "unsafe definitions are outside the checked fragment"
  let (parameters, result) ← parametersAndResult environment targetModules declaration.type
  let recursionArgument? := structuralRecursionArgument? environment name
  let selfReferential := declaration.value.getUsedConstants.contains name
    || (structuralRecursionValue? environment name).any (·.getUsedConstants.contains name)
  let (lambdaNames, body, recursionFields) ←
    match recursionArgument?, unfoldingEquation? with
    | some argument, some equationType =>
        if isMutuallyRecursive environment name then
          throw "mutual recursion is outside the checked fragment"
        unless argument < parameters.length do
          throw s!"structural recursion argument {argument} is outside {name}'s parameters"
        let (names, body) ← unfoldingEquationBody name parameters.length equationType
        pure (names, body, [("recursion", object [("argument", .num argument)])])
    | some _, none => throw s!"unfolding theorem for {name} is unavailable"
    | none, _ =>
        if selfReferential then
          throw "recursion Lean did not establish structurally is outside the checked fragment"
        let (names, body) := lambdaBody declaration.value
        pure (names, body, [])
  unless lambdaNames.length = parameters.length do
    throw "definition value does not expose the declared first-order parameters"
  for lambdaName in lambdaNames do
    ensureAsciiIdentifier lambdaName "parameter name"
  let parameters := List.zipWith (fun parameter lambdaName =>
    object [("name", .str lambdaName), ("type", parameter.type)]) parameters lambdaNames
  pure (node "function" ([
    ("name", .str name.toString),
    ← declarationModuleField environment name,
    ("parameters", array parameters),
    ("result", result)
  ] ++ recursionFields ++ [
    ("body", ← expressionNode environment targetModules body true)
  ] ++ documentationFields environment name))

/--
What a declaration's own text depends on. A structurally recursive definition is read through its
unfolding theorem, so its dependencies are the ones its own body names, not the `brecOn` scaffolding
the compiler built to justify it.
-/
private def declarationDependencies (environment : Environment) (name : Name) : List Name :=
  match environment.find? name with
  | none => []
  | some info =>
      let expressions := match info with
        | .defnInfo declaration =>
            match structuralRecursionValue? environment name with
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
module: a compiler-level replacement anywhere in that closure means the executable Lean differs
from the definitions this compiler read, so the whole closure is audited rather than the local
part of it plus one hop. The same walk records what happened to each constant, so the closure is
accounted for completely instead of only where it reached a generated file.
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
        if let some diagnostic := executableMetadataDiagnostic? environment name then
          throw s!"{name}: {diagnostic}"
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
      if seen.contains name then collectDeclarationsAux environment targetModules rest seen ordered
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
  match ensureDistinctDeclarationNames environment names with
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
    if (structuralRecursionArgument? environment name).isSome then
      let equationType ← Meta.MetaM.run' do
        let some equationName ← Meta.getUnfoldEqnFor? name | pure none
        pure ((← getEnv).find? equationName |>.map ConstantInfo.type)
      match equationType with
      | some equationType => unfoldingEquations := unfoldingEquations.insert name equationType
      | none => throwError "{name}: no unfolding theorem is available for its recursion"
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
      | .obj fields => Json.obj (fields.insert compare "span" span)
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
