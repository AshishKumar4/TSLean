import Lean

namespace TSLean.LeanToTypeScript

open Lean

private def fragmentVersion := "tslean-pure-first-order-v1"

private def array (items : List Json) : Json := .arr items.toArray

private def object (fields : List (String × Json)) : Json := .mkObj fields

private def node (kind : String) (fields : List (String × Json) := []) : Json :=
  object (("kind", .str kind) :: fields)

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

private def ensureDistinctDeclarationNames (names : List Name) : Except String Unit := do
  let mut seen : Std.HashSet String := {}
  for name in names do
    let localName := name.getString!
    if seen.contains localName then
      throw s!"{name}: emitted declaration name {localName} collides with another declaration"
    seen := seen.insert localName

private def declarationModule? (environment : Environment) (name : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? name
  environment.header.moduleNames[index]?

private def declaredInModules (environment : Environment) (modules : NameSet) (name : Name) : Bool :=
  (declarationModule? environment name).any modules.contains

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
              unless arguments.isEmpty do
                throw s!"constructor {name} carries data outside this fragment version"
              ensureAsciiIdentifier name.getString! "constructor name"
              pure (node "variant" [
                ("type", .str constructor.induct.toString),
                ("name", .str name.getString!)
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
  pure (object [("name", .str fieldName.getString!), ("type", fieldType)])

private def dataDeclaration (environment : Environment) (targetModules : NameSet)
    (name : Name) : Except String Json := do
  let declaration ← ordinaryDataInfo environment targetModules name
  unless declaration.numParams = 0 && declaration.numIndices = 0 do
    throw s!"generic or indexed data type {name} is outside this fragment version"
  if isStructure environment name then
    let fields := getStructureFields environment name
    pure (node "record" [
      ("name", .str name.toString),
      ("fields", array (← fields.toList.mapM (fieldDeclaration environment targetModules name)))
    ])
  else
    unless !declaration.ctors.isEmpty do
      throw s!"inductive data type {name} has no constructors"
    let mut constructors := []
    for constructorName in declaration.ctors do
      ensureAsciiDeclarationName constructorName
      let some (.ctorInfo constructor) := environment.find? constructorName
        | throw s!"constructor {constructorName} is absent"
      unless constructor.numFields = 0 do
        throw s!"constructor {constructorName} carries data outside this fragment version"
      constructors := .str constructorName.getString! :: constructors
    pure (node "enum" [
      ("name", .str name.toString),
      ("constructors", array constructors.reverse)
    ])

private def functionDeclaration (environment : Environment) (targetModules : NameSet) (name : Name) :
    Except String Json := do
  let some info := environment.find? name
    | throw s!"declaration {name} is absent from the elaborated environment"
  let .defnInfo declaration := info
    | throw s!"declaration {name} is not a definition"
  match declaration.safety with
  | .safe => pure ()
  | .partial => throw "partial definitions are outside the checked fragment"
  | .unsafe => throw "unsafe definitions are outside the checked fragment"
  if declaration.value.getUsedConstants.contains name then
    throw "recursive definitions are outside this fragment version"
  let (parameters, result) ← parametersAndResult environment targetModules declaration.type
  let (lambdaNames, body) := lambdaBody declaration.value
  unless lambdaNames.length = parameters.length do
    throw "definition value does not expose the declared first-order parameters"
  for lambdaName in lambdaNames do
    ensureAsciiIdentifier lambdaName "parameter name"
  let parameters := List.zipWith (fun parameter lambdaName =>
    object [("name", .str lambdaName), ("type", parameter.type)]) parameters lambdaNames
  pure (node "function" [
    ("name", .str name.toString),
    ("parameters", array parameters),
    ("result", result),
    ("body", ← expressionNode environment targetModules body true)
  ])

private def declarationDependencies (environment : Environment) (name : Name) : List Name :=
  match environment.find? name with
  | none => []
  | some info =>
      let expressions := match info with
        | .defnInfo declaration => [declaration.type, declaration.value]
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

private partial def auditExecutableMetadataAux (environment : Environment) (targetModules : NameSet)
    (pending : List Name) (seen : NameSet) : Except String Unit := do
  match pending with
  | [] => pure ()
  | name :: rest =>
      if seen.contains name then auditExecutableMetadataAux environment targetModules rest seen
      else
        let some info := environment.find? name
          | throw s!"{name}: declaration is absent from the elaborated environment"
        if let some diagnostic := executableMetadataDiagnostic? environment name then
          throw s!"{name}: {diagnostic}"
        let dependencies := match info with
          | .ctorInfo constructor => constructor.induct :: declarationDependencies environment name
          | .inductInfo declaration => declaration.ctors ++ declarationDependencies environment name
          | .defnInfo _ =>
              match environment.getProjectionStructureName? name with
              | some structureName => structureName :: declarationDependencies environment name
              | none => declarationDependencies environment name
          | _ => declarationDependencies environment name
        for dependency in dependencies do
          let some _ := environment.find? dependency
            | throw s!"{dependency}: declaration is absent from the elaborated environment"
          if let some diagnostic := executableMetadataDiagnostic? environment dependency then
            throw s!"{dependency}: {diagnostic}"
        let localNames := dependencies.filter (declaredInModules environment targetModules)
        auditExecutableMetadataAux environment targetModules (localNames ++ rest) (seen.insert name)

private def auditExecutableMetadata (environment : Environment) (targetModules : NameSet)
    (roots : List Name) : Except String Unit :=
  auditExecutableMetadataAux environment targetModules roots {}

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
            if let some structureName := environment.getProjectionStructureName? name then
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

private def exportPackage (sourceModule : Name) (targetModules : NameSet) (roots : List Name) : CoreM Json := do
  let environment ← getEnv
  for root in roots do
    unless declarationModule? environment root == some sourceModule do
      throwError "exported declaration {root} is not defined by source module {sourceModule}"
  match auditExecutableMetadata environment targetModules roots with
  | .ok () => pure ()
  | .error message => throwError message
  let names ← match collectDeclarations environment targetModules roots with
    | .ok value => pure value
    | .error message => throwError message
  let names := names.toArray.qsort nameTextLt |>.toList
  match ensureDistinctDeclarationNames names with
  | .ok () => pure ()
  | .error message => throwError message
  for name in names do
    match ensureDeclarationName name with
    | .ok () => pure ()
    | .error message => throwError "{name}: {message}"
  let mut declarations := []
  for name in names do
    let some info := environment.find? name
      | throwError "declaration {name} disappeared from the environment"
    let encoded ← match info with
      | .inductInfo _ => pure (dataDeclaration environment targetModules name)
      | .defnInfo _ => pure (functionDeclaration environment targetModules name)
      | _ => pure (.error s!"declaration {name} has an unsupported kind")
    match encoded with
    | .ok value => declarations := value :: declarations
    | .error message => throwError "{name}: {message}"
  pure (object [
    ("schemaVersion", .num 1),
    ("fragmentVersion", .str fragmentVersion),
    ("roots", array (roots.map (fun name => .str name.toString))),
    ("declarations", array declarations.reverse)
  ])

open Lean Elab Command in
syntax (name := tsleanExport) "#tslean_export " str str str+ : command

open Lean Elab Command in
elab_rules : command
  | `(#tslean_export $moduleName:str $targetModuleNames:str $roots:str*) => do
      let moduleName := moduleName.raw.isStrLit?.getD ""
      let targetModuleNames := targetModuleNames.raw.isStrLit?.getD ""
      let roots := roots.toList.map (fun root => root.raw.isStrLit?.getD "")
      let targetModules := targetModuleNames.splitOn "\n" |>.filter (!·.isEmpty) |>.map String.toName
        |>.foldl (fun modules name => modules.insert name) {}
      if moduleName.isEmpty || targetModules.isEmpty || roots.isEmpty || roots.any String.isEmpty then
        throwError "#tslean_export requires a source module, target module closure, and at least one declaration"
      let result ← try
        let package ← liftCoreM (exportPackage moduleName.toName targetModules (roots.map String.toName))
        pure (object [("ok", .bool true), ("package", package)])
      catch error =>
        let message ← error.toMessageData.toString
        pure (object [("ok", .bool false), ("error", .str message)])
      liftIO (IO.println result.compress)

end TSLean.LeanToTypeScript
