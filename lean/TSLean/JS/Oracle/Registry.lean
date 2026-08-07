namespace TSLean.JS.Oracle

inductive OracleDomain where
  | primitive
  | graph
  deriving DecidableEq

structure OperationSpec where
  arity : Nat
  domain : OracleDomain

def operationRegistry : List String :=
  ["add", "assign-primitive-prototype-is", "assign-string", "box-add", "box-loose", "box-number", "box-object", "box-prototype-is", "box-string", "box-valueof", "call-with-argument", "div", "finally-order", "finally-return", "format", "ge", "gt", "intrinsic-tostring", "intrinsic-valueof", "iterate-live", "key", "le", "logical-or", "loose", "lt", "mul", "mutate-intrinsic-prototype", "mutate-wrapper-prototype", "number", "parse", "rem", "short-circuit-assignment", "spread-count", "spread-overwrite", "spread-string", "string", "sub", "symbol-key-for", "throw-value", "truthiness-empty-array", "typeof-string-check", "utf16-fields", "value-add", "value-ge", "value-gt", "value-identity", "value-instanceof", "value-le", "value-loose", "value-lt", "value-number", "value-strict", "value-string", "while-call-once"]

def operationSpec? (operation : String) : Option OperationSpec :=
  if ["format", "key", "number", "parse", "string"].contains operation then some ⟨1, .primitive⟩
  else if ["add", "div", "ge", "gt", "le", "loose", "lt", "mul", "rem", "sub"].contains operation then some ⟨2, .primitive⟩
  else if ["assign-primitive-prototype-is", "assign-string", "box-add", "box-loose", "box-number", "box-object", "box-prototype-is", "box-string", "box-valueof", "call-with-argument", "finally-order", "finally-return", "intrinsic-tostring", "intrinsic-valueof", "iterate-live", "logical-or", "mutate-intrinsic-prototype", "mutate-wrapper-prototype", "short-circuit-assignment", "spread-count", "spread-overwrite", "spread-string", "symbol-key-for", "throw-value", "truthiness-empty-array", "typeof-string-check", "utf16-fields", "value-add", "value-ge", "value-gt", "value-identity", "value-instanceof", "value-le", "value-loose", "value-lt", "value-number", "value-strict", "value-string", "while-call-once"].contains operation then some ⟨1, .graph⟩
  else if [].contains operation then some ⟨2, .graph⟩
  else none

def operationArity? (operation : String) : Option Nat := (operationSpec? operation).map (·.arity)
def operationDomain? (operation : String) : Option OracleDomain := (operationSpec? operation).map (·.domain)

end TSLean.JS.Oracle
