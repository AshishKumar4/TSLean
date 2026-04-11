-- TSLean.V2.LeanAST
-- Typed AST for Lean 4 surface syntax — faithful port of src/codegen/lean-ast.ts.
-- Every type here mirrors the TS definition exactly.

namespace TSLean.V2.LeanAST

-- Types
inductive LeanTy where
  | TyName (name : String)
  | TyApp (fn : LeanTy) (args : Array LeanTy)
  | TyArrow (params : Array LeanTy) (ret : LeanTy)
  | TyTuple (elems : Array LeanTy)
  | TyParen (inner : LeanTy)
  deriving Repr, Inhabited

-- Patterns
inductive LeanPat where
  | PVar (name : String)
  | PWild
  | PCtor (name : String) (args : Array LeanPat)
  | PLit (value : String)
  | PNone
  | PSome (inner : LeanPat)
  | PTuple (elems : Array LeanPat)
  | PStruct (fields : Array (String × LeanPat))
  | POr (pats : Array LeanPat)
  | PAs (pattern : LeanPat) (name : String)
  deriving Repr, Inhabited

mutual

-- String interpolation part
inductive SInterpPart where
  | Str (value : String)
  | Expr (expr : LeanExpr)

-- Expressions
inductive LeanExpr where
  | Lit (value : String)
  | Var (name : String)
  | None
  | Default (ty : Option LeanTy)
  | Sorry (ty : Option LeanTy) (reason : Option String)
  | ArrayLit (elems : Array LeanExpr)
  | TupleLit (elems : Array LeanExpr)
  | App (fn : LeanExpr) (args : Array LeanExpr)
  | Paren (inner : LeanExpr)
  | Lam (params : Array String) (body : LeanExpr)
  | Let (name : String) (ty : Option LeanTy) (value : LeanExpr) (body : LeanExpr) (rec : Bool)
  | Bind (name : String) (value : LeanExpr) (body : LeanExpr)
  | If (cond : LeanExpr) (then_ : LeanExpr) (else_ : LeanExpr)
  | Match (scrutinee : LeanExpr) (arms : Array LeanMatchArm)
  | Do (body : LeanExpr)
  | Pure (value : LeanExpr)
  | Return (value : LeanExpr)
  | Throw (value : LeanExpr)
  | TryCatch (body : LeanExpr) (errName : String) (handler : LeanExpr)
  | Modify (fn : LeanExpr)
  | BinOp (op : String) (left : LeanExpr) (right : LeanExpr)
  | UnOp (op : String) (operand : LeanExpr)
  | FieldAccess (obj : LeanExpr) (field : String)
  | StructLit (fields : Array LeanFieldVal)
  | StructUpdate (base : LeanExpr) (fields : Array LeanFieldVal)
  | SInterp (parts : Array SInterpPart)
  | Seq (stmts : Array LeanExpr)
  | TypeAnnot (expr : LeanExpr) (ty : LeanTy)
  | LineComment (text : String) (expr : LeanExpr)
  | Panic (msg : String)

-- Match arm
inductive LeanMatchArm where
  | mk (pat : LeanPat) (guard : Option LeanExpr) (body : LeanExpr)

-- Field value
inductive LeanFieldVal where
  | mk (name : String) (value : LeanExpr)

end -- mutual

instance : Repr SInterpPart := ⟨fun _ _ => .text "SInterpPart"⟩
instance : Repr LeanExpr := ⟨fun _ _ => .text "LeanExpr"⟩
instance : Repr LeanMatchArm := ⟨fun _ _ => .text "LeanMatchArm"⟩
instance : Repr LeanFieldVal := ⟨fun _ _ => .text "LeanFieldVal"⟩
instance : Inhabited SInterpPart := ⟨.Str ""⟩
instance : Inhabited LeanExpr := ⟨.Lit ""⟩
instance : Inhabited LeanMatchArm := ⟨.mk .PWild none (.Lit "")⟩
instance : Inhabited LeanFieldVal := ⟨.mk "" (.Lit "")⟩

-- Type parameter
structure LeanTyParam where
  name : String
  explicit : Bool
  constraints : Option (Array String) := none
  deriving Repr, Inhabited

-- Function parameter
structure LeanParam where
  name : String
  ty : LeanTy
  implicit : Bool := false
  default_ : Option LeanExpr := none
  deriving Repr, Inhabited

-- Structure field
structure LeanField where
  name : String
  ty : LeanTy
  default_ : Option LeanExpr := none
  deriving Repr, Inhabited

-- Inductive constructor
structure LeanCtor where
  name : String
  fields : Array (Option String × LeanTy) -- (name?, type)
  deriving Repr, Inhabited

-- Declarations
inductive LeanDecl where
  | Def (partial_ : Bool) (name : String) (tyParams : Array LeanTyParam)
        (params : Array LeanParam) (retTy : LeanTy) (body : LeanExpr)
        (where_ : Option (Array LeanDecl)) (docComment : Option String)
        (comment : Option String)
  | Structure (name : String) (tyParams : Array LeanTyParam) (fields : Array LeanField)
              (extends_ : Option String) (deriving_ : Array String) (comment : Option String)
  | Inductive (name : String) (tyParams : Array LeanTyParam) (ctors : Array LeanCtor)
              (deriving_ : Array String) (comment : Option String)
  | Abbrev (name : String) (tyParams : Array LeanTyParam) (body : LeanTy) (comment : Option String)
  | Instance (typeClass : String) (args : Array LeanTy)
             (methods : Array (String × Array LeanParam × LeanExpr))
  | Theorem (name : String) (statement : String) (proof : String) (comment : Option String)
  | Class (name : String) (tyParams : Array LeanTyParam)
          (methods : Array (String × LeanTy)) (comment : Option String)
  | Mutual (decls : Array LeanDecl)
  | Namespace (name : String) (decls : Array LeanDecl)
  | Section (name : Option String) (decls : Array LeanDecl)
  | Import (module : String)
  | Open (namespaces : Array String)
  | Attribute (attr : String) (target : String)
  | Deriving (classes : Array String) (typeName : String)
  | StandaloneInstance (code : String)
  | Raw (code : String)
  | Comment (text : String)
  | Blank
  deriving Repr, Inhabited

-- File
structure LeanFile where
  banner : Option String := none
  sourcePath : Option String := none
  decls : Array LeanDecl
  deriving Repr, Inhabited

end TSLean.V2.LeanAST
