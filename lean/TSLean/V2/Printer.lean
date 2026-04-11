-- TSLean.V2.Printer
-- Pretty-printer: LeanAST → Lean 4 source text.
-- Faithful port of src/codegen/printer.ts — every function maps 1:1.
-- Produces byte-identical output to the TS printer for fixpoint bootstrap.

import TSLean.V2.LeanAST

namespace TSLean.V2.Printer

open TSLean.V2.LeanAST

-- ─── Configuration ──────────────────────────────────────────────────────────────

private def INDENT : String := "  "

-- ─── Lean keywords ──────────────────────────────────────────────────────────────

private def LEAN_KEYWORDS : Array String := #[
  "def","fun","let","in","if","then","else","match","with","do","return","where",
  "have","show","from","by","class","instance","structure","inductive","namespace",
  "end","open","import","theorem","lemma","example","variable","universe","abbrev",
  "opaque","partial","mutual","private","protected","section","attribute","and","or",
  "not","true","false","Type","Prop",
  "for","while","repeat","at","try","catch","throw","macro","syntax","tactic",
  "set_option","derive","deriving","extends","override"
]

private def sanitize (name : String) : String :=
  if LEAN_KEYWORDS.any (· == name) then "«" ++ name ++ "»"
  else name.map fun c =>
    if c.isAlphanum || c == '_' || c == '.' || c == '!' || c == '?' || c == '\'' then c
    else '_'

private def indent (depth : Nat) : String :=
  String.join (List.replicate depth INDENT)

-- ─── Forward declarations ───────────────────────────────────────────────────────

mutual

-- ─── Type printing ──────────────────────────────────────────────────────────────

partial def printTy (t : LeanTy) : String :=
  match t with
  | .TyName name => name
  | .TyApp fn args =>
    let fnS := printTy fn
    let argsS := String.intercalate " " (args.toList.map printTyAtom)
    s!"{fnS} {argsS}"
  | .TyArrow params ret =>
    let parts := params.toList.map printTyAtom ++ [printTy ret]
    String.intercalate " → " parts
  | .TyTuple elems =>
    if elems.size == 0 then "Unit"
    else if elems.size == 1 then printTy (elems.getD 0 default)
    else "(" ++ String.intercalate " × " (elems.toList.map printTy) ++ ")"
  | .TyParen inner => "(" ++ printTy inner ++ ")"

partial def printTyAtom (t : LeanTy) : String :=
  let s := printTy t
  match t with
  | .TyArrow .. | .TyTuple .. => "(" ++ s ++ ")"
  | .TyApp _ args => if args.size > 0 then "(" ++ s ++ ")" else s
  | _ => s

-- ─── Pattern printing ───────────────────────────────────────────────────────────

partial def printPat (p : LeanPat) : String :=
  match p with
  | .PVar name => sanitize name
  | .PWild => "_"
  | .PLit value => value
  | .PNone => ".none"
  | .PSome inner => ".some " ++ printPat inner
  | .PCtor name args =>
    let argsS := args.toList.map printPat
    if argsS.isEmpty then "." ++ sanitize name
    else "." ++ sanitize name ++ " " ++ String.intercalate " " argsS
  | .PTuple elems =>
    "(" ++ String.intercalate ", " (elems.toList.map printPat) ++ ")"
  | .PStruct fields =>
    "{ " ++ String.intercalate ", " (fields.toList.map fun (n, p) =>
      sanitize n ++ " := " ++ printPat p) ++ " }"
  | .POr pats =>
    String.intercalate " | " (pats.toList.map printPat)
  | .PAs pattern name =>
    printPat pattern ++ " as " ++ sanitize name

-- ─── Expression printing (inline, no leading indent) ────────────────────────────

partial def printExprInline (e : LeanExpr) : String :=
  match e with
  | .Lit value => value
  | .Var name => sanitize name
  | .None => "none"
  | .Default ty => match ty with
    | some t => "(default : " ++ printTy t ++ ")"
    | none => "default"
  | .Sorry ty reason =>
    match ty, reason with
    | some t, some r => "(sorry : " ++ printTy t ++ ") /- " ++ r ++ " -/"
    | some t, none => "(sorry : " ++ printTy t ++ ")"
    | none, some r => "sorry /- " ++ r ++ " -/"
    | none, none => "sorry"
  | .ArrayLit elems =>
    if elems.size == 0 then "#[]"
    else "#[" ++ String.intercalate ", " (elems.toList.map printExprInline) ++ "]"
  | .TupleLit elems =>
    "(" ++ String.intercalate ", " (elems.toList.map printExprInline) ++ ")"
  | .Paren inner => "(" ++ printExprInline inner ++ ")"
  | .TypeAnnot expr ty => "(" ++ printExprInline expr ++ " : " ++ printTy ty ++ ")"
  | .App fn args =>
    let fnS := printExprInline fn
    if args.size == 0 then fnS
    else fnS ++ " " ++ String.intercalate " " (args.toList.map printExprInline)
  | .Lam params body =>
    let ps := if params.size > 0 then String.intercalate " " params.toList else "_"
    "fun " ++ ps ++ " => " ++ printExprInline body
  | .Let name ty value body rec =>
    let kw := if rec then "let rec" else "let"
    let ann := match ty with | some t => " : " ++ printTy t | none => ""
    kw ++ " " ++ sanitize name ++ ann ++ " := " ++ printExprInline value ++ "; " ++ printExprInline body
  | .Bind name value body =>
    "let " ++ sanitize name ++ " ← " ++ printExprInline value ++ "; " ++ printExprInline body
  | .If cond then_ else_ =>
    "if " ++ printExprInline cond ++ " then " ++ printExprInline then_ ++ " else " ++ printExprInline else_
  | .Match scrutinee arms =>
    let scrut := printExprInline scrutinee
    let armsS := arms.toList.map fun arm => match arm with
      | .mk pat guard body =>
        let guardS := match guard with | some g => " if " ++ printExprInline g | none => ""
        "| " ++ printPat pat ++ guardS ++ " => " ++ printExprInline body
    "match " ++ scrut ++ " with " ++ String.intercalate " " armsS
  | .Do body => "do " ++ printExprInline body
  | .Pure value => "pure " ++ printExprInline value
  | .Return value => "return " ++ printExprInline value
  | .Throw value => "throw " ++ printExprInline value
  | .TryCatch body errName handler =>
    "tryCatch " ++ printExprInline body ++ " (fun " ++ sanitize errName ++ " => " ++ printExprInline handler ++ ")"
  | .Modify fn => "modify " ++ parenIfCompound fn
  | .BinOp op left right =>
    printExprInline left ++ " " ++ op ++ " " ++ printExprInline right
  | .UnOp op operand => op ++ printExprInline operand
  | .FieldAccess obj field => printExprInline obj ++ "." ++ sanitize field
  | .StructLit fields =>
    if fields.size == 0 then "{}"
    else "{ " ++ String.intercalate ", " (fields.toList.map fun f => match f with
      | .mk name value => sanitize name ++ " := " ++ printExprInline value) ++ " }"
  | .StructUpdate base fields =>
    let baseS := printExprInline base
    if fields.size == 0 then baseS
    else "{ " ++ baseS ++ " with " ++ String.intercalate ", " (fields.toList.map fun f => match f with
      | .mk name value => sanitize name ++ " := " ++ printExprInline value) ++ " }"
  | .SInterp parts =>
    let inner := String.join (parts.toList.map fun p => match p with
      | .Str value => value
      | .Expr expr => "{" ++ printExprInline expr ++ "}")
    "s!\"" ++ inner ++ "\""
  | .Seq stmts =>
    if stmts.size == 0 then "()"
    else if stmts.size == 1 then printExprInline (stmts.getD 0 default)
    else String.intercalate "; " (stmts.toList.map printExprInline)
  | .LineComment _ expr => printExprInline expr
  | .Panic msg => "panic! " ++ reprStr msg

-- ─── Expression printing (with indentation) ─────────────────────────────────────

partial def printExpr (e : LeanExpr) (depth : Nat) : String :=
  let ind := indent depth
  match e with
  | .Lit value => ind ++ value
  | .Var name => ind ++ sanitize name
  | .None => ind ++ "none"
  | .Default ty => match ty with
    | some t => ind ++ "(default : " ++ printTy t ++ ")"
    | none => ind ++ "default"
  | .Sorry ty reason =>
    match ty, reason with
    | some t, some r => ind ++ "(sorry : " ++ printTy t ++ ") /- " ++ r ++ " -/"
    | some t, none => ind ++ "(sorry : " ++ printTy t ++ ")"
    | none, some r => ind ++ "sorry /- " ++ r ++ " -/"
    | none, none => ind ++ "sorry"
  | .ArrayLit elems =>
    if elems.size == 0 then ind ++ "#[]"
    else ind ++ "#[" ++ String.intercalate ", " (elems.toList.map printExprInline) ++ "]"
  | .TupleLit elems => ind ++ "(" ++ String.intercalate ", " (elems.toList.map printExprInline) ++ ")"
  | .Paren inner => ind ++ "(" ++ printExprInline inner ++ ")"
  | .TypeAnnot expr ty => ind ++ "(" ++ printExprInline expr ++ " : " ++ printTy ty ++ ")"
  | .App fn args =>
    let fnS := printExprInline fn
    if args.size == 0 then ind ++ fnS
    else ind ++ fnS ++ " " ++ String.intercalate " " (args.toList.map printExprInline)
  | .Lam params body =>
    let ps := if params.size > 0 then String.intercalate " " params.toList else "_"
    let bodyS := printExprInline body
    if bodyS.any (· == '\n') then
      ind ++ "fun " ++ ps ++ " =>\n" ++ printExpr body (depth + 1)
    else ind ++ "fun " ++ ps ++ " => " ++ bodyS
  | .Let name ty value body rec =>
    let kw := if rec then "let rec" else "let"
    let ann := match ty with | some t => " : " ++ printTy t | none => ""
    let val := printExprInline value
    let bodyS := printExpr body depth
    ind ++ kw ++ " " ++ sanitize name ++ ann ++ " := " ++ val ++ "\n" ++ bodyS
  | .Bind name value body =>
    let val := printExprInline value
    let bodyS := printExpr body depth
    ind ++ "let " ++ sanitize name ++ " ← " ++ val ++ "\n" ++ bodyS
  | .If cond then_ else_ =>
    let condS := printExprInline cond
    let thenS := printExpr then_ (depth + 1)
    let elseS := printExpr else_ (depth + 1)
    ind ++ "if " ++ condS ++ " then\n" ++ thenS ++ "\n" ++ ind ++ "else\n" ++ elseS
  | .Match scrutinee arms =>
    let scrut := printExprInline scrutinee
    let armsS := arms.toList.map fun arm => match arm with
      | .mk pat guard body =>
        let guardS := match guard with | some g => " if " ++ printExprInline g | none => ""
        ind ++ INDENT ++ "| " ++ printPat pat ++ guardS ++ " => " ++ printExprInline body
    ind ++ "match " ++ scrut ++ " with\n" ++ String.intercalate "\n" armsS
  | .Do body =>
    ind ++ "do\n" ++ printExpr body (depth + 1)
  | .Pure value => ind ++ "pure " ++ printExprInline value
  | .Return value => ind ++ "return " ++ printExprInline value
  | .Throw value => ind ++ "throw " ++ parenIfCompound value
  | .TryCatch body errName handler =>
    ind ++ "tryCatch " ++ parenIfCompound body ++ " (fun " ++ sanitize errName ++ " => " ++ printExprInline handler ++ ")"
  | .Modify fn => ind ++ "modify " ++ parenIfCompound fn
  | .BinOp op left right =>
    ind ++ printExprInline left ++ " " ++ op ++ " " ++ printExprInline right
  | .UnOp op operand => ind ++ op ++ printExprInline operand
  | .FieldAccess obj field => ind ++ printExprInline obj ++ "." ++ sanitize field
  | .StructLit fields =>
    if fields.size == 0 then ind ++ "{}"
    else ind ++ "{ " ++ String.intercalate ", " (fields.toList.map fun f => match f with
      | .mk name value => sanitize name ++ " := " ++ printExprInline value) ++ " }"
  | .StructUpdate base fields =>
    let baseS := printExprInline base
    if fields.size == 0 then ind ++ baseS
    else ind ++ "{ " ++ baseS ++ " with " ++ String.intercalate ", " (fields.toList.map fun f => match f with
      | .mk name value => sanitize name ++ " := " ++ printExprInline value) ++ " }"
  | .SInterp parts =>
    let inner := String.join (parts.toList.map fun p => match p with
      | .Str value => value
      | .Expr expr => "{" ++ printExprInline expr ++ "}")
    ind ++ "s!\"" ++ inner ++ "\""
  | .Seq stmts =>
    if stmts.size == 0 then ind ++ "()"
    else if stmts.size == 1 then printExpr (stmts.getD 0 default) depth
    else String.intercalate "\n" (stmts.toList.map fun s => printExpr s depth)
  | .LineComment text expr =>
    ind ++ "-- " ++ text ++ "\n" ++ printExpr expr depth
  | .Panic msg => ind ++ "panic! " ++ reprStr msg

-- ─── parenIfCompound ────────────────────────────────────────────────────────────

partial def parenIfCompound (e : LeanExpr) : String :=
  let s := printExprInline e
  match e with
  | .Lam .. | .If .. | .Match .. | .Let .. | .Bind .. | .BinOp .. | .Do .. | .Seq .. => "(" ++ s ++ ")"
  | _ => s

end -- mutual

-- ─── Helpers ────────────────────────────────────────────────────────────────────

private def printParam (p : LeanParam) : String :=
  let ty := printTy p.ty
  let name := sanitize p.name
  if p.implicit then "{" ++ name ++ " : " ++ ty ++ "}"
  else match p.default_ with
    | some d => "(" ++ name ++ " : " ++ ty ++ " := " ++ printExprInline d ++ ")"
    | none => "(" ++ name ++ " : " ++ ty ++ ")"

private def fmtTyParams (params : Array LeanTyParam) (explicit : Bool) : String :=
  if params.size == 0 then ""
  else " " ++ String.intercalate " " (params.toList.map fun p =>
    let wrap := if explicit then ("(", ")") else ("{", "}")
    wrap.1 ++ p.name ++ " : Type" ++ wrap.2)

private def fmtTyParamsForDef (params : Array LeanTyParam) : String :=
  if params.size == 0 then ""
  else " " ++ String.intercalate " " (params.toList.map fun p =>
    let base := "{" ++ p.name ++ " : Type}"
    match p.constraints with
    | some cs => base ++ String.join (cs.toList.map fun c => " [" ++ c ++ " " ++ p.name ++ "]")
    | none => base)

private def stripCommentLine (line : String) : String :=
  let s := line.trimLeft
  -- Strip leading /**, /*, or * prefix (only at start of line)
  let s := if s.startsWith "/**" then (s.drop 3).toString.trimLeft
    else if s.startsWith "/*" then (s.drop 2).toString.trimLeft
    else if s.startsWith "* " then (s.drop 2).toString
    else if s == "*" then ""
    else s
  -- Strip trailing */ (only at end of line)
  let s := s.trimRight
  let s := if s.endsWith "*/" then s.dropRight 2 |>.trimRight else s
  s.trim

private def printCommentLines (text : String) (ind : String) : Array String :=
  let lines := text.splitOn "\n"
  lines.foldl (fun acc line =>
    let stripped := stripCommentLine line
    if stripped.isEmpty || stripped.startsWith "@" then acc
    else acc.push (ind ++ "-- " ++ stripped)
  ) #[]

-- ─── Declaration printing ───────────────────────────────────────────────────────

partial def printDecl (d : LeanDecl) (depth : Nat) : Array String :=
  let ind := indent depth
  match d with
  | .Blank => #[""]
  | .Comment text => printCommentLines text ind
  | .Raw code => (code.splitOn "\n").toArray.map fun line => line
  | .Import module => #[ind ++ "import " ++ module]
  | .Open namespaces => #[ind ++ "open " ++ String.intercalate " " namespaces.toList]
  | .Attribute attr target => #[ind ++ "attribute [" ++ attr ++ "] " ++ target]
  | .Deriving classes typeName =>
    #[ind ++ "deriving instance " ++ String.intercalate ", " classes.toList ++ " for " ++ typeName]
  | .StandaloneInstance code => #[ind ++ code]
  | .Abbrev name tyParams body comment =>
    let cLines := match comment with | some c => printCommentLines c ind | none => #[]
    let tp := fmtTyParams tyParams false
    cLines.push (ind ++ "abbrev " ++ sanitize name ++ tp ++ " := " ++ printTy body)
  | .Structure name tyParams fields extends_ deriving_ comment =>
    let cLines := match comment with | some c => printCommentLines c ind | none => #[]
    let tp := fmtTyParams tyParams true
    let ext := match extends_ with | some e => " extends " ++ e | none => ""
    let header := cLines.push (ind ++ "structure " ++ sanitize name ++ tp ++ ext ++ " where")
    let withMk := header.push (ind ++ INDENT ++ "mk ::")
    let withFields := fields.foldl (fun acc f =>
      let def_ := match f.default_ with
        | some d => " := " ++ printExpr d 0
        | none => ""
      acc.push (ind ++ INDENT ++ sanitize f.name ++ " : " ++ printTy f.ty ++ def_)
    ) withMk
    if deriving_.size > 0 then
      withFields.push (ind ++ INDENT ++ "deriving " ++ String.intercalate ", " deriving_.toList)
    else withFields
  | .Inductive name tyParams ctors deriving_ comment =>
    let cLines := match comment with | some c => printCommentLines c ind | none => #[]
    let tp := fmtTyParams tyParams true
    let header := cLines.push (ind ++ "inductive " ++ sanitize name ++ tp ++ " where")
    let withCtors := ctors.foldl (fun acc c =>
      if c.fields.size == 0 then acc.push (ind ++ "  | " ++ sanitize c.name)
      else
        let fs := String.intercalate " " (c.fields.toList.map fun (fname, ty) =>
          match fname with
          | some n => "(" ++ sanitize n ++ " : " ++ printTy ty ++ ")"
          | none => "(" ++ printTy ty ++ ")")
        acc.push (ind ++ "  | " ++ sanitize c.name ++ " " ++ fs)
    ) header
    if deriving_.size > 0 then
      withCtors.push (ind ++ "  deriving " ++ String.intercalate ", " deriving_.toList)
    else withCtors
  | .Def partial_ name tyParams params retTy body where_ docComment comment =>
    let cLines := match docComment with
      | some dc => #[ind ++ "/-- " ++ dc.trim ++ " -/"]
      | none => match comment with | some c => printCommentLines c ind | none => #[]
    let kw := if partial_ then "partial def" else "def"
    let tp := fmtTyParamsForDef tyParams
    let ps := String.intercalate " " (params.toList.map printParam)
    let psStr := if ps.isEmpty then "" else " " ++ ps
    let retStr := printTy retTy
    let bodyInline := printExprInline body
    let isSimple := !(bodyInline.any (· == '\n')) && bodyInline.length < 80 &&
      match body with
      | .Do .. | .If .. | .Match .. | .Seq .. | .LineComment .. | .Let .. | .Bind .. => false
      | _ => true
    let defLines := if isSimple then
        cLines.push (ind ++ kw ++ " " ++ sanitize name ++ tp ++ psStr ++ " : " ++ retStr ++ " := " ++ bodyInline)
      else
        let header := cLines.push (ind ++ kw ++ " " ++ sanitize name ++ tp ++ psStr ++ " : " ++ retStr ++ " :=")
        let bodyStr := printExpr body (depth + 1)
        bodyStr.splitOn "\n" |>.foldl (fun acc line => acc.push line) header
    match where_ with
    | some ws =>
      let withWhere := defLines.push (ind ++ "where")
      ws.foldl (fun acc w => acc ++ printDecl w (depth + 1)) withWhere
    | none => defLines
  | .Instance typeClass args methods =>
    let tArgs := String.intercalate " " (args.toList.map printTy)
    let header := #[ind ++ "instance : " ++ typeClass ++ " " ++ tArgs ++ " where"]
    methods.foldl (fun acc (name, params, body) =>
      let ps := String.intercalate " " (params.toList.map printParam)
      let psStr := if ps.isEmpty then "" else " " ++ ps
      acc.push (ind ++ INDENT ++ sanitize name ++ psStr ++ " := " ++ printExpr body 0)
    ) header
  | .Theorem name statement proof comment =>
    let cLines := match comment with | some c => printCommentLines c ind | none => #[]
    cLines.push (ind ++ "theorem " ++ sanitize name ++ " : " ++ statement ++ " := by")
    |>.push (ind ++ INDENT ++ proof)
  | .Class name tyParams methods comment =>
    let cLines := match comment with | some c => printCommentLines c ind | none => #[]
    let tp := fmtTyParams tyParams false
    let header := cLines.push (ind ++ "class " ++ sanitize name ++ tp ++ " where")
    methods.foldl (fun acc (name, ty) =>
      acc.push (ind ++ INDENT ++ sanitize name ++ " : " ++ printTy ty)
    ) header
  | .Mutual decls =>
    let header := #[ind ++ "mutual", ""]
    let body := decls.foldl (fun acc d => acc ++ printDecl d depth |>.push "") header
    body.push (ind ++ "end")
  | .Namespace name decls =>
    let header := #[ind ++ "namespace " ++ name, ""]
    let body := decls.foldl (fun acc d => acc ++ printDecl d depth) header
    body.push (ind ++ "end " ++ name)
  | .Section name decls =>
    let header := match name with
      | some n => #[ind ++ "section " ++ n, ""]
      | none => #[ind ++ "section", ""]
    let body := decls.foldl (fun acc d => acc ++ printDecl d depth |>.push "") header
    match name with
    | some n => body.push (ind ++ "end " ++ n)
    | none => body.push (ind ++ "end")

-- ─── Public API ─────────────────────────────────────────────────────────────────

def printFile (file : LeanFile) : String :=
  let lines : Array String := #[]
  let lines := match file.banner with
    | some b => lines.push ("-- " ++ b)
    | none => lines
  let lines := match file.sourcePath with
    | some p => lines.push ("-- Source: " ++ p)
    | none => lines
  let lines := if file.banner.isSome || file.sourcePath.isSome then lines.push "" else lines
  let lines := file.decls.foldl (fun acc d => acc ++ printDecl d 0) lines
  String.intercalate "\n" lines.toList

end TSLean.V2.Printer
