/**
 * @module codegen/lean-ast
 *
 * Typed AST for Lean 4 surface syntax — the intermediate representation
 * between the transpiler's IR and the final text output.
 *
 * Design: models exactly the Lean 4 constructs the transpiler emits.
 * Not a full Lean 4 grammar — just what we need. Every node here
 * maps to one and only one textual form in the printer.
 *
 * Pipeline:  IR → Rewrite → **Lowering (IR→LeanAST)** → Printer → Text
 */

// ─── Types ──────────────────────────────────────────────────────────────────────

/** Lean 4 type expression. */
export type LeanTy =
  | { tag: 'TyName'; name: string }                                    // String, Nat, Bool, MyStruct
  | { tag: 'TyApp'; fn: LeanTy; args: LeanTy[] }                      // Array T, Option (Array T)
  | { tag: 'TyArrow'; params: LeanTy[]; ret: LeanTy }                 // A → B → C
  | { tag: 'TyTuple'; elems: LeanTy[] }                                // A × B × C
  | { tag: 'TyParen'; inner: LeanTy }                                  // (T)

// ─── Patterns ───────────────────────────────────────────────────────────────────

/** Lean 4 match pattern. */
export type LeanPat =
  | { tag: 'PVar'; name: string }                                       // x
  | { tag: 'PWild' }                                                    // _
  | { tag: 'PCtor'; name: string; args: LeanPat[] }                    // .Circle radius
  | { tag: 'PLit'; value: string }                                      // 42, "hello", true
  | { tag: 'PNone' }                                                    // .none
  | { tag: 'PSome'; inner: LeanPat }                                   // .some x
  | { tag: 'PTuple'; elems: LeanPat[] }                                // (a, b)
  | { tag: 'PStruct'; fields: { name: string; pat: LeanPat }[] }      // { x := p, y := q }
  | { tag: 'POr'; pats: LeanPat[] };                                   // p₁ | p₂

// ─── Expressions ────────────────────────────────────────────────────────────────

/** A match arm: pattern + optional guard + body. */
export interface LeanMatchArm {
  pat: LeanPat;
  guard?: LeanExpr;
  body: LeanExpr;
}

/** A field in a struct literal or update. */
export interface LeanFieldVal {
  name: string;
  value: LeanExpr;
}

/** Lean 4 expression. */
export type LeanExpr =
  // Literals
  | { tag: 'Lit'; value: string }                                       // 42, 3.14, "hello", true, false, ()
  | { tag: 'Var'; name: string }                                        // x, self, Array.push
  | { tag: 'None' }                                                     // none
  | { tag: 'Default'; ty?: LeanTy }                                    // default or (default : T)
  | { tag: 'Sorry'; ty?: LeanTy; reason?: string }                    // sorry or (sorry : T) /- reason -/
  | { tag: 'ArrayLit'; elems: LeanExpr[] }                             // #[a, b, c]
  | { tag: 'TupleLit'; elems: LeanExpr[] }                             // (a, b, c)
  // Function application
  | { tag: 'App'; fn: LeanExpr; args: LeanExpr[] }                    // f a b c
  | { tag: 'Paren'; inner: LeanExpr }                                  // (expr)
  // Lambda
  | { tag: 'Lam'; params: string[]; body: LeanExpr }                  // fun x y => body
  // Bindings
  | { tag: 'Let'; name: string; ty?: LeanTy; value: LeanExpr;
      body: LeanExpr; rec?: boolean }                                   // let (rec) x (:T) := v \n body
  | { tag: 'Bind'; name: string; value: LeanExpr;
      body: LeanExpr }                                                  // let x ← v \n body
  // Control flow
  | { tag: 'If'; cond: LeanExpr; then_: LeanExpr; else_: LeanExpr }  // if c then t else e
  | { tag: 'Match'; scrutinee: LeanExpr; arms: LeanMatchArm[] }       // match s with | p => b
  // Do notation
  | { tag: 'Do'; body: LeanExpr }                                      // do \n body
  | { tag: 'Pure'; value: LeanExpr }                                   // pure v
  | { tag: 'Return'; value: LeanExpr }                                 // return v
  | { tag: 'Throw'; value: LeanExpr }                                  // throw v
  | { tag: 'TryCatch'; body: LeanExpr; errName: string;
      handler: LeanExpr }                                               // tryCatch b (fun e => h)
  | { tag: 'Modify'; fn: LeanExpr }                                    // modify f
  // Operators
  | { tag: 'BinOp'; op: string; left: LeanExpr; right: LeanExpr }    // a + b, a == b
  | { tag: 'UnOp'; op: string; operand: LeanExpr }                    // !x, -x
  // Field access & struct
  | { tag: 'FieldAccess'; obj: LeanExpr; field: string }              // x.field
  | { tag: 'StructLit'; fields: LeanFieldVal[] }                       // { a := 1, b := 2 }
  | { tag: 'StructUpdate'; base: LeanExpr;
      fields: LeanFieldVal[] }                                          // { base with a := 1 }
  // String interpolation
  | { tag: 'SInterp'; parts: SInterpPart[] }                           // s!"Hello, {name}!"
  // Sequencing (multiple statements in a do block or let chain)
  | { tag: 'Seq'; stmts: LeanExpr[] }                                  // stmt1 \n stmt2 \n ...
  // Annotations
  | { tag: 'TypeAnnot'; expr: LeanExpr; ty: LeanTy }                  // (expr : T)
  // Comments attached to expressions
  | { tag: 'LineComment'; text: string; expr: LeanExpr }              // -- comment \n expr
  // Panic
  | { tag: 'Panic'; msg: string };                                     // panic! "msg"

/** Part of an s!"..." interpolation: either literal text or an expression. */
export type SInterpPart =
  | { tag: 'Str'; value: string }
  | { tag: 'Expr'; expr: LeanExpr };

// ─── Declarations ───────────────────────────────────────────────────────────────

/** Lean 4 type parameter with optional constraints. */
export interface LeanTyParam {
  name: string;
  explicit: boolean;  // true = (T : Type), false = {T : Type}
  constraints?: string[];  // e.g. ["Inhabited", "BEq"]
}

/** Lean 4 function/def parameter. */
export interface LeanParam {
  name: string;
  ty: LeanTy;
  implicit?: boolean;       // {x : T}
  default_?: LeanExpr;      // (x : T := default)
}

/** Lean 4 structure field. */
export interface LeanField {
  name: string;
  ty: LeanTy;
  default_?: LeanExpr;
}

/** Lean 4 inductive constructor. */
export interface LeanCtor {
  name: string;
  fields: { name?: string; ty: LeanTy }[];
}

/** Lean 4 top-level declaration. */
export type LeanDecl =
  // Definitions
  | { tag: 'Def'; partial: boolean; name: string; tyParams: LeanTyParam[];
      params: LeanParam[]; retTy: LeanTy; body: LeanExpr;
      where_?: LeanDecl[]; docComment?: string; comment?: string }
  // Type definitions
  | { tag: 'Structure'; name: string; tyParams: LeanTyParam[];
      fields: LeanField[]; extends_?: string; deriving: string[];
      comment?: string }
  | { tag: 'Inductive'; name: string; tyParams: LeanTyParam[];
      ctors: LeanCtor[]; deriving: string[]; comment?: string }
  | { tag: 'Abbrev'; name: string; tyParams: LeanTyParam[];
      body: LeanTy; comment?: string }
  // Instances & theorems
  | { tag: 'Instance'; typeClass: string; args: LeanTy[];
      methods: { name: string; params: LeanParam[]; body: LeanExpr }[] }
  | { tag: 'Theorem'; name: string; statement: string; proof: string;
      comment?: string }
  // Class
  | { tag: 'Class'; name: string; tyParams: LeanTyParam[];
      methods: { name: string; ty: LeanTy }[]; comment?: string }
  // Grouping
  | { tag: 'Mutual'; decls: LeanDecl[] }
  | { tag: 'Namespace'; name: string; decls: LeanDecl[] }
  | { tag: 'Section'; name?: string; decls: LeanDecl[] }
  // Module-level
  | { tag: 'Import'; module: string }
  | { tag: 'Open'; namespaces: string[] }
  | { tag: 'Attribute'; attr: string; target: string }
  | { tag: 'Deriving'; classes: string[]; typeName: string }
  // Standalone instances (for mutual blocks)
  | { tag: 'StandaloneInstance'; code: string }
  // Escape hatch
  | { tag: 'Raw'; code: string }
  | { tag: 'Comment'; text: string }
  | { tag: 'Blank' };

// ─── File ───────────────────────────────────────────────────────────────────────

/** A complete Lean 4 source file. */
export interface LeanFile {
  banner?: string;
  sourcePath?: string;
  decls: LeanDecl[];
}
