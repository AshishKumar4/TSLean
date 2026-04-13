// Core IR for the TS→Lean 4 transpiler.
// System Fω with algebraic effect annotations.
// Every expression node carries a resolved type and effect signature.

// ─── Effects ────────────────────────────────────────────────────────────────

export type Effect =
  | { tag: 'Pure' }
  | { tag: 'State';  stateType: IRType }
  | { tag: 'IO' }
  | { tag: 'Async' }
  | { tag: 'Except'; errorType: IRType }
  | { tag: 'Combined'; effects: Effect[] };

export const Pure:  Effect = { tag: 'Pure' };
export const IO:    Effect = { tag: 'IO' };
export const Async: Effect = { tag: 'Async' };

export function stateEffect(stateType: IRType): Effect {
  return { tag: 'State', stateType };
}
export function exceptEffect(errorType: IRType): Effect {
  return { tag: 'Except', errorType };
}
export function combineEffects(effects: Effect[]): Effect {
  const flat = effects.flatMap(e => e.tag === 'Combined' ? e.effects : [e]);
  const noPure = flat.filter(e => e.tag !== 'Pure');
  const deduped = dedup(noPure);
  if (deduped.length === 0) return Pure;
  if (deduped.length === 1) return deduped[0];
  return { tag: 'Combined', effects: deduped };
}
function dedup(effects: Effect[]): Effect[] {
  const seen = new Set<string>();
  return effects.filter(e => {
    const k = JSON.stringify(e);
    if (seen.has(k)) return false;
    seen.add(k);
    return true;
  });
}

export function isPure(e: Effect): boolean   { return e.tag === 'Pure'; }
export function hasAsync(e: Effect): boolean  { return e.tag === 'Async'  || (e.tag === 'Combined' && e.effects.some(hasAsync)); }
export function hasState(e: Effect): boolean  { return e.tag === 'State'  || (e.tag === 'Combined' && e.effects.some(hasState)); }
export function hasExcept(e: Effect): boolean { return e.tag === 'Except' || (e.tag === 'Combined' && e.effects.some(hasExcept)); }
export function hasIO(e: Effect): boolean     { return e.tag === 'IO'     || (e.tag === 'Combined' && e.effects.some(hasIO)); }

// ─── Types ───────────────────────────────────────────────────────────────────

export type IRType =
  | { tag: 'Nat' }
  | { tag: 'Int' }
  | { tag: 'Float' }
  | { tag: 'String' }
  | { tag: 'Bool' }
  | { tag: 'Unit' }
  | { tag: 'Never' }
  | { tag: 'Option';    inner: IRType }
  | { tag: 'Array';     elem: IRType }
  | { tag: 'Tuple';     elems: IRType[] }
  | { tag: 'Function';  params: IRType[]; ret: IRType; effect: Effect }
  | { tag: 'Structure'; name: string; fields: Array<{ name: string; type: IRType }> }
  | { tag: 'Inductive'; name: string; typeParams: string[]; ctors: Array<{ name: string; fields: IRType[] }> }
  | { tag: 'TypeRef';   name: string; args: IRType[] }
  | { tag: 'TypeVar';   name: string }
  | { tag: 'Map';       key: IRType; value: IRType }
  | { tag: 'Set';       elem: IRType }
  | { tag: 'Promise';   inner: IRType }
  | { tag: 'Result';    ok: IRType; err: IRType }
  | { tag: 'Dependent'; param: string; paramType: IRType; body: IRType }
  | { tag: 'Subtype';   base: IRType; refinement: string }
  | { tag: 'Universe';  level: number };

// Primitive singletons
export const TyNat:    IRType = { tag: 'Nat' };
export const TyInt:    IRType = { tag: 'Int' };
export const TyFloat:  IRType = { tag: 'Float' };
export const TyString: IRType = { tag: 'String' };
export const TyBool:   IRType = { tag: 'Bool' };
export const TyUnit:   IRType = { tag: 'Unit' };
export const TyNever:  IRType = { tag: 'Never' };

// Type constructors
export const TyOption  = (inner: IRType): IRType => ({ tag: 'Option', inner });
export const TyArray   = (elem: IRType):  IRType => ({ tag: 'Array',  elem });
export const TyTuple   = (elems: IRType[]): IRType => ({ tag: 'Tuple', elems });
export const TyMap     = (key: IRType, value: IRType): IRType => ({ tag: 'Map', key, value });
export const TySet     = (elem: IRType):  IRType => ({ tag: 'Set',  elem });
export const TyPromise = (inner: IRType): IRType => ({ tag: 'Promise', inner });
export const TyResult  = (ok: IRType, err: IRType): IRType => ({ tag: 'Result', ok, err });
export const TyRef     = (name: string, args: IRType[] = []): IRType => ({ tag: 'TypeRef', name, args });
export const TyVar     = (name: string): IRType => ({ tag: 'TypeVar', name });
export const TyFn      = (params: IRType[], ret: IRType, effect: Effect = Pure): IRType =>
  ({ tag: 'Function', params, ret, effect });

// ─── Expressions ─────────────────────────────────────────────────────────────

export interface Span { file: string; line: number; col: number }

export interface IRNode { type: IRType; effect: Effect; span?: Span }

export type IRExpr =
  | ({ tag: 'LitNat';    value: number }    & IRNode)
  | ({ tag: 'LitInt';    value: number }    & IRNode)
  | ({ tag: 'LitFloat';  value: number }    & IRNode)
  | ({ tag: 'LitString'; value: string }    & IRNode)
  | ({ tag: 'LitBool';   value: boolean }   & IRNode)
  | ({ tag: 'LitUnit' }                     & IRNode)
  | ({ tag: 'LitNull' }                     & IRNode)
  | ({ tag: 'Var';       name: string }     & IRNode)
  | ({ tag: 'FieldAccess'; obj: IRExpr; field: string }               & IRNode)
  | ({ tag: 'IndexAccess'; obj: IRExpr; index: IRExpr }               & IRNode)
  | ({ tag: 'Lambda'; params: IRParam[]; body: IRExpr }               & IRNode)
  | ({ tag: 'App';    fn: IRExpr; args: IRExpr[] }                    & IRNode)
  | ({ tag: 'TypeApp'; fn: IRExpr; typeArgs: IRType[] }               & IRNode)
  | ({ tag: 'Let';    name: string; annot?: IRType; value: IRExpr; body: IRExpr } & IRNode)
  | ({ tag: 'IfThenElse'; cond: IRExpr; then: IRExpr; else_: IRExpr } & IRNode)
  | ({ tag: 'Match'; scrutinee: IRExpr; cases: IRCase[] }             & IRNode)
  | ({ tag: 'Sequence'; stmts: IRExpr[] }                             & IRNode)
  | ({ tag: 'StructLit'; typeName: string; fields: Array<{ name: string; value: IRExpr }> } & IRNode)
  | ({ tag: 'CtorApp'; ctor: string; args: IRExpr[] }                 & IRNode)
  | ({ tag: 'ArrayLit'; elems: IRExpr[] }                             & IRNode)
  | ({ tag: 'TupleLit'; elems: IRExpr[] }                             & IRNode)
  | ({ tag: 'DoBlock'; stmts: DoStmt[] }                              & IRNode)
  | ({ tag: 'Pure_';  value: IRExpr }                                 & IRNode)
  | ({ tag: 'Bind';   name: string; monad: IRExpr; body: IRExpr }     & IRNode)
  | ({ tag: 'StateGet' }                                              & IRNode)
  | ({ tag: 'StateSet'; value: IRExpr }                               & IRNode)
  | ({ tag: 'Throw';  error: IRExpr }                                 & IRNode)
  | ({ tag: 'TryCatch'; body: IRExpr; errName: string; handler: IRExpr } & IRNode)
  | ({ tag: 'Await';  expr: IRExpr }                                  & IRNode)
  | ({ tag: 'Assign'; target: IRExpr; value: IRExpr }                 & IRNode)
  | ({ tag: 'BinOp';  op: BinOp; left: IRExpr; right: IRExpr }       & IRNode)
  | ({ tag: 'UnOp';   op: UnOp;  operand: IRExpr }                   & IRNode)
  | ({ tag: 'Cast';   expr: IRExpr; targetType: IRType }              & IRNode)
  | ({ tag: 'IsType'; expr: IRExpr; testType: IRType }                & IRNode)
  | ({ tag: 'Return'; value: IRExpr }                                 & IRNode)
  | ({ tag: 'Panic';       msg: string }                                          & IRNode)
  | ({ tag: 'Hole' }                                                              & IRNode)
  // New nodes added in v3:
  | ({ tag: 'StructUpdate'; base: IRExpr; fields: Array<{ name: string; value: IRExpr }> } & IRNode)
  | ({ tag: 'TypeNarrow';  expr: IRExpr; narrowedType: IRType; narrowKind: 'typeof' | 'instanceof' | 'in' | 'truthy' } & IRNode)
  | ({ tag: 'YieldExpr';   value?: IRExpr }                                       & IRNode)
  | ({ tag: 'OptChain';    expr: IRExpr }                                         & IRNode)   // obj?.x already optional
  | ({ tag: 'MultiLet';    bindings: Array<{ name: string; type: IRType; value: IRExpr }>; body: IRExpr } & IRNode)
  | ({ tag: 'Labeled';     label: string; body: IRExpr }                          & IRNode)
  | ({ tag: 'Break';       label?: string }                                       & IRNode)
  | ({ tag: 'Continue';    label?: string }                                       & IRNode);

export interface IRParam {
  name: string;
  type: IRType;
  implicit?: boolean;
  default_?: IRExpr;
}

export interface IRCase { pattern: IRPattern; guard?: IRExpr; body: IRExpr }

export type IRPattern =
  | { tag: 'PVar';    name: string }
  | { tag: 'PLit';    value: string | number | boolean }
  | { tag: 'PCtor';   ctor: string; args: IRPattern[] }
  | { tag: 'PStruct'; fields: Array<{ name: string; pattern: IRPattern }> }
  | { tag: 'PTuple';  elems: IRPattern[] }
  | { tag: 'PWild' }
  | { tag: 'POr';     pats: IRPattern[] }
  | { tag: 'PAs';     pattern: IRPattern; name: string }
  | { tag: 'PString'; value: string }   // pre-rewrite discriminant string
  | { tag: 'PNone' }
  | { tag: 'PSome';   inner: IRPattern };

export type DoStmt =
  | { tag: 'DoBind';   name: string; expr: IRExpr }
  | { tag: 'DoLet';    name: string; value: IRExpr }
  | { tag: 'DoExpr';   expr: IRExpr }
  | { tag: 'DoReturn'; value: IRExpr };

export type BinOp =
  'Add' | 'Sub' | 'Mul' | 'Div' | 'Mod' |
  'Eq' | 'Ne' | 'Lt' | 'Le' | 'Gt' | 'Ge' |
  'And' | 'Or' |
  'BitAnd' | 'BitOr' | 'BitXor' | 'Shl' | 'Shr' |
  'Concat' | 'NullCoalesce';

export type UnOp = 'Not' | 'Neg' | 'BitNot';

// ─── Declarations ─────────────────────────────────────────────────────────────

export type IRDecl =
  | { tag: 'TypeAlias';    name: string; typeParams: string[]; body: IRType;  comment?: string }
  | { tag: 'StructDef';    name: string; typeParams: string[]; fields: Array<{ name: string; type: IRType; mutable?: boolean }>; deriving?: string[]; comment?: string; extends_?: string }
  | { tag: 'InductiveDef'; name: string; typeParams: string[]; ctors: Array<{ name: string; fields: Array<{ name?: string; type: IRType }> }>; comment?: string }
  | { tag: 'FuncDef';      name: string; typeParams: string[]; params: IRParam[]; retType: IRType; effect: Effect; body: IRExpr; comment?: string; isPartial?: boolean; where_?: IRDecl[]; docComment?: string }
  | { tag: 'InstanceDef';  typeClass: string; typeArgs: IRType[]; methods: IRDecl[]; comment?: string }
  | { tag: 'TheoremDef';   name: string; statement: string; proof: string; comment?: string }
  | { tag: 'ClassDecl';    name: string; typeParams: string[]; supers?: string[]; methods: Array<{ name: string; type: IRType; default_?: IRExpr }>; comment?: string }
  | { tag: 'Namespace';    name: string; decls: IRDecl[] }
  | { tag: 'RawLean';      code: string }
  | { tag: 'VarDecl';      name: string; type: IRType; value: IRExpr; mutable: boolean }
  // New in v3:
  | { tag: 'SectionDecl';  name?: string; decls: IRDecl[] }
  | { tag: 'AttributeDecl'; attr: string; target: string }
  | { tag: 'DeriveDecl';   typeName: string; classes: string[] };

// ─── Module ───────────────────────────────────────────────────────────────────

export interface IRImport { module: string; names?: string[] }

export interface IRModule {
  name: string;
  imports: IRImport[];
  decls: IRDecl[];
  comments: string[];
  sourceFile?: string;
}

// ─── Smart constructors ───────────────────────────────────────────────────────

export function litStr(v: string):  IRExpr { return { tag: 'LitString', value: v, type: TyString, effect: Pure }; }
export function litNat(v: number):  IRExpr { return { tag: 'LitNat',    value: v, type: TyNat,    effect: Pure }; }
export function litBool(v: boolean):IRExpr { return { tag: 'LitBool',   value: v, type: TyBool,   effect: Pure }; }
export function litUnit():          IRExpr { return { tag: 'LitUnit',              type: TyUnit,   effect: Pure }; }
export function litFloat(v: number):IRExpr { return { tag: 'LitFloat',  value: v, type: TyFloat,  effect: Pure }; }
export function litInt(v: number):  IRExpr { return { tag: 'LitInt',    value: v, type: TyInt,    effect: Pure }; }
export function varExpr(name: string, type: IRType = TyUnit): IRExpr { return { tag: 'Var', name, type, effect: Pure }; }
export function holeExpr(type: IRType = TyUnit): IRExpr { return { tag: 'Hole', type, effect: Pure }; }
export function structUpdate(base: IRExpr, fields: Array<{ name: string; value: IRExpr }>, type: IRType): IRExpr {
  return { tag: 'StructUpdate', base, fields, type, effect: base.effect };
}
export function appExpr(fn: IRExpr, args: IRExpr[]): IRExpr {
  return { tag: 'App', fn, args, type: TyUnit, effect: combineEffects([fn.effect, ...args.map(a => a.effect)]) };
}
export function seqExpr(stmts: IRExpr[]): IRExpr {
  if (stmts.length === 0) return litUnit();
  if (stmts.length === 1) return stmts[0];
  return { tag: 'Sequence', stmts, type: stmts[stmts.length - 1].type, effect: combineEffects(stmts.map(s => s.effect)) };
}
