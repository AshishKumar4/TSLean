// Stdlib mapping: TypeScript built-ins → Lean 4 equivalents.

import { IRType, BinOp, TyString, TyBool, TyNat, TyUnit, TyArray, TyOption } from '../ir/types.js';

// ─── Method translations ──────────────────────────────────────────────────────

export interface MethodTx {
  leanFn: string;
  argOrder?: 'normal' | 'flip';
  resultType: IRType;
  io?: boolean;
}

const STRING_METHODS: Record<string, MethodTx> = {
  length:       { leanFn: 'String.length',    resultType: TyNat },
  toUpperCase:  { leanFn: 'String.toUpper',   resultType: TyString },
  toLowerCase:  { leanFn: 'String.toLower',   resultType: TyString },
  trim:         { leanFn: 'String.trim',      resultType: TyString },
  trimStart:    { leanFn: 'String.trimLeft',  resultType: TyString },
  trimEnd:      { leanFn: 'String.trimRight', resultType: TyString },
  includes:     { leanFn: 'TSLean.Stdlib.String.includes', resultType: TyBool },
  startsWith:   { leanFn: 'String.startsWith', resultType: TyBool },
  endsWith:     { leanFn: 'String.endsWith',  resultType: TyBool },
  slice:        { leanFn: 'TSLean.Stdlib.String.slice', resultType: TyString },
  substring:    { leanFn: 'TSLean.Stdlib.String.slice', resultType: TyString },
  split:        { leanFn: 'String.splitOn',   resultType: TyArray(TyString) },
  replace:      { leanFn: 'TSLean.Stdlib.String.replaceFirst', resultType: TyString },
  replaceAll:   { leanFn: 'TSLean.Stdlib.String.replaceAll', resultType: TyString },
  indexOf:      { leanFn: 'TSLean.Stdlib.String.firstIndexOf', resultType: TyOption(TyNat) },
  lastIndexOf:  { leanFn: 'TSLean.Stdlib.String.lastIndexOf', resultType: TyOption(TyNat) },
  charAt:       { leanFn: 'String.get',       resultType: TyString },
  padStart:     { leanFn: 'TSLean.Stdlib.String.padStart', resultType: TyString },
  padEnd:       { leanFn: 'TSLean.Stdlib.String.padEnd',   resultType: TyString },
  repeat:       { leanFn: 'TSLean.Stdlib.String.repeat_',  resultType: TyString },
  at:           { leanFn: 'String.get?',      resultType: TyOption(TyString) },
  match:        { leanFn: 'TSLean.Stdlib.String.matchRegex', resultType: TyArray(TyString) },
  search:       { leanFn: 'TSLean.Stdlib.String.searchRegex', resultType: TyNat },
  concat:       { leanFn: 'String.append',    resultType: TyString },
  normalize:    { leanFn: 'id',               resultType: TyString },
  toString:     { leanFn: 'id',               resultType: TyString },
  valueOf:      { leanFn: 'id',               resultType: TyString },
};

const ARRAY_METHODS: Record<string, MethodTx> = {
  length:     { leanFn: 'Array.size',     resultType: TyNat },
  push:       { leanFn: 'Array.push',     resultType: TyUnit },
  pop:        { leanFn: 'Array.pop',      resultType: TyUnit },
  shift:      { leanFn: 'TSLean.Stdlib.Array.shift', resultType: TyUnit },
  unshift:    { leanFn: 'TSLean.Stdlib.Array.unshift', resultType: TyUnit },
  map:        { leanFn: 'Array.map',      resultType: TyArray({ tag: 'TypeVar', name: 'β' }) },
  filter:     { leanFn: 'Array.filter',   resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  reduce:     { leanFn: 'Array.foldl',    resultType: { tag: 'TypeVar', name: 'β' } },
  reduceRight:{ leanFn: 'Array.foldr',    resultType: { tag: 'TypeVar', name: 'β' } },
  forEach:    { leanFn: 'Array.forM',     resultType: TyUnit, io: true },
  find:       { leanFn: 'Array.find?',    resultType: TyOption({ tag: 'TypeVar', name: 'α' }) },
  findIndex:  { leanFn: 'Array.findIdx?', resultType: TyOption(TyNat) },
  findLast:   { leanFn: 'TSLean.Stdlib.Array.findLast', resultType: TyOption({ tag: 'TypeVar', name: 'α' }) },
  some:       { leanFn: 'Array.any',      resultType: TyBool },
  every:      { leanFn: 'Array.all',      resultType: TyBool },
  includes:   { leanFn: 'Array.contains', resultType: TyBool },
  indexOf:    { leanFn: 'Array.indexOf',  resultType: TyOption(TyNat) },
  slice:      { leanFn: 'Array.extract',  resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  splice:     { leanFn: 'TSLean.Stdlib.Array.splice', resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  concat:     { leanFn: 'Array.append',   resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  join:       { leanFn: 'String.intercalate', argOrder: 'flip', resultType: TyString },
  reverse:    { leanFn: 'Array.reverse',  resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  flat:       { leanFn: 'TSLean.Stdlib.Array.flatten', resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  flatMap:    { leanFn: 'TSLean.Stdlib.Array.flatMap', resultType: TyArray({ tag: 'TypeVar', name: 'β' }) },
  sort:       { leanFn: 'TSLean.Stdlib.Array.sort', resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  fill:       { leanFn: 'TSLean.Stdlib.Array.fill', resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  copyWithin: { leanFn: 'TSLean.Stdlib.Array.copyWithin', resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  at:         { leanFn: 'Array.get?',     resultType: TyOption({ tag: 'TypeVar', name: 'α' }) },
  with:       { leanFn: 'Array.set',      resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  keys:       { leanFn: 'List.range ∘ Array.size |>.toArray', resultType: TyArray(TyNat) },
  values:     { leanFn: 'Array.toList',   resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  entries:    { leanFn: 'Array.mapIdx (fun i x => (i, x))', resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  toString:   { leanFn: 'toString',       resultType: TyString },
};

const MAP_METHODS: Record<string, MethodTx> = {
  get:     { leanFn: 'AssocMap.find?',    resultType: TyOption({ tag: 'TypeVar', name: 'β' }) },
  set:     { leanFn: 'AssocMap.insert',   resultType: { tag: 'TypeRef', name: 'Map', args: [] } },
  has:     { leanFn: 'AssocMap.contains', resultType: TyBool },
  delete:  { leanFn: 'AssocMap.erase',    resultType: { tag: 'TypeRef', name: 'Map', args: [] } },
  size:    { leanFn: 'AssocMap.size',     resultType: TyNat },
  keys:    { leanFn: 'AssocMap.keys',     resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  values:  { leanFn: 'AssocMap.values',   resultType: TyArray({ tag: 'TypeVar', name: 'β' }) },
  entries: { leanFn: 'AssocMap.toList',   resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  forEach: { leanFn: 'AssocMap.forM',     resultType: TyUnit, io: true },
  clear:   { leanFn: 'fun _ => AssocMap.empty', resultType: { tag: 'TypeRef', name: 'Map', args: [] } },
};

const SET_METHODS: Record<string, MethodTx> = {
  add:     { leanFn: 'AssocSet.insert',   resultType: { tag: 'TypeRef', name: 'Set', args: [] } },
  has:     { leanFn: 'AssocSet.contains', resultType: TyBool },
  delete:  { leanFn: 'AssocSet.erase',    resultType: { tag: 'TypeRef', name: 'Set', args: [] } },
  size:    { leanFn: 'AssocSet.size',     resultType: TyNat },
  forEach: { leanFn: 'AssocSet.forM',     resultType: TyUnit, io: true },
  values:  { leanFn: 'AssocSet.toList',   resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  keys:    { leanFn: 'AssocSet.toList',   resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  entries: { leanFn: 'AssocSet.toList |>.map (fun x => (x, x))', resultType: TyArray({ tag: 'TypeVar', name: 'α' }) },
  clear:   { leanFn: 'fun _ => AssocSet.empty', resultType: { tag: 'TypeRef', name: 'Set', args: [] } },
};

export type ObjKind = 'String' | 'Array' | 'Map' | 'Set' | 'unknown';

export function lookupMethod(kind: ObjKind, method: string): MethodTx | undefined {
  switch (kind) {
    case 'String': return STRING_METHODS[method];
    case 'Array':  return ARRAY_METHODS[method];
    case 'Map':    return MAP_METHODS[method];
    case 'Set':    return SET_METHODS[method];
    default:       return undefined;
  }
}

// ─── Global function translations ─────────────────────────────────────────────

export interface GlobalTx { leanExpr: string; io?: boolean; maxArgs?: number }

const GLOBALS: Record<string, GlobalTx> = {
  'console.log':    { leanExpr: 'IO.println',           io: true },
  'console.error':  { leanExpr: 'IO.eprintln',          io: true },
  'console.warn':   { leanExpr: 'IO.eprintln',          io: true },
  'console.info':   { leanExpr: 'IO.println',           io: true },
  'Date.now':       { leanExpr: '0' },
  // Math.* sits in three tiers, and only two of them can name a carrier honestly.
  //
  // Tier 1 — proved. TSLean.Refinement.Math computes these from the binary64 encoding by
  // exact integer arithmetic, so what they return is a theorem rather than a property of
  // a runtime primitive. Lean's own operators are not these functions: `max 1 NaN` is 1,
  // `max 0 (-0)` is -0, `min 0 (-0)` is +0 and `Float.round (-0.5)` is -1, where Node
  // gives NaN, +0, -0 and -0. The constants are emitted as exact encodings rather than
  // decimal literals because the literal route is `Float.ofScientific`, whose rounding
  // this model already declines to trust at binary64 boundaries.
  'Math.abs':       { leanExpr: 'TSLean.Stdlib.Numeric.Math.abs' },
  'Math.sign':      { leanExpr: 'TSLean.Stdlib.Numeric.Math.sign' },
  'Math.trunc':     { leanExpr: 'TSLean.Stdlib.Numeric.Math.trunc' },
  'Math.floor':     { leanExpr: 'TSLean.Stdlib.Numeric.Math.floor' },
  'Math.ceil':      { leanExpr: 'TSLean.Stdlib.Numeric.Math.ceil' },
  'Math.round':     { leanExpr: 'TSLean.Stdlib.Numeric.Math.round' },
  'Math.max':       { leanExpr: 'TSLean.Stdlib.Numeric.Math.max' },
  'Math.min':       { leanExpr: 'TSLean.Stdlib.Numeric.Math.min' },
  'Math.PI':        { leanExpr: 'TSLean.Stdlib.Numeric.Math.PI' },
  'Math.E':         { leanExpr: 'TSLean.Stdlib.Numeric.Math.E' },
  'Math.LN2':       { leanExpr: 'TSLean.Stdlib.Numeric.Math.LN2' },
  'Math.LN10':      { leanExpr: 'TSLean.Stdlib.Numeric.Math.LN10' },
  'Math.SQRT2':     { leanExpr: 'TSLean.Stdlib.Numeric.Math.SQRT2' },
  'Math.SQRT1_2':   { leanExpr: 'TSLean.Stdlib.Numeric.Math.SQRT1_2' },
  // Tier 2 — one assumption. IEEE-754 mandates a correctly rounded square root, so
  // TSLean.Refinement.Math.Sqrt is the whole of what this mapping asks to be believed.
  'Math.sqrt':      { leanExpr: 'Float.sqrt' },
  // Tier 3 — absent. ECMA-262 leaves exp, log, log2, log10, sin, cos, tan, asin, acos,
  // atan, atan2, pow, cbrt and hypot implementation-approximated, so no Lean carrier can
  // claim Node's bits. They stay unmapped and degrade visibly instead.
  //
  // random is IO, and clz32/fround/imul are integer or float32 operations that this
  // Number model does not cover; all four remain unjustified stubs.
  'Math.random':    { leanExpr: 'IO.rand',              io: true },
  'Math.clz32':     { leanExpr: 'fun _ => 0' },
  'Math.fround':    { leanExpr: 'id' },
  'Math.imul':      { leanExpr: 'fun a b => a * b' },
  'parseInt':       { leanExpr: 'TSLean.Stdlib.Numeric.parseInt', maxArgs: 1 },
  'parseFloat':     { leanExpr: 'String.toFloat?', maxArgs: 1 },
  'Number.isNaN':       { leanExpr: 'Float.isNaN' },
  'Number.isFinite':    { leanExpr: 'TSLean.Stdlib.Numeric.FloatExt.isFinite' },
  'Number.isInteger':   { leanExpr: 'TSLean.Stdlib.Numeric.FloatExt.isInteger' },
  'Number.isSafeInteger': { leanExpr: 'TSLean.Stdlib.Numeric.FloatExt.isInteger' },
  'Number.parseInt':    { leanExpr: 'TSLean.Stdlib.Numeric.parseInt', maxArgs: 1 },
  'Number.parseFloat':  { leanExpr: 'String.toFloat?', maxArgs: 1 },
  'Number.MAX_SAFE_INTEGER': { leanExpr: '9007199254740991' },
  'Number.MIN_SAFE_INTEGER': { leanExpr: '-9007199254740991' },
  'Number.EPSILON':     { leanExpr: '2.220446049250313e-16' },
  'Number.POSITIVE_INFINITY': { leanExpr: 'Float.inf' },
  'Number.NEGATIVE_INFINITY': { leanExpr: '(-Float.inf)' },
  'Number.NaN':         { leanExpr: 'Float.nan' },
  'isNaN':          { leanExpr: 'Float.isNaN' },
  'isFinite':       { leanExpr: 'TSLean.Stdlib.Numeric.FloatExt.isFinite' },
  'JSON.stringify': { leanExpr: 'serialize' },
  'JSON.parse':     { leanExpr: 'deserialize' },
  'Object.keys':    { leanExpr: 'AssocMap.keys' },
  'Object.values':  { leanExpr: 'AssocMap.values' },
  'Object.entries': { leanExpr: 'AssocMap.toList' },
  'Object.assign':  { leanExpr: 'AssocMap.mergeWith (fun _ b => b)' },
  'Object.fromEntries': { leanExpr: 'AssocMap.ofList' },
  'Object.create':  { leanExpr: 'id', maxArgs: 1 },
  'Object.getPrototypeOf': { leanExpr: 'id', maxArgs: 1 },
  'Object.defineProperty': { leanExpr: 'TSLean.Stdlib.Object.defineProperty', maxArgs: 3 },
  'Array.from':     { leanExpr: 'List.toArray' },
  'Array.isArray':  { leanExpr: 'TSLean.Stdlib.Array.isArray', maxArgs: 1 },
  'Promise.resolve':{ leanExpr: 'pure' },
  'Promise.reject': { leanExpr: 'TSLean.Stdlib.Async.promiseReject', io: true },
  'Promise.all':    { leanExpr: 'TSLean.Stdlib.Async.promiseAll',    io: true },
  'Promise.race':   { leanExpr: 'TSLean.Stdlib.Async.promiseRace',   io: true },
  'Promise.allSettled': { leanExpr: 'TSLean.Stdlib.Async.promiseAllSettled', io: true },
  'Promise.any':    { leanExpr: 'TSLean.Stdlib.Async.promiseAny',    io: true },
  'setTimeout':     { leanExpr: 'TSLean.Stdlib.Async.setTimeout',    io: true },
  'setInterval':    { leanExpr: 'TSLean.Stdlib.Async.setInterval',   io: true },
  'queueMicrotask': { leanExpr: 'TSLean.Stdlib.Async.queueMicrotask', io: true },
  'structuredClone':{ leanExpr: 'id' },
  'clearTimeout':   { leanExpr: 'TSLean.Stdlib.Async.clearTimeout', io: false },
  'clearInterval':  { leanExpr: 'TSLean.Stdlib.Async.clearInterval', io: false },
  'btoa':           { leanExpr: 'id', maxArgs: 1 },
  'atob':           { leanExpr: 'id', maxArgs: 1 },
  'BigInt':         { leanExpr: 'Int.ofNat', maxArgs: 1 },
  'String.fromCharCode': { leanExpr: 'Char.ofNat', maxArgs: 1 },
  'encodeURIComponent': { leanExpr: 'TSLean.encodeURI' },
  'decodeURIComponent': { leanExpr: 'TSLean.decodeURI' },
  'fetch':              { leanExpr: 'WebAPI.fetch',           io: true },
  'crypto.randomUUID':  { leanExpr: '"uuid-stub"',            io: false },
  'crypto.getRandomValues': { leanExpr: 'default',            io: false },
};

export function lookupGlobal(name: string): GlobalTx | undefined { return GLOBALS[name]; }

// ─── Binary operator translation ──────────────────────────────────────────────

export function translateBinOp(op: BinOp, lhsType: IRType): string {
  if (op === 'Add' && lhsType.tag === 'String') return '++';
  switch (op) {
    case 'Add':          return '+';
    case 'Sub':          return '-';
    case 'Mul':          return '*';
    case 'Div':          return '/';
    case 'Mod':          return '%';
    case 'Eq':           return '==';
    case 'Ne':           return '!=';
    case 'Lt':           return '<';
    case 'Le':           return '<=';
    case 'Gt':           return '>';
    case 'Ge':           return '>=';
    case 'And':          return '&&';
    case 'Or':           return '||';
    case 'BitAnd':       return '&&&';
    case 'BitOr':        return '|||';
    case 'BitXor':       return '^^^';
    case 'Shl':          return '<<<';
    case 'Shr':          return '>>>';
    case 'Concat':       return '++';
    case 'NullCoalesce': return 'NullCoalesce'; // handled in codegen
    default:             return op;
  }
}

export function typeObjKind(t: IRType): ObjKind {
  if (t.tag === 'String') return 'String';
  if (t.tag === 'Array')  return 'Array';
  if (t.tag === 'Map')    return 'Map';
  if (t.tag === 'Set')    return 'Set';
  if (t.tag === 'TypeRef' && (t.name === 'Map' || t.name === 'AssocMap')) return 'Map';
  if (t.tag === 'TypeRef' && (t.name === 'Set' || t.name === 'AssocSet')) return 'Set';
  return 'unknown';
}
