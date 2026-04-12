// Stdlib mapping: TypeScript built-ins → Lean 4 equivalents.

import { IRType, BinOp, TyString, TyFloat, TyBool, TyNat, TyUnit, TyArray, TyOption } from '../ir/types.js';

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
  'Date.now':       { leanExpr: '0',                        io: false },  // IO.monoNanosNow is BaseIO Nat, hard to use in pure context
  'Math.floor':     { leanExpr: 'Float.floor' },
  'Math.ceil':      { leanExpr: 'Float.ceil' },
  'Math.round':     { leanExpr: 'Float.round' },
  'Math.abs':       { leanExpr: 'Float.abs' },
  'Math.sqrt':      { leanExpr: 'Float.sqrt' },
  'Math.max':       { leanExpr: 'max' },
  'Math.min':       { leanExpr: 'min' },
  'Math.pow':       { leanExpr: 'Float.pow' },
  'Math.log':       { leanExpr: 'Float.log' },
  'Math.log2':      { leanExpr: 'TSLean.Stdlib.Numeric.FloatExt.log2' },
  'Math.log10':     { leanExpr: 'TSLean.Stdlib.Numeric.FloatExt.log10' },
  'Math.exp':       { leanExpr: 'Float.exp' },
  'Math.sin':       { leanExpr: 'Float.sin' },
  'Math.cos':       { leanExpr: 'Float.cos' },
  'Math.tan':       { leanExpr: 'Float.tan' },
  'Math.atan2':     { leanExpr: 'Float.atan2' },
  'Math.asin':      { leanExpr: 'Float.asin' },
  'Math.acos':      { leanExpr: 'Float.acos' },
  'Math.atan':      { leanExpr: 'Float.atan' },
  'Math.trunc':     { leanExpr: 'TSLean.Stdlib.Numeric.FloatExt.trunc' },
  'Math.sign':      { leanExpr: 'TSLean.Stdlib.Numeric.sign ∘ Float.toUInt64 ∘ fun x => x' },
  'Math.random':    { leanExpr: 'IO.rand',              io: true },
  'Math.PI':        { leanExpr: '3.141592653589793' },
  'Math.E':         { leanExpr: '2.718281828459045' },
  'Math.LN2':       { leanExpr: '0.6931471805599453' },
  'Math.LN10':      { leanExpr: '2.302585092994046' },
  'Math.SQRT2':     { leanExpr: '1.4142135623730951' },
  'Math.SQRT1_2':   { leanExpr: '0.7071067811865476' },
  'Math.hypot':     { leanExpr: 'fun a b => Float.sqrt (a * a + b * b)' },
  'Math.cbrt':      { leanExpr: 'fun x => Float.pow x (1.0 / 3.0)' },
  'Math.clz32':     { leanExpr: 'fun _ => 0' },
  'Math.fround':    { leanExpr: 'id' },
  'Math.imul':      { leanExpr: 'fun a b => a * b' },
  'parseInt':       { leanExpr: 'fun s => s.toNat?.getD 0', maxArgs: 1 },
  'parseFloat':     { leanExpr: 'String.toFloat?', maxArgs: 1 },
  'Number.isNaN':       { leanExpr: 'Float.isNaN' },
  'Number.isFinite':    { leanExpr: 'TSLean.Stdlib.Numeric.FloatExt.isFinite' },
  'Number.isInteger':   { leanExpr: 'fun x => Float.floor x == x' },
  'Number.isSafeInteger': { leanExpr: 'fun x => Float.floor x == x' },
  'Number.parseInt':    { leanExpr: 'fun s => s.toNat?.getD 0', maxArgs: 1 },
  'Number.parseFloat':  { leanExpr: 'String.toFloat?', maxArgs: 1 },
  'Number.MAX_SAFE_INTEGER': { leanExpr: '9007199254740991' },
  'Number.MIN_SAFE_INTEGER': { leanExpr: '-9007199254740991' },
  'Number.EPSILON':     { leanExpr: '2.220446049250313e-16' },
  'Number.POSITIVE_INFINITY': { leanExpr: 'Float.inf' },
  'Number.NEGATIVE_INFINITY': { leanExpr: '(-Float.inf)' },
  'Number.NaN':         { leanExpr: 'Float.nan' },
  'isNaN':          { leanExpr: 'Float.isNaN' },
  'isFinite':       { leanExpr: 'TSLean.Stdlib.Numeric.FloatExt.isFinite' },
  'JSON.stringify': { leanExpr: 'serialize' },    // TSLean.serialize, opened via `open TSLean`
  'JSON.parse':     { leanExpr: 'deserialize' },  // TSLean.deserialize
  'Object.keys':    { leanExpr: 'AssocMap.keys' },
  'Object.values':  { leanExpr: 'AssocMap.values' },
  'Object.entries': { leanExpr: 'AssocMap.toList' },
  'Object.assign':  { leanExpr: 'AssocMap.mergeWith (fun _ b => b)' },
  'Array.from':     { leanExpr: 'Array.ofList' },
  'Array.isArray':  { leanExpr: 'fun _ => true' },
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
