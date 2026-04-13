# TSLean Standard Library Reference

This documents every JavaScript standard library function and method that TSLean maps to a Lean 4 equivalent. The mapping tables live in `src/stdlib/index.ts`. The Lean implementations are in `lean/TSLean/Stdlib/` (custom functions) or Lean 4's core library (built-in functions).

Methods marked with **IO** require the `IO` monad. All others are pure.

## String Methods

Source: `STRING_METHODS` in `src/stdlib/index.ts`, implementations in `lean/TSLean/Stdlib/String.lean`.

| JS Method | Lean Function | Signature | Return |
|-----------|--------------|-----------|--------|
| `s.length` | `String.length` | `String → Nat` | `Nat` |
| `s.toUpperCase()` | `String.toUpper` | `String → String` | `String` |
| `s.toLowerCase()` | `String.toLower` | `String → String` | `String` |
| `s.trim()` | `String.trim` | `String → String` | `String` |
| `s.trimStart()` | `String.trimLeft` | `String → String` | `String` |
| `s.trimEnd()` | `String.trimRight` | `String → String` | `String` |
| `s.includes(x)` | `TSLean.Stdlib.String.includes` | `String → String → Bool` | `Bool` |
| `s.startsWith(x)` | `String.startsWith` | `String → String → Bool` | `Bool` |
| `s.endsWith(x)` | `String.endsWith` | `String → String → Bool` | `Bool` |
| `s.indexOf(x)` | `TSLean.Stdlib.String.firstIndexOf` | `String → String → Option Nat` | `Option Nat` |
| `s.lastIndexOf(x)` | `TSLean.Stdlib.String.lastIndexOf` | `String → String → Option Nat` | `Option Nat` |
| `s.slice(i, j)` | `TSLean.Stdlib.String.slice` | `String → Nat → Nat → String` | `String` |
| `s.substring(i, j)` | `TSLean.Stdlib.String.slice` | `String → Nat → Nat → String` | `String` |
| `s.split(sep)` | `String.splitOn` | `String → String → Array String` | `Array String` |
| `s.replace(a, b)` | `TSLean.Stdlib.String.replaceFirst` | `String → String → String → String` | `String` |
| `s.replaceAll(a, b)` | `TSLean.Stdlib.String.replaceAll` | `String → String → String → String` | `String` |
| `s.repeat(n)` | `TSLean.Stdlib.String.repeat_` | `String → Nat → String` | `String` |
| `s.padStart(n, c)` | `TSLean.Stdlib.String.padStart` | `String → Nat → String → String` | `String` |
| `s.padEnd(n, c)` | `TSLean.Stdlib.String.padEnd` | `String → Nat → String → String` | `String` |
| `s.charAt(i)` | `String.get` | `String → Nat → String` | `String` |
| `s.at(i)` | `String.get?` | `String → Nat → Option String` | `Option String` |
| `s.concat(t)` | `String.append` | `String → String → String` | `String` |
| `s.match(re)` | `TSLean.Stdlib.String.matchRegex` | `String → String → Array String` | `Array String` |
| `s.search(re)` | `TSLean.Stdlib.String.searchRegex` | `String → String → Nat` | `Nat` |
| `s.normalize()` | `id` | `String → String` | `String` |
| `s.toString()` | `id` | `String → String` | `String` |
| `s.valueOf()` | `id` | `String → String` | `String` |

### String usage examples

```typescript
// TypeScript
const upper = name.toUpperCase();
const parts = path.split("/");
const has = msg.includes("error");
const idx = text.indexOf("needle");
const trimmed = input.trim();
const padded = id.padStart(8, "0");
```
```lean
-- Lean 4
let upper := String.toUpper name
let parts := String.splitOn path "/"
let has := TSLean.Stdlib.String.includes msg "error"
let idx := TSLean.Stdlib.String.firstIndexOf text "needle"
let trimmed := String.trim input
let padded := TSLean.Stdlib.String.padStart id 8 "0"
```

Note: `indexOf` returns `Option Nat` rather than `-1` on miss, aligning with Lean's convention of using `Option` for partial functions.

## Array Methods

Source: `ARRAY_METHODS` in `src/stdlib/index.ts`, implementations in `lean/TSLean/Stdlib/Array.lean`.

| JS Method | Lean Function | Return | Notes |
|-----------|--------------|--------|-------|
| `a.length` | `Array.size` | `Nat` | Property, not method |
| `a.push(x)` | `Array.push` | `Unit` | |
| `a.pop()` | `Array.pop` | `Unit` | |
| `a.shift()` | `TSLean.Stdlib.Array.shift` | `Unit` | |
| `a.unshift(x)` | `TSLean.Stdlib.Array.unshift` | `Unit` | |
| `a.map(f)` | `Array.map` | `Array B` | |
| `a.filter(p)` | `Array.filter` | `Array A` | |
| `a.reduce(f, init)` | `Array.foldl` | `B` | |
| `a.reduceRight(f, init)` | `Array.foldr` | `B` | |
| `a.find(p)` | `Array.find?` | `Option A` | Returns `Option`, not `undefined` |
| `a.findIndex(p)` | `Array.findIdx?` | `Option Nat` | Returns `Option Nat`, not `-1` |
| `a.findLast(p)` | `TSLean.Stdlib.Array.findLast` | `Option A` | |
| `a.some(p)` | `Array.any` | `Bool` | |
| `a.every(p)` | `Array.all` | `Bool` | |
| `a.includes(x)` | `Array.contains` | `Bool` | |
| `a.indexOf(x)` | `Array.indexOf` | `Option Nat` | Returns `Option Nat`, not `-1` |
| `a.slice(i, j)` | `Array.extract` | `Array A` | |
| `a.splice(i, n, ...)` | `TSLean.Stdlib.Array.splice` | `Array A` | |
| `a.sort()` | `TSLean.Stdlib.Array.sort` | `Array A` | |
| `a.reverse()` | `Array.reverse` | `Array A` | |
| `a.flat()` | `TSLean.Stdlib.Array.flatten` | `Array A` | |
| `a.flatMap(f)` | `TSLean.Stdlib.Array.flatMap` | `Array B` | |
| `a.concat(b)` | `Array.append` | `Array A` | |
| `a.join(sep)` | `String.intercalate` | `String` | Argument order flipped |
| `a.forEach(f)` | `Array.forM` | `IO Unit` | **IO** |
| `a.fill(v)` | `TSLean.Stdlib.Array.fill` | `Array A` | |
| `a.copyWithin(t, s, e)` | `TSLean.Stdlib.Array.copyWithin` | `Array A` | |
| `a.at(i)` | `Array.get?` | `Option A` | |
| `a.with(i, v)` | `Array.set` | `Array A` | |
| `a.keys()` | `List.range ∘ Array.size \|>.toArray` | `Array Nat` | |
| `a.values()` | `Array.toList` | `Array A` | |
| `a.entries()` | `Array.mapIdx (fun i x => (i, x))` | `Array (Nat × A)` | |
| `a.toString()` | `toString` | `String` | |

### Array usage examples

```typescript
// TypeScript
const doubled = nums.map(x => x * 2);
const evens = nums.filter(x => x % 2 === 0);
const sum = nums.reduce((acc, x) => acc + x, 0);
const found = users.find(u => u.name === "alice");
const sorted = items.sort();
const flat = nested.flat();
```
```lean
-- Lean 4
let doubled := Array.map (fun x => x * 2) nums
let evens := Array.filter (fun x => x % 2 == 0) nums
let sum := Array.foldl (fun acc x => acc + x) 0 nums
let found := Array.find? (fun u => u.name == "alice") users
let sorted := TSLean.Stdlib.Array.sort items
let flat := TSLean.Stdlib.Array.flatten nested
```

## Map Methods

Source: `MAP_METHODS` in `src/stdlib/index.ts`, implementations in `lean/TSLean/Stdlib/HashMap.lean`.

Maps use `AssocMap K V` (association list), defined in `lean/TSLean/Stdlib/HashMap.lean`. This is a pure Lean 4 implementation without Mathlib dependency.

| JS Method | Lean Function | Return | Notes |
|-----------|--------------|--------|-------|
| `m.get(k)` | `AssocMap.find?` | `Option V` | Returns `Option`, not `undefined` |
| `m.set(k, v)` | `AssocMap.insert` | `AssocMap K V` | Returns new map (pure) |
| `m.has(k)` | `AssocMap.contains` | `Bool` | |
| `m.delete(k)` | `AssocMap.erase` | `AssocMap K V` | Returns new map (pure) |
| `m.size` | `AssocMap.size` | `Nat` | |
| `m.keys()` | `AssocMap.keys` | `Array K` | |
| `m.values()` | `AssocMap.values` | `Array V` | |
| `m.entries()` | `AssocMap.toList` | `Array (K × V)` | |
| `m.forEach(f)` | `AssocMap.forM` | `IO Unit` | **IO** |
| `m.clear()` | `fun _ => AssocMap.empty` | `AssocMap K V` | Returns fresh empty map |

### Map usage examples

```typescript
// TypeScript
const m = new Map<string, number>();
m.set("a", 1);
const val = m.get("a");
const exists = m.has("b");
m.delete("a");
```
```lean
-- Lean 4
let m : AssocMap String Float := AssocMap.empty
let m := AssocMap.insert m "a" 1
let val := AssocMap.find? m "a"    -- : Option Float
let exists := AssocMap.contains m "b"
let m := AssocMap.erase m "a"
```

## Set Methods

Source: `SET_METHODS` in `src/stdlib/index.ts`, implementations in `lean/TSLean/Stdlib/HashSet.lean`.

Sets use `AssocSet T`, backed by an array with uniqueness.

| JS Method | Lean Function | Return | Notes |
|-----------|--------------|--------|-------|
| `s.add(x)` | `AssocSet.insert` | `AssocSet T` | Returns new set (pure) |
| `s.has(x)` | `AssocSet.contains` | `Bool` | |
| `s.delete(x)` | `AssocSet.erase` | `AssocSet T` | Returns new set (pure) |
| `s.size` | `AssocSet.size` | `Nat` | |
| `s.forEach(f)` | `AssocSet.forM` | `IO Unit` | **IO** |
| `s.values()` | `AssocSet.toList` | `Array T` | |
| `s.keys()` | `AssocSet.toList` | `Array T` | Same as values (Set symmetry) |
| `s.entries()` | `AssocSet.toList \|>.map (fun x => (x, x))` | `Array (T × T)` | |
| `s.clear()` | `fun _ => AssocSet.empty` | `AssocSet T` | Returns fresh empty set |

### Set usage examples

```typescript
// TypeScript
const s = new Set<string>();
s.add("hello");
const has = s.has("hello");
s.delete("hello");
```
```lean
-- Lean 4
let s : AssocSet String := AssocSet.empty
let s := AssocSet.insert s "hello"
let has := AssocSet.contains s "hello"
let s := AssocSet.erase s "hello"
```

## Math Functions and Constants

Source: `GLOBALS` table in `src/stdlib/index.ts`, implementations via Lean 4 built-in `Float` or `lean/TSLean/Stdlib/Numeric.lean`.

### Math functions

| JS Function | Lean Expression | Notes |
|-------------|----------------|-------|
| `Math.floor(x)` | `Float.floor x` | Built-in |
| `Math.ceil(x)` | `Float.ceil x` | Built-in |
| `Math.round(x)` | `Float.round x` | Built-in |
| `Math.abs(x)` | `Float.abs x` | Built-in |
| `Math.sqrt(x)` | `Float.sqrt x` | Built-in |
| `Math.max(a, b)` | `max a b` | Built-in |
| `Math.min(a, b)` | `min a b` | Built-in |
| `Math.pow(a, b)` | `Float.pow a b` | Built-in |
| `Math.log(x)` | `Float.log x` | Natural log |
| `Math.log2(x)` | `TSLean.Stdlib.Numeric.FloatExt.log2 x` | Custom |
| `Math.log10(x)` | `TSLean.Stdlib.Numeric.FloatExt.log10 x` | Custom |
| `Math.exp(x)` | `Float.exp x` | Built-in |
| `Math.sin(x)` | `Float.sin x` | Built-in |
| `Math.cos(x)` | `Float.cos x` | Built-in |
| `Math.tan(x)` | `Float.tan x` | Built-in |
| `Math.asin(x)` | `Float.asin x` | Built-in |
| `Math.acos(x)` | `Float.acos x` | Built-in |
| `Math.atan(x)` | `Float.atan x` | Built-in |
| `Math.atan2(y, x)` | `Float.atan2 y x` | Built-in |
| `Math.trunc(x)` | `TSLean.Stdlib.Numeric.FloatExt.trunc x` | Custom |
| `Math.sign(x)` | `TSLean.Stdlib.Numeric.sign ...` | Custom |
| `Math.random()` | `IO.rand` | **IO** |
| `Math.hypot(a, b)` | `fun a b => Float.sqrt (a * a + b * b)` | Inline lambda |
| `Math.cbrt(x)` | `fun x => Float.pow x (1.0 / 3.0)` | Inline lambda |
| `Math.clz32(x)` | `fun _ => 0` | Stub |
| `Math.fround(x)` | `id` | No-op (already Float) |
| `Math.imul(a, b)` | `fun a b => a * b` | Simplified |

### Math constants

| JS Constant | Lean Value |
|-------------|-----------|
| `Math.PI` | `3.141592653589793` |
| `Math.E` | `2.718281828459045` |
| `Math.LN2` | `0.6931471805599453` |
| `Math.LN10` | `2.302585092994046` |
| `Math.SQRT2` | `1.4142135623730951` |
| `Math.SQRT1_2` | `0.7071067811865476` |

## Number Functions and Constants

| JS Function/Constant | Lean Expression |
|----------------------|----------------|
| `Number.isNaN(x)` | `Float.isNaN x` |
| `Number.isFinite(x)` | `TSLean.Stdlib.Numeric.FloatExt.isFinite x` |
| `Number.isInteger(x)` | `fun x => Float.floor x == x` |
| `Number.isSafeInteger(x)` | `fun x => Float.floor x == x` |
| `Number.parseInt(s)` | `fun s => s.toNat?.getD 0` |
| `Number.parseFloat(s)` | `String.toFloat?` |
| `Number.MAX_SAFE_INTEGER` | `9007199254740991` |
| `Number.MIN_SAFE_INTEGER` | `-9007199254740991` |
| `Number.EPSILON` | `2.220446049250313e-16` |
| `Number.POSITIVE_INFINITY` | `Float.inf` |
| `Number.NEGATIVE_INFINITY` | `(-Float.inf)` |
| `Number.NaN` | `Float.nan` |
| `isNaN(x)` | `Float.isNaN x` |
| `isFinite(x)` | `TSLean.Stdlib.Numeric.FloatExt.isFinite x` |
| `parseInt(s)` | `fun s => s.toNat?.getD 0` |
| `parseFloat(s)` | `String.toFloat?` |

## Console / IO

| JS Function | Lean Expression | Notes |
|-------------|----------------|-------|
| `console.log(x)` | `IO.println x` | **IO** |
| `console.error(x)` | `IO.eprintln x` | **IO** |
| `console.warn(x)` | `IO.eprintln x` | **IO** (maps to stderr) |
| `console.info(x)` | `IO.println x` | **IO** |

## JSON

| JS Function | Lean Expression | Notes |
|-------------|----------------|-------|
| `JSON.stringify(x)` | `serialize x` | Axiomatized in TSLean.Stdlib.JSON |
| `JSON.parse(s)` | `deserialize s` | Axiomatized in TSLean.Stdlib.JSON |

## Promise / Async

Source: `lean/TSLean/Stdlib/Async.lean`.

| JS Function | Lean Expression | Notes |
|-------------|----------------|-------|
| `Promise.resolve(x)` | `pure x` | Built-in monadic pure |
| `Promise.reject(e)` | `TSLean.Stdlib.Async.promiseReject e` | **IO** |
| `Promise.all(xs)` | `TSLean.Stdlib.Async.promiseAll xs` | **IO** |
| `Promise.race(xs)` | `TSLean.Stdlib.Async.promiseRace xs` | **IO** |
| `Promise.allSettled(xs)` | `TSLean.Stdlib.Async.promiseAllSettled xs` | **IO** |
| `Promise.any(xs)` | `TSLean.Stdlib.Async.promiseAny xs` | **IO** |
| `setTimeout(f, ms)` | `TSLean.Stdlib.Async.setTimeout f ms` | **IO** |
| `setInterval(f, ms)` | `TSLean.Stdlib.Async.setInterval f ms` | **IO** |
| `queueMicrotask(f)` | `TSLean.Stdlib.Async.queueMicrotask f` | **IO** |

## Object Utilities

| JS Function | Lean Expression |
|-------------|----------------|
| `Object.keys(o)` | `AssocMap.keys o` |
| `Object.values(o)` | `AssocMap.values o` |
| `Object.entries(o)` | `AssocMap.toList o` |
| `Object.assign(a, b)` | `AssocMap.mergeWith (fun _ b => b) a b` |

## Other Globals

| JS Function | Lean Expression | Notes |
|-------------|----------------|-------|
| `Array.from(x)` | `Array.ofList x` | |
| `Array.isArray(x)` | `fun _ => true` | Always true (type-checked) |
| `Date.now()` | `0` | Stub (no clock in pure Lean) |
| `fetch(url)` | `WebAPI.fetch url` | **IO**; see Runtime/WebAPI.lean |
| `structuredClone(x)` | `id x` | No-op (Lean values are immutable) |
| `encodeURIComponent(s)` | `TSLean.encodeURI s` | |
| `decodeURIComponent(s)` | `TSLean.decodeURI s` | |
| `crypto.randomUUID()` | `"uuid-stub"` | Stub; no real UUID generation |
| `crypto.getRandomValues(a)` | `default` | Stub |

## Binary Operators

The `translateBinOp` function in `src/stdlib/index.ts` maps IR binary operators to Lean operators:

| IR Op | Lean Op | Notes |
|-------|---------|-------|
| `Add` | `+` | `++` when LHS is `String` |
| `Sub` | `-` | |
| `Mul` | `*` | |
| `Div` | `/` | |
| `Mod` | `%` | |
| `Eq` | `==` | Structural equality |
| `Ne` | `!=` | |
| `Lt` | `<` | |
| `Le` | `<=` | |
| `Gt` | `>` | |
| `Ge` | `>=` | |
| `And` | `&&` | |
| `Or` | `\|\|` | |
| `BitAnd` | `&&&` | |
| `BitOr` | `\|\|\|` | |
| `BitXor` | `^^^` | |
| `Shl` | `<<<` | |
| `Shr` | `>>>` | |
| `Concat` | `++` | String/array concatenation |
| `NullCoalesce` | (special) | Handled in codegen as `Option.getD` |

## Node.js Stubs (Axiomatized)

These are generated as opaque types with axiomatized functions in `lean/TSLean/Stubs/`. They type-check but do not execute — they exist so that transpiled code referencing Node.js APIs compiles in Lean.

### node:fs (`TSLean.Stubs.NodeFs`)
`readFileSync`, `writeFileSync`, `existsSync`, `mkdirSync`, `readdirSync`, `statSync`, `unlinkSync`, `renameSync`

### node:path (`TSLean.Stubs.NodePath`)
`join`, `resolve`, `dirname`, `basename`, `extname`, `relative`, `normalize`, `isAbsolute`, `sep`

### node:http (`TSLean.Stubs.NodeHttp`)
`createServer`, `request`, `Method`, `IncomingMessage`, `ServerResponse`

### process (`TSLean.Stubs.Process`)
`env`, `argv`, `exit`, `cwd`, `stdout`, `stderr`, `stdin`

### console (`TSLean.Stubs.Console`)
Delegates to `IO.println` and `IO.eprintln`.

## Custom .d.ts Stub Generation

The `src/stubs/dts-reader.ts` module can read `.d.ts` files from npm packages and generate Lean stub modules. Usage:

```bash
# Generates lean/TSLean/Stubs/SomePackage.lean from the package's type declarations
npx tsx src/cli.ts --generate-stubs some-package
```

This produces opaque types and axiomatized functions, cached in `.tslean-cache/stubs/`.
