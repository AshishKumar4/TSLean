# TSLean Standard Library Reference

## String Methods

| JS Method | Lean Function | Return Type |
|-----------|--------------|-------------|
| `s.length` | `String.length` | `Nat` |
| `s.toUpperCase()` | `String.toUpper` | `String` |
| `s.toLowerCase()` | `String.toLower` | `String` |
| `s.trim()` | `String.trim` | `String` |
| `s.trimStart()` | `String.trimLeft` | `String` |
| `s.trimEnd()` | `String.trimRight` | `String` |
| `s.includes(x)` | `TSLean.Stdlib.String.includes` | `Bool` |
| `s.startsWith(x)` | `String.startsWith` | `Bool` |
| `s.endsWith(x)` | `String.endsWith` | `Bool` |
| `s.indexOf(x)` | `TSLean.Stdlib.String.firstIndexOf` | `Option Nat` |
| `s.lastIndexOf(x)` | `TSLean.Stdlib.String.lastIndexOf` | `Option Nat` |
| `s.slice(i, j)` | `TSLean.Stdlib.String.slice` | `String` |
| `s.split(sep)` | `String.splitOn` | `Array String` |
| `s.replace(a, b)` | `TSLean.Stdlib.String.replaceFirst` | `String` |
| `s.replaceAll(a, b)` | `TSLean.Stdlib.String.replaceAll` | `String` |
| `s.repeat(n)` | `TSLean.Stdlib.String.repeat_` | `String` |
| `s.padStart(n, c)` | `TSLean.Stdlib.String.padStart` | `String` |
| `s.padEnd(n, c)` | `TSLean.Stdlib.String.padEnd` | `String` |
| `s.charAt(i)` | `String.get` | `String` |
| `s.concat(t)` | `String.append` | `String` |

## Array Methods

| JS Method | Lean Function | Return Type |
|-----------|--------------|-------------|
| `a.length` | `Array.size` | `Nat` |
| `a.push(x)` | `Array.push` | `Unit` |
| `a.pop()` | `Array.pop` | `Unit` |
| `a.shift()` | `TSLean.Stdlib.Array.shift` | `Unit` |
| `a.unshift(x)` | `TSLean.Stdlib.Array.unshift` | `Unit` |
| `a.map(f)` | `Array.map` | `Array B` |
| `a.filter(p)` | `Array.filter` | `Array A` |
| `a.reduce(f, init)` | `Array.foldl` | `B` |
| `a.find(p)` | `Array.find?` | `Option A` |
| `a.findIndex(p)` | `Array.findIdx?` | `Option Nat` |
| `a.some(p)` | `Array.any` | `Bool` |
| `a.every(p)` | `Array.all` | `Bool` |
| `a.includes(x)` | `Array.contains` | `Bool` |
| `a.indexOf(x)` | `Array.indexOf` | `Option Nat` |
| `a.slice(i, j)` | `Array.extract` | `Array A` |
| `a.splice(i, n, ...)` | `TSLean.Stdlib.Array.splice` | `Array A` |
| `a.sort()` | `TSLean.Stdlib.Array.sort` | `Array A` |
| `a.reverse()` | `Array.reverse` | `Array A` |
| `a.flat()` | `TSLean.Stdlib.Array.flatten` | `Array A` |
| `a.flatMap(f)` | `TSLean.Stdlib.Array.flatMap` | `Array B` |
| `a.concat(b)` | `Array.append` | `Array A` |
| `a.join(sep)` | `String.intercalate` | `String` |
| `a.forEach(f)` | `Array.forM` | `IO Unit` |

## Map Methods

| JS Method | Lean Function |
|-----------|--------------|
| `m.get(k)` | `AssocMap.find?` |
| `m.set(k, v)` | `AssocMap.insert` |
| `m.has(k)` | `AssocMap.contains` |
| `m.delete(k)` | `AssocMap.erase` |
| `m.size` | `AssocMap.size` |
| `m.keys()` | `AssocMap.keys` |
| `m.values()` | `AssocMap.values` |
| `m.entries()` | `AssocMap.toList` |
| `m.forEach(f)` | `AssocMap.forM` |
| `m.clear()` | `AssocMap.empty` |

## Global Functions

| JS Function | Lean Expression |
|-------------|----------------|
| `console.log(x)` | `IO.println x` |
| `console.error(x)` | `IO.eprintln x` |
| `Math.floor(x)` | `Float.floor x` |
| `Math.ceil(x)` | `Float.ceil x` |
| `Math.abs(x)` | `Float.abs x` |
| `Math.sqrt(x)` | `Float.sqrt x` |
| `Math.max(a, b)` | `max a b` |
| `Math.min(a, b)` | `min a b` |
| `Math.PI` | `3.141592653589793` |
| `parseInt(s)` | `s.toNat?.getD 0` |
| `JSON.stringify(x)` | `serialize x` |
| `JSON.parse(s)` | `deserialize s` |
| `Promise.all(xs)` | `TSLean.Stdlib.Async.promiseAll` |
| `Promise.race(xs)` | `TSLean.Stdlib.Async.promiseRace` |
| `setTimeout(ms, f)` | `TSLean.Stdlib.Async.setTimeout` |

## Node.js Stubs (Axiomatized)

- **node:fs**: readFileSync, writeFileSync, existsSync, mkdirSync, readdirSync, statSync
- **node:path**: join, resolve, dirname, basename, extname, relative, normalize
- **node:http**: createServer, request, Method/IncomingMessage/ServerResponse types
- **process**: env, argv, exit, cwd, stdout/stderr/stdin
