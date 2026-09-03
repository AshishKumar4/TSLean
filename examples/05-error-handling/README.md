# 05 — Error Handling

TypeScript's try/catch/finally maps to Lean's `tryCatch` and `ExceptT` monad transformer.

## Key patterns

- `throw new Error(msg)` → `throw msg` (in ExceptT context)
- `try { ... } catch (e) { ... }` → `tryCatch (do ...) (fun e => ...)`
- `finally { ... }` → let-bind + cleanup sequence
- Functions that throw → return type wrapped in `ExceptT String (IO T)`
