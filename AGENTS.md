# TSLean — TypeScript to Lean 4 Transpiler

## Quick Reference

```bash
# Install dependencies
bun install

# Run tests (vitest)
bun run test           # or: npx vitest run

# Transpile a single file
npx tsx src/cli.ts input.ts -o output.lean

# Build the Lean runtime library
export PATH="$HOME/.elan/bin:$PATH"
cd lean && lake build
```

## Project Structure

```
src/
  cli.ts              — CLI entry point
  codegen/            — Lean AST construction and printing
    lower.ts          — IR → LeanAST lowering (main codegen logic)
    printer.ts        — LeanAST → Lean 4 text rendering
    lean-ast.ts       — LeanAST type definitions
    v2.ts             — Pipeline orchestrator (lowerModule → printFile)
  parser/             — TypeScript → IR parsing
  ir/                 — Intermediate representation types
  rewrite/            — IR-level rewrite passes
  typemap/            — TS type → Lean type mapping
  stdlib/             — Lean stdlib function mappings
  stubs/              — Stub definitions for external APIs
lean/
  TSLean/             — Lean 4 runtime library
    Runtime/          — Basic types, Monad, Coercions, Validation
    Stdlib/           — Array, HashMap (AssocMap), HashSet, String, Numeric
    Effects/          — EffectKind, EffectSet
    DurableObjects/   — DO model (Storage, Http, WebSocket, RPC, etc.)
    Verification/     — ProofObligation, Invariants, Tactics
    Generated/        — Transpiler output stubs
  lakefile.toml       — Lake build config (pure Lean 4.16, no Mathlib)
```

## Lean 4 Setup

Lean 4.16.0 via elan: `export PATH="$HOME/.elan/bin:$PATH"`

The pin is exact, and it is not free to move: the Lean-to-TypeScript compiler
refuses a target project whose toolchain is not byte-identical to its own, and
Agent Core's formal library is `leanprover/lean4:v4.16.0`.

If elan does not already have the toolchain:
```bash
elan toolchain install leanprover/lean4:v4.16.0
```

## Lean Runtime Architecture

- `TSAny := String` — all erased TS types collapse to String
- `DOMonad = StateT sigma (ExceptT TSError IO)` — Durable Object monad
- `AssocMap` — list-backed hashmap (replaces Mathlib's AList)
- `AssocSet` — list-backed set (`List alpha`)
- Theorems use `sorry` where Lean 4.16 API gaps exist

## Codegen Pipeline

```
TS Source → Parser (parser/) → IR (ir/) → Rewrite (rewrite/) → Lower (codegen/lower.ts) → LeanAST → Print (codegen/printer.ts) → Lean 4
```

Key lowering decisions:
- `Map<K,V>` → `AssocMap K V`
- `Set<T>` → `Array T` (lowerType) — Set method calls map to Array operations
- `number` → `Float` (or `Nat` for known integers)
- `null`/`undefined` → `none` for Option types, `default` for others
- `{ ...a, ...b }` → `AssocMap.mergeWith (fun _ b => b) a b`
- Struct fields with function types → `Inhabited` only (no Repr/BEq deriving)

## Checking a single file against Lean

```bash
export PATH="$HOME/.elan/bin:$PATH"
npx tsx src/cli.ts path/to/file.ts -o /tmp/test.lean
cd lean && lake env lean /tmp/test.lean
```

## Known Error Patterns (for remaining failures)

1. **Unknown identifiers** — functions referenced before definition (needs def reordering/mutual blocks)
2. **expected structure** — struct update `{ x with ... }` on non-struct types
3. **synthInstanceFailed** — missing typeclass instances (Repr/BEq on types with IO fields)
4. **Application type mismatch** — generic type param vs TSAny, Option vs unwrapped
5. **Invalid field notation** — field access on types that lost their struct info during type erasure

## Code Style

- No duplicated logic; keep the transpiler DRY
- Test with `npx vitest run` before committing
- Verify Lean build with `lake build` before committing
- Prefer fixing root causes in the lowerer over post-processing hacks

## Multi-Agent Safety

Multiple agents may be working on this codebase. After writing Lean files, check for appended content:
```bash
for f in $(find lean/TSLean -name "*.lean"); do
  total=$(wc -l < "$f")
  last_end=$(grep -n "^end TSLean" "$f" | head -1 | cut -d: -f1)
  if [ -n "$last_end" ] && [ "$last_end" -lt "$total" ]; then
    head -"$last_end" "$f" > /tmp/f && mv /tmp/f "$f"
  fi
done
```
