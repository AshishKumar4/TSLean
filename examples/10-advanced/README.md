# 10 — Advanced: Limitations and Workarounds

Shows patterns that produce `sorry` in the Lean output, with recommended workarounds.

## Patterns that degrade

| Pattern | Why | Workaround |
|---|---|---|
| `typeof x === 'string'` | Runtime type check has no Lean equivalent | Use discriminated unions with a `type` tag |
| `text.match(/regex/)` | RegExp not expressible in pure Lean | Use string operations (split, includes, indexOf) |
| `Partial<T>` (generic) | Mapped types require `keyof` (no Lean equivalent) | Use concrete types or define manually |

## Using `--strict`

```bash
# This will ERROR instead of emitting sorry:
npx tsx src/cli.ts examples/10-advanced/limitations.ts -o output.lean --strict
```

The `--strict` flag scans the emitted Lean and rejects it if it carries any `sorry` axiom or `default` placeholder, useful for CI/CD pipelines where you want to guarantee complete translation. Because the check reads the artifact rather than the lowerer's bookkeeping, it also catches placeholders no degradation site recorded — a `⟨sorry⟩` instance emitted for mutually recursive types, for example.
