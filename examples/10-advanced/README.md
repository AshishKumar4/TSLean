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

The `--strict` flag turns sorry warnings into errors, useful for CI/CD pipelines where you want to guarantee complete translation.
