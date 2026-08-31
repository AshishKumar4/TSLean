> Edited & maintained by Claude; presented as-is.

# Round-trip examples

These sources go TypeScript to Lean to TypeScript. See [the round-trip
contract](../../docs/roundtrip.md) for the profile they are checked against.

| File                          | What it shows                                                        |
| ----------------------------- | -------------------------------------------------------------------- |
| `tier.ts`                     | Enumerations, a structure, `Option`, and a call chain that round-trips |
| `hostile-recursive-union.ts`  | A recursive data union the profile refuses, with the reason            |
| `hostile-mutable-class.ts`    | A mutating class the profile refuses, with the reason                  |

```bash
tslean roundtrip --source examples/roundtrip/tier.ts
tslean roundtrip --source examples/roundtrip/hostile-recursive-union.ts   # refuses
tslean roundtrip --source examples/roundtrip/hostile-mutable-class.ts     # refuses
```

A refusal is the expected result for a hostile source. The report names the declaration and
why the profile does not carry it.
