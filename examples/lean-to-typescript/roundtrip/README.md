> Edited & maintained by Claude; presented as-is.

# Lean-to-TypeScript round-trip examples

Each example is one Lean module and the TypeScript the compiler emits for it. There is no
handwritten TypeScript twin: everything under `<Name>/generated/` is compiler output, and
`registry.json` is the only place an example is declared.

Several examples carry a theorem about the definition they export. A theorem does not reach
the generated TypeScript; it constrains the Lean the TypeScript came from.

| Example | Lean module | Exported declarations |
| ------- | ----------- | --------------------- |
| [Parity](Parity/generated/) | `TSLean.Examples.Roundtrip.Parity` | step |
| [Sign](Sign/generated/) | `TSLean.Examples.Roundtrip.Sign` | negate |
| [Bits](Bits/generated/) | `TSLean.Examples.Roundtrip.Bits` | exclusive, anySet |
| [Tribool](Tribool/generated/) | `TSLean.Examples.Roundtrip.Tribool` | notT, andT |
| [Severity](Severity/generated/) | `TSLean.Examples.Roundtrip.Severity` | atLeast, worst |
| [Access](Access/generated/) | `TSLean.Examples.Roundtrip.Access` | admits |
| [Lifecycle](Lifecycle/generated/) | `TSLean.Examples.Roundtrip.Lifecycle` | advance, terminal |
| [Choice](Choice/generated/) | `TSLean.Examples.Roundtrip.Choice` | choose |
| [Priority](Priority/generated/) | `TSLean.Examples.Roundtrip.Priority` | before |
| [Flags](Flags/generated/) | `TSLean.Examples.Roundtrip.Flags` | union, meet |
| [Direction](Direction/generated/) | `TSLean.Examples.Roundtrip.Direction` | opposite, clockwise |
| [Suit](Suit/generated/) | `TSLean.Examples.Roundtrip.Suit` | colourOf, sameColour |
| [Traffic](Traffic/generated/) | `TSLean.Examples.Roundtrip.Traffic` | next, mayCross |
| [Guard](Guard/generated/) | `TSLean.Examples.Roundtrip.Guard` | verdictOf, admitted |
| [Window](Window/generated/) | `TSLean.Examples.Roundtrip.Window` | fullyOpen, flip |
| [Vote](Vote/generated/) | `TSLean.Examples.Roundtrip.Vote` | pair, carried |
| [Route](Route/generated/) | `TSLean.Examples.Roundtrip.Route` | routeOf |
| [Retry](Retry/generated/) | `TSLean.Examples.Roundtrip.Retry` | recover |
| [Consent](Consent/generated/) | `TSLean.Examples.Roundtrip.Consent` | granted |
| [Tier](Tier/generated/) | `TSLean.Examples.Roundtrip.Tier` | floorOf, isDirect, honours |

## Regenerate

```bash
bun run build
node scripts/generate-roundtrip-examples.mjs           # write
node scripts/generate-roundtrip-examples.mjs --check   # fail on drift
```

## Behaviour check

Every example has a runnable behaviour check. The round trip compiles the generated
TypeScript back to Lean, elaborates it, and runs three programs over the whole input domain
of every exported function: the generated TypeScript, the recovered Lean, and the Lean the
example was generated from.

```bash
node scripts/check-roundtrip-examples.mjs
```

The same command gates the other direction through the same public entry point:
`examples/roundtrip/tier.ts` has to hold, and both hostile sources have to be refused. A
hostile source that stops being refused fails the gate exactly as a good one that stops
round-tripping does.

The check reports how many inputs it applied and whether that exhausted the domain. It
reports counterexamples. It states no theorem. See [the round-trip
contract](../../../docs/roundtrip.md).

