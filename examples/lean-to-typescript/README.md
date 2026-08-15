# Lean to TypeScript pilot

`placement.generated.ts` is generated directly from the kernel-checked declarations in
`lean/TSLean/Examples/Placement.lean`. It is the executable TypeScript implementation;
there is no handwritten decision twin.

In a writable source checkout, build the package and regenerate the artifact and its
provenance manifest with:

```bash
bun run build
bun run lean-to-typescript:generate
```

Published packages expose the general `lean-to-typescript` executable for compiling a
separate Lean project; the command above is the repository's canonical pilot workflow.

The generator accepts only the declared pure, total, first-order fragment. Passing the
tests means the generated decision agreed with Lean on this example's complete 4,096-case
input domain. That is exhaustive evidence for this finite decision, not a general
TypeScript refinement proof.

`placement.adapter.ts` is the explicit runtime boundary registered for the pilot. It validates
plain placement-set data before calling the generated decision; it is not part of the compiler's
semantic correspondence claim.
