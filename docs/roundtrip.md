> Edited & maintained by Claude; presented as-is.

# Round trip

TSLean compiles Lean to TypeScript and TypeScript to Lean. Where the two directions carry
the same construct with the same declared semantics, a program can go round: Lean to
TypeScript to Lean, or TypeScript to Lean to TypeScript. This document states which
constructs those are, what a round trip checks, and what it does not claim.

Run one with:

```bash
tslean roundtrip --manifest examples/agent-core/facets/generated/tslean.manifest.json
tslean roundtrip --source examples/roundtrip/tier.ts
```

For `--manifest`, TSLean imports the original Lean module from the project path in the
manifest. Use `--source-root <dir>` only when that project moved. If neither path names a
Lake project with its own `lean-toolchain`, the original-source behavior check fails. TSLean
does not substitute its packaged runtime project, because that would compare the generated
TypeScript with a different source.

## The profile

The profile is the set of constructs both directions carry. It is a positive grammar over
the TypeScript type and syntax graph. A construct is inside the profile only when the
grammar derives it. Nothing is admitted by matching a name, a comment, or any other source
text.

### Types

| TypeScript                            | Lean               |
| ------------------------------------- | ------------------ |
| `boolean`                             | `Bool`             |
| `type E = "a" \| "b"`                 | `inductive E`      |
| `interface S` or `class S`            | `structure S`      |
| `T \| undefined`                      | `Option T`         |

An enumeration names its constructors with its own literals, so `"a"` in TypeScript and
`.a` in Lean are the same case. A literal that is not a Lean identifier cannot name a
constructor, so a union containing one is not an enumeration and leaves the profile.

A structure's fields are all `readonly` and all required, because a Lean structure field is
neither optional nor assignable in place. A structure that reaches itself leaves the
profile: the round trip enumerates value domains, and a recursive structure has no finite
one.

A class is inside the profile when it has exactly one constructor, that constructor takes
one initialiser carrying exactly the structure's fields, its body assigns every field from
the initialiser in declaration order, and it freezes the value. That is the one shape which
denotes a Lean structure introduction, so `new S(init)` and a Lean structure literal are the
same construction.

### Declarations

A function or method is inside the profile when it takes no type parameters, is neither
async nor a generator, has profile parameter and return types, and has a profile body. A
profile body binds constants, branches at the end, and returns.

Every other top-level form is outside the profile, including variable statements, enums,
and namespaces.

### Terms

Identifiers, `this`, field access on a structure, an enumeration literal, `true`, `false`,
`undefined`, `!`, `&&`, `||`, `===`, `!==`, a conditional expression, a call of a profile
function or method, `new S({ … })`, and an object literal that supplies every field of a
profile structure.

An equality over an enumeration never becomes Lean's derived equality. Lean derives equality
on an inductive by comparing constructor indices through `Nat.decEq`, which the
Lean-to-TypeScript fragment does not admit, so the comparison would leave the round trip. A
comparison against a literal decides every constructor of the enumeration, a comparison
between two values decides both, and a chain of comparisons of one value folds into a single
match. The fold is what makes the trip settle: a chain and a match are the same decision
written two ways, and the two compilers write it the two ways, so lowering each comparison on
its own would grow the term by one nesting level on every lap.

A call must name a declaration of the same program that is itself inside the profile. A call
into a library reaches semantics the round trip never checked.

## What a generated module carries beside its declarations

A Lean-to-TypeScript package carries decoders next to the declarations it came from. Those
decoders take the emitter's data union, which is every value a JSON document can deliver.
That union has no Lean carrier, so the decoders are outside the profile and the round trip
cannot carry them back.

The round trip drops them and then proves it dropped nothing else:

- the projection is cut on the syntax tree, not on names or text;
- the projected module must type-check on its own, so nothing it still needs was removed;
- every declaration the manifest records as the image of a Lean declaration must survive the
  projection, and a report names any that does not.

## What one run checks

Lean to TypeScript to Lean, from a generated package:

1. the generated TypeScript type-checks;
2. every declared Lean image is inside the profile, identified by owner and member together;
3. the projection type-checks on its own;
4. the recovered Lean carries no `sorry` and no `default`;
5. Lean accepts the recovered modules under the toolchain the project pins;
6. the generated TypeScript and the recovered Lean compute the same function over the
   enumerated input domain;
7. the generated TypeScript and **the Lean it was generated from** compute the same function
   over that domain;
8. a second lap produces the same projection and the same Lean.

Check 7 exists because checks 5 and 6 involve only the two compilers. A bug they share would
agree with itself. The Lean the package came from was written by hand and rewritten by
neither, so comparing against it closes that triangle. The public report exposes the recovered
comparison as `behaviour` and this original-source comparison as `sourceBehaviour`.

TypeScript to Lean to TypeScript, from TypeScript sources:

1. the source type-checks;
2. every source declaration is inside the profile;
3. the Lean carries no placeholder;
4. Lean accepts it;
5. the source TypeScript and the recovered Lean compute the same function over the
   enumerated input domain;
6. the Lean compiles back to TypeScript;
7. the regenerated TypeScript type-checks;
8. both sides declare the same enumerations, structures, and signatures;
9. a further lap produces the same Lean.

A fixed point is `f (f x) = f x`, so check 9 compares the second lap with the third. The
first lap starts from hand-written TypeScript and the compiler chooses its own declaration
order, so comparing the first lap with the second would report an ordering choice as a
defect. The comparison requires exactly the same module key set and the same normalized
imports, opens, and declarations. It does not ignore a module that appears only on the later
lap.

## Strict compilation

`tslean ts-to-lean --strict` accepts output only when Lean accepts it. A placeholder scan
reads the artifact, so it cannot see a lowering that is well-formed and ill-typed, and it
cannot see one that is well-typed and silently drops a call. Strict compilation therefore
elaborates the emitted module under the pinned toolchain as well. A toolchain it cannot run
is a refusal, because an unrun check is not an acceptance.

If Lean rejects a program, its behavior check is a failed check with `not run` in its detail.
The verifier keeps the earlier diagnostics. It does not claim that two programs agree when it
could not execute one.

## What a round trip does not claim

- It is not a proof. A report carries checks and counterexamples.
- Agreement over a finite domain says no counterexample was found in that domain. Each
  report states how many inputs it applied and whether that exhausted the domain.
- It says nothing about constructs outside the profile. The profile is small on purpose.
- It says nothing about a program's correctness. It compares two compilations of the same
  program with each other, not either of them with an intent.
- A module-private definition carries no separate observation. It is compiled, and Lean
  checks it, but the comparison reaches it only through the exported definitions that call
  it.
- A domain larger than the input budget is covered by its first inputs in odometer order, and
  the report says `SAMPLED, not exhausted` for that function. A domain too large to index is
  refused rather than sampled from a wrapped index.
- Two sources whose file base names collide compile to one Lean module name. The round trip
  refuses the pair rather than losing one of them.

## Counterexamples are kept

A disagreement is reported as the function, the inputs, and the two results:

```text
counterexample both sides compute the same function @ Policy.ts#Policy.equals({{true,true,true},write,false}, {{true,true,true},write,false})
  expected true
  actual   false
```

That output is the evidence. Nothing in the tool converts it into a verdict about the
compiler beyond the inputs it ran.
