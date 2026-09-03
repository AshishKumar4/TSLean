# 01 — Hello World

The simplest TSLean example. Pure functions map directly to Lean 4 definitions.

## Run

```bash
npx tsx src/cli.ts examples/01-hello-world/hello.ts -o examples/01-hello-world/output.lean
```

## What to look for

- `function greet(name: string): string` → `def greet (name : String) : String`
- `function add(a: number, b: number): number` → `def add (a b : Float) : Float`
- String interpolation → `s!"Hello, {name}!"`
- Constants → `def pi : Float := 3.14159`
