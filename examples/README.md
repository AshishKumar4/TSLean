> Edited & maintained by Claude; presented as-is.

# TSLean Examples

These 12 examples exercise the secondary TypeScript-to-Lean compiler.

## Running Examples

```bash
# Single file
bun run src/cli.ts ts-to-lean examples/01-hello-world/hello.ts --output output.lean

# Multi-file project
bun run src/cli.ts ts-to-lean examples/07-modules --output /tmp/output --no-lakefile

# With timing
bun run src/cli.ts ts-to-lean examples/01-hello-world/hello.ts --output output.lean --timing

# With Veil transition declarations
bun run src/cli.ts ts-to-lean examples/12-durable-objects/counter-do.ts --output output.lean --veil
```

## Example Index

| #                              | Topic                  | Key Features                                                  |
| ------------------------------ | ---------------------- | ------------------------------------------------------------- |
| [01](01-hello-world/)          | Hello World            | Pure functions, constants, string interpolation               |
| [02](02-types-and-interfaces/) | Types & Interfaces     | Structures, optional fields, type aliases, nested types       |
| [03](03-classes/)              | Classes                | State as structures, methods as functions, mutation modeling  |
| [04](04-generics/)             | Generics               | Implicit type params, constraints → type classes, multi-param |
| [05](05-error-handling/)       | Error Handling         | try/catch/finally, throw, ExceptT monad                       |
| [06](06-async/)                | Async/Await            | IO monad, do-notation, Promise unwrapping                     |
| [07](07-modules/)              | Modules                | Multi-file, cross-file imports, dependency resolution         |
| [08](08-discriminated-unions/) | Discriminated Unions   | Inductive types, pattern matching, exhaustive switch          |
| [09](09-real-world/)           | Real-World Patterns    | Todo API, config parser, event system                         |
| [10](10-advanced/)             | Advanced / Limitations | typeof → sorry, regex stubs, workarounds, --strict            |
| [11](11-cloudflare-workers/)   | Cloudflare Workers     | `export default { fetch }`, KV bindings, scheduled events     |
| [12](12-durable-objects/)      | Durable Objects        | Storage, WebSocket Hibernation, Alarms, RPC, `--veil`         |

## Expected Output

The `01-hello-world/expected-output.lean` file shows exactly what the transpiler produces. Compare your output against it to verify your installation is working correctly.
