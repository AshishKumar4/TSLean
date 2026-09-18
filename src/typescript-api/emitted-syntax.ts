/**
 * @module typescript-api/emitted-syntax
 *
 * The syntax the Lean-to-TypeScript compiler emits, and the printer that writes it out.
 *
 * This is the whole of TSLean's remaining dependency on TypeScript 6, and the only module that
 * names the package. It is not the only module that uses it: everything that emits imports
 * {@link emitted} from here — the emitter and the package layout that build the syntax, the
 * certificates and the compiler that record what printed it, and the tests that transpile or
 * print generated syntax. Everything that *reads* TypeScript — the parser, the type map, the
 * effect inference, the project reader, the round trip, and the type check of the emitted tree —
 * reads through {@link module:typescript-api/session}, which is TypeScript 7. The one parse on
 * this side of the line is one that exists only to be printed again, which is emission.
 *
 * ## Why emission did not move
 *
 * TypeScript 7 publishes a complete syntax factory (`typescript/unstable/ast/factory`) and a
 * printer (`Project.emitter.printNode`), and for uncommented syntax the two versions agree byte
 * for byte: twenty representative constructs — class bodies with parameter properties and
 * accessors, switch blocks, template expressions, `bigint` literals, keyword and predicate
 * types, and string literals carrying quotes, backslashes, astral-plane characters and control
 * characters — print identically under 6.0.2's `createPrinter` and 7.0.2's emitter.
 *
 * What 7.0.2 has no channel for is a comment on *constructed* syntax, and every generated
 * declaration, class member and interface member carries the Lean docstring it came from:
 *
 * - `addSyntheticLeadingComment` has no counterpart: the factory exposes no comment attachment,
 *   and the client's node object has no leading-comment field.
 * - A `JSDoc` node assigned to a constructed node's `jsDoc` is dropped — the wire encoder does
 *   not carry it — and placing one in a statement list crashes the server with
 *   `panic: unhandled statement: KindJSDoc`.
 * - The printer recovers comments from source positions, not from the tree: printing a *parsed*
 *   source file preserves them, printing a parsed declaration on its own drops them, and giving
 *   a constructed file the text to read them from scatters them over unrelated nodes.
 *
 * Emitting through 7.0.2 would therefore silently strip every docstring from the product, and
 * re-deriving the comments as text around a printed node would mean owning indentation and
 * placement for class and interface members — a printer written here, which the trust policy
 * refuses. So emission stays on the printer that supports it.
 *
 * ## Removal condition
 *
 * Three gaps have to close, not one, and each has its own callers:
 *
 * - **A comment on constructed syntax**: an `addSyntheticLeadingComment` equivalent, or `jsDoc`
 *   on the wire for factory-built nodes. `documented` in the emitter is the caller, and this is
 *   the gap the section above is about.
 * - **A printer over a whole file**: `createPrinter().printFile` and `EmitHint`, which the
 *   emitter and the certificates print through. 7.0.2 publishes `Emitter.printNode` and nothing
 *   else, and printing a file that mixes parsed nodes with constructed ones — what a transform
 *   over parsed source produces — panics the compiler server outright, on a nil dereference in
 *   the printer's `IsOuterExpression`. So `mutateFirstConjunction` in
 *   `tests/lean-to-typescript.test.ts` waits on this gap as well.
 * - **An in-process transpiler**: `transpileModule`, which two test files lower a generated
 *   module to JavaScript with so a decoder can be run against it. `typescript/unstable/sync` is
 *   a client to a compiler server whose only emit is `printNode`.
 *
 * Until all three close, `docs/trust.md` carries the pin as a trusted-base item.
 */

/**
 * The compiler emitted syntax is built with and printed by. A module that emits imports this as
 * `ts` — `import { emitted as ts }` — so the name inside that module says which compiler it is
 * talking to, and no emission file names the package itself.
 */
import emitted from 'typescript-emitter';

export { emitted };
