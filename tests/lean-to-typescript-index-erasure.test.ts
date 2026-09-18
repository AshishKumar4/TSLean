import { resolve } from 'node:path';
import { describe, expect, test } from 'vitest';
import { compileLeanToTypeScript } from '../src/lean-to-typescript/compiler.js';
import * as indexedInvariant from '../examples/lean-to-typescript/roundtrip/IndexedInvariant/generated/TSLean/Examples/Roundtrip/IndexedInvariant.js';

const repositoryRoot = resolve(import.meta.dirname, '..');
const projectRoot = resolve(repositoryRoot, 'lean');
const COMPILE_TIMEOUT_MS = 300_000;

/**
 * A type former's term index is erased only where erasing it is sound, and the boundary is checked
 * per type rather than assumed for the shape.
 *
 * These fixtures are real committed Lean modules, so each case drives the exporter the compiler
 * ships rather than a string built here. The admitted module is exercised end to end by the
 * round-trip registry; what this file pins is the other half — that a type whose content genuinely
 * depends on its index is REFUSED, and refused for its own stated reason.
 *
 * The refusals matter more than they look. Lean's own compiler erases all three of these indices:
 * `Lean.Compiler.LCNF.toMonoType` reports the same mono type at two distinct indices for
 * `DependentField.Slot` and `LengthIndexed.Fixed` as it does for a genuinely phantom index, because
 * Lean's runtime boxes every value and carries no types. A compiler that read Lean's erasure and
 * stopped there would emit one TypeScript type for `Slot true` and `Slot false` — whose fields are
 * a `string` and a `number` — and a decoder written against it would read the wrong field. So if
 * one of these tests starts passing compilation, the erasure has stopped being sound; it has not
 * become more capable.
 */
describe('index erasure', () => {
  function compile(module: string, declaration: string): unknown {
    return compileLeanToTypeScript({
      projectRoot,
      moduleName: `TSLean.Examples.Roundtrip.${module}`,
      sourcePath: resolve(projectRoot, 'TSLean/Examples/Roundtrip', `${module}.lean`),
      declarations: [`TSLean.Examples.Roundtrip.${module}.${declaration}`],
    });
  }

  test.each([
    [
      'a data field whose type mentions the index',
      'DependentField',
      'textOf',
      /Slot is indexed by the term parameter flag, and .*Slot\.mk declares a data field whose type mentions it/u,
    ],
    [
      'a length-indexed container',
      'LengthIndexed',
      'firstOf',
      /Fixed is indexed by the term parameter size, and .*Fixed\.mk declares a data field whose type mentions it/u,
    ],
    [
      'a use site at a computed index',
      'ComputedIndex',
      'chosen',
      /Label is applied at a computed index, which the emitted program never evaluates/u,
    ],
  ])(
    'refuses %s',
    (_label, module, declaration, diagnostic) => {
      let thrown: unknown;
      try {
        compile(module, declaration);
      } catch (error: unknown) {
        thrown = error;
      }
      expect(thrown).toBeInstanceOf(Error);
      // The declaration has to be named, not just the construct: a diagnostic that says only
      // "outside the checked fragment" does not tell an author which of their types to change.
      expect((thrown as Error).message).toMatch(diagnostic);
      expect((thrown as Error).message).toMatch(
        new RegExp(`TSLean\\.Examples\\.Roundtrip\\.${module}`, 'u'),
      );
    },
    COMPILE_TIMEOUT_MS,
  );

  test(
    'admits a phantom index, drops it from the emitted arity, and records it',
    () => {
      const compiled = compile('PhantomIndex', 'parse') as {
        readonly manifest: {
          readonly semantic: {
            readonly modules: readonly {
              readonly declarations: readonly {
                readonly declaration: string;
                readonly emitted: string;
                readonly erasedParameters?: readonly string[];
              }[];
            }[];
          };
        };
      };
      const declarations = compiled.manifest.semantic.modules.flatMap((module) => module.declarations);
      const label = declarations.find(
        (entry) => entry.declaration === 'TSLean.Examples.Roundtrip.PhantomIndex.Label',
      );
      expect(label).toBeDefined();
      // The Lean former is arity 1 and the emitted type is arity 0, so the index left the emitted
      // arity. It is recorded rather than merely dropped, which is what keeps the emitted type
      // relatable to the Lean family it stands for instead of just smaller than it.
      expect(label?.emitted).toBe('Label');
      expect(label?.erasedParameters).toEqual(['tag']);
      // A type that never had an index carries no record at all, so absence and erasure are
      // distinguishable rather than spelled the same way.
      const tag = declarations.find(
        (entry) => entry.declaration === 'TSLean.Examples.Roundtrip.PhantomIndex.Tag',
      );
      expect(tag).toBeDefined();
      expect(tag?.erasedParameters).toBeUndefined();
    },
    COMPILE_TIMEOUT_MS,
  );

  test(
    'subtracts an erased index and an erased proof field from the same constructor',
    () => {
      const compiled = compile('IndexedInvariant', 'stamp') as {
        readonly manifest: {
          readonly semantic: {
            readonly modules: readonly {
              readonly declarations: readonly {
                readonly declaration: string;
                readonly emitted: string;
                readonly erasedParameters?: readonly string[];
              }[];
            }[];
            readonly closure: readonly { readonly declaration: string; readonly role: string }[];
          };
        };
      };
      const declarations = compiled.manifest.semantic.modules.flatMap((module) => module.declarations);
      const stampType = declarations.find(
        (entry) => entry.declaration === 'TSLean.Examples.Roundtrip.IndexedInvariant.Stamp',
      );
      // The two erasures are recorded on one declaration: the index by name, and the dropped proof
      // field by the absence of its own projection from the closure plus the `Prop`-sorted
      // definition that typed it being classified erased.
      expect(stampType?.erasedParameters).toEqual(['tag']);
      const admitted = compiled.manifest.semantic.closure.find(
        (entry) => entry.declaration === 'TSLean.Examples.Roundtrip.IndexedInvariant.Admitted',
      );
      expect(admitted?.role).toBe('erased');
      expect(
        compiled.manifest.semantic.closure.some(
          (entry) => entry.declaration === 'TSLean.Examples.Roundtrip.IndexedInvariant.Stamp.admitted',
        ),
      ).toBe(false);
    },
    COMPILE_TIMEOUT_MS,
  );

  /**
   * The merged arity, observed by running the committed generated module rather than read off its
   * text. `Stamp.mk` is declared at arity three — the index, the level, the proof — and a consumer
   * receives a record with one own property, because both subtrahends applied at once. Drop either
   * half of the subtraction and the export fails outright: the constructor's arity check compares
   * `numParams - erasedParameters` and `numFields - erasedFields` separately.
   *
   * This test is also the fixture's only behavioural reader. The round-trip observation driver
   * cannot build a value of a record whose proof field was erased, so the registry marks the
   * example outside the behaviour profile and the agreement with Lean's own theorems
   * (`stampedLevel_low`, `stampedLevel_turn_high`) is checked here instead of there.
   */
  test('emits a record whose arity is the declared one less both erasures', () => {
    const built = indexedInvariant.stamp('run', 'high');
    expect(built.kind).toBe('some');
    if (built.kind !== 'some') throw new Error('a run stamp admits the demanding level');
    expect(Object.keys(built.value)).toEqual(['level']);

    // The index left the type, not the value: the emitted function still takes its tag, because
    // `admits` reads it.
    expect(indexedInvariant.runStamp('high')).toEqual(built);
    expect(indexedInvariant.stamp('turn', 'high')).toEqual({ kind: 'none' });

    // Erasure did not change what the program computes.
    expect(indexedInvariant.stampedLevel('turn', 'low')).toEqual({ kind: 'some', value: 'low' });
    expect(indexedInvariant.stampedLevel('turn', 'high')).toEqual({ kind: 'none' });
    expect(indexedInvariant.highRunLevel()).toBe('high');

    // A proof-carrying record gets no decoder, so no caller can hand the package data and claim
    // the invariant the dropped field asserts. The two enumerations beside it do carry one.
    expect(Object.hasOwn(indexedInvariant, 'Stamp')).toBe(false);
    expect(Object.hasOwn(indexedInvariant.Level, 'fromData')).toBe(true);
  });
});
