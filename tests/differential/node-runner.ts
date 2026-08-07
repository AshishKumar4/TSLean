import vm from 'node:vm';
import type { Canonicalizer } from './canonical.js';
import { materializeFixtures } from './fixture.js';
import { materializeGraphFixture, type MaterializedGraph } from './node-graph.js';
import type { DifferentialVector, Observation } from './types.js';

export type Operation = { id: string; domain: 'primitive' | 'graph'; arity: 1 | 2; source: string };

export function runNodeVector(vector: DifferentialVector, registry: Map<string, Operation>, canonicalizer: Canonicalizer): Observation {
  const operation = registry.get(vector.operation);
  if (operation === undefined) throw new Error(`unknown Node operation: ${vector.operation}`);
  if (vector.fixtures.length !== operation.arity) throw new Error(`${vector.id} has incorrect fixture arity`);
  const graphFixture = vector.fixtures.length === 1 && vector.fixtures[0].kind === 'graph';
  if ((operation.domain === 'graph') !== graphFixture) throw new Error(`${vector.id} has incorrect fixture domain`);
  const globals = Object.create(null);
  const context = vm.createContext(globals, {
    codeGeneration: { strings: false, wasm: false },
    name: `differential:${vector.id}`,
  });
  const intrinsicMetadata: {
    errorPrototypes: Map<object, string>;
    selections: Map<object, PropertyKey[]>;
    kinds: Map<object, 'object' | 'function' | 'array' | 'error'>;
  } = vm.runInContext(
    `(() => {
      const errorPrototypes = new Map([[Error.prototype, "Error"], [TypeError.prototype, "TypeError"], [RangeError.prototype, "RangeError"], [ReferenceError.prototype, "ReferenceError"], [SyntaxError.prototype, "SyntaxError"]]);
      const selections = new Map([[Object.prototype, []], ...[...errorPrototypes.keys()].map(value => [value, []])]);
      const kinds = new Map([...selections.keys()].map(value => [value, "object"]));
      return { errorPrototypes, selections, kinds };
    })()`,
    context,
  );
  let graph: MaterializedGraph | undefined;
  if (graphFixture && vector.fixtures[0].kind === 'graph') {
    graph = materializeGraphFixture(context, vector.fixtures[0], canonicalizer);
    globals.value = graph;
  } else {
    const values = materializeFixtures(vector.fixtures, canonicalizer);
    if (operation.arity === 1) globals.value = values[0];
    else {
      globals.left = values[0];
      globals.right = values[1];
    }
  }
  try {
    const result = vm.runInContext(vector.source, context, { timeout: 50 });
    return graph === undefined
      ? canonicalizer.observation(
        { type: 'normal', value: result }, [], [], intrinsicMetadata.selections,
        intrinsicMetadata.kinds, intrinsicMetadata.errorPrototypes,
      )
      : canonicalizer.observation(
        { type: 'normal', value: result }, graph.trace, graph.observe, graph.selections, graph.kinds, graph.errorPrototypes,
        graph.fixtureErrors,
      );
  } catch (error) {
    return graph === undefined
      ? canonicalizer.observation(
        { type: 'throw', value: error }, [], [], intrinsicMetadata.selections,
        intrinsicMetadata.kinds, intrinsicMetadata.errorPrototypes,
      )
      : canonicalizer.observation(
        { type: 'throw', value: error }, graph.trace, graph.observe, graph.selections, graph.kinds, graph.errorPrototypes,
        graph.fixtureErrors,
      );
  }
}
