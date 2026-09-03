import { describe, expect, it } from 'vitest';

import {
  LEAN_RUNTIME_ASSUMPTIONS,
  LEAN_RUNTIME_OPCODES,
  runtimeHelperRole,
  type LeanOpcode,
} from '../src/lean-to-typescript/ir.js';
import { helperOperationForms, inlineOperationForms } from '../src/lean-to-typescript/emitter.js';

/**
 * The `bytes` surface, from the hostile side.
 *
 * A `Uint8Array` is not an array exotic object: its bytes are the contents of a
 * `[[ViewedArrayBuffer]]` read through `[[ArrayLength]]`, and `TSLean/JS/Heap.lean` models no such
 * object, which is why `Target.State` carries an internal-slot table beside `State.closures`. The
 * three ways that representation can be got wrong are a slot payload of the wrong shape, an
 * iteration observation the Lean side does not fix, and an indexed read whose element type the
 * surface does not carry. Each of them is refused, and each refusal is checked here rather than
 * described.
 */
describe('the bytes surface refuses what its representation cannot carry', () => {
  const opcodes = Object.keys(LEAN_RUNTIME_OPCODES) as readonly LeanOpcode[];

  it('carries exactly the four byte rows whose Lean result type the surface admits', () => {
    expect(opcodes.filter((opcode) => opcode.startsWith('bytes.'))).toEqual([
      'bytes.empty',
      'bytes.size',
      'bytes.isEmpty',
      'bytes.append',
    ]);
    // Every byte row stands on the one typed-array assumption and on nothing else, so a byte
    // observation cannot borrow the dense-array assumption an ordinary array reads under.
    for (const opcode of opcodes.filter((candidate) => candidate.startsWith('bytes.'))) {
      expect(LEAN_RUNTIME_OPCODES[opcode].assumptions).toEqual(['typed-array.byte-sequence']);
      expect(LEAN_RUNTIME_OPCODES[opcode].assumptions).not.toContain('array.dense-element-sequence');
    }
    expect(LEAN_RUNTIME_ASSUMPTIONS['typed-array.byte-sequence']).toBeTypeOf('string');
  });

  it('refuses an indexed byte read, because a byte has no admitted type image', () => {
    // `ByteArray.get?` is `Option UInt8` and `ByteArray.toList` is `List UInt8`. `UInt8` is not an
    // admitted type form — its arithmetic wraps at its width and the registry carries no modular
    // family — so an element-touching row would have to invent a type image for a byte.
    for (const refused of ['bytes.get', 'bytes.set', 'bytes.toList', 'bytes.ofList', 'bytes.push']) {
      expect(Object.hasOwn(LEAN_RUNTIME_OPCODES, refused)).toBe(false);
    }
    expect(Object.hasOwn(LEAN_RUNTIME_ASSUMPTIONS, 'typed-array.integer-indexed-read')).toBe(false);
  });

  it('refuses every map row, because no Lean map fixes the entry order a Map iterates in', () => {
    // `Std.HashMap.toList` is constrained only up to `List.Perm` — `Std.HashMap.toList_insert_perm`
    // is a permutation law, not an order law — and `Std.TreeMap.toList` is ascending by `cmp`, which
    // a `Map`'s insertion-order iteration does not reproduce without a key comparator the
    // monomorphic IR carries no dictionary for. So no map row exists to be joined at all.
    expect(opcodes.filter((opcode) => opcode.startsWith('map.'))).toEqual([]);
    expect(Object.hasOwn(LEAN_RUNTIME_ASSUMPTIONS, 'map.entry-collection')).toBe(false);
  });

  it('prints the byte forms the Lean registry states, byte for byte', () => {
    const inline = inlineOperationForms();
    expect(inline.get('bytes.empty')).toBe('new Uint8Array()');
    expect(inline.get('bytes.size')).toBe('BigInt(value.length)');
    expect(inline.get('bytes.isEmpty')).toBe('value.length === 0');
    // A byte read never goes through the ordinary property store, so no byte form spreads the
    // operand or indexes it the way a dense-array form does.
    for (const form of ['bytes.empty', 'bytes.size', 'bytes.isEmpty'] as const) {
      expect(inline.get(form)).not.toContain('[...');
    }
    expect(helperOperationForms().get('bytes.append')).toBe(
      '(target => (target.set(left, 0), target.set(right, left.length), target))(new Uint8Array(left.length + right.length))',
    );
    // The concatenation is the one byte row that reaches the target as a declaration, because a
    // typed array has no concatenating method to write at the use site.
    expect(runtimeHelperRole(LEAN_RUNTIME_OPCODES['bytes.append'].runtimeSymbol)).toBe('bytes-concatenation');
    expect(inline.has('bytes.append')).toBe(false);
  });

  it('gives the concatenation helper a typed-array signature, not an array one', () => {
    const row = LEAN_RUNTIME_OPCODES['bytes.append'];
    expect(row.parameters([])).toEqual([{ kind: 'bytes' }, { kind: 'bytes' }]);
    expect(row.result([])).toEqual({ kind: 'bytes' });
    expect(row.typeParameters).toBe(0);
    expect(LEAN_RUNTIME_OPCODES['bytes.size'].result([])).toEqual({ kind: 'nat' });
    expect(LEAN_RUNTIME_OPCODES['bytes.isEmpty'].result([])).toEqual({ kind: 'boolean' });
    expect(LEAN_RUNTIME_OPCODES['bytes.empty'].parameters([])).toEqual([]);
  });

  it('runs the emitted concatenation body on real typed arrays, at the boundaries', () => {
    const concatenate = (left: Uint8Array, right: Uint8Array): Uint8Array =>
      ((target: Uint8Array) => (target.set(left, 0), target.set(right, left.length), target))(
        new Uint8Array(left.length + right.length),
      );
    expect([...concatenate(new Uint8Array([1, 2]), new Uint8Array([3]))]).toEqual([1, 2, 3]);
    expect([...concatenate(new Uint8Array(), new Uint8Array([9]))]).toEqual([9]);
    expect([...concatenate(new Uint8Array([9]), new Uint8Array())]).toEqual([9]);
    expect(concatenate(new Uint8Array(), new Uint8Array()).length).toBe(0);
    // A dense array of the same elements is a different object with a different length semantics,
    // which is exactly why the slot table is not the property store.
    expect(concatenate(new Uint8Array([1]), new Uint8Array([2])) instanceof Uint8Array).toBe(true);
    expect(Array.isArray(concatenate(new Uint8Array([1]), new Uint8Array([2])))).toBe(false);
  });
});
