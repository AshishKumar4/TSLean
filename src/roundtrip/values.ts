/**
 * @module roundtrip/values
 *
 * The value domain of a profile type, and one canonical text for every value.
 *
 * Every profile type is finite. A behavior check enumerates the whole domain when it fits
 * its bound, or a fixed prefix when it does not. A value is written three ways from the same
 * description: a Lean term, a JavaScript value, and a canonical text. The canonical text is
 * what the comparison reads, so a disagreement is reported as two strings a reader can put
 * side by side.
 */

import { TAGGED_OPTION } from '../typemap/index.js';
import type { ProfileType } from './profile.js';

/** A value of a profile type, independent of either language's representation. */
export type ProfileValue =
  | { readonly kind: 'boolean'; readonly value: boolean }
  | { readonly kind: 'enumeration'; readonly member: string }
  | { readonly kind: 'structure'; readonly fields: readonly ProfileValue[] }
  | { readonly kind: 'none' }
  | { readonly kind: 'some'; readonly value: ProfileValue };

/** How many values a type has. */
export function domainSize(type: ProfileType): number {
  switch (type.kind) {
    case 'boolean': return 2;
    case 'enumeration': return type.members.length;
    case 'option': return 1 + domainSize(type.inner);
    case 'structure': return type.fields.reduce((total, field) => total * domainSize(field.type), 1);
  }
}

/**
 * Every value of the type, in a fixed order.
 *
 * This is intentionally a full-domain API. A caller that needs only a prefix uses
 * {@link enumerateTuples}; it indexes the domain and does not allocate the product first.
 */
export function enumerateValues(type: ProfileType): readonly ProfileValue[] {
  const size = domainSize(type);
  if (!Number.isSafeInteger(size)) {
    throw new TypeError('the value domain is too large to materialise');
  }
  return Array.from({ length: size }, (_, index) => valueAt(type, index));
}

/** The value at one position of a type's domain, without building the domain. */
export function valueAt(type: ProfileType, index: number): ProfileValue {
  const size = domainSize(type);
  if (!Number.isSafeInteger(size) || !Number.isSafeInteger(index) || index < 0 || index >= size) {
    throw new RangeError(`index ${String(index)} is outside the type's finite domain`);
  }
  return valueAtWithin(type, index);
}

/** Value construction after {@link valueAt} has checked the outer index. */
function valueAtWithin(type: ProfileType, index: number): ProfileValue {
  switch (type.kind) {
    case 'boolean':
      return { kind: 'boolean', value: index === 1 };
    case 'enumeration':
      return { kind: 'enumeration', member: type.members[index]! };
    case 'option':
      return index === 0 ? { kind: 'none' } : { kind: 'some', value: valueAtWithin(type.inner, index - 1) };
    case 'structure': {
      const fields: ProfileValue[] = [];
      let rest = index;
      for (let position = type.fields.length - 1; position >= 0; position--) {
        const size = domainSize(type.fields[position].type);
        fields[position] = valueAtWithin(type.fields[position].type, rest % size);
        rest = Math.floor(rest / size);
      }
      return { kind: 'structure', fields };
    }
  }
}

/**
 * Argument tuples in odometer order, the last parameter varying fastest, up to `limit`
 * rows. The order matches the Lean driver's bounded `List.range` index calculation, so the
 * two sides walk the domain the same way and the caller can compare row by row.
 *
 * Only the rows asked for are built. A domain larger than `Number.MAX_SAFE_INTEGER` cannot
 * be indexed, so it is reported as unbounded rather than silently sampled from a wrapped
 * index.
 */
export function enumerateTuples(
  types: readonly ProfileType[],
  limit: number,
): readonly (readonly ProfileValue[])[] {
  const sizes = types.map(domainSize);
  const total = sizes.reduce((product, size) => product * size, 1);
  if (!Number.isSafeInteger(total)) {
    throw new TypeError('the input domain is too large to enumerate; lower the behaviour limit');
  }
  const rows: (readonly ProfileValue[])[] = [];
  for (let index = 0; index < Math.min(total, limit); index++) {
    const row: ProfileValue[] = [];
    let rest = index;
    for (let position = sizes.length - 1; position >= 0; position--) {
      row[position] = valueAt(types[position], rest % sizes[position]);
      rest = Math.floor(rest / sizes[position]);
    }
    rows.push(row);
  }
  return rows;
}

/** The one text both sides render a value to. */
export function renderValue(value: ProfileValue): string {
  switch (value.kind) {
    case 'boolean': return value.value ? 'true' : 'false';
    case 'enumeration': return value.member;
    case 'none': return 'none';
    case 'some': return `some(${renderValue(value.value)})`;
    case 'structure': return `{${value.fields.map(renderValue).join(',')}}`;
  }
}


/** The Lean type expression for a profile type, under the same qualification. */
export function leanType(type: ProfileType, qualify: (name: string) => string): string {
  switch (type.kind) {
    case 'boolean': return 'Bool';
    case 'enumeration': return qualify(type.name);
    case 'structure': return qualify(type.name);
    case 'option': return `Option (${leanType(type.inner, qualify)})`;
  }
}

/** The JavaScript value, built through the exports the projected module actually has. */
export function javaScriptValue(
  type: ProfileType,
  value: ProfileValue,
  exported: Readonly<Record<string, unknown>>,
): unknown {
  if (type.kind === 'boolean' && value.kind === 'boolean') return value.value;
  if (type.kind === 'enumeration' && value.kind === 'enumeration') return value.member;
  if (type.kind === 'option') {
    if (value.kind === 'none') return type.encoding === 'tagged' ? { kind: TAGGED_OPTION.absent } : undefined;
    const present = javaScriptValue(type.inner, (value as Extract<ProfileValue, { kind: 'some' }>).value, exported);
    return type.encoding === 'tagged' ? { kind: TAGGED_OPTION.present, value: present } : present;
  }
  if (type.kind === 'structure' && value.kind === 'structure') {
    const initialiser: Record<string, unknown> = {};
    for (const [index, field] of type.fields.entries()) {
      initialiser[field.name] = javaScriptValue(field.type, value.fields[index], exported);
    }
    if (type.introduced === 'interface') return initialiser;
    const constructor = exported[type.name];
    if (typeof constructor !== 'function') {
      throw new TypeError(`the projected module does not export a constructor for ${type.name}`);
    }
    return Reflect.construct(constructor, [initialiser]);
  }
  throw new TypeError(`value of kind ${value.kind} does not belong to a ${type.kind} type`);
}

/**
 * The profile value a JavaScript result denotes.
 *
 * @throws TypeError when the result does not belong to the declared type. That is a real
 * disagreement between the declaration and the running code, not a comparison detail.
 */
export function profileValue(type: ProfileType, result: unknown): ProfileValue {
  if (type.kind === 'boolean') {
    if (typeof result !== 'boolean') throw new TypeError(`expected a boolean, got ${describe(result)}`);
    return { kind: 'boolean', value: result };
  }
  if (type.kind === 'enumeration') {
    if (typeof result !== 'string' || !type.members.includes(result)) {
      throw new TypeError(`expected a case of ${type.name}, got ${describe(result)}`);
    }
    return { kind: 'enumeration', member: result };
  }
  if (type.kind === 'option') {
    if (type.encoding === 'undefined') {
      return result === undefined ? { kind: 'none' } : { kind: 'some', value: profileValue(type.inner, result) };
    }
    // A tagged option that arrives in any other shape is a disagreement between the
    // declaration and the running code, so it is reported rather than guessed at.
    if (result === null || typeof result !== 'object') {
      throw new TypeError(`expected a tagged option, got ${describe(result)}`);
    }
    const tagged = result as { readonly kind?: unknown; readonly value?: unknown };
    if (tagged.kind === TAGGED_OPTION.absent) return { kind: 'none' };
    if (tagged.kind !== TAGGED_OPTION.present) {
      throw new TypeError(`expected a tagged option, got ${describe(result)}`);
    }
    return { kind: 'some', value: profileValue(type.inner, tagged.value) };
  }
  if (result === null || typeof result !== 'object') {
    throw new TypeError(`expected a ${type.name}, got ${describe(result)}`);
  }
  const record = result as Record<string, unknown>;
  return {
    kind: 'structure',
    fields: type.fields.map((field) => profileValue(field.type, record[field.name])),
  };
}

function describe(value: unknown): string {
  return value === undefined ? 'undefined' : JSON.stringify(value) ?? String(value);
}
