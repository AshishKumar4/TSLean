import { execFileSync } from 'node:child_process';
import { resolve } from 'node:path';
import { describe, expect, it } from 'vitest';

describe('JS elaborated-environment trust audit', () => {
  it('discovers proof forms and rejects malformed trust records', () => {
    const output = execFileSync('bun', ['scripts/check-js-axioms.mjs', '--self-test'], {
      cwd: resolve(import.meta.dirname, '..'),
      encoding: 'utf8',
    });
    expect(output.trim()).toBe('synthetic environment audit passed');
  }, 20_000);

  it('discovers ordered-property transition theorems', () => {
    const output = execFileSync('lake', ['env', 'lean', '../tests/lean-fixtures/ordered-props-transitions.lean'], {
      cwd: resolve(import.meta.dirname, '../lean'),
      encoding: 'utf8',
    });
    expect(output).toContain('TSLean.JS.OrderedProps.ownKeys_delete');
  });
});
