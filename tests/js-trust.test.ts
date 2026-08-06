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
  });
});
