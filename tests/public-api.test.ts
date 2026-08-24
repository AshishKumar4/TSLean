import { describe, expect, test } from 'vitest';
import { compileLeanToTypeScript, compileTypeScriptToLean, verifyLeanToTypeScriptPackage } from '../src/index.js';
import * as leanToTypeScript from '../src/lean-to-typescript/index.js';
import * as typeScriptToLean from '../src/typescript-to-lean/index.js';

describe('bidirectional package facade', () => {
  test('exports each compiler through the root and its explicit direction', () => {
    expect(compileTypeScriptToLean).toBe(typeScriptToLean.compileTypeScriptToLean);
    expect(compileLeanToTypeScript).toBe(leanToTypeScript.compileLeanToTypeScript);
    expect(verifyLeanToTypeScriptPackage).toBe(leanToTypeScript.verifyLeanToTypeScriptPackage);
  });

  test('composes the typed TypeScript pipeline through one public call', () => {
    const result = compileTypeScriptToLean({
      fileName: '/virtual/answer.ts',
      sourceText: 'export function answer(): number { return 42; }',
    });

    expect(result.code).toContain('def answer');
    expect(result.degradations).toEqual([]);
  });
});
