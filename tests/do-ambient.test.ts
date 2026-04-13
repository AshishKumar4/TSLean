// Tests for Durable Object ambient injection.

import { describe, it, expect } from 'vitest';
import { hasDOPattern, CF_AMBIENT, DO_LEAN_IMPORTS } from '../src/do-model/ambient.js';

describe('hasDOPattern', () => {
  it('detects DurableObjectState',           () => expect(hasDOPattern('const s: DurableObjectState = ...')).toBe(true));
  it('detects DurableObjectStorage',         () => expect(hasDOPattern('this.state.storage.get("key")')).toBe(true));
  it('detects implements DurableObject',     () => expect(hasDOPattern('class Foo implements DurableObject {')).toBe(true));
  it('detects state.storage',                () => expect(hasDOPattern('this.state = state; this.state.storage')).toBe(true));
  it('detects DurableObjectNamespace',       () => expect(hasDOPattern('env: Env & { NS: DurableObjectNamespace }')).toBe(true));
  it('false on plain code',                  () => expect(hasDOPattern('function add(a: number, b: number) { return a + b; }')).toBe(false));
  it('false on class without DO pattern',    () => expect(hasDOPattern('class Counter { count = 0; }')).toBe(false));
  it('case-insensitive DurableObject name',  () => expect(hasDOPattern('class RoomDO implements DurableObjectBase {')).toBe(true));
});

describe('CF_AMBIENT', () => {
  it('contains DurableObjectState', () => expect(CF_AMBIENT).toContain('interface DurableObjectState'));
  it('contains DurableObjectStorage', () => expect(CF_AMBIENT).toContain('interface DurableObjectStorage'));
  it('contains get<T>',             () => expect(CF_AMBIENT).toContain('get<T'));
  it('contains put<T>',             () => expect(CF_AMBIENT).toContain('put<T'));
  it('contains delete(',            () => expect(CF_AMBIENT).toContain('delete('));
  it('contains Request',            () => expect(CF_AMBIENT).toContain('interface Request'));
  it('contains Response',           () => expect(CF_AMBIENT).toContain('interface Response'));
  it('contains WebSocket',          () => expect(CF_AMBIENT).toContain('interface WebSocket'));
  it('contains Env',                () => expect(CF_AMBIENT).toContain('interface Env'));
  it('contains crypto.randomUUID',  () => expect(CF_AMBIENT).toContain('randomUUID'));
  it('contains ExecutionContext',   () => expect(CF_AMBIENT).toContain('ExecutionContext'));
  it('contains URL',                () => expect(CF_AMBIENT).toContain('URL'));
});

describe('DO_LEAN_IMPORTS', () => {
  it('includes Http',        () => expect(DO_LEAN_IMPORTS).toContain('TSLean.DurableObjects.Http'));
  it('includes State',       () => expect(DO_LEAN_IMPORTS).toContain('TSLean.DurableObjects.State'));
  it('includes Storage',     () => expect(DO_LEAN_IMPORTS).toContain('TSLean.DurableObjects.Storage'));
  it('includes Model',       () => expect(DO_LEAN_IMPORTS).toContain('TSLean.DurableObjects.Model'));
  it('includes Monad',       () => expect(DO_LEAN_IMPORTS).toContain('TSLean.Runtime.Monad'));
  it('includes WebSocket',   () => expect(DO_LEAN_IMPORTS).toContain('TSLean.DurableObjects.WebSocket'));
  it('includes Alarm',       () => expect(DO_LEAN_IMPORTS).toContain('TSLean.DurableObjects.Alarm'));
  it('includes Transaction', () => expect(DO_LEAN_IMPORTS).toContain('TSLean.DurableObjects.Transaction'));
  it('includes RPC',         () => expect(DO_LEAN_IMPORTS).toContain('TSLean.DurableObjects.RPC'));
  it('has 9 entries',        () => expect(DO_LEAN_IMPORTS).toHaveLength(9));
});
