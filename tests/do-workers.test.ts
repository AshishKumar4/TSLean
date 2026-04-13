// Tests for Durable Objects and Workers support.

import { describe, it, expect } from 'vitest';
import { parseFile } from '../src/parser/index.js';
import { rewriteModule } from '../src/rewrite/index.js';
import { generateLean } from '../src/codegen/index.js';
import { generateVeilStub } from '../src/verification/veil-gen.js';

function transpile(fixture: string): string {
  const mod = parseFile({ fileName: `tests/fixtures/do-workers/${fixture}` });
  const rw = rewriteModule(mod);
  return generateLean(rw);
}

// ─── Worker entry point ───────────────────────────────────────────────────────

describe('Workers entry point', () => {
  it('parses export default { fetch }', () => {
    const lean = transpile('worker-basic.ts');
    expect(lean).toContain('namespace Worker');
    expect(lean).toContain('def fetch');
  });

  it('generates Response constructor', () => {
    const lean = transpile('worker-basic.ts');
    expect(lean).toContain('mkResponse');
  });

  it('generates URL.parse', () => {
    const lean = transpile('worker-basic.ts');
    expect(lean).toContain('URL.parse');
  });
});

// ─── Counter DO ───────────────────────────────────────────────────────────────

describe('Counter DO', () => {
  it('generates CounterState struct', () => {
    const lean = transpile('counter-do.ts');
    expect(lean).toContain('structure CounterState');
    expect(lean).toContain('count');
  });

  it('wraps methods in Counter namespace', () => {
    const lean = transpile('counter-do.ts');
    expect(lean).toContain('namespace Counter');
  });

  it('generates increment method', () => {
    const lean = transpile('counter-do.ts');
    expect(lean).toContain('increment');
  });

  it('generates Storage.put for state persistence', () => {
    const lean = transpile('counter-do.ts');
    expect(lean).toContain('Storage.put');
  });

  it('generates fetch handler', () => {
    const lean = transpile('counter-do.ts');
    expect(lean).toContain('Counter.fetch');
  });
});

// ─── Chat Room (WebSocket Hibernation) ────────────────────────────────────────

describe('Chat Room WS', () => {
  it('generates ChatRoomState or namespace', () => {
    const lean = transpile('chat-room-ws.ts');
    expect(lean).toContain('namespace ChatRoom');
  });

  it('recognizes WebSocketPair', () => {
    const lean = transpile('chat-room-ws.ts');
    expect(lean).toContain('WebSocketPair');
  });

  it('maps acceptWebSocket', () => {
    const lean = transpile('chat-room-ws.ts');
    expect(lean).toContain('WsDoState.openConn');
  });

  it('maps getTags', () => {
    const lean = transpile('chat-room-ws.ts');
    expect(lean).toContain('WsDoState.getTags');
  });

  it('maps getWebSockets', () => {
    const lean = transpile('chat-room-ws.ts');
    expect(lean).toContain('WsDoState');
  });

  it('generates webSocketMessage handler', () => {
    const lean = transpile('chat-room-ws.ts');
    expect(lean).toContain('webSocketMessage');
  });

  it('generates webSocketClose handler', () => {
    const lean = transpile('chat-room-ws.ts');
    expect(lean).toContain('webSocketClose');
  });
});

// ─── Rate Limiter (Alarms) ────────────────────────────────────────────────────

describe('Rate Limiter Alarms', () => {
  it('generates RateLimiterState or namespace', () => {
    const lean = transpile('rate-limiter-alarm.ts');
    expect(lean).toContain('namespace RateLimiter');
  });

  it('maps storage.getAlarm to AlarmState', () => {
    const lean = transpile('rate-limiter-alarm.ts');
    expect(lean).toContain('AlarmState');
  });

  it('maps storage.setAlarm', () => {
    const lean = transpile('rate-limiter-alarm.ts');
    expect(lean).toContain('AlarmState.schedule');
  });

  it('generates alarm handler', () => {
    const lean = transpile('rate-limiter-alarm.ts');
    expect(lean).toContain('alarm');
  });

  it('maps Storage.get for events', () => {
    const lean = transpile('rate-limiter-alarm.ts');
    expect(lean).toContain('Storage.get');
  });

  it('maps Storage.put for events', () => {
    const lean = transpile('rate-limiter-alarm.ts');
    expect(lean).toContain('Storage.put');
  });
});

// ─── Multi-DO RPC ─────────────────────────────────────────────────────────────

describe('Multi-DO RPC', () => {
  it('generates OrderServiceState', () => {
    const lean = transpile('multi-do-rpc.ts');
    expect(lean).toContain('namespace OrderService');
  });

  it('generates Storage.put for order creation', () => {
    const lean = transpile('multi-do-rpc.ts');
    expect(lean).toContain('Storage.put');
  });

  it('generates Storage.get for order retrieval', () => {
    const lean = transpile('multi-do-rpc.ts');
    expect(lean).toContain('Storage.get');
  });
});

// ─── Veil bridge ──────────────────────────────────────────────────────────────

describe('Veil bridge', () => {
  it('generates Veil stub for Counter DO', () => {
    const mod = parseFile({ fileName: 'tests/fixtures/do-workers/counter-do.ts' });
    const rw = rewriteModule(mod);
    const result = generateVeilStub(rw, 'Counter', 'TSLean.Generated.CounterDo');
    expect(result).not.toBeNull();
    expect(result.actions).toContain('action_increment');
    expect(result.actions).toContain('action_decrement');
    expect(result.actions).toContain('action_getCount');
    expect(result.actions).toContain('action_fetch');
    expect(result.leanCode).toContain('TransitionSystem State');
    expect(result.leanCode).toContain('veil_relation');
    expect(result.leanCode).toContain('safety_holds');
    expect(result.leanCode).toContain('invConsecution');
  });

  it('generates Veil stub for Rate Limiter DO', () => {
    const mod = parseFile({ fileName: 'tests/fixtures/do-workers/rate-limiter-alarm.ts' });
    const rw = rewriteModule(mod);
    const result = generateVeilStub(rw, 'RateLimiter', 'TSLean.Generated.RateLimiter');
    expect(result).not.toBeNull();
    expect(result.actions).toContain('action_fetch');
    expect(result.actions).toContain('action_alarm');
    expect(result.leanCode).toContain('TransitionSystem');
  });

  it('returns null for non-DO module', () => {
    const mod = parseFile({ fileName: 'tests/fixtures/basic/hello.ts' });
    const rw = rewriteModule(mod);
    const result = generateVeilStub(rw, 'NonExistent', 'TSLean.Generated.Hello');
    expect(result).toBeNull();
  });
});
