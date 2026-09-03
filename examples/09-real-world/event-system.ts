// 09-real-world/event-system.ts
// A typed event system showing generics + collections.
//
// Run: npx tsx src/cli.ts examples/09-real-world/event-system.ts -o output.lean

type EventHandler<T> = (data: T) => void;

interface EventEmitter<Events extends Record<string, unknown>> {
  handlers: Map<string, EventHandler<unknown>[]>;
}

function createEmitter(): EventEmitter<Record<string, unknown>> {
  return { handlers: new Map() };
}

function emit(emitter: EventEmitter<Record<string, unknown>>, event: string, data: unknown): void {
  const handlers = emitter.handlers.get(event);
  if (handlers) {
    handlers.forEach(h => h(data));
  }
}

function listEvents(emitter: EventEmitter<Record<string, unknown>>): string[] {
  const keys: string[] = [];
  emitter.handlers.forEach((_, key) => keys.push(key));
  return keys;
}

function handlerCount(emitter: EventEmitter<Record<string, unknown>>, event: string): number {
  const handlers = emitter.handlers.get(event);
  return handlers ? handlers.length : 0;
}
