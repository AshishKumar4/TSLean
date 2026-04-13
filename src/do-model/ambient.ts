// Cloudflare Workers / Durable Objects ambient declarations.
// Injected as a virtual file when DO patterns are detected so the TypeScript
// checker can resolve types without needing the @cloudflare/workers-types package.

import * as ts from 'typescript';

// ─── Detection ────────────────────────────────────────────────────────────────

export function hasDOPattern(source: string): boolean {
  return (
    source.includes('DurableObjectState') ||
    source.includes('DurableObjectStorage') ||
    source.includes('DurableObjectNamespace') ||
    source.includes('state.storage') ||
    /implements\s+\w*DurableObject/i.test(source)
  );
}

// ─── Ambient source ───────────────────────────────────────────────────────────

export const CF_AMBIENT = `
interface DurableObjectState {
  storage: DurableObjectStorage;
  id: DurableObjectId;
  blockConcurrencyWhile<T>(cb: () => Promise<T>): Promise<T>;
  waitUntil(p: Promise<any>): void;
  acceptWebSocket(ws: WebSocket, tags?: string[]): void;
  getWebSockets(tag?: string): WebSocket[];
  getTags(ws: WebSocket): string[];
  abort(reason?: string): void;
}
interface DurableObjectStorage {
  get<T = unknown>(key: string): Promise<T | undefined>;
  get<T = unknown>(keys: string[]): Promise<Map<string, T>>;
  put<T>(key: string, value: T): Promise<void>;
  put<T>(entries: Record<string, T>): Promise<void>;
  delete(key: string): Promise<boolean>;
  delete(keys: string[]): Promise<number>;
  deleteAll(): Promise<void>;
  list<T = unknown>(opts?: DurableObjectListOptions): Promise<Map<string, T>>;
  getAlarm(): Promise<number | null>;
  setAlarm(t: number | Date): Promise<void>;
  deleteAlarm(): Promise<void>;
  transaction<T>(cb: (txn: DurableObjectTransaction) => Promise<T>): Promise<T>;
}
interface DurableObjectTransaction extends DurableObjectStorage {
  rollback(): void;
}
interface DurableObjectListOptions {
  start?: string; startAfter?: string; end?: string;
  prefix?: string; reverse?: boolean; limit?: number;
}
interface DurableObjectId { toString(): string; equals(o: DurableObjectId): boolean; name?: string }
interface DurableObjectNamespace {
  idFromName(name: string): DurableObjectId;
  idFromString(id: string): DurableObjectId;
  newUniqueId(): DurableObjectId;
  get(id: DurableObjectId): DurableObjectStub;
}
interface DurableObjectStub {
  fetch(req: Request | string, init?: RequestInit): Promise<Response>;
  id: DurableObjectId;
}
interface Request {
  method: string; url: string;
  headers: Headers; body: ReadableStream | null;
  json(): Promise<any>; text(): Promise<string>;
  arrayBuffer(): Promise<ArrayBuffer>; clone(): Request;
}
interface Response {
  status: number; statusText: string;
  headers: Headers; body: ReadableStream | null; ok: boolean;
  json(): Promise<any>; text(): Promise<string>; clone(): Response;
}
declare function Response(body?: string | null, init?: ResponseInit): Response;
interface ResponseInit { status?: number; statusText?: string; headers?: Record<string, string> | Headers; webSocket?: WebSocket }
interface Headers {
  get(name: string): string | null;
  set(name: string, value: string): void;
  has(name: string): boolean;
  delete(name: string): void;
  entries(): IterableIterator<[string, string]>;
  forEach(cb: (v: string, k: string) => void): void;
}
interface WebSocket {
  send(data: string | ArrayBuffer): void;
  close(code?: number, reason?: string): void;
  readyState: number;
}
interface WebSocketPair { 0: WebSocket; 1: WebSocket }
declare function WebSocketPair(): { 0: WebSocket; 1: WebSocket };
interface ExecutionContext { waitUntil(p: Promise<any>): void; passThroughOnException(): void }
interface Env { [key: string]: any }
declare function URL(url: string): { pathname: string; searchParams: URLSearchParams; href: string; origin: string }
declare class URL { constructor(url: string); pathname: string; searchParams: URLSearchParams; href: string; origin: string }
interface URLSearchParams { get(name: string): string | null; has(name: string): boolean }
declare namespace crypto { function randomUUID(): string; function getRandomValues<T extends ArrayBufferView>(a: T): T }
`;

// ─── Augmented compiler host ───────────────────────────────────────────────────

export function makeAmbientHost(
  base: ts.CompilerHost,
  virtual: Map<string, string>
): ts.CompilerHost {
  return {
    ...base,
    getSourceFile(name, version, onError, shouldCreate) {
      if (virtual.has(name)) return ts.createSourceFile(name, virtual.get(name)!, version, true);
      return base.getSourceFile(name, version, onError, shouldCreate);
    },
    fileExists(name) { return virtual.has(name) || base.fileExists(name); },
    readFile(name)   { return virtual.has(name) ? virtual.get(name) : base.readFile(name); },
  };
}

// ─── Required Lean imports for DO files ──────────────────────────────────────

export const DO_LEAN_IMPORTS = [
  'TSLean.DurableObjects.Http',
  'TSLean.DurableObjects.State',
  'TSLean.DurableObjects.Storage',
  'TSLean.DurableObjects.Model',
  'TSLean.Runtime.Monad',
] as const;
