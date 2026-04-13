// Cloudflare Workers / Durable Objects ambient declarations.
// Injected as a virtual file when DO or Workers patterns are detected so the
// TypeScript checker can resolve types without needing @cloudflare/workers-types.

import * as ts from 'typescript';

// ─── Detection ────────────────────────────────────────────────────────────────

/** Detect Durable Object patterns in source text. */
export function hasDOPattern(source: string): boolean {
  return (
    source.includes('DurableObjectState') ||
    source.includes('DurableObjectStorage') ||
    source.includes('DurableObjectNamespace') ||
    source.includes('state.storage') ||
    /implements\s+\w*DurableObject/i.test(source) ||
    /extends\s+DurableObject/i.test(source)
  );
}

/** Detect Workers entry-point patterns (export default { fetch ... }). */
export function hasWorkersPattern(source: string): boolean {
  return (
    hasDOPattern(source) ||
    source.includes('ExecutionContext') ||
    source.includes('KVNamespace') ||
    source.includes('R2Bucket') ||
    source.includes('D1Database') ||
    /export\s+default\s*\{/.test(source)
  );
}

// ─── Ambient source ───────────────────────────────────────────────────────────

export const CF_AMBIENT = `
// ── Durable Objects ──────────────────────────────────────────────────────────

declare class DurableObject<E = any> {
  ctx: DurableObjectState;
  env: E;
  constructor(ctx: DurableObjectState, env: E);
}

interface DurableObjectState {
  storage: DurableObjectStorage;
  id: DurableObjectId;
  blockConcurrencyWhile<T>(cb: () => Promise<T>): Promise<T>;
  waitUntil(p: Promise<any>): void;
  acceptWebSocket(ws: WebSocket, tags?: string[]): void;
  getWebSockets(tag?: string): WebSocket[];
  setWebSocketAutoResponse(pair?: WebSocketRequestResponsePair): void;
  getWebSocketAutoResponse(): WebSocketRequestResponsePair | null;
  getWebSocketAutoResponseTimestamp(ws: WebSocket): Date | null;
  setHibernatableWebSocketEventTimeout(timeoutMs?: number): void;
  getHibernatableWebSocketEventTimeout(): number;
  getTags(ws: WebSocket): string[];
  abort: AbortSignal;
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
  sql: SqlStorage;
  getCurrentBookmark(): Promise<string>;
  getBookmarkForTime(timestamp: Date): Promise<string>;
  onNextSessionRestoreBookmark(bookmark: string): void;
}

interface SqlStorage {
  exec<T = unknown>(query: string, ...bindings: any[]): SqlStorageCursor<T>;
  ingest(filename: string, input: ArrayBuffer): { tableName: string; rowsRead: number; rowsWritten: number };
  databaseSize: number;
}

interface SqlStorageCursor<T = unknown> {
  [Symbol.iterator](): Iterator<T>;
  toArray(): T[];
  one(): T;
  columnNames: string[];
  rowsRead: number;
  rowsWritten: number;
}

interface DurableObjectTransaction extends DurableObjectStorage {
  rollback(): void;
}

interface DurableObjectListOptions {
  start?: string; startAfter?: string; end?: string;
  prefix?: string; reverse?: boolean; limit?: number;
}

interface DurableObjectId {
  toString(): string;
  equals(o: DurableObjectId): boolean;
  name?: string;
}

interface DurableObjectNamespace<T = any> {
  idFromName(name: string): DurableObjectId;
  idFromString(id: string): DurableObjectId;
  newUniqueId(): DurableObjectId;
  get(id: DurableObjectId): DurableObjectStub<T>;
  getExistingId(): DurableObjectId | null;
  jurisdiction(jurisdiction: string): DurableObjectNamespace<T>;
}

interface DurableObjectStub<T = any> {
  fetch(req: Request | string, init?: RequestInit): Promise<Response>;
  id: DurableObjectId;
  name?: string;
  // RPC: any public method on T is callable
  [key: string]: any;
}

interface AlarmInvocationInfo {
  retryCount: number;
  isRetry: boolean;
}

interface WebSocketRequestResponsePair {
  request: string;
  response: string;
}

// ── Web Platform ─────────────────────────────────────────────────────────────

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

interface ResponseInit {
  status?: number; statusText?: string;
  headers?: Record<string, string> | Headers;
  webSocket?: WebSocket;
}

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
  accept(): void;
  readyState: number;
  serializeAttachment(value: any): void;
  deserializeAttachment(): any;
}

interface WebSocketPair { 0: WebSocket; 1: WebSocket }
declare function WebSocketPair(): { 0: WebSocket; 1: WebSocket };

interface ExecutionContext {
  waitUntil(p: Promise<any>): void;
  passThroughOnException(): void;
}

interface Env { [key: string]: any }

declare function URL(url: string): { pathname: string; searchParams: URLSearchParams; href: string; origin: string }
declare class URL { constructor(url: string); pathname: string; searchParams: URLSearchParams; href: string; origin: string }
interface URLSearchParams { get(name: string): string | null; has(name: string): boolean }
declare namespace crypto { function randomUUID(): string; function getRandomValues<T extends ArrayBufferView>(a: T): T }

// ── Workers Bindings ─────────────────────────────────────────────────────────

interface KVNamespace {
  get(key: string, opts?: { type?: string; cacheTtl?: number }): Promise<string | null>;
  getWithMetadata<M = unknown>(key: string): Promise<{ value: string | null; metadata: M | null }>;
  put(key: string, value: string, opts?: { expiration?: number; expirationTtl?: number; metadata?: any }): Promise<void>;
  delete(key: string): Promise<void>;
  list(opts?: { prefix?: string; limit?: number; cursor?: string }): Promise<{ keys: { name: string; expiration?: number }[]; list_complete: boolean; cursor?: string }>;
}

interface R2Bucket {
  get(key: string): Promise<R2Object | null>;
  put(key: string, value: string | ArrayBuffer | ReadableStream, opts?: R2PutOptions): Promise<R2Object>;
  delete(key: string | string[]): Promise<void>;
  list(opts?: { prefix?: string; limit?: number; cursor?: string; delimiter?: string }): Promise<R2Objects>;
  head(key: string): Promise<R2Object | null>;
}
interface R2Object {
  key: string; size: number; etag: string; version: string;
  httpMetadata?: Record<string, string>; customMetadata?: Record<string, string>;
  body: ReadableStream;
  text(): Promise<string>; json(): Promise<any>; arrayBuffer(): Promise<ArrayBuffer>;
}
interface R2PutOptions { httpMetadata?: Record<string, string>; customMetadata?: Record<string, string> }
interface R2Objects { objects: R2Object[]; truncated: boolean; cursor?: string; delimitedPrefixes: string[] }

interface D1Database {
  prepare(query: string): D1PreparedStatement;
  exec(query: string): Promise<D1ExecResult>;
  batch(stmts: D1PreparedStatement[]): Promise<D1Result<unknown>[]>;
  dump(): Promise<ArrayBuffer>;
}
interface D1PreparedStatement {
  bind(...values: any[]): D1PreparedStatement;
  first<T = unknown>(column?: string): Promise<T | null>;
  all<T = unknown>(): Promise<D1Result<T>>;
  raw<T = unknown>(): Promise<T[]>;
  run(): Promise<D1ExecResult>;
}
interface D1Result<T = unknown> {
  results: T[];
  success: boolean;
  meta: { duration: number; changes: number; last_row_id: number; rows_read: number; rows_written: number };
}
interface D1ExecResult { count: number; duration: number }

interface Queue<T = unknown> {
  send(message: T, opts?: { contentType?: string; delaySeconds?: number }): Promise<void>;
  sendBatch(messages: { body: T; contentType?: string; delaySeconds?: number }[]): Promise<void>;
}
interface MessageBatch<T = unknown> {
  messages: Message<T>[];
  queue: string;
  ackAll(): void;
  retryAll(opts?: { delaySeconds?: number }): void;
}
interface Message<T = unknown> {
  id: string; body: T; timestamp: Date;
  ack(): void; retry(opts?: { delaySeconds?: number }): void;
}

interface ScheduledEvent {
  scheduledTime: number;
  cron: string;
  noRetry(): void;
}

interface ReadableStream {}
interface ArrayBuffer {}
interface ArrayBufferView {}
interface AbortSignal {}
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
  'TSLean.DurableObjects.WebSocket',
  'TSLean.DurableObjects.Alarm',
  'TSLean.DurableObjects.Transaction',
  'TSLean.DurableObjects.RPC',
  'TSLean.Runtime.Monad',
] as const;

/** Lean imports for Workers bindings (KV, R2, D1, Queue). */
export const WORKERS_LEAN_IMPORTS = [
  'TSLean.Workers.KV',
  'TSLean.Workers.R2',
  'TSLean.Workers.D1',
  'TSLean.Workers.Queue',
  'TSLean.Workers.Scheduler',
] as const;
