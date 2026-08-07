import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { resolve } from 'node:path';
import type { CanonicalDatum, Observation, OracleRequest, OracleResponse } from './types.js';

type JsonValue = null | boolean | number | string | JsonValue[] | { [key: string]: JsonValue };

type Batch = {
  responses: OracleResponse[];
  remaining: number;
  resolve: (responses: OracleResponse[]) => void;
  reject: (error: Error) => void;
  timer: NodeJS.Timeout;
  completion?: NodeJS.Immediate;
  settled: boolean;
  writeCallbackDone: boolean;
  drainDone: boolean;
};

type PendingLine = { batch: Batch; index: number };

type Closing = {
  resolve: () => void;
  reject: (error: Error) => void;
  timer: NodeJS.Timeout;
};

type Running = {
  child: ChildProcessWithoutNullStreams;
  stderr: string;
  stderrTruncated: boolean;
  closing?: Closing;
};

export type LeanOracleOptions = {
  executable?: string;
  spawnChild?: () => ChildProcessWithoutNullStreams;
  requestTimeoutMs?: number;
  closeTimeoutMs?: number;
  stderrLimit?: number;
};

const stderrTruncationMarker = '\n...[oracle stderr truncated]';

function isObject(value: JsonValue): value is { [key: string]: JsonValue } {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function hasExactKeys(value: { [key: string]: JsonValue }, keys: string[]): boolean {
  return Object.keys(value).sort().join('\0') === [...keys].sort().join('\0');
}

function isStringDatum(value: JsonValue): value is { type: 'string'; units: number[] } {
  return isObject(value) && hasExactKeys(value, ['type', 'units']) && value.type === 'string' &&
    Array.isArray(value.units) && value.units.every((unit) => typeof unit === 'number' && Number.isInteger(unit) && unit >= 0 && unit <= 65535);
}

function isCanonicalDatum(value: JsonValue): value is CanonicalDatum {
  if (!isObject(value) || typeof value.type !== 'string') return false;
  if (value.type === 'undefined' || value.type === 'null') return hasExactKeys(value, ['type']);
  if (value.type === 'boolean') return hasExactKeys(value, ['type', 'value']) && typeof value.value === 'boolean';
  if (value.type === 'number') {
    return hasExactKeys(value, ['type', 'bits']) && typeof value.bits === 'string' && /^(?:0|[1-9][0-9]*)$/.test(value.bits) &&
      BigInt(value.bits) <= 18446744073709551615n;
  }
  if (value.type === 'string') return isStringDatum(value);
  if (value.type === 'bigint') {
    return hasExactKeys(value, ['type', 'decimal']) && typeof value.decimal === 'string' && /^(?:0|-?[1-9][0-9]*)$/.test(value.decimal);
  }
  if (value.type === 'symbol') {
    return hasExactKeys(value, ['type', 'kind', 'identity']) &&
      (value.kind === 'registered' || value.kind === 'well-known' || value.kind === 'unique') &&
      typeof value.identity === 'string' && value.identity.length > 0;
  }
  if (value.type === 'error') return hasExactKeys(value, ['type', 'identity', 'name', 'message']) &&
    typeof value.identity === 'string' && isStringDatum(value.name) && isStringDatum(value.message);
  return value.type === 'object' && hasExactKeys(value, ['type', 'identity']) &&
    typeof value.identity === 'string' && value.identity.length > 0;
}

function isCanonicalDescriptor(value: JsonValue): boolean {
  if (!isObject(value) || typeof value.kind !== 'string') return false;
  if (value.kind === 'data') {
    return hasExactKeys(value, ['kind', 'value', 'writable', 'enumerable', 'configurable']) &&
      isCanonicalDatum(value.value) && typeof value.writable === 'boolean' &&
      typeof value.enumerable === 'boolean' && typeof value.configurable === 'boolean';
  }
  return value.kind === 'accessor' && hasExactKeys(value, ['kind', 'get', 'set', 'enumerable', 'configurable']) &&
    isCanonicalDatum(value.get) && isCanonicalDatum(value.set) &&
    typeof value.enumerable === 'boolean' && typeof value.configurable === 'boolean';
}

function isCanonicalObject(value: JsonValue): boolean {
  return isObject(value) && hasExactKeys(value, ['identity', 'kind', 'prototype', 'extensible', 'properties']) &&
    typeof value.identity === 'string' &&
    (value.kind === 'object' || value.kind === 'function' || value.kind === 'array' || value.kind === 'error') &&
    isCanonicalDatum(value.prototype) && typeof value.extensible === 'boolean' && Array.isArray(value.properties) &&
    value.properties.every((property) => isObject(property) && hasExactKeys(property, ['key', 'descriptor']) &&
      isCanonicalDatum(property.key) && isCanonicalDescriptor(property.descriptor));
}

function isObservation(value: JsonValue): value is Observation {
  if (!isObject(value) || (!hasExactKeys(value, ['completion', 'trace']) &&
      !hasExactKeys(value, ['completion', 'trace', 'objects']) &&
      !hasExactKeys(value, ['completion', 'trace', 'roots', 'objects'])) || !isObject(value.completion) ||
      !hasExactKeys(value.completion, ['type', 'value']) ||
      (value.completion.type !== 'normal' && value.completion.type !== 'throw') ||
      !isCanonicalDatum(value.completion.value) || !Array.isArray(value.trace)) return false;
  const traceValid = value.trace.every((entry) => isObject(entry) && hasExactKeys(entry, ['event', 'detail']) &&
    typeof entry.event === 'string' && isCanonicalDatum(entry.detail));
  if (!traceValid) return false;
  if (Object.hasOwn(value, 'roots') && (!Array.isArray(value.roots) || !value.roots.every(isCanonicalDatum))) return false;
  return !Object.hasOwn(value, 'objects') ||
    (Array.isArray(value.objects) && value.objects.every(isCanonicalObject));
}

function isOracleResponse(value: JsonValue): value is OracleResponse {
  if (!isObject(value) || (typeof value.id !== 'string' && value.id !== null) || typeof value.status !== 'string') return false;
  if (value.status === 'ok') return hasExactKeys(value, ['id', 'status', 'observation']) && isObservation(value.observation);
  return value.status === 'protocol-error' && hasExactKeys(value, ['id', 'status', 'error']) && isObject(value.error) &&
    hasExactKeys(value.error, ['code', 'message']) && typeof value.error.code === 'string' && typeof value.error.message === 'string';
}

function parseResponse(line: string): OracleResponse {
  let parsed: JsonValue;
  try {
    parsed = JSON.parse(line);
  } catch (error) {
    throw new Error(`oracle emitted invalid JSON: ${line}`, { cause: error });
  }
  if (!isOracleResponse(parsed)) throw new Error(`oracle emitted an invalid response: ${line}`);
  return parsed;
}

export class LeanOracle {
  readonly #cwd: string;
  readonly #executable: string;
  readonly #spawnChild?: () => ChildProcessWithoutNullStreams;
  readonly #requestTimeoutMs: number;
  readonly #closeTimeoutMs: number;
  readonly #stderrLimit: number;
  #running?: Running;
  #pending: PendingLine[] = [];
  #batch?: Batch;
  #deferredFailure?: Error;

  constructor(root: string, options: LeanOracleOptions = {}) {
    this.#cwd = resolve(root, 'lean');
    this.#executable = options.executable ?? resolve(this.#cwd, '.lake/build/bin/js-model-oracle');
    this.#spawnChild = options.spawnChild;
    this.#requestTimeoutMs = options.requestTimeoutMs ?? 30_000;
    this.#closeTimeoutMs = options.closeTimeoutMs ?? 5_000;
    this.#stderrLimit = options.stderrLimit ?? 64 * 1024;
  }

  #start(): Running {
    if (this.#running !== undefined) return this.#running;
    const child = this.#spawnChild?.() ?? spawn(this.#executable, [], { cwd: this.#cwd, stdio: ['pipe', 'pipe', 'pipe'] });
    const running: Running = { child, stderr: '', stderrTruncated: false };
    this.#running = running;
    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    let stdoutBuffer = '';
    child.stdout.on('data', (chunk: string) => {
      stdoutBuffer += chunk;
      for (;;) {
        const newline = stdoutBuffer.indexOf('\n');
        if (newline < 0) break;
        const line = stdoutBuffer.slice(0, newline).replace(/\r$/, '');
        stdoutBuffer = stdoutBuffer.slice(newline + 1);
        this.#handleLine(running, line);
      }
    });
    child.stderr.on('data', (chunk: string) => this.#appendStderr(running, chunk));
    child.on('error', (error) => this.#fail(running, new Error(`oracle process error: ${error.message}`, { cause: error })));
    child.stdin.on('error', (error) => this.#fail(running, new Error(`oracle stdin error: ${error.message}`, { cause: error })));
    child.stdout.on('error', (error) => this.#fail(running, new Error(`oracle stdout error: ${error.message}`, { cause: error })));
    child.stdout.on('close', () => {
      if (this.#running !== running || running.closing !== undefined) return;
      const suffix = stdoutBuffer.length === 0 ? '' : ` with unterminated output: ${stdoutBuffer}`;
      this.#fail(running, new Error(`oracle stdout closed unexpectedly${suffix}`));
    });
    child.on('exit', (code, signal) => {
      if (this.#running === running && running.closing === undefined) {
        const detail = running.stderr.trim();
        this.#fail(running, new Error(
          `oracle exited unexpectedly (code=${code}, signal=${signal})${detail ? `: ${detail}` : ''}`,
        ));
      }
    });
    child.on('close', (code, signal) => this.#handleClose(running, code, signal));
    return running;
  }

  #appendStderr(running: Running, chunk: string): void {
    if (running.stderrTruncated) return;
    const available = this.#stderrLimit - running.stderr.length;
    if (chunk.length <= available) {
      running.stderr += chunk;
      return;
    }
    running.stderr += chunk.slice(0, Math.max(0, available)) + stderrTruncationMarker;
    running.stderrTruncated = true;
  }

  #handleLine(running: Running, line: string): void {
    if (this.#running !== running) return;
    const pending = this.#pending.shift();
    if (pending === undefined) {
      this.#fail(running, new Error(`oracle emitted unsolicited or excess stdout: ${line}`));
      return;
    }
    try {
      pending.batch.responses[pending.index] = parseResponse(line);
    } catch (error) {
      this.#fail(running, error instanceof Error ? error : new Error(String(error)));
      return;
    }
    pending.batch.remaining -= 1;
    this.#maybeCompleteBatch(pending.batch);
  }

  #maybeCompleteBatch(batch: Batch): void {
    if (batch.remaining === 0 && batch.writeCallbackDone && batch.drainDone && batch.completion === undefined) {
      batch.completion = setImmediate(() => this.#resolveBatch(batch));
    }
  }

  #resolveBatch(batch: Batch): void {
    if (this.#batch !== batch || batch.settled) return;
    batch.settled = true;
    clearTimeout(batch.timer);
    this.#batch = undefined;
    batch.resolve(batch.responses);
  }

  #rejectBatch(error: Error): boolean {
    const batch = this.#batch;
    if (batch === undefined || batch.settled) return false;
    batch.settled = true;
    clearTimeout(batch.timer);
    if (batch.completion !== undefined) clearImmediate(batch.completion);
    this.#batch = undefined;
    this.#pending = [];
    batch.reject(error);
    return true;
  }

  #fail(running: Running, error: Error, deferIfUnobserved = true): void {
    if (this.#running !== running) return;
    this.#running = undefined;
    const observed = this.#rejectBatch(error);
    const closing = running.closing;
    if (closing !== undefined) {
      clearTimeout(closing.timer);
      closing.reject(error);
    } else if (!observed && deferIfUnobserved) {
      this.#deferredFailure = error;
    }
    if (!running.child.killed) running.child.kill('SIGKILL');
  }

  #handleClose(running: Running, code: number | null, signal: NodeJS.Signals | null): void {
    if (this.#running !== running) return;
    const detail = running.stderr.trim();
    if (running.closing !== undefined) {
      this.#running = undefined;
      clearTimeout(running.closing.timer);
      if (code === 0 && signal === null && detail.length === 0) running.closing.resolve();
      else running.closing.reject(new Error(`oracle close failed (code=${code}, signal=${signal})${detail ? `: ${detail}` : ''}`));
      return;
    }
    this.#fail(running, new Error(`oracle closed unexpectedly (code=${code}, signal=${signal})${detail ? `: ${detail}` : ''}`));
  }

  exchangeLines(lines: string[]): Promise<OracleResponse[]> {
    if (this.#batch !== undefined) return Promise.reject(new Error('oracle already has an active batch'));
    if (lines.length === 0) return Promise.resolve([]);
    const injected = lines.find((line) => /[\r\n]/.test(line));
    if (injected !== undefined) return Promise.reject(new Error('oracle records must not contain CR or LF'));
    const deferred = this.#deferredFailure;
    if (deferred !== undefined) {
      this.#deferredFailure = undefined;
      return Promise.reject(deferred);
    }
    let running: Running;
    try {
      running = this.#start();
    } catch (error) {
      return Promise.reject(new Error('failed to start oracle process', { cause: error }));
    }
    return new Promise<OracleResponse[]>((resolveBatch, rejectBatch) => {
      const batch: Batch = {
        responses: new Array<OracleResponse>(lines.length),
        remaining: lines.length,
        resolve: resolveBatch,
        reject: rejectBatch,
        timer: setTimeout(() => {
          this.#fail(running, new Error(`oracle batch timed out after ${this.#requestTimeoutMs}ms`));
        }, this.#requestTimeoutMs),
        settled: false,
        writeCallbackDone: false,
        drainDone: false,
      };
      this.#batch = batch;
      lines.forEach((_, index) => this.#pending.push({ batch, index }));
      try {
        const accepted = running.child.stdin.write(`${lines.join('\n')}\n`, (error) => {
          if (error !== null && error !== undefined) {
            this.#fail(running, new Error(`oracle write failed: ${error.message}`, { cause: error }));
            return;
          }
          batch.writeCallbackDone = true;
          this.#maybeCompleteBatch(batch);
        });
        if (accepted) {
          batch.drainDone = true;
        } else {
          running.child.stdin.once('drain', () => {
            if (this.#running !== running) return;
            batch.drainDone = true;
            this.#maybeCompleteBatch(batch);
          });
        }
      } catch (error) {
        this.#fail(running, new Error('oracle write failed', { cause: error }));
      }
    });
  }

  async requestBatch(requests: OracleRequest[]): Promise<OracleResponse[]> {
    const responses = await this.exchangeLines(requests.map((request) => JSON.stringify(request)));
    responses.forEach((response, index) => {
      if (response.id !== requests[index].id) {
        const error = new Error(
          `oracle response correlation failed at ${index}: expected ${requests[index].id}, received ${response.id}`,
        );
        const running = this.#running;
        if (running !== undefined) this.#fail(running, error, false);
        throw error;
      }
    });
    return responses;
  }

  async restart(): Promise<void> {
    this.#deferredFailure = undefined;
    if (this.#running !== undefined) await this.close();
    this.#start();
  }

  async close(): Promise<void> {
    const deferred = this.#deferredFailure;
    if (deferred !== undefined) {
      this.#deferredFailure = undefined;
      throw deferred;
    }
    const running = this.#running;
    if (running === undefined) return;
    if (this.#batch !== undefined) throw new Error('cannot close oracle with a pending batch');
    await new Promise<void>((resolveClose, rejectClose) => {
      const closing: Closing = {
        resolve: resolveClose,
        reject: rejectClose,
        timer: setTimeout(() => {
          this.#fail(running, new Error(`oracle close timed out after ${this.#closeTimeoutMs}ms`), false);
        }, this.#closeTimeoutMs),
      };
      running.closing = closing;
      try {
        running.child.stdin.end();
      } catch (error) {
        this.#fail(running, new Error('oracle stdin close failed', { cause: error }), false);
      }
    });
  }
}
