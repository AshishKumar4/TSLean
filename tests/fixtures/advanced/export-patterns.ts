// Various export patterns

interface Config {
  host: string;
  port: number;
  debug?: boolean;
}

interface ApiResult<T> {
  data: T;
  status: number;
  message: string;
}

function createConfig(host: string, port: number): Config {
  return { host, port, debug: false };
}

function makeSuccess<T>(data: T): ApiResult<T> {
  return { data, status: 200, message: 'ok' };
}

function makeError<T>(message: string): ApiResult<T> {
  return { data: undefined as unknown as T, status: 500, message };
}

// Named exports
export { Config, ApiResult, createConfig, makeSuccess, makeError };

// Re-exports
export type { Config as AppConfig };

// Default export (object style)
export default {
  createConfig,
  makeSuccess,
  makeError,
};
