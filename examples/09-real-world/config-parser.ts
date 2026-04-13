// 09-real-world/config-parser.ts
// A configuration parser showing error handling + types.
//
// Run: npx tsx src/cli.ts examples/09-real-world/config-parser.ts -o output.lean

interface Config {
  host: string;
  port: number;
  debug: boolean;
  maxRetries: number;
}

const DEFAULT_CONFIG: Config = {
  host: 'localhost',
  port: 8080,
  debug: false,
  maxRetries: 3,
};

function parsePort(value: string): number {
  const port = parseInt(value);
  if (port < 1 || port > 65535) {
    throw new Error(`Invalid port: ${value}`);
  }
  return port;
}

function mergeConfig(base: Config, overrides: Partial<Config>): Config {
  return {
    host: overrides.host ?? base.host,
    port: overrides.port ?? base.port,
    debug: overrides.debug ?? base.debug,
    maxRetries: overrides.maxRetries ?? base.maxRetries,
  };
}

function validateConfig(config: Config): boolean {
  return config.port > 0 && config.port <= 65535 && config.maxRetries >= 0;
}
