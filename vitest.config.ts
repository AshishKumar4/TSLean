import { defineConfig } from 'vitest/config';
export default defineConfig({ test: { globals: true, include: ['tests/**/*.test.ts'], fileParallelism: false, hookTimeout: 120000, testTimeout: 30000 } });
