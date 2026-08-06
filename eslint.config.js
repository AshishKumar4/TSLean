import js from '@eslint/js';
import { defineConfig, globalIgnores } from 'eslint/config';
import prettier from 'eslint-config-prettier';
import tseslint from 'typescript-eslint';

export default defineConfig(
  globalIgnores(['dist/**', 'node_modules/**', 'lean/**']),
  {
    files: ['src/**/*.ts', 'scripts/*.mjs'],
    extends: [js.configs.recommended, tseslint.configs.recommended, prettier],
  },
);
