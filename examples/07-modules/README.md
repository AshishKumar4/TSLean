# 07 — Modules (Multi-File)

Multi-file TypeScript projects transpile with correct cross-file imports.

## Run

```bash
npx tsx src/cli.ts compile --project examples/07-modules/ -o /tmp/modules-output/ --no-lakefile
```

## What happens

- `types.ts` → `Modules/Types.lean` (structures + functions)
- `cart.ts` → `Modules/Cart.lean` (imports Types)
- Cross-file imports resolve: `import { Item } from './types'` → `import Project.Types`
- Dependency order: `Types` compiled before `Cart`
