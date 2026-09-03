# 02 — Types and Interfaces

Shows how TypeScript interfaces and type aliases map to Lean 4 structures and abbreviations.

## Key mappings

| TypeScript | Lean 4 |
|---|---|
| `interface Point { x: number }` | `structure Point where x : Float` |
| `age?: number` | `age : Option Float` |
| `type Name = string` | `abbrev Name := String` |
| `User[]` | `Array User` |
