# 08 — Discriminated Unions

TypeScript discriminated unions map to Lean 4 inductive types with pattern matching.

## The pattern

```typescript
type Shape = { kind: 'circle'; radius: number } | { kind: 'rect'; width: number; height: number };

function area(s: Shape): number {
  switch (s.kind) {
    case 'circle': return Math.PI * s.radius * s.radius;
    case 'rect':   return s.width * s.height;
  }
}
```

becomes:

```lean
inductive Shape where
  | circle (radius : Float)
  | rect (width : Float) (height : Float)

def area (s : Shape) : Float :=
  match s with
  | .circle radius => 3.141592653589793 * radius * radius
  | .rect width height => width * height
```

The discriminant field (`kind`, `type`, `tag`, `ok`) is detected automatically.
