// Discriminated unions → Lean inductive types

type Shape =
  | { kind: "circle";    radius: number }
  | { kind: "rectangle"; width: number; height: number }
  | { kind: "triangle";  base: number;  height: number };

type Color = "red" | "green" | "blue" | "yellow";

type Tree<T> =
  | { tag: "leaf"; value: T }
  | { tag: "node"; left: Tree<T>; right: Tree<T>; value: T };

type Either<L, R> =
  | { type: "left";  value: L }
  | { type: "right"; value: R };

function areaShape(s: Shape): number {
  switch (s.kind) {
    case "circle":    return Math.PI * s.radius * s.radius;
    case "rectangle": return s.width * s.height;
    case "triangle":  return 0.5 * s.base * s.height;
  }
}

function perimeter(s: Shape): number {
  switch (s.kind) {
    case "circle":    return 2 * Math.PI * s.radius;
    case "rectangle": return 2 * (s.width + s.height);
    case "triangle":  return s.base * 3;
  }
}

function treeDepth<T>(t: Tree<T>): number {
  switch (t.tag) {
    case "leaf": return 1;
    case "node": return 1 + Math.max(treeDepth(t.left), treeDepth(t.right));
  }
}

function mapEither<L, R, S>(e: Either<L, R>, f: (r: R) => S): Either<L, S> {
  switch (e.type) {
    case "left":  return { type: "left",  value: e.value };
    case "right": return { type: "right", value: f(e.value) };
  }
}
