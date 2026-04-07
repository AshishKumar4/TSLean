// Interfaces → Lean structures

interface Point { readonly x: number; readonly y: number }
interface Rectangle { topLeft: Point; bottomRight: Point }
interface Named { name: string; description?: string }

function distance(p1: Point, p2: Point): number {
  const dx = p2.x - p1.x;
  const dy = p2.y - p1.y;
  return Math.sqrt(dx * dx + dy * dy);
}

function area(r: Rectangle): number {
  return (r.bottomRight.x - r.topLeft.x) * (r.bottomRight.y - r.topLeft.y);
}

function makePoint(x: number, y: number): Point { return { x, y }; }
