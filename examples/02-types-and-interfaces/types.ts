// 02-types-and-interfaces/types.ts
// Interfaces and type aliases map to Lean structures and abbreviations.
//
// Run: npx tsx src/cli.ts examples/02-types-and-interfaces/types.ts -o output.lean

// Interface → structure Point where x : Float; y : Float
interface Point {
  x: number;
  y: number;
}

// Interface with optional field → Option String
interface User {
  name: string;
  email: string;
  age?: number;
}

// Type alias → abbrev Name : Type := String
type Name = string;

// Nested structure
interface Address {
  street: string;
  city: string;
  zip: string;
}

interface Company {
  name: string;
  address: Address;
  employees: User[];
}

// Functions using interfaces
function distance(a: Point, b: Point): number {
  const dx = a.x - b.x;
  const dy = a.y - b.y;
  return Math.sqrt(dx * dx + dy * dy);
}

function fullName(user: User): string {
  return user.name;
}
