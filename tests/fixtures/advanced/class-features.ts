// Class inheritance, static methods, getters/setters, string enums

enum Status {
  Active = "ACTIVE",
  Inactive = "INACTIVE",
  Pending = "PENDING",
}

enum Direction {
  North,
  South,
  East,
  West,
}

abstract class Animal {
  protected name: string;
  constructor(name: string) {
    this.name = name;
  }
  abstract sound(): string;
  describe(): string {
    return `${this.name} says ${this.sound()}`;
  }
}

class Dog extends Animal {
  private breed: string;
  constructor(name: string, breed: string) {
    super(name);
    this.breed = breed;
  }
  sound(): string {
    return 'woof';
  }
  get fullDescription(): string {
    return `${this.name} (${this.breed})`;
  }
}

class Cat extends Animal {
  sound(): string { return 'meow'; }
}

class Circle {
  private _radius: number;
  constructor(radius: number) {
    this._radius = radius;
  }
  get radius(): number {
    return this._radius;
  }
  set radius(value: number) {
    if (value < 0) throw new Error('Radius must be positive');
    this._radius = value;
  }
  get area(): number {
    return Math.PI * this._radius * this._radius;
  }
  static fromDiameter(d: number): Circle {
    return new Circle(d / 2);
  }
  static unitCircle(): Circle {
    return new Circle(1);
  }
}
