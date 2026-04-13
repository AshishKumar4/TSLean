// Type narrowing: typeof, instanceof, in, discriminated by value

type StringOrNumber = string | number;

function processValue(x: StringOrNumber): string {
  if (typeof x === 'string') {
    return x.toUpperCase();
  } else {
    return x.toString();
  }
}

class Animal { name: string = ''; }
class Dog extends Animal { bark(): void { console.log('woof'); } }
class Cat extends Animal { meow(): void { console.log('meow'); } }

function makeSound(animal: Animal): void {
  if (animal instanceof Dog) {
    animal.bark();
  } else if (animal instanceof Cat) {
    animal.meow();
  }
}

interface HasName { name: string }
interface HasAge  { age: number }

function describeEntity(entity: HasName | HasAge): string {
  if ('name' in entity) {
    return `Named: ${entity.name}`;
  } else {
    return `Age: ${entity.age}`;
  }
}

function isString(x: unknown): x is string {
  return typeof x === 'string';
}

function isPositiveNumber(x: unknown): x is number {
  return typeof x === 'number' && x > 0;
}
