export function identity<T>(x: T): T {
  return x;
}

export function constant<T>(x: T): () => T {
  return () => x;
}

export function pipe<A, B>(f: (a: A) => B): (a: A) => B {
  return f;
}

export function compose<A, B, C>(f: (b: B) => C, g: (a: A) => B): (a: A) => C {
  return (a: A) => f(g(a));
}

export function first<A, B>(pair: [A, B]): A {
  return pair[0];
}

export function second<A, B>(pair: [A, B]): B {
  return pair[1];
}
