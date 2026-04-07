// Generics: type parameters, higher-kinded patterns

function identity<T>(x: T): T { return x; }
function constant<T, U>(x: T): (u: U) => T { return (_u) => x; }
function compose<A, B, C>(f: (a: A) => B, g: (b: B) => C): (a: A) => C { return (a) => g(f(a)); }

interface Pair<A, B> { first: A; second: B }
function makePair<A, B>(a: A, b: B): Pair<A, B> { return { first: a, second: b }; }
function swapPair<A, B>(p: Pair<A, B>): Pair<B, A> { return { first: p.second, second: p.first }; }

function mapOpt<T, U>(opt: T | undefined, f: (v: T) => U): U | undefined {
  if (opt === undefined) return undefined;
  return f(opt);
}

function flatMapOpt<T, U>(opt: T | undefined, f: (v: T) => U | undefined): U | undefined {
  if (opt === undefined) return undefined;
  return f(opt);
}
