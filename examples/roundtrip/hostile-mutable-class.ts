/**
 * A hostile source. The round trip has to refuse it and say why.
 *
 * A Lean structure field is not assignable in place, so a class that mutates its own state
 * denotes no Lean structure. The profile refuses the class rather than lowering it to a
 * structure whose behaviour would differ the first time a method wrote to it.
 *
 * This is valid TypeScript. Only the profile refuses it, which is the point: a round trip
 * carries less than a language does, and it has to say so rather than translate anyway.
 */

export class Counter {
    public value: boolean;
    public constructor(value: boolean) {
        this.value = value;
    }
    public toggle(): boolean {
        this.value = this.value === false;
        return this.value;
    }
}
