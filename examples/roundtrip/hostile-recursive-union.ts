/**
 * A hostile source. The round trip has to refuse it and say why.
 *
 * `GeneratedData` is a recursive union of everything a JSON document can deliver. It has no
 * Lean carrier, so the profile refuses it and every declaration that mentions it. Running
 * `tslean roundtrip --source examples/roundtrip/hostile-recursive-union.ts` reports the
 * refusal rather than compiling something weaker and calling it a round trip.
 */

export type GeneratedData = boolean | string | readonly GeneratedData[] | {
    readonly [key: string]: GeneratedData;
};

export type Mode = "strict" | "lenient";

export function requireMode(value: GeneratedData, name: string): Mode {
    if (value === "strict" || value === "lenient") {
        return value;
    }
    throw new TypeError(`${name} must name a Mode`);
}
