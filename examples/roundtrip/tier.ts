/**
 * A TypeScript source inside the round-trip profile.
 *
 * `tslean roundtrip --source examples/roundtrip/tier.ts` compiles it to Lean, compiles that
 * Lean back to TypeScript, and requires the two TypeScript sides to declare and compute the
 * same thing.
 */

/** Which tier serves a call. */
export type Tier = "direct" | "mediated";

/** What the call does. */
export type Impact = "observe" | "mutate" | "administer";

/** What the caller holds. */
export interface Session {
    readonly owned: boolean;
    readonly writable: boolean;
}

/** The weakest tier the impact admits under this session. */
export function floorOf(impact: Impact, session: Session): Tier {
    return impact === "observe"
        ? "direct"
        : impact === "mutate"
            ? (session.owned && session.writable ? "direct" : "mediated")
            : "mediated";
}

/** The impact served directly, when there is one. */
export function servedDirectly(impact: Impact, session: Session): Impact | undefined {
    return floorOf(impact, session) === "direct" ? impact : undefined;
}
