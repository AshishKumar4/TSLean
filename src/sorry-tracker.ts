// Tracks sorry/degradation points during transpilation for reporting.

export interface SorryEntry {
  location: string;     // file:line or function name
  reason: string;       // why sorry was emitted
  category: SorryCategory;
  hint?: string;        // workaround suggestion
}

export type SorryCategory =
  | 'unresolved-expr'     // expression the parser couldn't handle
  | 'unresolved-type'     // type the lowerer couldn't map
  | 'runtime-api'         // JS/Node runtime API call (fs, path, etc.)
  | 'type-test'           // typeof/instanceof check
  | 'inductive-field'     // field access on inductive type
  | 'mutation'            // unsupported mutation pattern
  | 'control-flow'        // unsupported control flow
  | 'generator'           // generator/yield
  | 'other';

export class SorryTracker {
  private entries: SorryEntry[] = [];

  add(entry: SorryEntry): void {
    this.entries.push(entry);
  }

  get count(): number { return this.entries.length; }
  get all(): readonly SorryEntry[] { return this.entries; }

  /** Group entries by category for summary reporting. */
  byCat(): Map<SorryCategory, SorryEntry[]> {
    const m = new Map<SorryCategory, SorryEntry[]>();
    for (const e of this.entries) {
      const list = m.get(e.category) ?? [];
      list.push(e);
      m.set(e.category, list);
    }
    return m;
  }

  /** Format as a human-readable summary. */
  summary(): string {
    if (this.entries.length === 0) return '';
    const lines = [`\n-- Sorry summary: ${this.entries.length} degraded expression(s)`];
    for (const [cat, entries] of this.byCat()) {
      lines.push(`--   ${cat}: ${entries.length}`);
      for (const e of entries.slice(0, 5)) {
        const hint = e.hint ? ` (hint: ${e.hint})` : '';
        lines.push(`--     ${e.location}: ${e.reason}${hint}`);
      }
      if (entries.length > 5) lines.push(`--     ... and ${entries.length - 5} more`);
    }
    return lines.join('\n');
  }

  /** Format a single sorry as a Lean comment. */
  static formatComment(entry: SorryEntry): string {
    const hint = entry.hint ? ` -- hint: ${entry.hint}` : '';
    return `/- sorry: ${entry.reason} at ${entry.location}${hint} -/`;
  }
}

// Global tracker for the current transpilation (reset per file)
let _current: SorryTracker | null = null;

export function currentTracker(): SorryTracker {
  if (!_current) _current = new SorryTracker();
  return _current;
}

export function resetTracker(): SorryTracker {
  _current = new SorryTracker();
  return _current;
}
