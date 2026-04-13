// Tracks degraded expressions during transpilation for reporting.
// Distinguishes between actual `sorry` (axiom, blocks proofs) and
// `default` (type-correct Inhabited placeholder, compiles fine).

export type DegradationLevel =
  | 'sorry'     // actual sorry axiom — blocks proofs, marks incomplete
  | 'default';  // Inhabited default — type-correct, compiles, approximate value

export interface SorryEntry {
  location: string;     // file:line or function name
  reason: string;       // why the expression was degraded
  category: SorryCategory;
  level: DegradationLevel;
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

  add(entry: Omit<SorryEntry, 'level'> & { level?: DegradationLevel }): void {
    this.entries.push({ level: 'default', ...entry });
  }

  /** Add a true sorry (axiom — blocks proofs). */
  addSorry(entry: Omit<SorryEntry, 'level'>): void {
    this.entries.push({ ...entry, level: 'sorry' });
  }

  /** Add a default placeholder (type-correct, compiles fine). */
  addDefault(entry: Omit<SorryEntry, 'level'>): void {
    this.entries.push({ ...entry, level: 'default' });
  }

  get count(): number { return this.entries.length; }
  get sorryCount(): number { return this.entries.filter(e => e.level === 'sorry').length; }
  get defaultCount(): number { return this.entries.filter(e => e.level === 'default').length; }
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

  /** Format as a human-readable summary appended to Lean output. */
  summary(): string {
    if (this.entries.length === 0) return '';
    const sorrys = this.sorryCount;
    const defaults = this.defaultCount;
    const parts: string[] = [];
    if (defaults > 0) parts.push(`${defaults} default placeholder(s)`);
    if (sorrys > 0) parts.push(`${sorrys} sorry axiom(s)`);
    const lines = [`\n-- Degradation summary: ${parts.join(', ')}`];
    if (sorrys > 0) {
      lines.push(`-- ⚠ ${sorrys} sorry axiom(s) block formal verification`);
    }
    for (const [cat, entries] of this.byCat()) {
      const catSorrys = entries.filter(e => e.level === 'sorry').length;
      const catDefaults = entries.filter(e => e.level === 'default').length;
      const catParts: string[] = [];
      if (catDefaults > 0) catParts.push(`${catDefaults} default`);
      if (catSorrys > 0) catParts.push(`${catSorrys} sorry`);
      lines.push(`--   ${cat}: ${catParts.join(', ')}`);
    }
    return lines.join('\n');
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
