// Pipeline timing instrumentation.
// Tracks elapsed time for each transpilation phase.

export interface PhaseTime {
  phase: string;
  ms: number;
}

export class PipelineTimer {
  private phases: PhaseTime[] = [];
  private current: { phase: string; start: number } | null = null;

  start(phase: string): void {
    this.end();  // end previous phase if any
    this.current = { phase, start: performance.now() };
  }

  end(): void {
    if (this.current) {
      const ms = performance.now() - this.current.start;
      this.phases.push({ phase: this.current.phase, ms });
      this.current = null;
    }
  }

  get total(): number {
    return this.phases.reduce((sum, p) => sum + p.ms, 0);
  }

  get all(): readonly PhaseTime[] { return this.phases; }

  /** Format as a human-readable timing report. */
  report(): string {
    this.end();
    const total = this.total;
    if (total === 0) return '';
    const lines = ['Timing:'];
    for (const p of this.phases) {
      const pct = ((p.ms / total) * 100).toFixed(0);
      const bar = '█'.repeat(Math.max(1, Math.round(p.ms / total * 20)));
      lines.push(`  ${p.phase.padEnd(12)} ${p.ms.toFixed(0).padStart(5)}ms ${pct.padStart(3)}% ${bar}`);
    }
    lines.push(`  ${'total'.padEnd(12)} ${total.toFixed(0).padStart(5)}ms`);
    return lines.join('\n');
  }
}

// Global timer for the current transpilation
let _timer: PipelineTimer | null = null;

export function currentTimer(): PipelineTimer {
  if (!_timer) _timer = new PipelineTimer();
  return _timer;
}

export function resetTimer(): PipelineTimer {
  _timer = new PipelineTimer();
  return _timer;
}
