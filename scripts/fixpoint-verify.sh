#!/usr/bin/env bash
# fixpoint-verify.sh — Verify fixpoint between TS and Lean transpilers.
#
# For each test file:
#   1. Transpile with TS pipeline: npx tsx src/cli.ts file.ts → gen1.lean
#   2. Preprocess: npx tsx src/preprocessor/tsc-to-json.ts file.ts → file.json
#   3. Transpile with Lean pipeline: ./lean/.lake/build/bin/tslean file.json → gen2.lean
#   4. Compare gen1.lean vs gen2.lean
#
# Exit 0 if all fixpoint targets match, 1 otherwise.
set -euo pipefail

PROJ="$(cd "$(dirname "$0")/.." && pwd)"
TMP="/tmp/fixpoint_verify"
mkdir -p "$TMP"

cd "$PROJ"
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"

# Build Lean executable
echo "Building Lean transpiler..."
cd lean && lake build tslean 2>&1 | tail -1 && cd "$PROJ"
TSLEAN="$PROJ/lean/.lake/build/bin/tslean"

# Fixpoint targets
declare -a TARGETS=(
  # Trivial inputs (must match)
  "tests/fixtures/basic/hello.ts"
  "tests/fixtures/basic/interfaces.ts"
  "tests/fixtures/basic/classes.ts"
  "tests/fixtures/generics/discriminated-unions.ts"
  "tests/fixtures/effects/async.ts"
  "tests/fixtures/durable-objects/counter.ts"
  # V2 codegen files (the crown jewels)
  "src/codegen/lean-ast.ts"
  "src/codegen/printer.ts"
  "src/codegen/lower.ts"
  "src/codegen/v2.ts"
)

echo ""
echo "═══ Fixpoint Verification ═══"
echo ""

total=0
identical=0
failed=0

# Phase 1: Transpile all files with TS pipeline
echo "Phase 1: TS transpilation..."
for f in "${TARGETS[@]}"; do
  base=$(basename "$f" .ts | tr '-' '_')
  npx tsx src/cli.ts "$f" -o "$TMP/ts_${base}.lean" 2>/dev/null &
done
wait
echo "  Done."

# Phase 2: Preprocess all files to JSON
echo "Phase 2: JSON preprocessing..."
for f in "${TARGETS[@]}"; do
  base=$(basename "$f" .ts | tr '-' '_')
  npx tsx src/preprocessor/tsc-to-json.ts "$f" "$TMP/${base}.json" 2>/dev/null &
done
wait
echo "  Done."

# Phase 3: Transpile all JSON with Lean pipeline
echo "Phase 3: Lean transpilation..."
for f in "${TARGETS[@]}"; do
  base=$(basename "$f" .ts | tr '-' '_')
  "$TSLEAN" "$TMP/${base}.json" 2>/dev/null > "$TMP/lean_${base}.lean" || true
done
echo "  Done."
echo ""

# Phase 4: Compare
set +e  # Don't exit on diff failures
for f in "${TARGETS[@]}"; do
  base=$(basename "$f" .ts | tr '-' '_')
  total=$((total + 1))

  if [ ! -f "$TMP/ts_${base}.lean" ] || [ ! -f "$TMP/lean_${base}.lean" ]; then
    echo "  ✗ $base: missing output"
    failed=$((failed + 1))
    continue
  fi

  ts_lines=$(wc -l < "$TMP/ts_${base}.lean")
  lean_lines=$(wc -l < "$TMP/lean_${base}.lean")

  if diff "$TMP/ts_${base}.lean" "$TMP/lean_${base}.lean" > /dev/null 2>&1; then
    echo "  ✓ $base: IDENTICAL (${ts_lines}L)"
    identical=$((identical + 1))
  else
    diff_count=$(diff "$TMP/ts_${base}.lean" "$TMP/lean_${base}.lean" | grep "^[<>]" | wc -l)
    echo "  ✗ $base: ${diff_count} differing lines (TS=${ts_lines}L Lean=${lean_lines}L)"
    failed=$((failed + 1))
  fi
done

echo ""
echo "═══ Results: ${identical}/${total} identical, ${failed} different ═══"
echo ""

if [ "$failed" -eq 0 ]; then
  echo "FIXPOINT ACHIEVED ✓"
  exit 0
else
  echo "Fixpoint not yet achieved — ${failed} files differ"
  exit 1
fi
