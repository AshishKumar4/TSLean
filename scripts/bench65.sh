#!/bin/bash
# Batch test: transpile all 64 core Agents SDK .ts files → Lean 4, count PASS/FAIL.
# PASS = zero errors (warnings like "unused variable" are OK).
set -euo pipefail
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"

TSLEAN=/workspace/tslean
SDK=/workspace/agents-sdk/packages/agents/src
OUTDIR=/tmp/bench65

rm -rf "$OUTDIR" && mkdir -p "$OUTDIR"

PASS=0; FAIL=0; TOTAL=0
PASS_LIST=""; FAIL_LIST=""

while IFS= read -r file; do
    TOTAL=$((TOTAL+1))
    rel="${file#$SDK/}"
    out="$OUTDIR/$(echo "$rel" | tr '/' '_').lean"

    # Transpile
    cd "$TSLEAN"
    if ! npx tsx src/cli.ts "$file" -o "$out" 2>/dev/null >/dev/null; then
        FAIL=$((FAIL+1))
        FAIL_LIST="$FAIL_LIST\nTRANSPILE_FAIL: $rel"
        continue
    fi

    # Check with Lean — count only lines containing "error" (not "warning")
    cd "$TSLEAN/lean"
    errs=$(lake env lean "$out" 2>&1 | grep -c "^.*: error" || true)

    if [ "$errs" -eq 0 ]; then
        PASS=$((PASS+1))
        PASS_LIST="$PASS_LIST\n  $rel"
    else
        FAIL=$((FAIL+1))
        first=$(lake env lean "$out" 2>&1 | grep ": error" | head -1)
        FAIL_LIST="$FAIL_LIST\n  FAIL($errs): $rel  [$first]"
    fi
done < <(find "$SDK" -name "*.ts" \
    -not -path "*test*" -not -path "*tests*" -not -path "*__tests__*" \
    -not -path "*/cli/*" -not -path "*/cli-tests/*" -not -path "*/e2e-tests/*" \
    -not -path "*/react-tests/*" -not -path "*/x402-tests/*" -not -path "*/tests-d/*" \
    -not -name "*.test.ts" -not -name "*.test-d.ts" \
    -not -name "setup.ts" -not -name "env.d.ts" -not -name "vitest.config.ts" \
    | sort)

echo "==============================="
echo "  RESULTS: $PASS / $TOTAL pass"
echo "==============================="
echo -e "\nPASSING:$PASS_LIST"
echo -e "\nFAILING (sorted by error count):$(echo -e "$FAIL_LIST" | sort -t'(' -k2 -n)"
