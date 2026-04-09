#!/usr/bin/env bash
# Self-hosting script: regenerate all 11 SelfHost Lean files from TS source
# Usage: ./scripts/self-host.sh [--check]
#   --check: only count errors, don't replace files
set -euo pipefail

cd "$(dirname "$0")/.."
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"

SELFHOST_DIR="lean/TSLean/Generated/SelfHost"
TMP_DIR="/tmp/selfhost_regen"
mkdir -p "$TMP_DIR"

# Source files → output names
declare -A FILES=(
  ["src/do-model/ambient.ts"]="DoModel_Ambient"
  ["src/ir/types.ts"]="ir_types"
  ["src/stdlib/index.ts"]="stdlib_index"
  ["src/typemap/index.ts"]="typemap_index"
  ["src/effects/index.ts"]="effects_index"
  ["src/parser/index.ts"]="parser_index"
  ["src/codegen/index.ts"]="codegen_index"
  ["src/rewrite/index.ts"]="rewrite_index"
  ["src/project/index.ts"]="project_index"
  ["src/verification/index.ts"]="verification_index"
  ["src/cli.ts"]="src_cli"
)

# Files that need Prelude import (all except ir_types which defines the base types)
NEEDS_PRELUDE=("stdlib_index" "typemap_index" "effects_index" "parser_index" "codegen_index" "rewrite_index" "project_index" "verification_index" "src_cli")

echo "=== Regenerating SelfHost files ==="

total_errors=0
for src in "${!FILES[@]}"; do
  name="${FILES[$src]}"
  out="$TMP_DIR/${name}.lean"

  echo -n "  $name: "
  npx tsx src/cli.ts "$src" -o "$out" 2>/dev/null

  # Add Prelude import for files that need it
  for pf in "${NEEDS_PRELUDE[@]}"; do
    if [ "$name" = "$pf" ]; then
      # Insert Prelude import after the last import line
      sed -i '/^import /a import TSLean.Generated.SelfHost.Prelude' "$out" 2>/dev/null || true
      # Deduplicate (in case it was already there)
      awk '!seen[$0]++ || !/^import TSLean.Generated.SelfHost.Prelude$/' "$out" > "${out}.tmp" && mv "${out}.tmp" "$out"
      break
    fi
  done

  # Copy ir_types → IR_Types as well (capital version for imports)
  if [ "$name" = "ir_types" ]; then
    cp "$out" "$TMP_DIR/IR_Types.lean"
  fi

  # Count errors
  errs=$(cd lean && lake env lean "$out" 2>&1 | grep -c "^.*: error" || true)
  total_errors=$((total_errors + errs))
  if [ "$errs" = "0" ]; then
    echo "✅ OK"
  else
    echo "❌ $errs errors"
  fi
done

echo ""
echo "=== Total: $total_errors errors across 11 files ==="

if [ "${1:-}" = "--check" ]; then
  echo "(check mode — files not copied)"
  exit 0
fi

echo ""
echo "=== Copying to $SELFHOST_DIR ==="
for src in "${!FILES[@]}"; do
  name="${FILES[$src]}"
  cp "$TMP_DIR/${name}.lean" "$SELFHOST_DIR/${name}.lean"
  if [ "$name" = "ir_types" ]; then
    cp "$TMP_DIR/IR_Types.lean" "$SELFHOST_DIR/IR_Types.lean"
  fi
done

echo "=== Verifying lake build ==="
cd lean && lake build 2>&1 | tail -3
