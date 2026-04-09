#!/usr/bin/env bash
# Self-hosting pipeline: transpile → post-process → compile
# Usage: bash scripts/self-host.sh
set -euo pipefail

PROJ="$(cd "$(dirname "$0")/.." && pwd)"
LEAN_SH="$PROJ/lean/TSLean/Generated/SelfHost"
TMP="/tmp/selfhost_pipeline"
PP="$PROJ/scripts/selfhost-postprocess.ts"

mkdir -p "$TMP"

echo "═══ TSLean Self-Hosting Pipeline ═══"

# Sources in dependency order
declare -a NAMES=(ir_types effects_index stdlib_index typemap_index rewrite_index
  verification_index DoModel_Ambient codegen_index parser_index project_index src_cli)
declare -A SRC
SRC[ir_types]=src/ir/types.ts
SRC[effects_index]=src/effects/index.ts
SRC[stdlib_index]=src/stdlib/index.ts
SRC[typemap_index]=src/typemap/index.ts
SRC[rewrite_index]=src/rewrite/index.ts
SRC[verification_index]=src/verification/index.ts
SRC[DoModel_Ambient]=src/do-model/ambient.ts
SRC[codegen_index]=src/codegen/index.ts
SRC[parser_index]=src/parser/index.ts
SRC[project_index]=src/project/index.ts
SRC[src_cli]=src/cli.ts

FIX_IR="$PROJ/scripts/fix-ir-types.ts"

echo ""
echo "Step 1: Transpile + post-process"
for name in "${NAMES[@]}"; do
  src="${SRC[$name]}"
  raw="$TMP/${name}_raw.lean"
  out="$TMP/${name}.lean"
  cd "$PROJ"
  if npx tsx src/cli.ts "$src" -o "$raw" 2>/dev/null; then
    if [ "$name" = "ir_types" ]; then
      # ir_types uses dedicated fix script (avoids regex bugs in general postprocessor)
      npx tsx "$FIX_IR" "$raw" "$out" 2>&1 | head -1
    elif npx tsx "$PP" "$raw" "$out" 2>&1 | head -1; then
      :
    else
      echo "  ! $name: post-process failed, using raw"
      cp "$raw" "$out"
    fi
  else
    echo "  ✗ $name: transpile failed"
  fi
done

echo ""
echo "Step 2: Install"
for name in "${NAMES[@]}"; do
  f="$TMP/${name}.lean"
  [ -f "$f" ] && cp "$f" "$LEAN_SH/${name}.lean" && echo "  ✓ ${name}.lean ($(wc -l < "$f") lines)"
done

echo "-- Redirect" > "$LEAN_SH/IR_Types.lean"
echo "import TSLean.Generated.SelfHost.ir_types" >> "$LEAN_SH/IR_Types.lean"
echo "  ✓ IR_Types.lean → ir_types.lean"

echo ""
echo "Step 3: lake build"
cd "$PROJ/lean"
export PATH="/opt/lean4/lean-4.29.0-linux/bin:$PATH"
if lake build 2>&1 | tail -3; then
  echo ""
  echo "═══ Self-hosting: PASSED ═══"
else
  echo ""
  echo "═══ Self-hosting: FAILED ═══"
  lake build 2>&1 | grep "error:" | head -10
  exit 1
fi
