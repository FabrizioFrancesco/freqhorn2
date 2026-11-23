#!/bin/sh

# Call counts and timings (xaihorn --profile) for the sample-0 benchmarks with 1, 2 and 3
# layers of bench_xai_ha, saved to profile.txt. Override the selection with LAYERS="1 2 3"
# and SAMPLES="0", and the per-run time limit (seconds) with TIMEOUT.

DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/.." && pwd)"
BIN="${XAIHORN:-$ROOT/build/tools/xai/xaihorn}"
BENCH="$ROOT/bench_xai_ha"
OUT="$DIR/profile.txt"
LAYERS="${LAYERS:-1 2 3}"
SAMPLES="${SAMPLES:-0}"
TIMEOUT="${TIMEOUT:-600}"

if [ ! -x "$BIN" ]; then
  echo "xaihorn binary not found: $BIN" >&2
  exit 1
fi

{
  for l in $LAYERS; do
    for s in $SAMPLES; do
      f=$(find "$BENCH" -name "heart_attack_50x${l}_s${s}.smt2" | head -1)
      if [ -z "$f" ]; then
        echo "heart_attack_50x${l}_s${s}.smt2 not found in $BENCH" >&2
        continue
      fi
      echo "######## $(basename "$f")"
      perl -e 'alarm shift; exec @ARGV' "$TIMEOUT" "$BIN" --profile "$f" 2>&1 >/dev/null |
        grep -v "^INV SYN ROUND\|^$"
      echo
    done
  done
} | tee "$OUT"
