#!/bin/sh

# Invariant size across all layer counts of bench_xai_ha, using sample 0 only.
# Output format is the same as invariant_size.sh; it is also saved to size_evolution.txt.

DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/.." && pwd)"
BENCH="$ROOT/bench_xai_ha"
OUT="$DIR/size_evolution.txt"

FILES=$(find "$BENCH" -name "*_s0.smt2" | awk -F'x' '{ split($NF, a, "_"); print a[1], $0 }' | sort -n | cut -d' ' -f2-)

if [ -z "$FILES" ]; then
  echo "no sample-0 benchmarks found in $BENCH" >&2
  exit 1
fi

"$DIR/invariant_size.sh" $FILES | tee "$OUT"
