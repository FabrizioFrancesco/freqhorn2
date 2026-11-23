#!/bin/sh

# substituteCoefficients statistics (selects found, substitutions, DAG size before -> after) for each
# sample-0 benchmark of bench_xai_ha, saved to substitute_coefficients.txt.
# Each block of substituteCoefficients lines is the preimage computation following the
# "layer L" marker (the lemma ((!(y=L)) || ...) just added). Runs are cut after TIMEOUT seconds.

DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/.." && pwd)"
BIN="${XAIHORN:-$ROOT/build/tools/xai/xaihorn}"
BENCH="$ROOT/bench_xai_ha"
OUT="$DIR/substitute_coefficients.txt"
TIMEOUT="${TIMEOUT:-300}"

if [ ! -x "$BIN" ]; then
  echo "xaihorn binary not found: $BIN" >&2
  exit 1
fi

FILES=$(find "$BENCH" -name "*_s0.smt2" | awk -F'x' '{ split($NF, a, "_"); print a[1], $0 }' | sort -n | cut -d' ' -f2-)

if [ -z "$FILES" ]; then
  echo "no sample-0 benchmarks found in $BENCH" >&2
  exit 1
fi

run() {
  echo "== $(basename "$1")"
  start=$(date +%s)
  perl -e 'alarm shift; exec @ARGV' "$TIMEOUT" "$BIN" --debug 2 "$1" 2>/dev/null | awk '
    /^Added lemma for [^:]*: \(\(!\(_FH_0=[0-9]+\)/ {
      match($0, /_FH_0=[0-9]+/)
      print "layer " substr($0, RSTART + 6, RLENGTH - 6)
      next
    }
    /^substituteCoefficients:/ { print }
  '
  echo "-- $(( $(date +%s) - start ))s"
  echo
}

{
  for f in $FILES; do
    run "$f"
  done
} | tee "$OUT"
