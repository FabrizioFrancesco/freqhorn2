#!/bin/sh

# Number of lemmas xaihorn adds for each sample-0 benchmark of bench_xai_ha, saved to lemma_count.txt.
# With SKIP_CHECKS, processFact first adds every frozen (select ...)=const fact, then one lemma
# ((!(y=i)) || ...) for i = L..0. The first of these already carries L, so xaihorn is stopped there,
# before the expensive preimage computations; the total is frozen + L + 1.

DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$DIR/.." && pwd)"
BIN="${XAIHORN:-$ROOT/build/tools/xai/xaihorn}"
BENCH="$ROOT/bench_xai_ha"
OUT="$DIR/lemma_count.txt"

if [ ! -x "$BIN" ]; then
  echo "xaihorn binary not found: $BIN" >&2
  exit 1
fi

FILES=$(find "$BENCH" -name "*_s0.smt2" | awk -F'x' '{ split($NF, a, "_"); print a[1], $0 }' | sort -n | cut -d' ' -f2-)

if [ -z "$FILES" ]; then
  echo "no sample-0 benchmarks found in $BENCH" >&2
  exit 1
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

count() {
  mkfifo "$TMP/out"
  "$BIN" --debug 1 "$1" 2>/dev/null > "$TMP/out" &
  pid=$!
  awk -v name="$(basename "$1")" '
    /^Added lemma for [^:]*: / {
      sub(/^Added lemma for [^:]*: /, "")
      if ($0 ~ /^\(select\(.*\)=-?[0-9\/.]+\)$/) { frozen++; next }
      if (match($0, /=[0-9]+\)/)) last = substr($0, RSTART + 1, RLENGTH - 2)
      exit
    }
    END {
      if (last == "") printf "%-32s %8d %8s %8s\n", name, frozen, "-", "-"
      else printf "%-32s %8d %8d %8d\n", name, frozen, last + 1, frozen + last + 1
    }' < "$TMP/out"
  kill "$pid" 2>/dev/null
  wait "$pid" 2>/dev/null
  rm -f "$TMP/out"
}

{
  printf "%-32s %8s %8s %8s\n" file frozen layers lemmas
  for f in $FILES; do
    count "$f"
  done
} | tee "$OUT"
