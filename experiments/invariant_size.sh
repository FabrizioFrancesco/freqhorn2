#!/bin/sh

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${XAIHORN:-$ROOT/build/tools/xai/xaihorn}"

if [ $# -eq 0 ]; then
  echo "usage: $0 <file.smt2 | dir>..." >&2
  exit 1
fi

if [ ! -x "$BIN" ]; then
  echo "xaihorn binary not found: $BIN" >&2
  exit 1
fi

measure() {
  if [ ! -f "$1" ]; then
    echo "skipping $1: not a file" >&2
    return
  fi
  "$BIN" --debug 1 "$1" 2>/dev/null | awk -v name="$1" '
    /^Added lemma for [^:]*: / {
      sub(/^Added lemma for [^:]*: /, "")
      n++
      if ($0 ~ /^\(select\(.*\)=-?[0-9\/.]+\)$/) { frozen++; next }
      len = length($0)
      props++
      total += len
      if (len > max) max = len
    }
    END { printf "%-48s %8d %8d %8d %14d %14d\n", name, n, frozen, props, total, max }'
}

printf "%-48s %8s %8s %8s %14s %14s\n" file lemmas frozen layers layer_chars max_chars

for arg in "$@"; do
  if [ -d "$arg" ]; then
    # subfolders included, e.g. the class<c>/ folders written by preprocessing/sort.py
    for f in $(find "$arg" -name "*.smt2" | sort); do
      measure "$f"
    done
  else
    measure "$arg"
  fi
done
