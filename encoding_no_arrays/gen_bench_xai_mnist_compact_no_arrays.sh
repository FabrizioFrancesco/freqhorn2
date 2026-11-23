#!/usr/bin/env bash
# Writes the array-free version of every .smt2 under ../bench_xai_mnist_compact_padding
# into ../bench_xai_mnist_compact_no_arrays/class<c>/ (same file names), using remove_arrays.py.
set -euo pipefail

cd "$(dirname "$0")"

IN="../bench_xai_mnist_compact_padding"
OUT="../bench_xai_mnist_compact_no_arrays"

mkdir -p "$OUT"
find "$IN" -name '*.smt2' -print0 | xargs -0 python3 remove_arrays.py -o "$OUT"
python3 ../preprocessing/sort.py "$OUT"

echo "Generated $(find "$OUT" -name '*.smt2' | wc -l | tr -d ' ') files in $OUT"
