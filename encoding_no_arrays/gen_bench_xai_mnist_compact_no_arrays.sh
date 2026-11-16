#!/usr/bin/env bash
# Writes the array-free version of every ../bench_xai_mnist_compact_padding/*.smt2
# into ../bench_xai_mnist_compact_no_arrays (same file names), using remove_arrays.py.
set -euo pipefail

cd "$(dirname "$0")"

IN="../bench_xai_mnist_compact_padding"
OUT="../bench_xai_mnist_compact_no_arrays"

mkdir -p "$OUT"
python3 remove_arrays.py "$IN"/*.smt2 -o "$OUT"

echo "Generated $(ls "$OUT"/*.smt2 | wc -l | tr -d ' ') files in $OUT"
