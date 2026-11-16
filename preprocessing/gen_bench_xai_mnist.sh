#!/usr/bin/env bash
# Generates one .smt2 per (network, sample) pair into ../bench_xai_mnist
# (or ../bench_xai_mnist_compact_padding with COMPACT=1):
#   mnist_50x<k>_s<i>.smt2  for every mnist/*.nnet and every sample index i in SAMPLES.
# MNIST files are large (~35 MB per layer, since layers are padded to 784x784),
# so only the selected samples are generated, e.g.: SAMPLES="0 3 7" ./gen_bench_xai_mnist.sh
# COMPACT=1 uses the converter's compact padding encoding (same semantics, much smaller files).
# The last CSV column is the class and is passed as which_class;
# the features are zero-padded up to the network's maximum layer size.
set -euo pipefail

cd "$(dirname "$0")"

CSV="mnist/mnist_s100_scaled.csv"
OUT="../bench_xai_mnist"
CONV="nnet2smt_tie_break.py"
SAMPLES="${SAMPLES:-0}"
COMPACT="${COMPACT:-0}"

MODE=""
if [ "$COMPACT" = "1" ]; then
    OUT="../bench_xai_mnist_compact_padding"
    MODE="compact"
fi

mkdir -p "$OUT"

for nnet in mnist/*.nnet; do
    name=$(basename "$nnet" .nnet)
    mls=$(awk -F, '!/^\/\// {print $4; exit}' "$nnet")
    for i in $SAMPLES; do
        # Sample i is on line i+2 (line 1 is the header)
        row=$(awk -v n=$((i+2)) 'NR==n {print; exit}' "$CSV" | tr -d '\r')
        cls=${row##*,}
        sample=$(echo "${row%,*}" | awk -F, -v n="$mls" '{s=$0; for (k=NF; k<n; k++) s=s",0"; print s}')
        python3 "$CONV" "$nnet" "$OUT/${name}_s${i}.smt2" "$cls" "$sample" $MODE
    done
    echo "$name done"
done

echo "Generated $(ls "$OUT"/*.smt2 | wc -l | tr -d ' ') files in $OUT"
