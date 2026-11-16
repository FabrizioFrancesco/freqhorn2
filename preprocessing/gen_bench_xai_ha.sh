#!/usr/bin/env bash
# Generates one .smt2 per (network, sample) pair into ../bench_xai_ha:
#   heart_attack_50x<k>_s<i>.smt2  for every heart_attack/*.nnet and every CSV row i.
# The last CSV column is the class and is passed as which_class;
# the 13 features are zero-padded up to the network's maximum layer size.
set -euo pipefail

cd "$(dirname "$0")"

CSV="heart_attack/heart_attack_s100_scaled.csv"
OUT="../bench_xai_ha"
CONV="nnet2smt_tie_break.py"

mkdir -p "$OUT"

for nnet in heart_attack/*.nnet; do
    name=$(basename "$nnet" .nnet)
    mls=$(awk -F, '!/^\/\// {print $4; exit}' "$nnet")
    i=0
    tail -n +2 "$CSV" | tr -d '\r' | while IFS= read -r row; do
        [ -z "$row" ] && continue
        cls=${row##*,}
        sample=$(echo "${row%,*}" | awk -F, -v n="$mls" '{s=$0; for (k=NF; k<n; k++) s=s",0"; print s}')
        python3 "$CONV" "$nnet" "$OUT/${name}_s${i}.smt2" "$cls" "$sample"
        i=$((i+1))
    done
    echo "$name done"
done

echo "Generated $(ls "$OUT"/*.smt2 | wc -l | tr -d ' ') files in $OUT"
