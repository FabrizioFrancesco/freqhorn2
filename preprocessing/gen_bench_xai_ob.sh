#!/usr/bin/env bash
# Generates one .smt2 per (network, sample) pair into ../bench_xai_ob:
#   class<c>/obesity_50x<k>_s<i>.smt2  for every obesity/*.nnet and every CSV row i.
# The last CSV column is the class and is passed as which_class;
# the features are zero-padded up to the network's maximum layer size.
set -euo pipefail

cd "$(dirname "$0")"

CSV="obesity/obesity_s100_scaled.csv"
OUT="../bench_xai_ob"
CONV="nnet2smt_tie_break.py"

mkdir -p "$OUT"

for nnet in obesity/*.nnet; do
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

# move every file into $OUT/class<c>/, by the class its query encodes
python3 sort.py "$OUT"

echo "Generated $(find "$OUT" -name '*.smt2' | wc -l | tr -d ' ') files in $OUT"
