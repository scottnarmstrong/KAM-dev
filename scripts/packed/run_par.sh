#!/bin/bash
# V2-PACKED-PROD-TPP: build the modules of one generated chain with up to J Lean processes at a time, in the
# dependency waves of `jet_prod_gen.py`'s module list: the book and the ledger parts (they import only the core),
# then `Data`, then the block theorems `B<i>`, then `Chain`. Each module goes through `run_gated.sh` (cap CAP, the
# memory gate, DEADLINE). Stops after the first wave with a failure. Resumable (receipts with exit 0 are skipped).
# Usage: run_par.sh CAP PKGDIR LIST LOGDIR J
cap=$1; pkg=$2; list=$3; logdir=$4; j=$5
here=$(cd "$(dirname "$0")" && pwd)
for pat in '\.(Book|Led[0-9]+)$' '\.Data$' '\.B[0-9]+$' '\.Chain$'; do
  grep -E "$pat" "$list" | xargs -r -P "$j" -I{} bash "$here/run_gated.sh" "$cap" "$pkg" {} "$logdir" \
    || { echo "STOP: a module of wave $pat failed"; exit 1; }
done
echo "WAVES DONE $list"
