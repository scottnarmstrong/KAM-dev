#!/bin/bash
# V2-PACKED-PROD-TPP (untrusted tooling): the driver of the T'' run; data under .lake/v2-packed-prod/tpp (prep:
# jet_extract_low.py on ~/kam-data/v2-packed-prod/gen_tpp_L18/state.pkl, then jet_low_gen.py --mirror-only).
# T'' (PROD-TPP): emit and build both chains, one Lean process at a time under 4G; no Lean start after 04:30 UTC.
# Resumable: rerun this script (the runner skips modules whose receipts say exit 0; emission is redone only when
# its module list is missing).
cd /home/scott/KAM-dev-worktrees/v2-packed
T=.lake/v2-packed-prod/tpp; PK=.lake/v2-packed-prod/pkg; L=.lake/v2-packed-prod/logs
export DEADLINE=${DEADLINE-1793593800}  # 04:30 UTC 2 Nov; DEADLINE= disables it
waitmirror() { until grep -q '^real' $T/$1_mirror.log 2>/dev/null; do sleep 30; done; [ -s $T/$1_mirror.pkl ]; }
emit() {  # stage lc seg-io
  [ -s $PK/modules_TPP_$1.txt ] && return 0
  ( time bash scripts/packed/py_capped.sh scripts/packed/jet_prod_gen.py $T/$2.json $T/$2_mirror.pkl $PK \
      --stage=$1 --tree=TPP --seg-io=$3 --led-nodes=40 ) > $T/$2_emit.log 2>&1
}
waitmirror low || { echo "STOP: low mirror"; exit 1; }
emit Low low 40 || { echo "STOP: low emit"; exit 1; }
bash scripts/packed/run_modules.sh 4G $PK $PK/modules_TPP_Low.txt $L/tpp_low || exit 1
waitmirror full || { echo "STOP: full mirror"; exit 1; }
emit Full full 13 || { echo "STOP: full emit"; exit 1; }
bash scripts/packed/run_modules.sh 4G $PK $PK/modules_TPP_Full.txt $L/tpp_full || exit 1
printf 'LG00P.TPP.Jet.Low.ChainCert\nLG00P.TPP.Jet.Full.ChainCert\n' > $T/chaincert.txt
bash scripts/packed/run_modules.sh 4G $PK $T/chaincert.txt $L/tpp_cert || exit 1
echo "PIPE DONE"
