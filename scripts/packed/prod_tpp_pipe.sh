#!/bin/bash
# V2-PACKED-PROD-TPP (untrusted tooling): the driver of the T'' run; data under .lake/v2-packed-prod/tpp (prep:
# prod_tpp_prep.sh: jet_extract_low.py on ~/kam-data/v2-packed-prod/gen_tpp_L18/state.pkl, then the mirrors).
# Emits and builds Low (then its bridge corollary), then Full (then its corollary), each chain with up to J = 3 Lean
# processes at a time (run_par.sh: dependency waves; each process under 4G, started only while the user's anon
# memory is below 18 GB; owner decision of 1 Nov: run18 stopped, its three slots free). No module starts after
# 04:30 UTC 2 Nov (DEADLINE= disables). Resumable: rerun (receipts with exit 0 are skipped; a chain is emitted again
# only when its module list is missing).
cd /home/scott/KAM-dev-worktrees/v2-packed
T=.lake/v2-packed-prod/tpp; PK=.lake/v2-packed-prod/pkg; L=.lake/v2-packed-prod/logs
export DEADLINE=${DEADLINE-1793593800}
J=${J:-3}
waitmirror() { until grep -q '^real' $T/$1_mirror.log 2>/dev/null; do sleep 30; done; [ -s $T/$1_mirror.pkl ]; }
emit() {  # stage lc seg-io
  if [ -f $T/$2_emit.log ] && ! grep -q '^real' $T/$2_emit.log; then  # an emission in progress
    until grep -q '^real' $T/$2_emit.log; do sleep 10; done
  fi
  [ -s $PK/modules_TPP_$1.txt ] && return 0
  ( time bash scripts/packed/py_capped.sh scripts/packed/jet_prod_gen.py $T/$2.json $T/$2_mirror.pkl $PK \
      --stage=$1 --tree=TPP --seg-io=$3 --led-nodes=40 ) > $T/$2_emit.log 2>&1
  [ -s $PK/modules_TPP_$1.txt ]
}
chain() {  # stage lc seg-io
  waitmirror $2 || { echo "STOP: $2 mirror"; exit 1; }
  emit $1 $2 $3 || { echo "STOP: $2 emit"; exit 1; }
  bash scripts/packed/run_par.sh 4G $PK $PK/modules_TPP_$1.txt $L/tpp_$2 $J || exit 1
  bash scripts/packed/run_gated.sh 4G $PK LG00P.TPP.Jet.$1.ChainCert $L/tpp_cert || { echo "STOP: $1 cert"; exit 1; }
  echo "CHAIN DONE $1 $(date -u +%H:%M:%S)"
}
chain Low low 40
chain Full full 13
echo "PIPE DONE"
