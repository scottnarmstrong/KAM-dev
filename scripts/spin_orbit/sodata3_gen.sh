#!/bin/bash
# SO-DATA3: generate + check one N = 65 torus under the v2 sizing (SO-V2PKG d01b: L = 20, CertFixed 96,
# cut-offs 100000 / 160, budgets 1e-20 / 1e-8), per-side graph SOS margins, optional exact disp.
#   sodata3_gen.sh which OUTTAG SLACK_LO SLACK_HI [DISP]
w=$1; TAG=$2
D=/mnt/HC_Volume_106379410/kam-data/so-data3
OUT=$D/$TAG; mkdir -p $OUT
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 SO_N=65 SO_DATA_DIR=$D/L20 SO_PREC=96 SO_PKG=$D/pkgR2.json SO_SHARP=1 \
  SO_BUDGET_FULL=20 SO_CUT_LOW=160 SO_DISP_COEF=420000 SO_GRAPH_SLACK_LO=$3 SO_GRAPH_SLACK_HI=$4
[ -n "$5" ] && export SO_DISP=$5
/usr/bin/time -v timeout 14400 nice -n 10 python3 sofx_gen.py $w $OUT > $OUT/$w.log 2>&1
echo "GENDONE $w $TAG rc=$?"
