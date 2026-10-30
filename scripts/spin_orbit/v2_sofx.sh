#!/bin/bash
# SO-V2PKG: the landed sub-checks (sofx_gen.py, fixed-point mirror) on a re-truncated torus, v2 disp sizing.
#   v2_sofx.sh N which L PREC OUTTAG [DISP_COEF] [GRAPH_SLACK] [CUT_LOW] [BUDGET_FULL]
N=$1; w=$2; L=$3; PREC=$4; TAG=$5
B=/mnt/HC_Volume_106379410/kam-data/so-v2pkg/N$N
OUT=$B/sofx_$TAG; mkdir -p $OUT
cd "$(dirname "$0")"
export OMP_NUM_THREADS=1 SO_N=$N SO_DATA_DIR=$B/L$L SO_PREC=$PREC SO_PKG=$B/pkgR2.json SO_SHARP=1 \
  SO_BUDGET_FULL=${9:-20} SO_CUT_LOW=${8:-160} SO_DISP_COEF=${6:-420000} SO_GRAPH_SLACK=${7:-3/10000}
/usr/bin/time -v timeout 14400 nice -n 10 python3 sofx_gen.py $w $OUT > $OUT/$w.log 2>&1
echo "SOFXDONE $N $w L=$L tag=$TAG rc=$?"
