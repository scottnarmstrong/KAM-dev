#!/bin/bash
# SO-V2PKG: re-emit an archived torus at truncation L (rot_emit.py), output to kam-data/so-v2pkg.
#   v2_emit_scan.sh N which L [rho]
N=$1; w=$2; L=$3; RHO=${4:-1/140}
SRC=/mnt/HC_Volume_106379410/kam-data/so-gen3/g3/N$N
OUT=/mnt/HC_Volume_106379410/kam-data/so-v2pkg/N$N
mkdir -p $OUT
cd "$(dirname "$0")"
S=$(python3 -c "import math;print(math.ceil(3.33*$L)+24)")
export OMP_NUM_THREADS=1 SO_N=$N SO_DATA_DIR=$SRC SO_RHO=$RHO
timeout 3600 nice -n 10 python3 rot_emit.py $w $L $L $L $S 2 11/5 $OUT/${w}_L${L}.json > $OUT/emit_${w}_L${L}.log 2>&1
echo "EMITDONE $N $w L=$L rc=$?"
