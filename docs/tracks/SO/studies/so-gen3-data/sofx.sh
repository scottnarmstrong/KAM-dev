#!/bin/bash
N=$1; w=$2; PREC=$3; PKG=$4; OUT=$5; D=/root/code/KAM-inp-sogen3/.drafts/scratch/g3
cd /root/code/KAM-inp-sogen3/scripts/spin_orbit
export OMP_NUM_THREADS=1 SO_N=$N SO_DATA_DIR=$D/N$N SO_PREC=$PREC SO_PKG=$PKG SO_SHARP=1 SO_BUDGET_FULL=36 SO_CUT_LOW=${CUT_LOW:-30}
mkdir -p $OUT
/usr/bin/time -v timeout 14400 nice -n 10 python3 sofx_gen.py $w $OUT > $OUT/$w.log 2>&1
echo "SOFXDONE $N $w rc=$?"
