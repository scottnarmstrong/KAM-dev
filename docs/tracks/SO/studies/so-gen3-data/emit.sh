#!/bin/bash
N=$1; w=$2; L=$3; D=/root/code/KAM-inp-sogen3/.drafts/scratch/g3
cd /root/code/KAM-inp-sogen3/scripts/spin_orbit
export OMP_NUM_THREADS=1 SO_N=$N SO_DATA_DIR=$D/N$N SO_RHO=${RHO:-1/70}
S=$(python3 -c "import math;print(math.ceil(3.33*$L)+24)")
timeout 3600 nice -n 10 python3 rot_emit.py $w $L $L $L $S 2 11/5 $D/N$N/${w}_rot.json > $D/N$N/emit_rot_$w.log 2>&1
echo "EMITDONE $N $w rc=$?"
