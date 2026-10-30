#!/bin/bash
N=$1; w=$2; D=/root/code/KAM-inp-sogen3/.drafts/scratch/g3
cd /root/code/KAM-inp-sogen3/scripts/spin_orbit
export OMP_NUM_THREADS=1 SO_N=$N SO_DATA_DIR=$D/N$N
rm -f $D/N$N/scan_$w.jsonl
timeout 3600 nice -n 10 python3 rot_scan.py $w $D/N$N/scan_$w.jsonl ${SCAN:-26,26,26 28,28,28 29,29,29 30,30,30 31,31,31 32,32,32 33,33,33 34,34,34 36,36,36} > $D/N$N/scan_$w.log 2>&1
echo "SCANDONE $N $w rc=$?"
