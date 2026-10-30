#!/bin/bash
# usage: hp.sh N  (runs lower then upper)
N=$1; D=/root/code/KAM-inp-sogen3/.drafts/scratch/g3/N$N
cd /root/code/KAM-inp-sogen3/scripts/spin_orbit
export OMP_NUM_THREADS=1 SO_N=$N SO_HP_BITS=360 SO_PBITS=300
for w in lower upper; do
  timeout 10800 nice -n 10 python3 run_hp.py $w $D 4 8 && \
  timeout 3600 nice -n 10 python3 emit.py $w $D/${w}_512.pkl $D/$w.json 1e-80
  echo "DONE $N $w rc=$?"
done
