#!/bin/sh
# SR-3 ALIAS: the gate-2 tube measurement with V' at tube degree Lv = 8 on the 128^2 grid and on a 256^2 grid
# (zero padding: twice the 128 grid's Nyquist, over twice the largest retained mode, 2 x 55 < 128).
set -e
D=scripts/sjsu/gate2
VP=$PWD/scripts/sjsu/rigor/results/vprime.json
L=scripts/sjsu/rigor/results
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 FT_THREADS=${FT_THREADS:-4} FT_PULL_PROCS=${FT_PULL_PROCS:-3}
for G in 128 256; do
  SJSU_VPRIME=$VP /usr/bin/time -v python3 $D/torus2.py --stage1 sr-vp-s1 --L 8 --K 50 --LB 6 --kol 4 --G2 $G --Lv 8 \
    --tag sr3-vp-L8-g$G-v8 > $L/sr3-vp-L8-g$G-v8.log 2>&1
done
echo done > $L/sr3.done
