#!/bin/sh
# SR-2 part 2 (and the SR-3 baseline): the gate-2 producer with the float Jacobi V and with the exact V'.
# Run from the repository root as a systemd user unit (see GATES report); serial, one heavy job.
set -e
D=scripts/sjsu/gate2
VP=$PWD/scripts/sjsu/rigor/results/vprime.json
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 FT_THREADS=${FT_THREADS:-4} FT_PULL_PROCS=${FT_PULL_PROCS:-3}
L=scripts/sjsu/rigor/results
python3 $D/torus.py --L 6 --K 30 --LB 3 --kol 5 --recenter 1 --G2 64 --tag sr-base-s1 > $L/sr-base-s1.log 2>&1
SJSU_VPRIME=$VP python3 $D/torus.py --L 6 --K 30 --LB 3 --kol 5 --recenter 1 --G2 64 --tag sr-vp-s1 > $L/sr-vp-s1.log 2>&1
python3 $D/torus2.py --stage1 sr-base-s1 --L 8 --K 50 --LB 6 --kol 4 --G2 128 --Lv 12 --tag sr-base-L8 > $L/sr-base-L8.log 2>&1
SJSU_VPRIME=$VP python3 $D/torus2.py --stage1 sr-vp-s1 --L 8 --K 50 --LB 6 --kol 4 --G2 128 --Lv 12 --tag sr-vp-L8 > $L/sr-vp-L8.log 2>&1
echo done > $L/sr2_rerun.done
