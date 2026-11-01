#!/bin/bash
# MAG-2b: the production sofx mirror run (GENERATE + CHECK) of the magnetic torus; writes $O/MIRROR_DONE rc=..
O=${O:-/mnt/HC_Volume_106379410/kam-data/mag/prod}
cd "$(dirname "$0")/../spin_orbit" || exit 2
export PYTHONPATH=$(cd ../magnetic && pwd) OMP_NUM_THREADS=1 SO_CLIENT=sofx_mag SO_DATA_DIR=$O SO_PREC=128 \
  SO_BUDGET_FULL=27 SO_CUT_LOW=600 SO_DISP_COEF=700000000
rm -f "$O/MIRROR_DONE"
/usr/bin/time -v python3 -B sofx_gen.py mag "$O/gen" > "$O/gen.log" 2>&1
echo "rc=$? $(date -u +%H:%M)" > "$O/MIRROR_DONE"
