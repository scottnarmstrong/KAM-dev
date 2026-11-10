#!/bin/bash
# MAG-2b: the routeARefined witness (exact refined claim, X*, caps, disp) of the production certificate.
O=${O:-/mnt/HC_Volume_106379410/kam-data/mag/prod}
cd "$(dirname "$0")" || exit 2
export OMP_NUM_THREADS=1 SO_CLIENT=sofx_mag SO_DATA_DIR=$O SO_PREC=128 SO_BUDGET_FULL=27 SO_CUT_LOW=600 \
  PYTHONPATH=$(pwd):$(cd ../spin_orbit && pwd)
rm -f "$O/WITNESS_DONE"
/usr/bin/time -v python3 -B mag_witness.py "$O/gen" "$O/mag_witness.json" > "$O/witness.log" 2>&1
echo "rc=$? $(date -u +%H:%M)" > "$O/WITNESS_DONE"
