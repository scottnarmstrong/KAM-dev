#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p .drafts/coil
pin=79b6152e779a62287da76fb4a49918e38575b3d6
if [ ! -d .drafts/coil/PlasmaLean/.git ]; then
  git clone https://github.com/siddhartha-gadgil/PlasmaLean.git .drafts/coil/PlasmaLean
  git -C .drafts/coil/PlasmaLean checkout --detach "$pin"
fi
test "$(git -C .drafts/coil/PlasmaLean rev-parse HEAD)" = "$pin"
run() {
  systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 \
    nice -n 10 env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 \
    python3 -B scripts/coil/pilot.py "$@"
}
run fit --plan 8x16 12x24 16x40 --out .drafts/coil/fit.json
run fit --plan 20x56 --start .drafts/coil/torus-16x40.npz --out .drafts/coil/fit20.json
for mode in trace diagnostics precision; do
  run "$mode" --torus .drafts/coil/torus-20x56.npz --out ".drafts/coil/$mode.json"
done
