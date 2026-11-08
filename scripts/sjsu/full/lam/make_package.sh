#!/bin/bash
# Assemble the lam package of the SJSU-FULL gates into PKG (default kam-data/sjsu-full/lam-gates).
# usage: make_package.sh MAIN_1E9_BIN G5_REAL_DIR G5_TINY_DIR SMOKE_REF_DIR [PKG]
set -euo pipefail
MAINBIN=$1; G5REAL=$2; G5TINY=$3; SMOKE=$4
PKG=${5:-/mnt/HC_Volume_106379410/kam-data/sjsu-full/lam-gates}
HERE=$(cd "$(dirname "$0")" && pwd); FULL=$(dirname "$HERE"); REPO=$(cd "$FULL/../../.." && pwd)
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p $T/repo/scripts/sjsu/full $T/repo/applications/sjsu $T/repo/data $T/repo/smoke $T/g5/tiny
cp $FULL/{jets,model,nf,ladder,stage2,g6_model_gap,g2_modulation,make_points,validate_e6}.py $FULL/points.json $T/repo/scripts/sjsu/full/
cp -r $REPO/applications/sjsu/scripts $REPO/applications/sjsu/validation $T/repo/applications/sjsu/
find $T/repo -name __pycache__ -prune -exec rm -rf {} +
head -c $((26 * 8 * 4600)) "$MAINBIN" > $T/repo/data/main_20Myr.bin      # first 4600 blocks (20.3 Myr)
cp $SMOKE/{g1,g3,g6}.json $T/repo/smoke/
python3 $FULL/g5_sources.py $T/g5
cp -r $G5REAL/{Kernel,Native,blocks.txt,meta.json} $T/g5/
cp -r $G5TINY/{Kernel,Native,blocks.txt} $T/g5/tiny/
mkdir -p $PKG
(cd $T && tar -cf - repo | zstd -q -19 -T4 -o $PKG/repo.tar.zst -f)
(cd $T && tar -cf - g5 | zstd -q -19 -T4 -o $PKG/g5.tar.zst -f)
python3 $HERE/make_jobs.py $PKG/jobs.tsv $(ls $G5REAL/Kernel | wc -l)
cp $HERE/{run.sh,pool.py,verify_return.py,WORKSTATION-BRIEF.md} $PKG/
(cd $PKG && sha256sum repo.tar.zst g5.tar.zst jobs.tsv pool.py run.sh verify_return.py WORKSTATION-BRIEF.md > SHA256SUMS)
ls -la $PKG
