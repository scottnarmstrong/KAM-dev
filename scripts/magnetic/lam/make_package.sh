#!/bin/bash
# Build the MAG-LAM package: the magnetic certificate chain (KAM.Magnetic.Data) for lam. Reissue 2 (MAG5): DONE
# (default done5b.txt) = the 2,411 chain modules built so far (801 + 28 here, 1,582 returned by lam on 2026-11-08).
set -euo pipefail
OUT=/mnt/HC_Volume_106379410/kam-data/mag/lam
SRC=/mnt/HC_Volume_106379410/kam-mag/KAM-mag
D=/mnt/HC_Volume_106379410/kam-data/mag
COMMIT=$(git -C $SRC rev-parse HEAD)
cd "$OUT"
echo "== $(date -u +%T) consumer scan (no module outside a product's own evaluates its full remainder bound)"
python3 $SRC/scripts/magnetic/mag_consumer_scan.py $SRC | tail -1
python3 $SRC/scripts/magnetic/mag_consumer_scan.py $SRC > /dev/null
echo "== $(date -u +%T) bundle $COMMIT"
git -C $SRC bundle create $OUT/mag.bundle mag-pilot
git -C $SRC bundle verify $OUT/mag.bundle >/dev/null
echo "== $(date -u +%T) data (untracked generated sources)"
(cd $SRC && find KAM/Magnetic/Data -type f | sort) > $OUT/data.list
tar -C $SRC -cf - -T $OUT/data.list | zstd -q -T6 -3 -o $OUT/data.tar.zst -f
(cd $SRC && sha256sum $(cat $OUT/data.list)) > $OUT/data_sha256.txt
echo "== $(date -u +%T) config"
tar -C $SRC/.lake -cf - config | zstd -q -T6 -3 -o $OUT/config.tar.zst -f
DONE=${DONE:-$D/done7.txt}
echo "== $(date -u +%T) build: the core closure ($(wc -l < $D/core-closure.txt) modules) + the $(wc -l < $DONE) built chain modules"
cat $D/core-closure.txt $DONE > $OUT/prebuilt.txt
cp $DONE $OUT/done.txt; cp $D/core-closure.txt $OUT/core-roots.txt
(cd $SRC/.lake/build && for m in $(cat $OUT/prebuilt.txt); do s=${m//.//}; ls lib/lean/$s.* ir/$s.* 2>/dev/null; done) | sort -u > $OUT/build.list
tar -C $SRC/.lake/build -cf - -T $OUT/build.list | zstd -q -T6 -3 -o $OUT/build.tar.zst -f
echo "== $(date -u +%T) packages"
P=$(readlink -f $SRC/.lake/packages)
tar -C "$P" -cf - . | zstd -q -T6 -3 -o $OUT/packages.tar.zst -f
cp $SRC/scripts/magnetic/mag_lam_pool.py $OUT/
echo "$COMMIT" > $OUT/COMMIT
sha256sum mag.bundle data.tar.zst data_sha256.txt config.tar.zst build.tar.zst packages.tar.zst done.txt core-roots.txt \
  mag_lam_pool.py run_mag.sh COMMIT WORKSTATION-BRIEF.md > SHA256SUMS
ls -la $OUT; echo "== $(date -u +%T) PACKAGE-DONE"
