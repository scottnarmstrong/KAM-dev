#!/bin/bash
# sim5.sh: simulate lam's unpack + check of the reissue-2 package at another path (packages symlinked, not unpacked)
set -euo pipefail
X=/mnt/HC_Volume_106379410/kam-data/mag/lam; S=/mnt/HC_Volume_106379410/kam-data/mag/sim5
rm -rf $S; mkdir -p $S; cd $X
sha256sum -c --quiet SHA256SUMS && echo "sums OK"
c=$(cat COMMIT)
git clone -q --no-checkout mag.bundle $S/tree
git -C $S/tree fetch -q $X/mag.bundle mag-pilot
git -C $S/tree checkout -q -B mag-pilot "$c"
zstd -dc data.tar.zst | tar -C $S/tree -xf -
(cd $S/tree && sha256sum -c --quiet $X/data_sha256.txt) && echo "data OK"
mkdir -p $S/tree/.lake/build
ln -sfn /root/code/KAM/.lake/packages $S/tree/.lake/packages
zstd -dc build.tar.zst | tar -C $S/tree/.lake/build -xf -
zstd -dc config.tar.zst | tar -C $S/tree/.lake -xf -
zstd -dc packages.tar.zst | tar -t | wc -l
cd $S/tree
nice lake build --no-build $(cat $X/core-roots.txt) $(cat $X/done.txt) > $S/check-nobuild.log 2>&1 && echo "no-build OK"
P=KAM.Magnetic.Data.Mag.Seg.Prod
MAG_DRY=1 MAG_DONE=$X/done.txt MAG_PROBES=$P.M8RemR1,KAM.Magnetic.Data.Mag.Seg.Full.S12,KAM.Magnetic.Data.Mag.Seg.Low.S70,$P.M109 python3 $X/mag_lam_pool.py $S/tree $S/dry 1 KAM.Magnetic.Data.Mag.Seg.Checks
flock /mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock env MAG_DONE=$X/done.txt MAG_DEFAULT_CAP=10G python3 $X/mag_lam_pool.py $S/tree $S/smoke 1 $P.M209RemR1 | tail -2
echo SIM-DONE
