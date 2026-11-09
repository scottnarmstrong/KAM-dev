#!/bin/bash
# post_return.sh ARCHIVE.tar.zst STAGING: after a lam MAG return (run HERE, MAG worktree), in order:
#   1. verify_return.py (sums, olean hashes, class table) into STAGING, then seed STAGING/lib and STAGING/ir;
#   2. `lake build --no-build` of the chain target KAM.Magnetic.Data.Mag.Seg.Checks (must be rc 0: nothing stale);
#   3. Passes and the provider, one module at a time in the heavy lane (probe lock, 10G scope);
#   4. the seal DRY RUN: a scratch copy of the frozen anchor with the sealed body (`by exact` the provider) is
#      elaborated against the built tree, plus `#print axioms` of the provider. No frozen file or manifest is
#      touched (the seal itself is a separate, reviewed step).
set -euo pipefail
ARC=$1; STG=$2
WT=/mnt/HC_Volume_106379410/kam-mag/KAM-mag
D=/mnt/HC_Volume_106379410/kam-data/mag
SCR=$D/sealdry; mkdir -p $SCR
LD=$WT/.lake/sealdry; mkdir -p $LD   # lean wants its input inside the root; .lake is not tracked
cd $WT
echo "== $(date -u +%H:%M) 1. verify + seed"
python3 $WT/scripts/magnetic/lam/verify_return.py "$ARC" "$STG"
(cd "$STG" && sha256sum -c --quiet sha256.txt)
cp -a "$STG/lib" "$STG/ir" $WT/.lake/build/
echo "== $(date -u +%H:%M) 2. chain up to date"
nice lake build --no-build KAM.Magnetic.Data.Mag.Seg.Checks > $SCR/checks-nobuild.log 2>&1 \
  || { tail -20 $SCR/checks-nobuild.log; echo "STOP: the chain is not up to date"; exit 1; }
tail -1 $SCR/checks-nobuild.log
echo "== $(date -u +%H:%M) 3. Passes and the provider (heavy lane)"
$D/kbuild5/kb.sh KAM.Magnetic.Data.Mag.Passes KAM.Provider.Magnetic.MagneticBarrier
echo "== $(date -u +%H:%M) 4. seal dry run (scratch copy; frozen file untouched)"
F=KAM/Frozen/Magnetic/Theorems/MagneticBarrier.lean
python3 - "$WT/$F" "$LD/MagneticBarrierSealed.lean" <<'EOF'
import sys
src, dst = sys.argv[1:3]
t = open(src).read()
old = "  -- FROZEN_ANCHOR_PROOF_BEGIN\n  by sorry\n  -- FROZEN_ANCHOR_PROOF_END\n"
new = "  -- FROZEN_ANCHOR_PROOF_BEGIN\n  by exact KAM.Provider.Magnetic.magnetic_barrier\n  -- FROZEN_ANCHOR_PROOF_END\n"
assert t.count(old) == 1, "the draft body is not the expected `by sorry`"
open(dst, "w").write(t.replace(old, new))
EOF
diff $WT/$F $LD/MagneticBarrierSealed.lean || true
flock /mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock systemd-run --user --scope -q -p MemoryMax=10G \
  -p MemorySwapMax=0 nice -n 5 lake env lean -o $LD/MagneticBarrierSealed.olean $LD/MagneticBarrierSealed.lean \
  > $SCR/sealed.log 2>&1 && echo "sealed anchor elaborates (rc 0)" || { cat $SCR/sealed.log; exit 1; }
printf 'import KAM.Provider.Magnetic.MagneticBarrier\n#print axioms KAM.Provider.Magnetic.magnetic_barrier\n' \
  > $LD/Axioms.lean
nice lake env lean $LD/Axioms.lean | tee $SCR/axioms.txt
echo "== $(date -u +%H:%M) POST-RETURN DONE"
