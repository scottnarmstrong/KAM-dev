#!/bin/bash
# mag_lean.sh MODULE...: elaborate the given KAM.Magnetic.* modules in order into .lake/mag-build of this worktree
# (oleans of everything else from KAM-inp's build; nothing else is rebuilt).  Capped: 6 GB, nice 10, gated on
# MemAvailable >= 12 GB.  Prints module, rc, wall s, max RSS kB.
WT=$(cd "$(dirname "$0")/../.." && pwd); OUT=$WT/.lake/mag-build
# overlay: a symlink tree of KAM-inp's KAM oleans (refreshed when absent), our modules written over it
[ -d "$OUT/KAM/Certificate" ] || { mkdir -p "$OUT"; cp -rs /root/code/KAM-inp/.lake/build/lib/lean/KAM "$OUT/KAM"; }
for M in "$@"; do
  while [ "$(awk '/MemAvailable/{print $2}' /proc/meminfo)" -lt 12000000 ]; do sleep 30; done
  rel=${M//.//}; mkdir -p "$OUT/$(dirname "$rel")"; rm -f "$OUT/$rel.olean" "$OUT/$rel.ilean"
  t0=$(date +%s)
  ( cd /root/code/KAM-inp && /usr/bin/time -f "%M" -o "$OUT/$rel.rss" systemd-run --user --scope -q -p MemoryMax=6G \
      -p MemorySwapMax=0 nice -n 10 lake env sh -c "LEAN_PATH=$OUT:\$LEAN_PATH exec lean --root=$WT -o $OUT/$rel.olean -i $OUT/$rel.ilean $WT/$rel.lean" ) > "$OUT/$rel.log" 2>&1
  rc=$?; echo "$M rc=$rc $(( $(date +%s) - t0 ))s rss=$(tail -1 "$OUT/$rel.rss")kB"; [ $rc -ne 0 ] && { tail -20 "$OUT/$rel.log"; exit $rc; }
done
exit 0
