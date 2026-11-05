#!/bin/bash
# LOCK-DATA B3 lever (b) under the partial memory budget (root-b8): up to LANES (default 3) concurrent elaboration
# lanes, each one module = one `lake build` through the I/N/P compile gate in its own scope (MemoryMax=2G, no swap),
# started only while MemAvailable >= 10 GB.  Modules are given as dependency levels (one file per level, built in
# order, so every lane's imports are already built).
#   lock_lane3.sh LOGDIR LEVEL_FILE [LEVEL_FILE ...]      (LANES=3 by default; env LANES)
L=$1; shift; mkdir -p "$L"
WT=$(cd "$(dirname "$0")/../.." && pwd)
G=/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh
lane() {
  m=$1
  until [ "$(awk '/MemAvailable/{print $2}' /proc/meminfo)" -ge 10485760 ]; do sleep 20; done
  systemd-run --user --scope -q -p MemoryMax=2G -p MemorySwapMax=0 bash -c '
    cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup); t0=$(date +%s)
    '"$G"' '"$WT"' '"$m"' > '"$L/$m"'.log 2>&1; rc=$?
    echo "'"$m"' rc=$rc wall=$(( $(date +%s) - t0 ))s peak=$(cat $cg/memory.peak) oom=$(grep oom_kill $cg/memory.events | awk "{print \$2}")"'
}
export -f lane; export L WT G
for lv in "$@"; do
  echo "level $lv $(wc -l < "$lv") $(date -u +%T)"
  xargs -a "$lv" -P "${LANES:-3}" -I{} bash -c 'lane {}' | tee -a "$L/summary.txt" | grep -v ' rc=0 ' 
done
echo "done $(date -u +%T) fails=$(grep -vc ' rc=0 ' "$L/summary.txt")"
