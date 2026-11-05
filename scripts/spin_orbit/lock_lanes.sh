#!/bin/bash
# LOCK-DATA (B3 lever (b), approved by root-b8): elaborate many light data modules in up to 6 parallel lanes.
#   lock_lanes.sh LOG MODULE_LIST_FILE [LANES]
# One `lake build` over the listed modules (Lake runs independent modules in parallel), in a scope capped at
# LANES CPUs (CPUQuota) and LANES x 0.9 GB + 0.6 GB memory, no swap, nice 5; logs the cgroup peak.
# Only for light data modules (<= 0.9 GB each, measured); heavy kernel modules go through lock_kbuild.sh.
L=$1; LIST=$2; N=${3:-6}
cd "$(dirname "$0")/../.." || exit 2
MEM=$(( N * 900 + 600 ))M
{ date -u; git rev-parse HEAD; echo "lanes $N mem $MEM modules $(wc -l < "$LIST")"; } > "$L"
systemd-run --user --scope -q -p MemoryMax=$MEM -p MemorySwapMax=0 -p CPUQuota=$(( N * 100 ))% bash -c '
  cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
  /usr/bin/time -v nice -n 5 lake build $(cat '"$LIST"'); rc=$?
  echo "MEMPEAK $(cat $cg/memory.peak 2>/dev/null || echo UNMEASURED)"
  echo "OOMKILL $(grep oom_kill $cg/memory.events | awk "{print \$2}")"
  echo "rc=$rc"' >> "$L" 2>&1
tail -4 "$L"
