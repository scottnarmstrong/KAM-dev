#!/bin/bash
# LOCK-DATA standing rule: every lock job runs memory-capped (LOCK_MEM, default 6G under the current memory budget;
# no swap) at nice 10, and starts only once MemAvailable >= 8 GB; prints the cgroup peak.
#   capped.sh CMD ARGS...
until [ "$(awk '/MemAvailable/{print $2}' /proc/meminfo)" -ge 8388608 ]; do sleep 30; done
exec systemd-run --user --scope -q -p MemoryMax=${LOCK_MEM:-6G} -p MemorySwapMax=0 bash -c '
  cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
  nice -n 10 "$@"; rc=$?
  echo "CAPPED rc=$rc peak=$(cat $cg/memory.peak 2>/dev/null || echo UNMEASURED) oom=$(grep oom_kill $cg/memory.events | awk "{print \$2}")" >&2
  exit $rc' _ "$@"
