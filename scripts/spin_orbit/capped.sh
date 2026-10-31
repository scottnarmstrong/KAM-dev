#!/bin/bash
# LOCK-DATA standing rule: every lock job runs memory-capped (8 GB, no swap) at nice 10; prints the cgroup peak.
#   capped.sh CMD ARGS...
exec systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 bash -c '
  cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
  nice -n 10 "$@"; rc=$?
  echo "CAPPED rc=$rc peak=$(cat $cg/memory.peak 2>/dev/null || echo UNMEASURED) oom=$(grep oom_kill $cg/memory.events | awk "{print \$2}")" >&2
  exit $rc' _ "$@"
