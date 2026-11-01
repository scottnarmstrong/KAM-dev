#!/bin/bash
# V2-PACKED-GEN: build the stale core modules needed by the given targets, ONE Lean process at a time: repeatedly take
# the first module `lake build --no-build` reports out of date (its imports are then fresh) and build it alone, under
# a 4 GiB scope, after waiting while the user's anonymous memory is above 20 GB.
# Usage: CORE_DIR=<core worktree> scripts/packed/run_core_frontier.sh MODULE...
cd "${CORE_DIR:-$(cd "$(dirname "$0")/../.." && pwd)}" || exit 2
for i in $(seq 1 200); do
  m=$(lake build --no-build "$@" 2>&1 | grep -oE '✖ \[[0-9]+/[0-9]+\] Building \S+' | head -1 | awk '{print $4}')
  [ -z "$m" ] && { echo "all fresh"; exit 0; }
  while [ "$(awk '$1 == "anon" {print $2}' /sys/fs/cgroup/user.slice/user-$(id -u).slice/memory.stat)" -gt 20000000000 ]; do
    sleep 30
  done
  r=$(nice -n 5 systemd-run --user --scope -q -p MemoryMax=4G -p MemorySwapMax=0 env LEAN_NUM_THREADS=1 \
      /usr/bin/time -f "%U %S %e %M" lake build "$m" 2>&1)
  echo "$m: $(echo "$r" | grep -E "Built $m|error:" | head -1 | cut -c1-120) | $(echo "$r" | tail -1)"
  echo "$r" | grep -q "Built $m" || { echo "FAILED $m"; exit 1; }
done
