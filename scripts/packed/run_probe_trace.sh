#!/bin/bash
# V2-PACKED-JET-MEM: run ONE Lean probe alone in a memory-capped scope (as run_probe.sh) and record, besides
# LOGDIR/<name>.{out,cost}, the cgroup charge every 0.1 s (LOGDIR/<name>.trace: seconds since start, bytes), so the
# data-elaboration plateau and the kernel's growth can be told apart.
# Usage: run_probe_trace.sh CAP FILE LOGDIR
cap=$1; f=$2; logdir=$3
name=$(basename "$f" .lean)
mkdir -p "$logdir"
cd "$(dirname "$0")/../.." || exit 2
systemd-run --user --scope -q -p MemoryMax="$cap" -p MemorySwapMax=0 bash -c '
  cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
  tr="$2/$3.trace"; : > "$tr"
  t0=$(date +%s.%N)
  ( while true; do echo "$(echo "$(date +%s.%N) - $t0" | bc) $(cat $cg/memory.current 2>/dev/null || echo 0)" >> "$tr";
      sleep 0.1; done ) &
  smp=$!
  LEAN_NUM_THREADS=1 /usr/bin/time -f "wall_s %e\nuser_s %U\nsys_s %S\nmaxrss_kb %M\nexit %x" \
    nice -n 5 lake env lean "$1" > "$2/$3.out" 2> "$2/$3.cost"
  kill $smp 2>/dev/null
  echo "cgroup_sampled_peak_bytes $(sort -k2 -n "$tr" | tail -1 | cut -d" " -f2)" >> "$2/$3.cost"
  echo "oom_kill $(grep oom_kill $cg/memory.events | awk "{print \$2}")" >> "$2/$3.cost"
' _ "$f" "$logdir" "$name"
pkill -f "tr=\"\$2/\$3.trace\"" 2>/dev/null
tc=$(grep -o "type checking took [0-9.]*m\?s" "$logdir/$name.out" | tail -1)
echo "$name: $(grep -E "user_s|sys_s|exit|peak|oom" "$logdir/$name.cost" | tr '\n' ' ') | $tc"
