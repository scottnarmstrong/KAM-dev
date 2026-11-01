#!/bin/bash
# V2-PACKED gate: run ONE Lean probe file alone in a memory-capped scope and record its costs.
# Usage: run_probe.sh CAP FILE LOGDIR      (CAP e.g. 4G)
# Records LOGDIR/<name>.out (Lean output, incl. `type checking took …` from `set_option profiler true`)
# and LOGDIR/<name>.cost: wall, user, sys, max RSS, the cgroup charge sampled every 0.2 s (this
# kernel has no memory.peak), the OOM-kill count and the exit code. Pattern of SO-CSPLIT-GATE and
# LG00-CERT's run_probe.sh; one Lean process at a time, niced, LEAN_NUM_THREADS=1.
cap=$1; f=$2; logdir=$3
name=$(basename "$f" .lean)
mkdir -p "$logdir"
cd "$(dirname "$0")/../.." || exit 2
systemd-run --user --scope -q -p MemoryMax="$cap" -p MemorySwapMax=0 bash -c '
  cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
  pkf="$2/$3.peak"
  ( pk=0; while true; do c=$(cat $cg/memory.current 2>/dev/null || echo 0); [ "$c" -gt "$pk" ] && pk=$c;
      echo $pk > "$pkf"; sleep 0.2; done ) &
  smp=$!
  LEAN_NUM_THREADS=1 /usr/bin/time -f "wall_s %e\nuser_s %U\nsys_s %S\nmaxrss_kb %M\nexit %x" \
    nice -n 5 lake env lean "$1" > "$2/$3.out" 2> "$2/$3.cost"
  kill $smp 2>/dev/null
  echo "cgroup_sampled_peak_bytes $(cat "$pkf")" >> "$2/$3.cost"; rm -f "$pkf"
  echo "oom_kill $(grep oom_kill $cg/memory.events | awk "{print \$2}")" >> "$2/$3.cost"
' _ "$f" "$logdir" "$name"
tc=$(grep -o "type checking took [0-9.]*m\?s" "$logdir/$name.out" | tail -1)
echo "$name: $(tr '\n' ' ' < "$logdir/$name.cost") | $tc"
