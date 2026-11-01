#!/bin/bash
# V2-PACKED-PROD: build ONE module of a Lake package alone in a memory-capped scope and record its costs.
# Usage: run_module.sh CAP PKGDIR MODULE LOGDIR      (CAP e.g. 4G)
# The module's imports must be built already, so `lake build MODULE` runs exactly one Lean process.
# Records LOGDIR/<MODULE>.out (Lake's output) and LOGDIR/<MODULE>.cost: wall, user, sys, max RSS, the cgroup charge
# sampled every 0.2 s, the OOM-kill count and the exit code (the pattern of run_probe.sh).
cap=$1; pkg=$2; mod=$3; logdir=$4
mkdir -p "$logdir"
logdir=$(cd "$logdir" && pwd)
cd "$pkg" || exit 2
systemd-run --user --scope -q -p MemoryMax="$cap" -p MemorySwapMax=0 bash -c '
  cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
  pkf="$2/$1.peak"
  ( pk=0; while true; do c=$(cat $cg/memory.current 2>/dev/null || echo 0); [ "$c" -gt "$pk" ] && pk=$c;
      echo $pk > "$pkf"; sleep 0.2; done ) &
  smp=$!
  LEAN_NUM_THREADS=1 /usr/bin/time -f "wall_s %e\nuser_s %U\nsys_s %S\nmaxrss_kb %M\nexit %x" \
    nice -n 5 lake build "$1" > "$2/$1.out" 2> "$2/$1.cost"
  kill $smp 2>/dev/null
  echo "cgroup_sampled_peak_bytes $(cat "$pkf")" >> "$2/$1.cost"; rm -f "$pkf"
  echo "oom_kill $(grep oom_kill $cg/memory.events | awk "{print \$2}")" >> "$2/$1.cost"
' _ "$mod" "$logdir"
echo "$mod: $(grep -v "^Command" "$logdir/$mod.cost" | tr '\n' ' ')"
