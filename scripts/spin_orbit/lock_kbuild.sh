#!/bin/bash
# LOCK-DATA: kernel-pass modules, one at a time, each alone on the first free probe lane (lane 1, else lane 2,
# else FIFO wait on lane 1), in a scope with MemoryMax=8G (the lock's per-theorem rule) and MemorySwapMax=0.
#   lock_kbuild.sh LOGDIR Module [Module ...]   -> LOGDIR/<Module>.log, and one summary line per module on stdout
#   (rc, user+sys CPU s, wall, cgroup memory.peak, oom_kill).  Dependencies must already be built (compile gate).
L=$1; shift; mkdir -p "$L"
cd "$(dirname "$0")/../.." || exit 2
T=/mnt/HC_Volume_106379410/orchestrator-tools
run() {
  until [ "$(awk "/MemAvailable/{print \$2}" /proc/meminfo)" -ge 8388608 ]; do sleep 30; done
  m=$1; log=$L/$m.log
  systemd-run --user --scope -q -p MemoryMax=${LOCK_MEM:-6G} -p MemorySwapMax=0 bash -c '
    cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
    /usr/bin/time -v nice -n 5 lake build '"$m"' ; rc=$?
    echo "MEMPEAK $(cat $cg/memory.peak 2>/dev/null || echo UNMEASURED)"
    echo "OOMKILL $(grep oom_kill $cg/memory.events 2>/dev/null | awk "{print \$2}")"
    echo "rc=$rc"' >> "$log" 2>&1
}
for m in "$@"; do
  log=$L/$m.log; { date -u; git rev-parse HEAD; df -h / | tail -1; } > "$log"
  exec 8>$T/.kernel-probe.lock 9>$T/.kernel-probe-lane2.lock
  # LANE=1|2 pins one lane (strictly serial); default: first free lane
  case "$LANE" in
    1) flock 8; lane=1 ;;
    2) flock 9; lane=2 ;;
    *) if flock -n 8; then lane=1; elif flock -n 9; then lane=2; else flock 8; lane=1; fi ;;
  esac
  echo "lane $lane" >> "$log"
  run "$m"
  exec 8>&- 9>&-
  u=$(grep 'User time' "$log" | awk '{print $NF}'); s=$(grep 'System time' "$log" | awk '{print $NF}')
  rcl=$(grep '^rc=' "$log" | tail -1); [ -n "$rcl" ] || rcl="rc=OOM-or-killed"
  echo "$m $rcl cpu=$( [ -n "$u" ] && echo "$u + $s" | bc) wall=$(grep Elapsed "$log" | awk '{print $NF}') \
peak=$(grep MEMPEAK "$log" | awk '{print $2}') oom=$(grep OOMKILL "$log" | awk '{print $2}') lane=$lane"
  [ "$rcl" = "rc=0" ] || { echo "STOP: $m failed; dependents not dispatched"; break; }
done
