#!/bin/bash
# V2-PACKED-CONS-PERF (untrusted tooling): elaborate ONE module's source with `lean` directly, against a package's
# built oleans (read only: no Lake, nothing is written into the package), in a memory-capped scope, and record
# its costs. Measures the module alone, whatever the state of its dependencies' traces (a `lake build MODULE`
# also rebuilds every stale dependency in the same process).
# Usage: cons_perf_run.sh CAP CORE PKG SRC NAME LOGDIR [lean -D options...]
#   CAP     e.g. 4G
#   CORE    the core worktree (its .lake/build/lib/lean and .lake/packages/*/.lake/build/lib/lean)
#   PKG     the scratch package (its .lake/build/lib/lean)
#   SRC     the source file to elaborate (anywhere; its module name is given by -R = the directory of the root)
#   NAME    the label of this run (LOGDIR/NAME.out, LOGDIR/NAME.cost)
# Waits first while the user's anonymous memory is above 20 GB. Output: `lean`'s messages (the profiler's lines
# with -Dprofiler=true) in NAME.out; wall, user, sys, max RSS, the cgroup charge sampled every 0.2 s, the OOM-kill
# count and the exit code in NAME.cost. The olean goes to LOGDIR/NAME.olean (scratch), or to $OLEAN if set.
# $LP_EXTRA (colon-separated) is appended to the search path: further packages' build dirs, and the build dir of
# modules compiled earlier this way (V2-PACKED-CONS-BRIDGE: one module after another, each against the previous).
cap=$1; core=$2; pkg=$3; src=$4; name=$5; logdir=$6; shift 6
mkdir -p "$logdir"
logdir=$(cd "$logdir" && pwd)
lp="$core/.lake/build/lib/lean"
for d in "$core"/.lake/packages/*/.lake/build/lib/lean; do lp="$lp:$d"; done
lp="$lp:$pkg/.lake/build/lib/lean"
[ -n "${LP_EXTRA:-}" ] && lp="$lp:$LP_EXTRA"
olean=${OLEAN:-$logdir/$name.olean}
mkdir -p "$(dirname "$olean")"
lean=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
root=${ROOT:-$(dirname "$src")}
while true; do
  a=$(grep '^anon ' /sys/fs/cgroup/user.slice/user-1004.slice/memory.stat | awk '{print $2}')
  [ "$a" -lt 20000000000 ] && break
  echo "waiting: user anon $a" >&2; sleep 30
done
LEAN_PATH="$lp" systemd-run --user --scope -q -p MemoryMax="$cap" -p MemorySwapMax=0 --setenv=LEAN_PATH="$lp" \
  bash -c '
  cg=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)
  lean=$1; src=$2; name=$3; logdir=$4; root=$5; olean=$6; shift 6
  pkf="$logdir/$name.peak"
  ( pk=0; while true; do c=$(cat $cg/memory.current 2>/dev/null || echo 0); [ "$c" -gt "$pk" ] && pk=$c;
      echo $pk > "$pkf"; sleep 0.2; done ) &
  smp=$!
  LEAN_NUM_THREADS=1 /usr/bin/time -f "wall_s %e\nuser_s %U\nsys_s %S\nmaxrss_kb %M\nexit %x" \
    nice -n 5 "$lean" -R "$root" -DautoImplicit=false -DrelaxedAutoImplicit=false "$@" \
      -o "$olean" "$src" > "$logdir/$name.out" 2> "$logdir/$name.cost"
  kill $smp 2>/dev/null
  echo "cgroup_sampled_peak_bytes $(cat "$pkf")" >> "$logdir/$name.cost"; rm -f "$pkf"
  echo "oom_kill $(grep oom_kill $cg/memory.events | awk "{print \$2}")" >> "$logdir/$name.cost"
  # /usr/bin/time reports exit 0 for a process killed by a signal: record the kill as a failure
  if grep -q "terminated by signal" "$logdir/$name.cost" || ! grep -q "^oom_kill 0" "$logdir/$name.cost"; then
    echo "killed 1" >> "$logdir/$name.cost"; sed -i "s/^exit 0$/exit 137/" "$logdir/$name.cost"
  fi
' _ "$lean" "$src" "$name" "$logdir" "$root" "$olean" "$@"
echo "$name: $(grep -v "^Command" "$logdir/$name.cost" | tr '\n' ' ')"
