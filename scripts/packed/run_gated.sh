#!/bin/bash
# V2-PACKED-PROD-TPP: build ONE module through `run_module.sh`, for a parallel runner (`run_par.sh`). Starts are
# serialized by a lock on LOGDIR/.start.lock: a start waits while the user's anonymous memory is at or above
# ANON_MAX (default 18 GB), refuses after DEADLINE (epoch seconds, if set; exit 3), and holds the lock START_GAP s
# (default 3) after the start, so that starts are spaced. Skips a module whose receipt says exit 0.
# Usage: run_gated.sh CAP PKGDIR MODULE LOGDIR
cap=$1; pkg=$2; m=$3; logdir=$4
here=$(cd "$(dirname "$0")" && pwd)
st=/sys/fs/cgroup/user.slice/user-$(id -u).slice/memory.stat
mkdir -p "$logdir"
if [ -f "$logdir/$m.cost" ] && grep -q "^exit 0$" "$logdir/$m.cost"; then exit 0; fi
exec 9>"$logdir/.start.lock"
flock 9
while [ "$(awk '$1 == "anon" {print $2}' "$st")" -ge "${ANON_MAX:-18000000000}" ]; do sleep 20; done
if [ -n "$DEADLINE" ] && [ "$(date +%s)" -ge "$DEADLINE" ]; then echo "STOP: deadline before $m"; exit 3; fi
( sleep "${START_GAP:-3}" ) &
exec 9>&-
bash "$here/run_module.sh" "$cap" "$pkg" "$m" "$logdir"
grep -q "^exit 0$" "$logdir/$m.cost"
