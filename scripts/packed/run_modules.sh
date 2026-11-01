#!/bin/bash
# V2-PACKED-PROD: build the modules of LIST (one name per line, in dependency order) one at a time through
# `run_module.sh` under the memory cap CAP; a module whose LOGDIR/<name>.cost records `exit 0` is skipped (resume).
# Stops at the first failure (the later modules may import it). Waits while the user's anonymous memory is above
# 20 GB before each module (the LG00 kernel run shares the machine).
# Usage: run_modules.sh CAP PKGDIR LIST LOGDIR
cap=$1; pkg=$2; list=$3; logdir=$4
here=$(cd "$(dirname "$0")" && pwd)
st=/sys/fs/cgroup/user.slice/user-$(id -u).slice/memory.stat
while read -r m; do
  [ -z "$m" ] && continue
  if [ -f "$logdir/$m.cost" ] && grep -q "^exit 0$" "$logdir/$m.cost"; then
    continue
  fi
  while [ "$(awk '$1 == "anon" {print $2}' "$st")" -gt 20000000000 ]; do sleep 30; done
  bash "$here/run_module.sh" "$cap" "$pkg" "$m" "$logdir"
  grep -q "^exit 0$" "$logdir/$m.cost" || { echo "STOP: $m failed"; exit 1; }
done < "$list"
