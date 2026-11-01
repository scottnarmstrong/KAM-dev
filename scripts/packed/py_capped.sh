#!/bin/bash
# Run a heavy Python tool under the orchestrator's rule (2026-11-01): a hard 8 GiB cap without swap, niced, and
# only while the user's anonymous memory is at most 20 GB (the LG00 kernel run shares the 32 GB cap).
# Usage: py_capped.sh SCRIPT.py ARGS...      (runs `python3 -I SCRIPT.py ARGS...`)
st=/sys/fs/cgroup/user.slice/user-$(id -u).slice/memory.stat
while [ "$(awk '$1 == "anon" {print $2}' "$st")" -gt 20000000000 ]; do
  sleep 30
done
exec systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10 python3 -I -B "$@"
