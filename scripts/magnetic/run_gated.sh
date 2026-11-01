#!/bin/bash
# Usage: run_gated.sh <args to mag_producer.py>; waits for MemAvailable >= 12 GB, then runs capped and niced.
while [ "$(awk '/MemAvailable/{print $2}' /proc/meminfo)" -lt 12000000 ]; do sleep 30; done
cd "$(dirname "$0")"
exec systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10 python3 -B mag_producer.py "$@"
