#!/bin/bash
# Reproduce all outputs under the mandatory resource rules (transient systemd unit, nice 10, 6G, no swap).
set -e
B=/root/code/KAM-inp-b3prod/docs/tracks/B/b3
run() { # name args...
  local name=$1; shift
  local U=b3-prod-$(date +%H%M%S)-$name
  systemd-run --user --wait --collect --unit=$U -p MemoryMax=6G -p MemorySwapMax=0 --nice=10 \
    --working-directory=$B/producer /usr/bin/time -v python3 -B -I "$@" >/dev/null 2>&1 || true
  sleep 1
  journalctl --user -u $U --no-pager -o cat > $B/out/$name.log
}
run E1-run run_e1.py $B/out 5 2 2
run E1-twostep-run run_e1.py $B/out/twostep 5 3
run verify-run verify.py $B/out/hh-cert.json
