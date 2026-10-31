#!/bin/bash
# SO-DATA3: build kernel-pass modules one at a time, each alone under the kernel-probe lock and a 10 GB cap.
#   sodata3_kbuild.sh LOGDIR Module [Module ...]   -> LOGDIR/<Module>.log (lake output + /usr/bin/time -v)
# The dependencies must already be built (through the compile gate); this builds only the pass module.
L=$1; shift; mkdir -p $L
cd "$(dirname "$0")/../.."
for m in "$@"; do
  df -h / | tail -1 > $L/$m.log
  flock /mnt/HC_Volume_106379410/orchestrator-tools/.kernel-probe.lock \
    systemd-run --user --scope -p MemoryMax=10G -p MemorySwapMax=0 \
    /usr/bin/time -v nice -n 5 lake build $m >> $L/$m.log 2>&1
  rc=$?
  echo "rc=$rc" >> $L/$m.log
  echo "$m rc=$rc $(grep -E 'Elapsed' $L/$m.log | awk '{print $NF}') $(grep 'Maximum resident' $L/$m.log | awk '{print $NF}')kB"
done
