#!/bin/bash
# V2-PACKED-CONS-DATA (untrusted tooling): compile the data study's modules (cons_data_gen.py) with `lean`, one
# process at a time under CAP after the 20 GB anon wait (cons_perf_run.sh), against the integration core and LG00's
# scratch package (kam-lg00, for `LG00.Format`), read only. Oleans: $DD/build/lib/lean; logs: $DD/logs.
# Usage: cons_data_build.sh CAP MODULE...
set -eu
cap=$1; shift
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
DD=${DD:-$root/.lake/v2-packed-data}
INT=${INT:-/home/scott/KAM-dev-worktrees/v2-packed-gen-int}
LG00PKG=${LG00PKG:-/home/scott/KAM-dev-worktrees/v2-packed-gen/.lake/lg00-packed}
mkdir -p "$DD/build/lib/lean" "$DD/logs"
for m in "$@"; do
  rel=$(echo "$m" | tr . /)
  ROOT="$DD/src" OLEAN="$DD/build/lib/lean/$rel.olean" \
    LP_EXTRA="$LG00PKG/.lake/build/lib/lean:$DD/build/lib/lean" \
    bash "$here/cons_perf_run.sh" "$cap" "$INT" "$INT/.lake/lg00p" "$DD/src/$rel.lean" "$m" "$DD/logs" \
    -Dprofiler=true -Dprofiler.threshold=100 > /dev/null
  c="$DD/logs/$m.cost"
  printf "%-24s user %6s sys %5s wall %6s exit %s peak %5.2f GB\n" "$m" "$(grep '^user_s' "$c" | cut -d' ' -f2)" \
    "$(grep '^sys_s' "$c" | cut -d' ' -f2)" "$(grep '^wall_s' "$c" | cut -d' ' -f2)" \
    "$(grep '^exit' "$c" | cut -d' ' -f2)" "$(awk '/peak_bytes/ {print $2 / 1e9}' "$c")"
  grep -q "^exit 0" "$c" || { echo "FAILED $m:"; grep -v "^\s*$" "$DD/logs/$m.out" | head -20; exit 1; }
done
