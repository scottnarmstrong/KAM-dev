#!/bin/bash
# V2-PACKED-CONS-BRIDGE (untrusted tooling): compile the bridge modules of one tree with `lean`, one process at a time
# under CAP (default 4G), after the 20 GB anon wait (cons_perf_run.sh), against kamx-pk-gen's built packages, read
# only: the integration core and package (kam-lg00p) and LG00's scratch package (kam-lg00). Nothing is written into
# them; the oleans go to $BR/build/lib/lean, the logs to $BR/logs/<tree>.
# Usage: cons_bridge_build.sh TREE [CAP] [MODULE...]   (default: LG00B.Congr LG00B.<T>.Fields LG00B.<T>.Main)
set -eu
tree=$1; cap=${2:-4G}; shift $(( $# >= 2 ? 2 : 1 ))
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
BR=${BR:-$root/.lake/v2-packed-bridge}
INT=${INT:-/home/scott/KAM-dev-worktrees/v2-packed-gen-int}
LG00PKG=${LG00PKG:-/home/scott/KAM-dev-worktrees/v2-packed-gen/.lake/lg00-packed}
mods=${*:-LG00B.Congr LG00B.$tree.Fields LG00B.$tree.Main}
mkdir -p "$BR/build/lib/lean" "$BR/logs/$tree"
for m in $mods; do
  rel=$(echo "$m" | tr . /)
  ROOT="$BR/src" OLEAN="$BR/build/lib/lean/$rel.olean" LP_EXTRA="$LG00PKG/.lake/build/lib/lean:$BR/build/lib/lean" \
    bash "$here/cons_perf_run.sh" "$cap" "$INT" "$INT/.lake/lg00p" "$BR/src/$rel.lean" "$m" "$BR/logs/$tree" \
    -Dprofiler=true -Dprofiler.threshold=100 | grep -o -E "^[^ ]+:|wall_s [0-9.]+|user_s [0-9.]+|sys_s [0-9.]+|exit [0-9]+|peak_bytes [0-9]+" | tr '\n' ' '
  echo
  if ! grep -q "^exit 0" "$BR/logs/$tree/$m.cost"; then
    echo "FAILED $m:"; grep -v "^\s*$" "$BR/logs/$tree/$m.out" | head -30; exit 1
  fi
done
