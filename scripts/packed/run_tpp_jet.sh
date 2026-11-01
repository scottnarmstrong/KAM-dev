#!/bin/bash
# V2-PACKED-GEN: T''s jet route while kamx-packed builds T''s chains (untrusted driver).
# 1. wait for the chain-free run (run_packed.py into LOGDIR) and kamx-packed's full mirror (its log's `real` line);
# 2. emit the jet route on T'' (gen_packed.py --stages jet --ham-ported, assembly modules unsuffixed: `…PK.MainJ`);
# 3. pass after pass until `LG00P.TPP.PK.MainJ` passes or the deadline: mirror kamx-packed's T'' chain modules
#    (sources; artifacts once built: gen_pkg.py --keep-config), then build every module whose imports are ready
#    (run_packed.py --jobs 2 --anon-gb 18 --never-build LG00P.TPP.Jet.: their chains are never built here).
# Usage: run_tpp_jet.sh LOGDIR      (from anywhere; RUN_DEADLINE in the environment: no Lean start after it)
set -u
log=$1
G=/home/scott/KAM-dev-worktrees/v2-packed-gen
I=/home/scott/KAM-dev-worktrees/v2-packed-gen-int
INT=$I/.lake/lg00p
THEIRS=${PROD_PKG:-/home/scott/KAM-dev-worktrees/v2-packed/.lake/v2-packed-prod/pkg}
T=${PROD_TPP:-/home/scott/KAM-dev-worktrees/v2-packed/.lake/v2-packed-prod/tpp}
: "${RUN_DEADLINE:=1793593800}"; export RUN_DEADLINE
py="bash $G/scripts/packed/py_capped.sh"
while pgrep -u "$(id -u)" -f "run_packed.py $log " >/dev/null; do sleep 20; done
until grep -q '^real' "$T/full_mirror.log" 2>/dev/null && [ -s "$T/full_mirror.pkl" ]; do sleep 30; done
echo "full mirror complete; $(date -u +%H:%M:%S)"
if [ ! -s "$INT/packed_LG00P_TPP.json" ]; then
  $py "$G/scripts/packed/gen_packed.py" --tree TPP --prefix LG00P --pkg "$INT" --stages jet --ham-ported \
    --asm-suffix '' --jet-low "$T/low_mirror.pkl" --jet-full "$T/full_mirror.pkl" > "$log.gen.log" 2>&1 ||
    { echo "STOP: emission failed"; tail -20 "$log.gen.log"; exit 1; }
fi
echo "emitted: $(grep -c . "$INT/modules_TPP.json" 2>/dev/null) lines of module list; $(date -u +%H:%M:%S)"
n=0
while [ "$(date +%s)" -lt "$RUN_DEADLINE" ]; do
  n=$((n + 1))
  mods=$(cd "$THEIRS" && find LG00P/TPP/Jet -name '*.lean' 2>/dev/null | sed 's|\.lean$||; s|/|.|g' | tr '\n' ' ')
  [ -n "$mods" ] && $py "$G/scripts/packed/gen_pkg.py" --pkg "$INT" --keep-config --lg00 "$THEIRS" $mods \
    > "$log.mirror.log" 2>&1
  echo "=== pass $n $(date -u +%H:%M:%S): $(grep -h 'sources copied' "$log.mirror.log" 2>/dev/null)"
  python3 -I "$I/scripts/packed/run_packed.py" "$log" 4G --jobs 2 --anon-gb 18 --pkg "$INT" \
    --never-build LG00P.TPP.Jet. LG00P.TPP.PK.MainJ > "$log.pass.out" 2>&1
  grep -E 'stale \(to build\)|^DONE|^STOP|EXTRA|BLOCKED disk' "$log.pass.out"
  grep -cE '^(BLOCKED|FOREIGN|SKIP)' "$log.pass.out" | sed 's/^/  waiting on kamx-packed: /'
  awk -F'\t' 'NF >= 7 && $7 != "0"' "$log.pass.out"
  if awk -F'\t' '$1 == "LG00P.TPP.PK.MainJ" && $7 == "0"' "$log/ledger.tsv" | grep -q .; then
    echo "T'' PROVED: LG00P.TPP.PK.MainJ passed; $(date -u +%H:%M:%S)"
    exit 0
  fi
  awk -F'\t' '$8 == "built"' "$log.pass.out" | grep -q . || sleep 120    # nothing built: wait for kamx-packed
done
echo "STOP: deadline"
exit 1
