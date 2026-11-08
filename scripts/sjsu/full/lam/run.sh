#!/bin/bash
# run.sh: the SJSU-FULL go/no-go gate computations G1, G3, G6 (confirmation) and G5 on one big Linux machine.
# Research measurements (float64 numerics, one throwaway core-only Lean package); nothing of the KAM library is built.
#
# Run as root (sudo -i), one phase at a time:
#   bash run.sh setup     # apt packages, Python venv (numpy, mpmath), elan + Lean v4.35.0, memory scopes
#   bash run.sh fetch     # download the package over Tailscale, verify SHA256SUMS
#   bash run.sh unpack    # unpack repo.tar.zst and g5.tar.zst into ROOTDIR, build the G5 scratch package
#   bash run.sh check     # smoke tests against shipped reference outputs (~2 min); must end "check OK"
#   bash run.sh run       # start the job pool detached (survives logout)
#   bash run.sh status    # progress
#   bash run.sh return    # pack the results and send them by Taildrop
#   bash run.sh stop      # stop the pool (exact PID) and wait for its jobs to end
#
# Environment: LANES (24), BUDGET_GB (230: sum of the memory caps of running jobs), BASE (package URL),
# DEST (Taildrop target, ubuntu-16gb-nbg1-1), ROOTDIR (/root/kam-sjsu-full-gates), XFER (/root/xfer-sjsu-full),
# NO_SEND=1 (return without Taildrop).
set -euo pipefail
PHASES=("$@"); [ ${#PHASES[@]} -ge 1 ] || { sed -n 2,19p "$0"; exit 2; }
[ "$(id -u)" = 0 ] || { echo "STOP: run as root (sudo -i)"; exit 1; }
LANES=${LANES:-24}
BUDGET_GB=${BUDGET_GB:-230}
BASE=${BASE:-http://100.124.142.13:8765}
DEST=${DEST:-ubuntu-16gb-nbg1-1}
ROOTDIR=${ROOTDIR:-/root/kam-sjsu-full-gates}
XFER=${XFER:-/root/xfer-sjsu-full}
TOOLCHAIN=leanprover/lean4:v4.35.0
LEAN_GITHASH=eb6cafb7290e8bd5f2937522d8d804f58f02bafc
TC=/root/.elan/toolchains/leanprover--lean4---v4.35.0
FILES="repo.tar.zst g5.tar.zst jobs.tsv pool.py run.sh verify_return.py WORKSTATION-BRIEF.md"
RUN=$ROOTDIR/run
export XDG_RUNTIME_DIR=/run/user/0
export PATH=$TC/bin:/root/.elan/bin:$PATH
export PY=$ROOTDIR/venv/bin/python3 LEAN=$TC/bin/lean G5=$ROOTDIR/g5 REPO=$ROOTDIR/repo
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
say() { echo "== $(date -u +%H:%M:%S) $*"; }
die() { echo "STOP: $*"; exit 1; }
running() { local p; p=$(cat $RUN/pool.pid 2>/dev/null || echo 0); [ "$p" != 0 ] && kill -0 "$p" 2>/dev/null; }

setup() {
  say setup
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -q && apt-get install -yq python3 python3-venv curl zstd time
  test -x /root/.elan/bin/elan || curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  /root/.elan/bin/elan toolchain install $TOOLCHAIN
  local gh; gh=$($TC/bin/lean --githash)
  [ "$gh" = $LEAN_GITHASH ] || die "Lean v4.35.0 here is commit $gh, expected $LEAN_GITHASH"
  mkdir -p $ROOTDIR
  test -x $ROOTDIR/venv/bin/python3 || python3 -m venv $ROOTDIR/venv
  $ROOTDIR/venv/bin/pip install -q numpy==2.2.6 mpmath==1.3.0
  loginctl enable-linger root
  for _ in $(seq 30); do [ -S /run/user/0/bus ] && break; sleep 1; done
  local m; m=$(systemd-run --user --scope -q -p MemoryMax=1G -p MemorySwapMax=0 \
    bash -c 'cat /sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)/memory.max')
  [ "$m" = 1073741824 ] || die "systemd --user memory scopes do not work (memory.max=$m)"
  say "setup OK: $($PY -c 'import numpy, mpmath; print("numpy", numpy.__version__, "mpmath", mpmath.__version__)'); $(nproc) threads, $(awk '/MemTotal/{print int($2/1048576)}' /proc/meminfo) GB RAM"
}

fetch() {
  say "fetch from $BASE"
  mkdir -p $XFER; cd $XFER
  curl -sSf "$BASE/SHA256SUMS" -o SHA256SUMS
  for f in $FILES; do
    if [ -f "$f" ] && grep " $f\$" SHA256SUMS | sha256sum -c --quiet - 2>/dev/null; then say "  $f (have it)"; continue; fi
    say "  $f"; curl -sSf --retry 5 --retry-delay 10 "$BASE/$f" -o "$f"
  done
  sha256sum -c SHA256SUMS || die "checksum mismatch: delete the bad file in $XFER and rerun fetch"
  say "fetch OK"
}

unpack() {
  say "unpack into $ROOTDIR"
  running && die "the pool is running; stop it first"
  cd $XFER; sha256sum -c --quiet SHA256SUMS || die "checksums"
  rm -rf $ROOTDIR/repo $ROOTDIR/g5; mkdir -p $ROOTDIR $RUN
  zstd -dc repo.tar.zst | tar -C $ROOTDIR -xf -
  zstd -dc g5.tar.zst | tar -C $ROOTDIR -xf -
  cp jobs.tsv pool.py run.sh $RUN/
  (cd $G5 && lake build 2>&1 | tail -3) || die "lake build of the G5 scratch package failed"
  test -x $G5/.lake/build/bin/g5check || die "no g5check executable"
  test -f $G5/.lake/build/lib/lean/G5/Mirror.olean || die "no G5/Mirror.olean"
  say "unpack OK: $(ls $G5/Kernel | wc -l) kernel blocks, $(ls $G5/Native | wc -l) native blocks"
}

check() {
  say "check (smoke tests against reference outputs)"
  local S=$RUN/smoke; rm -rf $S; mkdir -p $S
  cd $REPO/scripts/sjsu/full
  $PY ladder.py points.json -1 $S/g1.json --grid 16,16,8 --N 3 --quiet
  $PY stage2.py points.json 0 $S/g3.json --grid 16,16,8 --NI 2 --M 3 --quiet > /dev/null
  $PY g6_model_gap.py $REPO/data/main_20Myr.bin $S/g6.json --orders 2 --dfinal 4 --years 1e6 > /dev/null
  $PY - "$S" "$REPO/smoke" <<'PYEOF' || die "numerical smoke results differ from the reference"
import json, sys
S, R = sys.argv[1], sys.argv[2]
bad = []
def rel(a, b):
    return abs(a - b) / max(abs(b), 1e-300)
a, b = json.load(open(S + '/g1.json')), json.load(open(R + '/g1.json'))
for ra, rb in zip(a['ladder'], b['ladder']):
    for o in ('F1', 'LU'):
        if rel(ra[o]['remainder'], rb[o]['remainder']) > 1e-7: bad.append(('g1', ra['order'], o))
a, b = json.load(open(S + '/g3.json')), json.load(open(R + '/g3.json'))
for ra, rb in zip(a['stage2_ladder'], b['stage2_ladder']):
    if rel(ra['LS']['remainder'], rb['LS']['remainder']) > 1e-7: bad.append(('g3', ra['order']))
a, b = json.load(open(S + '/g6.json')), json.load(open(R + '/g6.json'))
for x, y in zip(a['models']['2']['g'], b['models']['2']['g']):
    if rel(x, y) > 1e-8: bad.append(('g6', x, y))
print('numerical smoke:', 'OK' if not bad else bad)
sys.exit(1 if bad else 0)
PYEOF
  cd $G5/tiny
  for m in Kernel Native; do
    LEAN_PATH=$G5/.lake/build/lib/lean $LEAN $m/B000.lean > $S/g5_$m.out 2>&1 || die "G5 tiny $m block failed: $(head -5 $S/g5_$m.out)"
    grep -q "error:" $S/g5_$m.out && die "G5 tiny $m block reported an error"
  done
  $G5/.lake/build/bin/g5check $G5/tiny/blocks.txt > $S/g5_exe.out || die "G5 tiny exe failed"
  grep -q "TOTAL ok=true" $S/g5_exe.out || die "G5 tiny exe did not report ok"
  say "check OK"
}

run() {
  running && die "the pool is already running (pid $(cat $RUN/pool.pid))"
  cd $RUN
  LANES=$LANES BUDGET_GB=$BUDGET_GB setsid nohup $PY $RUN/pool.py $RUN/jobs.tsv $RUN > $RUN/pool.out 2>&1 < /dev/null &
  echo $! > $RUN/pool.pid
  say "pool started (pid $(cat $RUN/pool.pid)); follow with: bash run.sh status"
}

status() {
  local n p f
  n=$(grep -vc '^#' $RUN/jobs.tsv)
  p=$(grep -l '"verdict": "pass"' $RUN/res/*.json 2>/dev/null | wc -l)
  f=$(grep -l '"verdict": "fail"' $RUN/res/*.json 2>/dev/null | wc -l)
  if running; then say "running (pid $(cat $RUN/pool.pid)): $p pass, $f fail of $n"; else say "not running: $p pass, $f fail of $n"; fi
  tail -4 $RUN/pool.out 2>/dev/null || true
  [ "$f" = 0 ] || { echo "failed jobs:"; grep -l '"verdict": "fail"' $RUN/res/*.json | xargs -n1 basename | sed 's/.json$//'; }
  [ "$p" = "$n" ] && ! running && say "done pass=$p not_passed=0"
  return 0
}

ret() {
  running && die "the pool is still running; wait for it (or stop it) first"
  local stamp arc
  stamp=$(date -u +%Y%m%dT%H%M%SZ); arc=/root/sjsu-full-gates-results-$stamp.tar.zst
  (cd $RUN && { grep -vc '^#' jobs.tsv | sed 's/^/jobs /'; echo "pass $(grep -l '"verdict": "pass"' res/*.json | wc -l)";
     echo "fail $(grep -l '"verdict": "fail"' res/*.json 2>/dev/null | wc -l)"; echo "host $(hostname) $(nproc) threads";
     echo "packed $(date -u +%FT%TZ)"; } > RETURN-MANIFEST.txt
   tar -cf - RETURN-MANIFEST.txt jobs.tsv pool.out res out log smoke | zstd -q -19 -T0 -o $arc)
  sha256sum $arc | tee $arc.sha256
  ls -la $arc
  if [ "${NO_SEND:-0}" = 1 ]; then say "NO_SEND=1: not sending"; return 0; fi
  tailscale file cp $arc $arc.sha256 "$DEST:" && say "return OK: sent $(basename $arc) to $DEST"
}

stop() {
  running || { say "not running"; return 0; }
  local p; p=$(cat $RUN/pool.pid)
  kill -TERM "$p"
  while kill -0 "$p" 2>/dev/null; do sleep 2; done
  say "stopped"
}

for ph in "${PHASES[@]}"; do
  case $ph in
    setup) setup ;; fetch) fetch ;; unpack) unpack ;; check) check ;; run) run ;;
    status) status ;; return) ret ;; stop) stop ;;
    *) die "unknown phase $ph" ;;
  esac
done
