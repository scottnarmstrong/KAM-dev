#!/bin/bash
# LOCK-REMOTE: kernel chains on a rented machine (Hetzner CCX63, owner D70; CCX53 also works with LANES=11), as ONE runbook (untrusted tooling;
# .drafts/briefs/offload-main/LOCK-REMOTE.md, PKG-LOCK-DATA-RUN.md UPDATE/UPDATE 2/UPDATE 3).
#
#   lock_remote_runbook.sh [--dry-run] [--seq|--par] [--targets lock[,mag]] PHASE [PHASE ...]
#
# Targets: scripts/spin_orbit/remote_targets/<name>.env (lock.env; mag.env.example is the hook for the magnetic
# pilot). One provisioning and one packages transfer for all targets; one remote worktree, core build, return
# directory and log directory per target.
# Modes (phase `run`): --par (default) one shared lane pool, the first target has priority; --seq the targets one
# after another, each with all lanes (remote_pool.py).
#
# Phases (each idempotent; `all` = preflight provision transfer check run):
#   preflight   local only: frozen commits, clean tracked trees, untracked sources, free space, dry schedules
#   hcloud-create / hcloud-delete   (API-token mode only; HCLOUD_TOKEN from the environment, never stored)
#   provision   remote: apt rsync/git/python3/time, elan + the lean-toolchain, systemd --user scope check
#   transfer    per target: git bundle of its frozen commit, rsync -L of its untracked sources, its core .lake/build
#               (without its chain outputs); once: .lake/packages (shared when the manifests agree)
#   check       remote, per target: `lake build --no-build KAM` up to date BEFORE anything is built
#   run         remote: remote_pool.py over the targets (LANES x LOCK_MEM), continue past failures, detached
#   status      remote: the combined STATUS file and per-target failures
#   return      per target: outputs + logs to $VOL/remote-<date>/<target>/; overlay links; local --no-build checks
#   audit       local, per target: stratified leanchecker replay, one module at a time under MemoryMax=10G
#
# --dry-run prints every command and executes nothing remote (no ssh/rsync/hcloud); local read-only preflight
# computations still run so the printed counts are real.
#
# Parameters (environment): HOST (required unless --dry-run), KEY (default /root/.ssh/kam_build_ed25519),
# LANES (17: a CCX63, 48 vCPU / 192 GB; 17 x 10G leaves ~22 GB for the page cache and lake), LOCK_MEM (10G),
# LOCK_GATE kB (11534336), HTYPE (ccx63), STAMP (UTC date), AUDIT_PCT (5), AUDIT_SEED (65),
# FROZEN_<name> (override a target's commit), TARGET_DIR (target files; default remote_targets/).
set -u
DRY=0; MODE=--par; TARGETS=lock
while [ $# -gt 0 ]; do
  case "$1" in
    --dry-run) DRY=1; shift ;;
    --seq|--par) MODE=$1; shift ;;
    --targets) TARGETS=$2; shift 2 ;;
    *) break ;;
  esac
done
[ $# -ge 1 ] || { sed -n 2,32p "$0"; exit 2; }

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
VOL=/mnt/HC_Volume_106379410/kam-data/so-lock
HOST=${HOST:-}
if [ -z "$HOST" ]; then
  if [ $DRY = 1 ]; then HOST=REMOTE_HOST
  else for ph in "$@"; do case "$ph" in preflight|audit|hcloud-create) ;; *) echo "HOST unset"; exit 2 ;; esac; done; fi
fi
KEY=${KEY:-/root/.ssh/kam_build_ed25519}
LANES=${LANES:-17}
LOCK_MEM=${LOCK_MEM:-10G}
LOCK_GATE=${LOCK_GATE:-11534336}
STAMP=${STAMP:-$(date -u +%Y%m%d)}
WORK=${WORK:-$VOL/remote-work}          # local state: bundles, file lists, jobs file, dry runs
AUDIT_PCT=${AUDIT_PCT:-5}
AUDIT_SEED=${AUDIT_SEED:-65}
TOOLCHAIN=$(cat "$ROOT/lean-toolchain")
SSHO="-i $KEY -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ServerAliveInterval=30"
RPKG=/root/kam-packages                 # shared packages on the remote
RCHAIN=/root/chain                      # remote jobs file, STATUS, logs/<target>
mkdir -p "$WORK"

say() { echo "== $(date -u +%H:%M:%S) $*"; }
L() { echo "+ $*"; [ $DRY = 1 ] || eval "$@"; }                                     # local, printed
R() { echo "+ [remote $HOST] $*"; [ $DRY = 1 ] || ssh $SSHO root@"$HOST" "$*"; }   # remote, printed
die() { echo "STOP: $*"; exit 1; }

# load target NAME into T_* (and FROZEN)
load() {
  local f="${TARGET_DIR:-$HERE/remote_targets}/$1.env"
  [ -f "$f" ] || die "no target file $f (copy $1.env.example and fill it in)"
  unset T_FROZEN T_FROZEN_FILE
  # shellcheck disable=SC1090
  source "$f"
  grep -q TODO "$f" && die "target $1: $f still has TODO values"
  local ov="FROZEN_$1"
  FROZEN=${!ov:-${T_FROZEN:-$(grep -oE '[0-9a-f]{40}' "${T_FROZEN_FILE:-/dev/null}" 2>/dev/null | head -1)}}
  [ -n "$FROZEN" ] || die "target $1: no frozen commit"
  REMENV="source \$HOME/.elan/env; cd $T_RDIR"
}
each() { local t; for t in ${TARGETS//,/ }; do load "$t"; "$@"; done; }

preflight_one() {
  say "preflight $T_NAME (local, read-only)"
  git -C "$T_SRC" cat-file -e "$FROZEN^{commit}" 2>/dev/null || die "$T_NAME: frozen commit $FROZEN unknown"
  echo "frozen commit $FROZEN ($(git -C "$T_SRC" log -1 --format=%s "$FROZEN" | cut -c1-80))"
  [ "$(git -C "$T_SRC" rev-parse HEAD)" = "$FROZEN" ] || echo "note: $T_NAME HEAD $(git -C "$T_SRC" rev-parse --short HEAD) != frozen"
  if [ -n "$(git -C "$T_SRC" status --porcelain --untracked-files=no)" ]; then
    [ $DRY = 1 ] && echo "WARN (dry-run): tracked changes in $T_SRC; a real run stops here" || die "tracked changes in $T_SRC"
  fi
  (cd "$T_SRC" && git ls-files --others --exclude-standard $T_SRCDIRS) > "$WORK/$T_NAME.untracked"
  echo "untracked sources: $(wc -l < "$WORK/$T_NAME.untracked"); dangling links: $(cd "$T_SRC" && while read -r f; do [ -e "$f" ] || echo "$f"; done < "$WORK/$T_NAME.untracked" | wc -l)"
  echo "source volume (dereferenced): $(cd "$T_SRC" && du -shL -c $(cat "$WORK/$T_NAME.untracked") 2>/dev/null | tail -1 | cut -f1)"
  echo "packages: $(readlink -f "$T_SRC/.lake/packages") manifest $(md5sum < "$T_SRC/lake-manifest.json" | cut -c1-12)"
}

preflight() {
  each preflight_one
  echo "free on volume: $(df -h $VOL | tail -1 | awk '{print $4}') (return needs about 15-20 GB per chain)"
  jobs_json local > "$WORK/jobs.local.json"
  LOCK_DRY=1 python3 "$HERE/remote_pool.py" "$WORK/jobs.local.json" "$LANES" "$MODE" || die "dry schedule failed"
}

# the jobs file for remote_pool.py (local paths for the dry schedule, remote paths for the run)
jobs_json() {
  local where=$1 first=1 t
  echo "["
  for t in ${TARGETS//,/ }; do
    load "$t"
    local root=$T_RDIR; [ "$where" = local ] && root=$T_SRC
    [ $first = 1 ] || echo ","
    first=0
    printf '  {"name": "%s", "root": "%s", "pfx": "%s", "targets": [%s], "logdir": "%s/logs/%s"}' \
      "$T_NAME" "$root" "$T_PFX" "$(for x in $T_TARGETS; do printf '"%s",' "$x"; done | sed 's/,$//')" \
      "$([ "$where" = local ] && echo "$WORK/dry" || echo $RCHAIN)" "$T_NAME"
  done
  echo; echo "]"
}

hcloud_create() {
  say "hcloud-create (API-token mode; token read from HCLOUD_TOKEN, never written)"
  [ $DRY = 1 ] || [ -n "${HCLOUD_TOKEN:-}" ] || die "HCLOUD_TOKEN unset"
  L "hcloud ssh-key create --name kam-lock-build --public-key-from-file $KEY.pub || true"
  L "hcloud server create --name kam-lock-build --type ${HTYPE:-ccx63} --image ubuntu-24.04 --location nbg1 --ssh-key kam-lock-build"
  L "hcloud server ip kam-lock-build   # -> export HOST=<ip>"
}
hcloud_delete() { say "hcloud-delete (only after return + check)"; L "hcloud server delete kam-lock-build"; }

provision() {
  say "provision"
  R "uname -a; nproc; free -g; df -h /"
  R "export DEBIAN_FRONTEND=noninteractive; apt-get update -q && apt-get install -yq rsync git python3 time curl"
  R "test -x \$HOME/.elan/bin/elan || curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none"
  R "source \$HOME/.elan/env; elan toolchain install $TOOLCHAIN && lean --version"
  # the per-module caps need a user manager with the memory controller delegated
  R "loginctl enable-linger root; export XDG_RUNTIME_DIR=/run/user/0; systemctl --user is-system-running || true; cat /sys/fs/cgroup/user.slice/user-0.slice/user@0.service/cgroup.controllers"
  R "export XDG_RUNTIME_DIR=/run/user/0; systemd-run --user --scope -q -p MemoryMax=1G -p MemorySwapMax=0 bash -c 'cat /sys/fs/cgroup\$(cut -d: -f3 /proc/self/cgroup)/memory.max'"
}

PKG_SENT=""
transfer_one() {
  say "transfer $T_NAME"
  [ -s "$WORK/$T_NAME.untracked" ] || (cd "$T_SRC" && git ls-files --others --exclude-standard $T_SRCDIRS) > "$WORK/$T_NAME.untracked"
  L "git -C $T_SRC bundle create $WORK/$T_NAME.bundle $FROZEN $T_BRANCH"
  L "git -C $T_SRC bundle verify $WORK/$T_NAME.bundle"
  R "mkdir -p $T_RDIR /root/xfer $RPKG"
  L "rsync -a -e 'ssh $SSHO' $WORK/$T_NAME.bundle root@$HOST:/root/xfer/"
  R "test -d $T_RDIR/.git || git clone -q /root/xfer/$T_NAME.bundle $T_RDIR; cd $T_RDIR && git fetch -q /root/xfer/$T_NAME.bundle $T_BRANCH && git checkout -q -B $T_BRANCH $FROZEN && git rev-parse HEAD"
  L "rsync -aL --files-from=$WORK/$T_NAME.untracked -e 'ssh $SSHO' $T_SRC/ root@$HOST:$T_RDIR/"
  # packages: once (identical manifests share $RPKG; a different manifest gets its own copy)
  local pk; pk=$(md5sum < "$T_SRC/lake-manifest.json" | cut -c1-12)
  if [ -z "$PKG_SENT" ] || [ "$PKG_SENT" = "$pk" ]; then
    [ -n "$PKG_SENT" ] || L "rsync -a --info=stats1 -e 'ssh $SSHO' $(readlink -f "$T_SRC/.lake/packages")/ root@$HOST:$RPKG/"
    PKG_SENT=$pk
    R "mkdir -p $T_RDIR/.lake && ln -sfn $RPKG $T_RDIR/.lake/packages"
  else
    L "rsync -a --info=stats1 -e 'ssh $SSHO' $(readlink -f "$T_SRC/.lake/packages")/ root@$HOST:$T_RDIR/.lake/packages/"
  fi
  L "rsync -a --info=stats1 --exclude=/lib/lean/$T_OUTREL --exclude=/ir/$T_OUTREL -e 'ssh $SSHO' $(readlink -f "$T_SRC/.lake/build")/ root@$HOST:$T_RDIR/.lake/build/"
  [ -d "$T_SRC/.lake/config" ] && L "rsync -a -e 'ssh $SSHO' $T_SRC/.lake/config/ root@$HOST:$T_RDIR/.lake/config/"
  R "cd $T_RDIR && find $T_SRCDIRS -name '*.lean' | wc -l && git status --porcelain --untracked-files=no | wc -l"
}
transfer() { each transfer_one; }

check_one() {
  say "check $T_NAME: nothing may need building before the run"
  R "$REMENV && lake build --no-build KAM; echo NOBUILD_KAM_rc=\$?"
  if [ $DRY = 0 ]; then
    ssh $SSHO root@"$HOST" "$REMENV && lake build --no-build KAM" >/dev/null 2>&1 \
      || die "$T_NAME: remote core is not up to date (trace inputs differ); do not build"
  fi
}
check() { each check_one; }

run_chain() {
  say "run $MODE: targets $TARGETS, $LANES lanes x $LOCK_MEM, gate $LOCK_GATE kB"
  jobs_json remote > "$WORK/jobs.remote.json"
  cat "$WORK/jobs.remote.json"
  R "mkdir -p $RCHAIN"
  L "rsync -a -e 'ssh $SSHO' $WORK/jobs.remote.json root@$HOST:$RCHAIN/jobs.json"
  load "${TARGETS%%,*}"       # the driver is run from the first target's tree (remote_pool.py, lock_mlane.py)
  R "$REMENV && export XDG_RUNTIME_DIR=/run/user/0 && LOCK_DRY=1 python3 scripts/spin_orbit/remote_pool.py $RCHAIN/jobs.json $LANES $MODE"
  R "$REMENV && export XDG_RUNTIME_DIR=/run/user/0 && LOCK_MEM=$LOCK_MEM LOCK_GATE=$LOCK_GATE nohup setsid python3 scripts/spin_orbit/remote_pool.py $RCHAIN/jobs.json $LANES $MODE > $RCHAIN/pool.out 2>&1 < /dev/null & echo \$! > $RCHAIN/pool.pid; cat $RCHAIN/pool.pid"
}

status() {
  R "kill -0 \$(cat $RCHAIN/pool.pid) 2>/dev/null && echo RUNNING || echo FINISHED; cat $RCHAIN/STATUS; for d in $RCHAIN/logs/*/; do echo \"\$d: \$(grep -cE ' rc=(1|OOM|SKIP)' \$d/summary.out) failed/skipped\"; grep -E ' rc=(1|OOM)' \$d/summary.out | head -10; done; grep '^done' $RCHAIN/pool.out; free -g | head -2"
}

return_one() {
  local RET=$VOL/remote-$STAMP/$T_NAME
  say "return $T_NAME to $RET"
  # real directories named like the module dir (leanchecker does not follow a symlinked module directory)
  L "mkdir -p $RET/lib/lean/$T_OUTREL $RET/ir/$T_OUTREL $RET/logs"
  L "rsync -a -e 'ssh $SSHO' root@$HOST:$T_RDIR/.lake/build/lib/lean/$T_OUTREL/ $RET/lib/lean/$T_OUTREL/"
  L "rsync -a -e 'ssh $SSHO' root@$HOST:$T_RDIR/.lake/build/ir/$T_OUTREL/ $RET/ir/$T_OUTREL/"
  L "rsync -a -e 'ssh $SSHO' root@$HOST:$RCHAIN/logs/$T_NAME/ $RET/logs/"
  L "rsync -a -e 'ssh $SSHO' root@$HOST:$RCHAIN/pool.out root@$HOST:$RCHAIN/STATUS $RET/../"
  L "ssh $SSHO root@$HOST 'cd $T_RDIR && git rev-parse HEAD' > $RET/remote_head.txt"
  L "grep -q $FROZEN $RET/remote_head.txt || { echo 'STOP: remote HEAD differs from the frozen commit'; exit 1; }"
  L "(cd $T_SRC && readlink .lake/build/lib/lean/$T_OUTREL > $RET/prev_lib_lean.link; readlink .lake/build/ir/$T_OUTREL > $RET/prev_ir.link)"
  L "(cd $T_SRC && ln -sfn $RET/lib/lean/$T_OUTREL .lake/build/lib/lean/$T_OUTREL && ln -sfn $RET/ir/$T_OUTREL .lake/build/ir/$T_OUTREL)"
  local x
  for x in $T_NOBUILD; do L "(cd $T_SRC && lake build --no-build $x; echo NOBUILD_${T_NAME}_rc=\$?)   # $x"; done
  echo "(anything reported as needing a build = the trace inputs differ: STOP and report; roll back with the prev_*.link targets)"
}
ret() { each return_one; }

audit_one() {
  local RET=$VOL/remote-$STAMP/$T_NAME
  say "audit $T_NAME: stratified leanchecker sample (one module at a time, MemoryMax=10G, gate 12 GB)"
  local f
  {
    for f in $(cd "$T_SRC" && ls $T_AUDIT_FIXED 2>/dev/null); do echo "$f"; done | sed 's|\.lean$||; s|/|.|g'
    (cd "$T_SRC" && find $T_AUDIT_POOL -name '*.lean') | sed 's|\.lean$||; s|/|.|g' | sort | python3 -c "
import random,sys
xs=[l.strip() for l in sys.stdin if l.strip()]
random.seed($AUDIT_SEED); k=max(1,len(xs)*$AUDIT_PCT//100)
print('\n'.join(sorted(random.sample(xs,k))))"
  } > "$WORK/$T_NAME.audit_sample.txt"
  echo "sample: $(wc -l < "$WORK/$T_NAME.audit_sample.txt") modules -> $WORK/$T_NAME.audit_sample.txt"
  # $RET LAST: leanchecker finds the target's oleans by walking real directories (it does not enter the symlinked
  # module dir), while imports resolve through the first search-path entry that has a `KAM/` dir. With $RET first,
  # every core import resolved into $RET and failed ("object file … does not exist"; 2026-11-05 return).
  local lp chk; lp="$(cd "$T_SRC" && lake env printenv LEAN_PATH):$RET/lib/lean"
  chk="$HOME/.elan/toolchains/$(sed 's|/|--|; s|:|---|' "$T_SRC/lean-toolchain")/bin/leanchecker"
  while read -r m; do
    L "until [ \$(awk '/MemAvailable/{print \$2}' /proc/meminfo) -ge 12582912 ]; do sleep 30; done; systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 nice -n 10 env LEAN_PATH=$lp /usr/bin/time -f '%e s %M kB' $chk $m >> $WORK/$T_NAME.audit.log 2>&1; echo \"$m rc=\$?\" >> $WORK/$T_NAME.audit.log"
  done < "$WORK/$T_NAME.audit_sample.txt"
}
audit() { each audit_one; }

for ph in "$@"; do
  case "$ph" in
    all) preflight; provision; transfer; check; run_chain ;;
    preflight) preflight ;;
    hcloud-create) hcloud_create ;;
    hcloud-delete) hcloud_delete ;;
    provision) provision ;;
    transfer) transfer ;;
    check) check ;;
    run) run_chain ;;
    status) status ;;
    return) ret ;;
    audit) audit ;;
    *) echo "unknown phase $ph"; exit 2 ;;
  esac
done
