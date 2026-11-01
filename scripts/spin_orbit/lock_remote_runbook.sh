#!/bin/bash
# LOCK-DATA / LOCK-REMOTE: the lock's full kernel chain on a rented machine (Hetzner CCX53), as ONE runbook
# (untrusted tooling; .drafts/briefs/offload-main/LOCK-REMOTE.md and the UPDATE of PKG-LOCK-DATA-RUN.md).
#
#   lock_remote_runbook.sh [--dry-run] PHASE [PHASE ...]
#
# Phases, in order (each idempotent; `all` = preflight provision transfer check run):
#   preflight   local only: frozen commit, clean tracked tree, segment tree linked, free space, file lists
#   hcloud-create / hcloud-delete   (API-token mode only; needs HCLOUD_TOKEN in the environment, never stored)
#   provision   remote: apt rsync/git/python3/time, elan + the repo's lean-toolchain, systemd --user scope check
#   transfer    git bundle of the frozen commit; rsync -L of the untracked lock sources (base data + segment tree);
#               .lake/packages and the core .lake/build (no LockN65 outputs)
#   check       remote: `lake build --no-build KAM` must report everything up to date BEFORE any build
#   run         remote: lock_mlane.py, LANES heavy lanes x LOCK_MEM, continue past failures (detached; setsid)
#   status      remote: tally of the running chain
#   return      rsync the LockN65 outputs + logs to $VOL/remote-<date>/; place them in the local overlay;
#               `lake build --no-build` of AssemblyN65 and KAMLunarLock here (anything to rebuild = STOP)
#   audit       local: stratified leanchecker replay (every Pass module, Passes, AssemblyN65, a seeded random 5 %
#               of the segment modules), one at a time under MemoryMax=10G
#
# --dry-run prints every command and touches nothing remote (no ssh/rsync/hcloud is executed); local read-only
# preflight computations still run so the printed file counts are real.
#
# Parameters (environment; nothing secret lives in the repo):
#   HOST       remote address (required unless --dry-run; dry-run shows REMOTE_HOST)
#   KEY        ssh private key (default /root/.ssh/kam_build_ed25519)
#   RDIR       remote worktree (default /root/kam)
#   FROZEN     commit to build (default: the hash in .drafts/REEMIT-DONE)
#   SEGTREE    emitted segment tree root (default: the target of KAM/SpinOrbit/Data/LockN65/Seg's links)
#   LANES      heavy lanes (default 11); LOCK_MEM (10G); LOCK_GATE kB (default 11534336 = 11 GiB)
#   TARGET     chain target (default KAM.SpinOrbit.Data.LockN65.AssemblyN65; its closure is the whole chain)
#   STAMP      date tag of the return directory (default: today, UTC)
#   AUDIT_PCT  sample percentage of segment modules (default 5); AUDIT_SEED (default 65)
set -u
DRY=0
[ "${1:-}" = "--dry-run" ] && { DRY=1; shift; }
[ $# -ge 1 ] || { sed -n 2,40p "$0"; exit 2; }

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
cd "$ROOT" || exit 2
VOL=/mnt/HC_Volume_106379410/kam-data/so-lock
PFX=KAM.SpinOrbit.Data.LockN65
HOST=${HOST:-}
if [ -z "$HOST" ]; then
  if [ $DRY = 1 ]; then HOST=REMOTE_HOST
  else for ph in "$@"; do case "$ph" in preflight|audit|hcloud-create) ;; *) echo "HOST unset"; exit 2 ;; esac; done; fi
fi
KEY=${KEY:-/root/.ssh/kam_build_ed25519}
RDIR=${RDIR:-/root/kam}
FROZEN=${FROZEN:-$(cat .drafts/REEMIT-DONE 2>/dev/null | grep -oE '[0-9a-f]{40}' | head -1)}
LANES=${LANES:-11}
LOCK_MEM=${LOCK_MEM:-10G}
LOCK_GATE=${LOCK_GATE:-11534336}
TARGET=${TARGET:-$PFX.AssemblyN65}
STAMP=${STAMP:-$(date -u +%Y%m%d)}
RET=$VOL/remote-$STAMP
WORK=${WORK:-$VOL/remote-work}          # local state: bundle, file lists, logs of this runbook
AUDIT_PCT=${AUDIT_PCT:-5}
AUDIT_SEED=${AUDIT_SEED:-65}
TOOLCHAIN=$(cat lean-toolchain)
SSHO="-i $KEY -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ServerAliveInterval=30"
LOCKDIR=KAM/SpinOrbit/Data/LockN65

say() { echo "== $(date -u +%H:%M:%S) $*"; }
# run a local command (printed; skipped in dry-run)
L() { echo "+ $*"; [ $DRY = 1 ] || eval "$@"; }
# run a remote command (printed; never executed in dry-run)
R() { echo "+ [remote $HOST] $*"; [ $DRY = 1 ] || ssh $SSHO root@"$HOST" "$*"; }
die() { echo "STOP: $*"; exit 1; }
REMENV="source \$HOME/.elan/env; cd $RDIR"

preflight() {
  say "preflight (local, read-only)"
  [ -n "$FROZEN" ] || die "no frozen commit (.drafts/REEMIT-DONE missing; set FROZEN)"
  git cat-file -e "$FROZEN^{commit}" 2>/dev/null || die "frozen commit $FROZEN unknown"
  echo "frozen commit $FROZEN ($(git log -1 --format=%s "$FROZEN" | cut -c1-80))"
  [ "$(git rev-parse HEAD)" = "$FROZEN" ] || echo "note: HEAD $(git rev-parse --short HEAD) != frozen; the bundle carries the frozen commit, the untracked sources come from this worktree"
  [ -z "$(git status --porcelain --untracked-files=no)" ] || die "tracked changes in the worktree"
  local seg; seg=${SEGTREE:-$(readlink "$LOCKDIR/Seg/CharE.lean" | sed 's|/KAM/SpinOrbit/Data/LockN65/Seg/CharE.lean||')}
  echo "segment tree: $seg"
  mkdir -p "$WORK"
  git ls-files --others --exclude-standard "$LOCKDIR" > "$WORK/untracked.txt"
  local n nb; n=$(wc -l < "$WORK/untracked.txt"); nb=$(grep -c "/Seg/" "$WORK/untracked.txt")
  echo "untracked lock sources: $n ($nb in Seg/); dangling links: $(while read -r f; do [ -e "$f" ] || echo "$f"; done < "$WORK/untracked.txt" | wc -l)"
  echo "source volume (dereferenced): $(du -shL --files0-from=<(tr '\n' '\0' < "$WORK/untracked.txt") -c 2>/dev/null | tail -1 | cut -f1)"
  echo "packages: $(readlink -f .lake/packages)  ($(du -sh "$(readlink -f .lake/packages)" 2>/dev/null | cut -f1))"
  echo "free on volume: $(df -h $VOL | tail -1 | awk '{print $4}') (return needs about 15-20 GB)"
  LOCK_DRY=1 python3 scripts/spin_orbit/lock_mlane.py "$WORK/dry" "$LANES" "$TARGET" > "$WORK/schedule.txt" 2>&1 \
    || echo "dry schedule rc=$? (see $WORK/schedule.txt)"
  head -2 "$WORK/schedule.txt"
}

hcloud_create() {
  say "hcloud-create (API-token mode; token read from HCLOUD_TOKEN, never written)"
  [ $DRY = 1 ] || [ -n "${HCLOUD_TOKEN:-}" ] || die "HCLOUD_TOKEN unset"
  L "hcloud ssh-key create --name kam-lock-build --public-key-from-file $KEY.pub || true"
  L "hcloud server create --name kam-lock-build --type ccx53 --image ubuntu-24.04 --location nbg1 --ssh-key kam-lock-build"
  L "hcloud server ip kam-lock-build   # -> export HOST=<ip>"
}
hcloud_delete() {
  say "hcloud-delete (only after return + check)"
  L "hcloud server delete kam-lock-build"
}

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

transfer() {
  say "transfer"
  mkdir -p "$WORK"
  [ -s "$WORK/untracked.txt" ] || git ls-files --others --exclude-standard "$LOCKDIR" > "$WORK/untracked.txt"
  L "git bundle create $WORK/frozen.bundle $FROZEN inp-lockdata"
  L "git bundle verify $WORK/frozen.bundle"
  R "mkdir -p $RDIR /root/xfer"
  L "rsync -a -e 'ssh $SSHO' $WORK/frozen.bundle root@$HOST:/root/xfer/"
  R "test -d $RDIR/.git || git clone -q /root/xfer/frozen.bundle $RDIR; cd $RDIR && git fetch -q /root/xfer/frozen.bundle inp-lockdata && git checkout -q -B inp-lockdata $FROZEN && git rev-parse HEAD"
  # the lock's generated sources are symlinks into the volume: dereference
  L "rsync -aL --files-from=$WORK/untracked.txt -e 'ssh $SSHO' ./ root@$HOST:$RDIR/"
  # dependencies and the core build, identical artifacts (never rebuilt remotely)
  L "rsync -a --info=stats1 -e 'ssh $SSHO' $(readlink -f .lake/packages)/ root@$HOST:$RDIR/.lake/packages/"
  L "rsync -a --info=stats1 --exclude=/lib/lean/KAM/SpinOrbit/Data/LockN65 --exclude=/ir/KAM/SpinOrbit/Data/LockN65 -e 'ssh $SSHO' $(readlink -f .lake/build)/ root@$HOST:$RDIR/.lake/build/"
  L "rsync -a -e 'ssh $SSHO' .lake/config/ root@$HOST:$RDIR/.lake/config/"
  R "cd $RDIR && find $LOCKDIR -name '*.lean' | wc -l && git status --porcelain --untracked-files=no | wc -l"
}

check() {
  say "check: nothing may need building before the run"
  R "$REMENV && lake build --no-build KAM; echo NOBUILD_KAM_rc=\$?"
  if [ $DRY = 0 ]; then
    ssh $SSHO root@"$HOST" "$REMENV && lake build --no-build KAM" >/dev/null 2>&1 || die "remote core is not up to date: the trace inputs differ; do not build"
  fi
}

run_chain() {
  say "run: $LANES lanes x $LOCK_MEM, gate $LOCK_GATE kB, target $TARGET"
  R "$REMENV && export XDG_RUNTIME_DIR=/run/user/0 && mkdir -p /root/chain && LOCK_DRY=1 python3 scripts/spin_orbit/lock_mlane.py /root/chain/logs $LANES $TARGET | head -2"
  R "$REMENV && export XDG_RUNTIME_DIR=/run/user/0 && LOCK_MEM=$LOCK_MEM LOCK_GATE=$LOCK_GATE setsid nohup python3 scripts/spin_orbit/lock_mlane.py /root/chain/logs $LANES $TARGET > /root/chain/chain.out 2>&1 < /dev/null & echo \$! > /root/chain/chain.pid; cat /root/chain/chain.pid"
}

status() {
  R "cat /root/chain/chain.pid; kill -0 \$(cat /root/chain/chain.pid) 2>/dev/null && echo RUNNING || echo FINISHED; head -1 /root/chain/chain.out; grep -c ' rc=0 ' /root/chain/chain.out; grep -E ' rc=(1|OOM|SKIP)' /root/chain/chain.out | head -20; tail -1 /root/chain/chain.out; free -g | head -2"
}

ret() {
  say "return to $RET"
  # real directories named LockN65 (leanchecker does not follow a symlinked module directory; audit uses
  # $RET/lib/lean as an extra LEAN_PATH root)
  L "mkdir -p $RET/lib/lean/$LOCKDIR $RET/ir/$LOCKDIR $RET/logs"
  L "rsync -a -e 'ssh $SSHO' root@$HOST:$RDIR/.lake/build/lib/lean/$LOCKDIR/ $RET/lib/lean/$LOCKDIR/"
  L "rsync -a -e 'ssh $SSHO' root@$HOST:$RDIR/.lake/build/ir/$LOCKDIR/ $RET/ir/$LOCKDIR/"
  L "rsync -a -e 'ssh $SSHO' root@$HOST:/root/chain/ $RET/logs/"
  L "ssh $SSHO root@$HOST 'cd $RDIR && git rev-parse HEAD' > $RET/remote_head.txt"
  L "grep -q $FROZEN $RET/remote_head.txt || { echo 'STOP: remote HEAD differs from the frozen commit'; exit 1; }"
  # place: the overlay links point at the returned trees (the previous targets are recorded for rollback)
  L "readlink .lake/build/lib/lean/$LOCKDIR > $RET/prev_lib_lean.link; readlink .lake/build/ir/$LOCKDIR > $RET/prev_ir.link"
  L "ln -sfn $RET/lib/lean/$LOCKDIR .lake/build/lib/lean/$LOCKDIR; ln -sfn $RET/ir/$LOCKDIR .lake/build/ir/$LOCKDIR"
  L "lake build --no-build $TARGET; echo NOBUILD_TARGET_rc=\$?"
  L "lake build --no-build KAMLunarLock; echo NOBUILD_LIB_rc=\$?   # the generated root parts list the landed set; regenerated at landing"
  echo "(anything reported as needing a build = the trace inputs differ: STOP and report; roll back with the prev_*.link targets)"
}

audit() {
  say "audit: stratified leanchecker sample (one module at a time, MemoryMax=10G, gate 12 GB)"
  mkdir -p "$WORK"
  local seg; seg=$(cd "$ROOT" && find $LOCKDIR/Seg -name '*.lean' | sed 's|\.lean$||; s|/|.|g' | sort)
  {
    ls $LOCKDIR/Pass/*.lean 2>/dev/null | sed 's|\.lean$||; s|/|.|g'
    echo "$PFX.Passes"; echo "$PFX.AssemblyN65"
    echo "$seg" | python3 -c "
import random,sys
xs=[l.strip() for l in sys.stdin if l.strip()]
random.seed($AUDIT_SEED); k=max(1,len(xs)*$AUDIT_PCT//100)
print('\n'.join(sorted(random.sample(xs,k))))"
  } > "$WORK/audit_sample.txt"
  echo "sample: $(wc -l < "$WORK/audit_sample.txt") modules -> $WORK/audit_sample.txt"
  local lp chk; lp="$RET/lib/lean:$(lake env printenv LEAN_PATH)"
  chk="$HOME/.elan/toolchains/$(sed 's|/|--|; s|:|---|' lean-toolchain)/bin/leanchecker"
  while read -r m; do
    L "until [ \$(awk '/MemAvailable/{print \$2}' /proc/meminfo) -ge 12582912 ]; do sleep 30; done; systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 nice -n 10 env LEAN_PATH=$lp /usr/bin/time -f '%e s %M kB' $chk $m >> $WORK/audit.log 2>&1; echo \"$m rc=\$?\" >> $WORK/audit.log"
  done < "$WORK/audit_sample.txt"
}

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
