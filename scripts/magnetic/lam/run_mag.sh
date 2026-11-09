#!/bin/bash
# run_mag.sh: build the KAM magnetic-barrier certificate chain (KAM.Magnetic.Data, branch mag-pilot) on one big
# Linux machine. Lake builds every module, one module per process, each in its own memory scope.
#
# Run as root (sudo -i), one phase at a time or `all`:
#
#   bash run_mag.sh setup     # apt packages, elan + Lean v4.35.0, systemd user session for root (memory scopes)
#   bash run_mag.sh fetch     # download the package from the KAM server over Tailscale, verify SHA256SUMS
#   bash run_mag.sh unpack    # git clone the bundle, unpack sources, prebuilt oleans, packages into /root/kam-mag
#   bash run_mag.sh check     # the shipped build must be up to date (`lake build --no-build`), then ONE smoke module
#   bash run_mag.sh run       # start the pool detached: probes first at 48G, then LANES lanes with measured caps
#   bash run_mag.sh status    # progress (STATUS is rewritten every minute while running)
#   bash run_mag.sh return    # pack the new oleans + hashes + results.tsv, send them over Taildrop
#   bash run_mag.sh stop      # stop the pool (exact PID) and wait for its builds to end
#   bash run_mag.sh all       # setup fetch unpack check run
#
# Parameters (environment): LANES (default 20), BASE (package URL), DEST (Taildrop target, default
# ubuntu-16gb-nbg1-1). Every phase is idempotent; `run` skips modules lake already has up to date (a few seconds
# each), so rerunning it only retries the failed or missing ones.
set -euo pipefail
PHASES=("$@"); [ ${#PHASES[@]} -ge 1 ] || { sed -n 2,19p "$0"; exit 2; }
[ "$(id -u)" = 0 ] || { echo "STOP: run as root (sudo -i)"; exit 1; }

LANES=${LANES:-20}
BASE=${BASE:-http://100.124.142.13:8765/mag}
DEST=${DEST:-ubuntu-16gb-nbg1-1}
TOOLCHAIN=leanprover/lean4:v4.35.0
LEAN_GITHASH=eb6cafb7290e8bd5f2937522d8d804f58f02bafc
XFER=/root/xfer-mag
TREE=/root/kam-mag
PKG=/root/kam-mag-packages
CHAIN=/root/kam-mag-chain
TARGET=KAM.Magnetic.Data.Mag.Seg.Checks
P=KAM.Magnetic.Data.Mag.Seg.Prod
# reissue 3 (MAG5): the probes, built first at 48G so that every class cap comes from completed runs: the largest
# remainder-range module (M8RemR1), one Full and one Low product consumer (now on `magM<k>_lit`), and M109 (the
# product with its side checks and prefix split). A class starts once ONE of its probes has passed.
PROBES=$P.M8RemR1,KAM.Magnetic.Data.Mag.Seg.Full.S12,KAM.Magnetic.Data.Mag.Seg.Low.S70,$P.M109
SMOKE=$P.M209RemR1
FILES="mag.bundle data.tar.zst data_sha256.txt config.tar.zst build.tar.zst packages.tar.zst done.txt core-roots.txt mag_lam_pool.py run_mag.sh COMMIT WORKSTATION-BRIEF.md"
export XDG_RUNTIME_DIR=/run/user/0
say() { echo "== $(date -u +%H:%M:%S) $*"; }
die() { echo "STOP: $*"; exit 1; }
elanenv() { # shellcheck disable=SC1091
  source /root/.elan/env; export PATH=/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH; }
running() { local p; p=$(cat $CHAIN/pool.pid 2>/dev/null || echo 0); [ "$p" != 0 ] && kill -0 "$p" 2>/dev/null; }

setup() {
  say setup
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -q && apt-get install -yq git python3 time curl zstd
  test -x /root/.elan/bin/elan || curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  elanenv; elan toolchain install $TOOLCHAIN
  local gh; gh=$(elan run $TOOLCHAIN lean --githash)
  [ "$gh" = $LEAN_GITHASH ] || die "Lean v4.35.0 here is commit $gh, expected $LEAN_GITHASH"
  loginctl enable-linger root
  for _ in $(seq 30); do [ -S /run/user/0/bus ] && break; sleep 1; done
  local m; m=$(systemd-run --user --scope -q -p MemoryMax=1G -p MemorySwapMax=0 \
    bash -c 'cat /sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup)/memory.max')
  [ "$m" = 1073741824 ] || die "systemd --user memory scopes do not work (memory.max=$m)"
  say "setup OK: memory scopes work; $(nproc) threads, $(awk '/MemTotal/{print int($2/1048576)}' /proc/meminfo) GB RAM"
}

fetch() {
  say "fetch from $BASE"
  mkdir -p $XFER; cd $XFER
  curl -sSf "$BASE/SHA256SUMS" -o SHA256SUMS
  for f in $FILES; do
    if [ -f "$f" ] && grep " $f\$" SHA256SUMS | sha256sum -c --quiet - 2>/dev/null; then say "  $f (have it)"; continue; fi
    # a file that is present but does not match is stale (the server copy changed): fetch it whole. Only the
    # large archives resume a partial download, and a resumed file that still does not match is fetched whole.
    case "$f" in
      *.tar.zst|*.bundle) [ -f "$f" ] && mv "$f" "$f.part"
        curl -sSf -C - --retry 5 --retry-delay 10 "$BASE/$f" -o "$f.part" || true
        mv "$f.part" "$f"
        grep " $f\$" SHA256SUMS | sha256sum -c --quiet - 2>/dev/null \
          || { say "  $f: resumed copy does not match, fetching it whole"; rm -f "$f"; curl -sSf --retry 5 "$BASE/$f" -o "$f"; } ;;
      *) rm -f "$f"; say "  $f"; curl -sSf --retry 5 --retry-delay 10 "$BASE/$f" -o "$f" ;;
    esac
  done
  sha256sum -c SHA256SUMS || die "checksum mismatch: delete the bad file in $XFER and rerun fetch"
  say "fetch OK"
}

unpack() {
  say unpack
  running && die "the pool is running; stop it first"
  cd $XFER; sha256sum -c --quiet SHA256SUMS || die "checksums"
  local c; c=$(cat COMMIT)
  test -d $TREE/.git || git clone -q --no-checkout mag.bundle $TREE
  git -C $TREE fetch -q $XFER/mag.bundle mag-pilot
  git -C $TREE checkout -q -B mag-pilot "$c"
  [ "$(git -C $TREE rev-parse HEAD)" = "$c" ] || die "wrong commit"
  zstd -dc data.tar.zst | tar -C $TREE -xf -
  (cd $TREE && sha256sum -c --quiet $XFER/data_sha256.txt) || die "chain sources do not match data_sha256.txt"
  mkdir -p $PKG $TREE/.lake/build
  zstd -dc packages.tar.zst | tar -C $PKG -xf -
  ln -sfn $PKG $TREE/.lake/packages
  zstd -dc build.tar.zst | tar -C $TREE/.lake/build -xf -
  zstd -dc config.tar.zst | tar -C $TREE/.lake -xf -
  mkdir -p $CHAIN; cp done.txt core-roots.txt mag_lam_pool.py $CHAIN/
  [ "$(git -C $TREE status --porcelain --untracked-files=no | wc -l)" = 0 ] || die "tracked changes in $TREE"
  say "unpack OK: HEAD $c, $(wc -l < data_sha256.txt) chain sources verified, $(du -sh $TREE/.lake/build | cut -f1) build"
}

check() {
  say "check: the shipped core closure and the $(wc -l < $CHAIN/done.txt) prebuilt chain modules must be up to date (nothing may build)"
  running && die "the pool is running"
  elanenv; cd $TREE
  lake build --no-build $(cat $CHAIN/core-roots.txt) $(cat $CHAIN/done.txt) > $CHAIN/check-nobuild.log 2>&1 \
    || { tail -20 $CHAIN/check-nobuild.log; die "the shipped build is not up to date here; do NOT build it, report this"; }
  MAG_DRY=1 MAG_DONE=$CHAIN/done.txt MAG_PROBES=$PROBES python3 $CHAIN/mag_lam_pool.py $TREE $CHAIN/logs-dry 1 $TARGET
  say "  smoke: one chain module ($SMOKE, 10G scope)"
  MAG_DONE=$CHAIN/done.txt MAG_DEFAULT_CAP=10G python3 $CHAIN/mag_lam_pool.py $TREE $CHAIN/logs-smoke 1 $SMOKE \
    > $CHAIN/smoke.out 2>&1 || { tail -5 $CHAIN/smoke.out; die "smoke build failed (see $CHAIN/logs-smoke)"; }
  tail -2 $CHAIN/smoke.out
  say "check OK"
}

run() {
  running && die "already running (pid $(cat $CHAIN/pool.pid)); use status"
  [ -f $CHAIN/smoke.out ] || die "run check first"
  elanenv; cd $TREE
  say "run: $LANES lanes; probes first at 48G (one module per process, cap + 2 GB available to start)"
  MAG_DONE=$CHAIN/done.txt MAG_PROBES=$PROBES MAG_PROBE_CAP=48G MAG_DEFAULT_CAP=16G MAG_TIMEOUT=1800 MAG_TIMEOUTS=Prod:5400 nohup setsid python3 \
    $CHAIN/mag_lam_pool.py $TREE $CHAIN/logs "$LANES" $TARGET >> $CHAIN/pool.out 2>&1 < /dev/null &
  echo $! > $CHAIN/pool.pid
  sleep 5; running || die "the pool did not start (see $CHAIN/pool.out)"
  say "started pid $(cat $CHAIN/pool.pid); progress: bash $0 status (log $CHAIN/pool.out)"
}

status() {
  if running; then echo "RUNNING (pid $(cat $CHAIN/pool.pid))"; else echo "NOT RUNNING"; fi
  cat $CHAIN/logs/STATUS 2>/dev/null || true
  tail -3 $CHAIN/pool.out 2>/dev/null || true
  grep -h '^STOP\|^done ' $CHAIN/pool.out 2>/dev/null || true
  echo "failures so far: $(grep -c ' rc=[^0S]' $CHAIN/pool.out 2>/dev/null || true)"
}

stop() {   # SIGTERM the pool by its exact PID; its running scopes finish or are stopped below by exact unit
  local p; p=$(cat $CHAIN/pool.pid 2>/dev/null || echo 0)
  if [ "$p" != 0 ] && kill -0 "$p" 2>/dev/null; then say "stopping pool pid $p"; kill "$p"; fi
  while [ "$p" != 0 ] && kill -0 "$p" 2>/dev/null; do sleep 5; done
  say "stopped (running lake builds end on their own; check with: systemctl --user list-units 'run-*.scope')"
}

ret() {
  running && die "still running; wait for the 'done ... fail=0 skip=0 todo=0' line in status"
  grep -q '^done .* fail=0 skip=0 todo=0' $CHAIN/pool.out \
    || echo "WARNING: the chain did not finish clean (see status); sending what exists so it can be diagnosed"
  local stamp; stamp=$(date -u +%Y%m%d-%H%M); local pk=$CHAIN/return-$stamp; rm -rf "$pk"; mkdir -p "$pk"
  cd $TREE/.lake/build
  awk -F'\t' '$3=="pass"{print $1}' $CHAIN/logs/results.tsv $CHAIN/logs-smoke/results.tsv | sort -u > "$pk/built.txt"
  for m in $(cat "$pk/built.txt"); do s=${m//.//}; ls lib/lean/$s.* ir/$s.* 2>/dev/null; done | sort -u > "$pk/files.txt"
  xargs -d "\n" -a "$pk/files.txt" sha256sum > "$pk/sha256.txt"   # one argv would exceed ARG_MAX (lam MAG-3)
  cp $CHAIN/logs/results.tsv $CHAIN/logs-smoke/results.tsv "$pk/" 2>/dev/null || true
  mv "$pk/results.tsv" "$pk/results-run.tsv" 2>/dev/null || true
  cp $CHAIN/pool.out $CHAIN/logs/STATUS "$pk/" 2>/dev/null || true
  local out=/root/mag-results-$stamp.tar.zst
  tar -cf - -T "$pk/files.txt" -C "$pk" . | zstd -q -T16 -3 -o "$out" -f
  sha256sum "$out" > "$out.sha256"
  say "packed $(du -h "$out" | cut -f1): $out ($(wc -l < "$pk/built.txt") modules)"
  if command -v tailscale >/dev/null; then
    tailscale file cp "$out" "$out.sha256" "$DEST:" && say "sent to $DEST over Taildrop" \
      || echo "Taildrop failed: send $out and $out.sha256 to the KAM server another way"
  else echo "no tailscale: send $out and $out.sha256 to the KAM server another way"; fi
}

for ph in "${PHASES[@]}"; do
  case "$ph" in
    setup) setup ;; fetch) fetch ;; unpack) unpack ;; check) check ;; run) run ;; status) status ;;
    return) ret ;; stop) stop ;;
    all) setup; fetch; unpack; check; run ;;
    *) die "unknown phase $ph" ;;
  esac
done
