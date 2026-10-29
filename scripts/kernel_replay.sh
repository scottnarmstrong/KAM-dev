#!/bin/bash
# Replay the declarations of the KAM library through Lean's `leanchecker` (kernel replay of every
# constant of each module, `Lean.Kernel.Environment.replay`, against an environment built from the
# module's imports). An axiom report is not a kernel check: this is the gate that catches
# declarations added with `debug.skipKernelTC` or through `addDecl` (landing-guards.md section 1).
#
# usage: scripts/kernel_replay.sh [--full | --fast] [--timeout MINUTES] [--mem-gb GB] [--batch N] [--log FILE]
#   --full   (default) every module of the library: `leanchecker --fresh KAM` (the root's whole import
#            closure, Mathlib included, in one process) plus the modules the root does not reach (the
#            DRAFT_SORRY anchors and their providers), enumerated from the source tree.
#   --fast   only the frozen anchors, their implementation modules (manifest) and every module under
#            KAM/Provider.
#   --timeout  wall-clock limit (default 90); the run is stopped and fails when it is exceeded.
#   --batch    modules per leanchecker process (default 4).
#   --mem-gb   address-space cap for the process, `ulimit -v` (default 40; Lean mmaps the oleans).
# Prerequisite: the library is built (`lake build`); this script never builds.
# Exit 0 only if leanchecker exits 0, every expected module is reported as replayed, and nothing
# but the `replaying ...` progress lines was printed. Runs one niced process (nice -n 10) and prints
# wall time and peak resident memory.
set -euo pipefail

mode=full timeout_min=90 mem_gb=40 batch=4 log=""
while [ $# -gt 0 ]; do
  case $1 in
    --full) mode=full ;;
    --fast) mode=fast ;;
    --timeout) timeout_min=${2:?}; shift ;;
    --mem-gb) mem_gb=${2:?}; shift ;;
    --batch) batch=${2:?}; shift ;;
    --log) log=${2:?}; shift ;;
    -h|--help) sed -n '2,22p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"
toolchain_bin=/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin
export PATH="$toolchain_bin:$PATH"
command -v leanchecker >/dev/null || { echo "KERNEL-REPLAY FAILED: leanchecker not found" >&2; exit 2; }
[ -f .lake/build/lib/lean/KAM.olean ] || { echo "KERNEL-REPLAY FAILED: library not built (no KAM.olean)" >&2; exit 2; }
work=$(mktemp -d "${TMPDIR:-/tmp}/kernel-replay.XXXXXX")
trap 'rm -rf "$work"' EXIT
[ -n "$log" ] || log="$work/replay.log"

# Expected module set (one per line), and the leanchecker arguments.
python3 -I - "$root" "$mode" "$work" <<'PY'
import json, sys
from pathlib import Path
root, mode, work = Path(sys.argv[1]), sys.argv[2], Path(sys.argv[3])
def mod(p: Path) -> str:
    return '.'.join(p.relative_to(root).with_suffix('').parts)
everything = {mod(p) for p in (root / 'KAM').rglob('*.lean')}
if mode == 'full':
    # `leanchecker --fresh KAM` replays the whole import closure of the root (Mathlib and every KAM
    # module the root reaches). Modules outside that closure (the DRAFT_SORRY anchors and their
    # providers, which the quarantine keeps out of the root) are replayed on top of it, one batch each.
    import re
    imp = re.compile(r'(?m)^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+(?:all[ \t]+)?(KAM(?:\.\S+)?)[ \t]*$')
    seen, todo = set(), ['KAM']
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        f = root / (m.replace('.', '/') + '.lean') if m != 'KAM' else root / 'KAM.lean'
        todo += imp.findall(f.read_text(encoding='utf-8'))
    outside = everything - seen
    expected = outside | {'KAM with --fresh'}
    args = sorted(outside)
else:
    manifest = json.loads((root / 'manifest/frozen-anchors.json').read_text())
    expected = set()
    for a in manifest['anchors']:
        expected.add('.'.join(Path(a['path']).with_suffix('').parts))
        impl = a.get('implementation')
        if impl and impl.get('module'):
            expected.add(impl['module'])
    expected |= {m for m in everything if m.startswith('KAM.Provider.')}
    missing = sorted(expected - everything)
    if missing:
        sys.exit('manifest names modules without a source file: ' + ', '.join(missing))
    args = sorted(expected)
(work / 'expected.txt').write_text('\n'.join(sorted(expected)) + '\n')
(work / 'args.txt').write_text('\n'.join(args) + '\n')
PY
n_expected=$(wc -l < "$work/expected.txt")
echo "kernel replay: mode=$mode, $n_expected expected modules, timeout ${timeout_min} min, ulimit -v ${mem_gb} GB"

mapfile -t modules < "$work/args.txt"
# Batches bound the memory of one process and keep one batch's loss from losing the whole run; each
# batch re-imports the environment (about 16 s, 2 GB). The leanchecker binary is run directly with the
# project's LEAN_PATH (no `lake` wrapper process).
lean_path=$(lake env printenv LEAN_PATH)
start=$(date +%s)
deadline=$(( start + timeout_min * 60 ))
rc=0 peak=0 cpu=0 batches=0
: > "$log"
# run_batch LABEL ARG...: one leanchecker process; sets brc and updates peak/cpu/batches.
run_batch() {
  local label=$1; shift
  local now rss ut st
  now=$(date +%s)
  if [ "$now" -ge "$deadline" ]; then brc=124; return; fi
  batches=$((batches + 1))
  set +e
  (
    ulimit -v $((mem_gb * 1024 * 1024))
    export LEAN_PATH="$lean_path"
    exec /usr/bin/time -f '%M %U %S' -o "$work/time.txt" \
      timeout --signal=TERM --kill-after=30 "$(( deadline - now ))s" \
      nice -n 10 leanchecker --verbose "$@"
  ) >>"$log" 2>&1
  brc=$?
  set -e
  read -r rss ut st < <(tail -n 1 "$work/time.txt") || true
  [[ "${rss:-}" =~ ^[0-9]+$ ]] || { rss=0 ut=0 st=0; }
  [ "${rss:-0}" -gt "$peak" ] && peak=$rss
  cpu=$(python3 -c "print(round($cpu + ${ut:-0} + ${st:-0}))")
  echo "  batch $batches ($label): rc=$brc, $(( $(date +%s) - start )) s elapsed"
}
brc=0
if [ "$mode" = full ]; then
  run_batch "--fresh KAM: whole import closure of the root" --fresh KAM
  rc=$brc
fi
for ((i = 0; i < ${#modules[@]} && rc == 0; i += batch)); do
  run_batch "modules $(( i + 1 )).. of ${#modules[@]}" "${modules[@]:i:batch}"
  rc=$brc
done
elapsed=$(( $(date +%s) - start ))

status=0
if [ "$rc" -eq 124 ] || { [ "$rc" -eq 137 ] && [ "$elapsed" -ge $((timeout_min * 60)) ]; }; then
  echo "KERNEL-REPLAY FAILED: stopped after the ${timeout_min}-minute limit (rc=$rc)" >&2; status=1
elif [ "$rc" -ne 0 ]; then
  echo "KERNEL-REPLAY FAILED: leanchecker exited with $rc" >&2; status=1
fi
# Everything that is not a progress line is a diagnostic: failures print there.
noise=$(grep -v '^replaying ' "$log" || true)
if [ -n "$noise" ]; then
  echo "KERNEL-REPLAY FAILED: unexpected output from leanchecker:" >&2
  printf '%s\n' "$noise" | head -40 >&2; status=1
fi
sed -n 's/^replaying //p' "$log" | LC_ALL=C sort -u > "$work/replayed.txt"
missing=$(LC_ALL=C comm -23 "$work/expected.txt" "$work/replayed.txt" || true)
if [ -n "$missing" ]; then
  echo "KERNEL-REPLAY FAILED: expected modules not replayed ($(printf '%s\n' "$missing" | wc -l)):" >&2
  printf '%s\n' "$missing" | head -20 >&2; status=1
fi
echo "replayed $(wc -l < "$work/replayed.txt") modules (of $n_expected expected) in $batches batches; wall ${elapsed}s;" \
     "peak RSS $(( peak / 1024 )) MiB (largest batch); cpu ${cpu} s"
[ "$log" = "$work/replay.log" ] || echo "log: $log"
if [ "$status" -eq 0 ]; then echo "KERNEL-REPLAY OK ($mode)"; else exit 1; fi
