#!/bin/bash
# Replay the declarations of the KAM library through Lean's `leanchecker` (kernel replay of every
# constant of each module, `Lean.Kernel.Environment.replay`, against an environment built from the
# module's imports). An axiom report is not a kernel check: this is the gate that catches
# declarations added with `debug.skipKernelTC` or through `addDecl` (landing-guards.md section 1).
#
# usage: scripts/kernel_replay.sh [--full | --fast] [--timeout MINUTES] [--mem-gb GB] [--log FILE]
#   --full   (default) every module of the library: the whole `KAM.*` tree, frozen anchors and
#            provider modules and DRAFT_SORRY anchors included (the root file skips some, so the
#            module list is enumerated from the source tree, not read from `KAM.lean`).
#   --fast   only the frozen anchors, their implementation modules (manifest) and every module under
#            KAM/Provider.
#   --timeout  wall-clock limit (default 90); the run is stopped and fails when it is exceeded.
#   --mem-gb   address-space cap for the process, `ulimit -v` (default 40; Lean mmaps the oleans).
# Prerequisite: the library is built (`lake build`); this script never builds.
# Exit 0 only if leanchecker exits 0, every expected module is reported as replayed, and nothing
# but the `replaying ...` progress lines was printed. Runs one niced process (nice -n 10) and prints
# wall time and peak resident memory.
set -euo pipefail

mode=full timeout_min=90 mem_gb=40 log=""
while [ $# -gt 0 ]; do
  case $1 in
    --full) mode=full ;;
    --fast) mode=fast ;;
    --timeout) timeout_min=${2:?}; shift ;;
    --mem-gb) mem_gb=${2:?}; shift ;;
    --log) log=${2:?}; shift ;;
    -h|--help) sed -n '2,19p' "$0"; exit 0 ;;
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
    expected = everything
    args = ['KAM']          # prefix match: every module `KAM.*`; verified against `expected` below
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
start=$(date +%s)
set +e
(
  ulimit -v $((mem_gb * 1024 * 1024))
  exec /usr/bin/time -f 'PEAK_RSS_KB %M\nCPU_SECONDS %U+%S' -o "$work/time.txt" \
    timeout --signal=TERM --kill-after=30 "${timeout_min}m" \
    nice -n 10 lake env leanchecker --verbose "${modules[@]}"
) >"$log" 2>&1
rc=$?
set -e
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
sed -n 's/^replaying //p' "$log" | sort -u > "$work/replayed.txt"
missing=$(comm -23 "$work/expected.txt" "$work/replayed.txt" || true)
extra=$(comm -13 "$work/expected.txt" "$work/replayed.txt" || true)
if [ -n "$missing" ]; then
  echo "KERNEL-REPLAY FAILED: expected modules not replayed ($(printf '%s\n' "$missing" | wc -l)):" >&2
  printf '%s\n' "$missing" | head -20 >&2; status=1
fi
if [ -n "$extra" ] && [ "$mode" = full ]; then
  echo "KERNEL-REPLAY FAILED: modules replayed that are not in the source tree:" >&2
  printf '%s\n' "$extra" | head -20 >&2; status=1
fi
peak=$(sed -n 's/^PEAK_RSS_KB //p' "$work/time.txt" 2>/dev/null || true)
cpu=$(sed -n 's/^CPU_SECONDS //p' "$work/time.txt" 2>/dev/null || true)
echo "replayed $(wc -l < "$work/replayed.txt") modules (of $n_expected expected); wall ${elapsed}s;" \
     "peak RSS $(( ${peak:-0} / 1024 )) MiB; cpu ${cpu:-?} s"
[ "$log" = "$work/replay.log" ] || echo "log: $log"
if [ "$status" -eq 0 ]; then echo "KERNEL-REPLAY OK ($mode)"; else exit 1; fi
