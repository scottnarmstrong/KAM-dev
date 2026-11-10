#!/usr/bin/env bash
# Reproduce the floating-point MAG-PITCH comparison, sequentially. No Lean.
# Each job is capped in Python at 3500 CPU seconds and in systemd at 4 GiB.
set -euo pipefail
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_dir=$(CDPATH= cd -- "$script_dir/../../.." && pwd)
cd "$repo_dir"
pitch_out=${1:-.drafts/mag-pitch/reproduction}
mkdir -p "$pitch_out/results" "$pitch_out/refined"
run() {
  local label=$1
  shift
  systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0 \
    nice -n 10 env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
    python3 -B "$script_dir/$1" "${@:2}" > "$pitch_out/$label.log" 2>&1
}
run uncontrolled circle_scan.py --model uncontrolled --max-n 512 --out "$pitch_out/results"
run controlled circle_scan.py --model controlled --max-n 512 --out "$pitch_out/results"
run controlled-refined circle_scan.py --model controlled --max-n 1024 --out "$pitch_out/refined"
run greene-uncontrolled-32 greene.py --model uncontrolled --max-den 74 --spp 32 \
  --stop .0014 --step .00005 --out "$pitch_out/results/greene-uncontrolled-32.json"
run greene-uncontrolled-64 greene.py --model uncontrolled --max-den 241 --spp 64 \
  --stop .0012 --step .00002 --out "$pitch_out/results/greene-uncontrolled-64.json"
run greene-uncontrolled-refine greene.py --model uncontrolled --max-den 136 --spp 64 \
  --resume "$pitch_out/results/greene-uncontrolled-64.json" --tolerance 8e-11 \
  --stop .0012 --step .000005 --out "$pitch_out/results/greene-uncontrolled-refine.json"
run greene-uncontrolled-128 greene.py --model uncontrolled --max-den 241 --spp 128 \
  --resume "$pitch_out/results/greene-uncontrolled-64.json" --symmetry zero \
  --tolerance 8e-11 --stop .00096 --step .000005 \
  --out "$pitch_out/results/greene-uncontrolled-128.json"
run greene-controlled-64 greene.py --model controlled --max-den 241 --spp 64 \
  --stop .0045 --step .00005 --out "$pitch_out/results/greene-controlled-64.json"
run greene-controlled-refine greene.py --model controlled --max-den 241 --spp 64 \
  --resume "$pitch_out/results/greene-controlled-64.json" --symmetry zero \
  --tolerance 8e-11 --stop .005 --step .00001 \
  --out "$pitch_out/results/greene-controlled-refine.json"
run controlled-residue-validation diagnostics.py --root "$pitch_out" \
  --refine-residues "$pitch_out/results/greene-controlled-refine.json" \
  --out "$pitch_out/results/controlled-residue-validation.json"
run diagnostics diagnostics.py --root "$pitch_out" --out "$pitch_out/results/diagnostics.json"
run transport transport.py --periods 512 --steps 32 --out "$pitch_out/results/transport.json"
# The measured whole sequence is well below the brief's three CPU-hour budget.
# Fail if future machine/library drift causes its reported process CPU to exceed it.
python3 -B - "$pitch_out" <<'PY'
import json
import sys
from pathlib import Path
files = list(Path(sys.argv[1]).glob('results/*.json')) + list(Path(sys.argv[1]).glob('refined/*.json'))
seconds = sum(json.loads(p.read_text()).get('cpu_seconds', 0) for p in files)
print(f'Reported process CPU: {seconds:.1f} seconds')
if seconds > 10800:
    raise SystemExit('Three CPU-hour budget exceeded')
PY
