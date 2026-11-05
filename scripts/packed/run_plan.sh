#!/bin/bash
# V2-PACKED-JET-FULL: run every block of a packed-chain plan (`jet_low_gen.py`'s <Stage>Plan.json) in plan order,
# one Lean process at a time, each through `run_probe.sh` under the memory cap CAP.
# A block whose LOGDIR/<name>.cost already records `exit 0` is skipped (resume after an interruption).
# Usage: run_plan.sh CAP PLAN.json PROBEDIR LOGDIR
cap=$1; plan=$2; dir=$3; logdir=$4
cd "$(dirname "$0")/../.." || exit 2
for b in $(python3 -I -c 'import json, sys; print(" ".join(b["name"] for b in json.load(open(sys.argv[1]))["blocks"]
                                                  if b["kind"] != "given"))' "$plan"); do
  if [ -f "$logdir/$b.cost" ] && grep -q "^exit 0$" "$logdir/$b.cost"; then
    continue
  fi
  bash scripts/packed/run_probe.sh "$cap" "$dir/$b.lean" "$logdir" | sed 's/cumulative profiling times:.*typeclass inference [0-9.]*ms//'
done
