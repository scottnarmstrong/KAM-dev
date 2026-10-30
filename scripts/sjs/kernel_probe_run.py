#!/usr/bin/env python3
"""SJS-FEAS kernel probes: run ONE Lean probe file under `/usr/bin/time -v` and record the result.

usage: kernel_probe_run.py PROBE.lean [--tag TAG] [--meta META.json] [--timeout 900] [--results OUT.json]

Runs `nice -n 5 timeout T lake env lean PROBE.lean` from the worktree root (one Lean process; the caller runs probes
sequentially, never in parallel), parses the Lean profiler lines (`set_option profiler true` in the probe) and the
`/usr/bin/time -v` report, and appends one JSON record to the results file:

  tag, file, bytes, exit, wall_s, user_s, sys_s, rss_gb,
  kernel_s   -- the LAST "type checking took" line (the probe's theorem is its last declaration), seconds,
  tc_lines   -- every "type checking took" value above the probe's threshold (seconds),
  elab_s     -- the sum of every "elaboration took" line (seconds), errors (first lines), meta (the generator's
                sidecar, if given).

Untrusted measurement tooling; no Lean source is modified.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def to_s(val, unit):
    v = float(val)
    return v / 1000.0 if unit == "ms" else v


def run(path, timeout):
    cmd = ["/usr/bin/time", "-v", "nice", "-n", "5", "timeout", str(timeout), "lake", "env", "lean", path]
    t0 = time.time()
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    t1 = time.time()
    out = p.stdout + "\n" + p.stderr
    rec = dict(exit=p.returncode, wall_py=t1 - t0)
    tc, el = [], 0.0
    for m in re.finditer(r"type checking took ([0-9.]+)(ms|s)\b", out):
        tc.append(to_s(m.group(1), m.group(2)))
    for m in re.finditer(r"elaboration took ([0-9.]+)(ms|s)\b", out):
        el += to_s(m.group(1), m.group(2))
    rec["tc_lines"] = tc
    rec["kernel_s"] = tc[-1] if tc else None
    rec["elab_s"] = el
    m = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)", out)
    if m:
        parts = [float(x) for x in m.group(1).split(":")]
        w = 0.0
        for x in parts:
            w = w * 60 + x
        rec["wall_s"] = w
    m = re.search(r"User time \(seconds\): ([0-9.]+)", out)
    rec["user_s"] = float(m.group(1)) if m else None
    m = re.search(r"System time \(seconds\): ([0-9.]+)", out)
    rec["sys_s"] = float(m.group(1)) if m else None
    m = re.search(r"Maximum resident set size \(kbytes\): ([0-9]+)", out)
    rec["rss_gb"] = int(m.group(1)) / 1024.0 / 1024.0 if m else None
    errs = [ln for ln in out.splitlines() if "error" in ln.lower() and "took" not in ln][:8]
    rec["errors"] = errs
    other = {}
    for m in re.finditer(r"^([a-zA-Z ]+?) took ([0-9.]+)(ms|s)\b", out, re.M):
        k = m.group(1).strip()
        other[k] = other.get(k, 0.0) + to_s(m.group(2), m.group(3))
    rec["profile"] = other
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("probe")
    ap.add_argument("--tag", default=None)
    ap.add_argument("--meta", default=None)
    ap.add_argument("--timeout", type=int, default=900)
    ap.add_argument("--results", default=os.path.join(ROOT, "scripts/sjs/results/kernel_probes_raw.jsonl"))
    a = ap.parse_args()
    rec = dict(tag=a.tag or os.path.basename(a.probe), file=a.probe,
               bytes=os.path.getsize(os.path.join(ROOT, a.probe)), date=time.strftime("%Y-%m-%d %H:%M:%S"))
    if a.meta:
        with open(os.path.join(ROOT, a.meta)) as f:
            rec["meta"] = json.load(f)
    try:
        la = os.getloadavg()[0]
    except OSError:
        la = None
    rec["load_before"] = la
    rec.update(run(a.probe, a.timeout))
    os.makedirs(os.path.dirname(a.results), exist_ok=True)
    with open(a.results, "a") as f:
        f.write(json.dumps(rec) + "\n")
    short = {k: rec.get(k) for k in ("tag", "exit", "kernel_s", "elab_s", "wall_s", "user_s", "rss_gb")}
    print(json.dumps(short))
    if rec["errors"]:
        print("\n".join(rec["errors"]), file=sys.stderr)


if __name__ == "__main__":
    main()
