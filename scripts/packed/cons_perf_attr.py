#!/usr/bin/env python3
"""V2-PACKED-CONS-PERF (untrusted tooling): re-attribute a `run_packed.py` ledger to the modules Lake actually built.

`run_packed.py` (V2-PACKED-GEN) books each `lake build MODULE` process to MODULE. It resumes by skipping the modules
whose last ledger row passed, without asking Lake whether they are still up to date; when the generator re-emits
their sources (or a shared import changes) between runs, the next target's `lake build` rebuilds the stale ones
inside its own process, and the ledger charges their cost to that target, while their obsolete earlier builds stay
in their own rows. This script reads LOGDIR/ledger.tsv and LOGDIR/<module>.log (Lake's output: one
`Built M (t)` line per job) and prints, read only:
  1. every row whose process built more than its target: the process CPU, the target's own job time, and the
     dependencies it rebuilt with their job times;
  2. per group of modules (GROUPS, as the V2-PACKED-GEN handoff's table): the ledger's figure (user + sys of each
     module's last row, as `run_packed.py --summary`); the same less the rebuilt dependencies' job time (each
     row then carries its own process: its job, Lake's start and the imports); and the final build of each
     module (the job time of its latest `Built` line over all logs, by log mtime; no Lake start).
Lake's job time is the wall time of the module's own Lean process (≈ its CPU: one thread, nice 5).
`--dump=DIR` also writes DIR/ledger.tsv (a copy) and DIR/built.json (each log's mtime and `Built` lines), a
receipt the script reads back in place of LOGDIR when LOGDIR holds a built.json (the logs may be in /tmp).
Usage: python3 -I scripts/packed/cons_perf_attr.py LOGDIR [--rows-only] [--dump=DIR]
"""
import json
import os
import shutil
import re
import sys

BUILT = re.compile(r"Built (\S+) \(([0-9.]+)(m?s)\)")
GROUPS = [  # (label, test) in order; the first match wins
    ("torsion assemblies (TorsJ.Core, TorsJ)", lambda m: m.endswith(".PK.TorsJ.Core") or m.endswith(".PK.TorsJ")),
    ("torsion on the jet (stages, D2K, LowOk)", lambda m: ".PK.TorsJ." in m),
    ("packed data and fronts", lambda m: ".PK.Data." in m or ".PK.Front" in m or m.endswith(".PK.HamJet")),
    ("Gram (B2)", lambda m: ".PK.Gram" in m),
    ("frames on the jet", lambda m: ".PK.FramesJ" in m),
    ("invariance on the jet", lambda m: ".PK.InvJ" in m),
    ("energy on the jet", lambda m: ".PK.EnJ" in m),
    ("jet-route assemblies (PK.Asm, Xfer, MainJ)", lambda m: ".PK." in m),
    ("ported Hamiltonian balls", lambda m: ".Balls." in m or m.endswith(".Kernel.BallSplit")),
    ("ported chain-free LG00 proof", lambda m: True),
]


def secs(t, u):
    return float(t) / (1000.0 if u == "ms" else 1.0)


def group(m):
    for lab, f in GROUPS:
        if f(m):
            return lab


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    rows_only = "--rows-only" in sys.argv
    d = os.path.abspath(args[0])
    last = {}
    for l in open(os.path.join(d, "ledger.tsv")):
        f = l.rstrip("\n").split("\t")
        if len(f) >= 8:
            last[f[0]] = f
    logs = {}
    if os.path.exists(os.path.join(d, "built.json")):
        logs = {m: (v[0], [tuple(x) for x in v[1]]) for m, v in json.load(open(os.path.join(d, "built.json"))).items()}
    else:
        for fn in os.listdir(d):
            if fn.endswith(".log") and fn[:-4] in last:
                p = os.path.join(d, fn)
                logs[fn[:-4]] = (os.path.getmtime(p), BUILT.findall(open(p, errors="replace").read()))
    dump = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--dump=")), None)
    if dump:
        os.makedirs(dump, exist_ok=True)
        shutil.copyfile(os.path.join(d, "ledger.tsv"), os.path.join(dump, "ledger.tsv"))
        with open(os.path.join(dump, "built.json"), "w") as f:
            json.dump({m: [v[0], [list(x) for x in v[1]]] for m, v in sorted(logs.items())}, f, indent=0)
    final = {}                                   # module -> (log mtime, job s, booked to)
    deps = {}                                    # row -> the job time of the dependencies it rebuilt
    print("1. rows whose process built more than its target")
    print("%-34s %7s %7s %5s %9s" % ("row", "CPU-s", "own s", "deps", "deps' s"))
    extra = 0.0
    for m in sorted(logs, key=lambda k: logs[k][0]):
        mt, b = logs[m]
        for n, t, u in b:
            if n not in final or mt >= final[n][0]:
                final[n] = (mt, secs(t, u), m)
        if len(b) > 1:
            own = sum(secs(t, u) for n, t, u in b if n == m)
            dep = sum(secs(t, u) for n, t, u in b if n != m)
            extra += dep
            deps[m] = dep
            f = last[m]
            print("%-34s %7.1f %7.1f %5d %9.1f" % (m.split(".", 2)[-1], float(f[1]) + float(f[2]), own,
                                                   len(b) - 1, dep))
    print("rebuilt dependencies booked to other rows: %.1f s of job time" % extra)
    if rows_only:
        return 0
    led, fin = {}, {}
    for m, f in last.items():
        if f[7] == "built":
            g = led.setdefault(group(m), [0, 0.0, 0.0])
            g[0] += 1
            g[1] += float(f[1]) + float(f[2])
            g[2] += float(f[1]) + float(f[2]) - deps.get(m, 0.0)
    for n, (_, t, _) in final.items():
        g = fin.setdefault(group(n), [0, 0.0])
        g[0] += 1
        g[1] += t
    print("\n2. per group: the ledger (last row of each module, CPU-s) against each module's final build (job s)")
    print("%-42s %5s %8s %8s %5s %8s" % ("group", "rows", "ledger", "- deps", "mods", "final"))
    for k in [lab for lab, _ in GROUPS]:
        if k in led or k in fin:
            a, b = led.get(k, [0, 0.0, 0.0]), fin.get(k, [0, 0.0])
            print("%-42s %5d %8.1f %8.1f %5d %8.1f" % (k, a[0], a[1], a[2], b[0], b[1]))
    print("%-42s %5d %8.1f %8.1f %5d %8.1f" % ("total", sum(v[0] for v in led.values()),
                                               sum(v[1] for v in led.values()), sum(v[2] for v in led.values()),
                                               sum(v[0] for v in fin.values()), sum(v[1] for v in fin.values())))
    return 0


if __name__ == "__main__":
    sys.exit(main())
