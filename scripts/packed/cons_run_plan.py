#!/usr/bin/env python3
"""V2-PACKED-CONS gate: build the scratch package's modules one at a time (`cons_run.sh`), in order, and summarize.

Modules: the certificate copies (`--cert`), the shared data and the probes of `cons_plan.json`. A module already
recorded with exit 0 in LOGDIR is skipped (resumable). Prints one line per module and writes LOGDIR/summary.json:
per probe user + sys CPU, kernel time (`type checking took`), the cgroup peak, the exit code and the decision
(probes state `= true` or `= false`; a passing build means the kernel decided the stated Boolean).
Usage: python3 -I scripts/packed/cons_run_plan.py PKG LOGDIR [--cap=4G] [--only=PREFIX]
"""
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CERT = ["Format", "FormatK", "FormatQ", "Coeffs0", "Coeffs1", "Ham"] + ["JetOps%d" % i for i in range(7)] + \
    ["Jet", "TP.Data.DCoeffs", "TP.Data.E0", "TP.Data.W8", "TP.Data.Cert"]


def cost(logdir, mod):
    p = os.path.join(logdir, mod + ".cost")
    if not os.path.exists(p):
        return None
    d = {}
    for line in open(p):
        m = re.match(r"(\w+) (-?[\d.]+)$", line.strip())
        if m:
            d[m.group(1)] = float(m.group(2))
    out = open(os.path.join(logdir, mod + ".out")).read() if os.path.exists(os.path.join(logdir, mod + ".out")) else ""
    tc = re.findall(r"type checking took ([\d.]+)(m?s)", out)
    if tc:
        d["kernel_s"] = max(float(v) / (1000 if u == "ms" else 1) for v, u in tc)
    return d


def main():
    pkg, logdir = sys.argv[1], sys.argv[2]
    cap = next((a.split("=")[1] for a in sys.argv if a.startswith("--cap=")), "4G")
    only = next((a.split("=")[1] for a in sys.argv if a.startswith("--only=")), None)
    plan = json.load(open(os.path.join(pkg, "cons_plan.json")))
    pre = plan["data"][0].split(".")[0]
    mods = [pre + "." + m for m in CERT] + plan["data"] + [p["module"] for p in plan["probes"]]
    if only:
        mods = [m for m in mods if m.startswith(only)]
    summ = {}
    for mod in mods:
        c = cost(logdir, mod)
        if c is None or c.get("exit") != 0:
            subprocess.run([os.path.join(HERE, "cons_run.sh"), cap, pkg, mod, logdir], check=False)
            c = cost(logdir, mod)
        summ[mod] = c
        print(mod, c, flush=True)
    with open(os.path.join(logdir, "summary.json"), "w") as f:
        json.dump(summ, f, indent=1)


if __name__ == "__main__":
    main()
