#!/usr/bin/env python3
"""V2-PACKED-CONS gate: the per-module costs of a run of `cons_run_plan.py`, grouped by consumer.

For every module of `cons_plan.json` (the certificate copies, the shared data, the probes): user + sys CPU, the kernel
time (`type checking took`, the largest of the module's lines), the sampled cgroup peak and the exit code. A probe
states one Boolean `= true` or `= false`; exit 0 means the kernel decided it as stated. Groups: the certificate
copies, the shared data, the data-only controls, the shared Gram link (`CG*`), the torsion (`TJ*`), the frames'
`sup |T|` (`FRT*`), the invariance (`IV*`), the energy (`EN*`); controls (`*Ctl*`, `*Obs*`, `*Tight`) are counted
apart from the checks a production proof needs.
Usage: python3 -I scripts/packed/cons_gate_sum.py PKG LOGDIR [OUT.json]
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cons_run_plan import CERT, cost  # noqa: E402


def group(mod, pre):
    if mod.startswith(pre + ".TP.Cons.P."):
        nm = mod.split(".")[-1]
        if nm.startswith("ConsData"):
            return "data control", nm
        kind = "control" if ("Ctl" in nm or "Obs" in nm or nm.endswith("Tight")) else "check"
        for p, g in (("CG", "Gram link (shared)"), ("TJ", "torsion"), ("FRT", "frames sup |T|"), ("IV", "invariance"),
                     ("EN", "energy")):
            if nm.startswith(p):
                return "%s %s" % (g, kind), nm
        return "other", nm
    if mod.startswith(pre + ".TP.Cons."):
        return "shared data", mod.split(".")[-1]
    return "certificate copy", mod[len(pre) + 1:]


def main():
    pkg, logdir = sys.argv[1], sys.argv[2]
    plan = json.load(open(os.path.join(pkg, "cons_plan.json")))
    pre = plan["data"][0].split(".")[0]
    mods = [pre + "." + m for m in CERT] + plan["data"] + [p["module"] for p in plan["probes"]]
    stmt = {}
    for p in plan["probes"]:
        src = open(os.path.join(pkg, *p["module"].split(".")) + ".lean").read()
        stmt[p["module"]] = "false" if re.search(r"= false := by", src) else "true"
    rows, groups = [], {}
    for m in mods:
        c = cost(logdir, m) or {}
        g, nm = group(m, pre)
        cpu = c.get("user_s", 0) + c.get("sys_s", 0)
        r = dict(module=m, group=g, name=nm, cpu_s=round(cpu, 2), kernel_s=c.get("kernel_s"),
                 peak_gb=round(c.get("cgroup_sampled_peak_bytes", 0) / 1e9, 3), exit=c.get("exit"),
                 oom=c.get("oom_kill"), states=stmt.get(m))
        rows.append(r)
        G = groups.setdefault(g, dict(n=0, cpu_s=0.0, kernel_s=0.0, peak_gb=0.0, failed=[]))
        G["n"] += 1
        G["cpu_s"] += cpu
        G["kernel_s"] += c.get("kernel_s") or 0
        G["peak_gb"] = max(G["peak_gb"], r["peak_gb"])
        if c.get("exit") != 0:
            G["failed"].append(nm)
    for G in groups.values():
        G["cpu_s"], G["kernel_s"] = round(G["cpu_s"], 1), round(G["kernel_s"], 1)
    out = dict(groups=groups, rows=rows)
    print("%-34s %5s %10s %10s %8s  %s" % ("group", "n", "CPU s", "kernel s", "peak GB", "failed"))
    for g, G in groups.items():
        print("%-34s %5d %10.1f %10.1f %8.2f  %s" % (g, G["n"], G["cpu_s"], G["kernel_s"], G["peak_gb"],
                                                    ",".join(G["failed"])))
    print()
    for r in rows:
        if r["states"]:
            print("%-14s %-22s states %-5s exit %s  cpu %7.1f  kernel %7s  peak %.2f GB" % (
                r["group"].split()[0], r["name"], r["states"], r["exit"], r["cpu_s"],
                "%.2f" % r["kernel_s"] if r["kernel_s"] is not None else "-", r["peak_gb"]))
    if len(sys.argv) > 3:
        with open(sys.argv[3], "w") as f:
            json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
