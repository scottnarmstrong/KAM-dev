#!/usr/bin/env python3
"""V2-PACKED-JET gate: sum the receipts of the packed sub-segments and compare with the landed range (untrusted
tooling, read-only).

Reads LOGDIR/JSeg_<k>.{cost,out} (one process per sub-segment, `run_probe.sh`), the data-only control JData_0 and
the landed figures of `jet_landed.py` (a JSON file). Prints the packed totals (processes, CPU = user + system,
kernel `type checking`, the largest cgroup charge), the per-heavy-step rates and the ratio to the landed CPU.
Usage: python3 -I scripts/packed/jet_gate_sum.py LOGDIR JetGate.json LANDED.json
"""
import json
import os
import re
import sys


def cost(path):
    kv = {}
    for line in open(path):
        p = line.split()
        if len(p) == 2:
            kv[p[0]] = p[1]
    return kv


def kernel_s(path):
    m = re.findall(r"type checking took ([0-9.]+)(m?s)", open(path).read())
    if not m:
        return None
    v, u = m[-1]
    return float(v) / (1000 if u == "ms" else 1)


def main():
    logs, gate, landed = sys.argv[1], json.load(open(sys.argv[2])), json.load(open(sys.argv[3]))
    rows = []
    for sub in gate["sub_segments"]:
        nm = sub["name"]
        c = cost(os.path.join(logs, nm + ".cost"))
        rows.append(dict(name=nm, heavy=sub["heavy"], imports=sub["imports"], exports=sub["exports"],
                         exit=int(c["exit"]), oom=int(c.get("oom_kill", 0)),
                         cpu=float(c["user_s"]) + float(c["sys_s"]), wall=float(c["wall_s"]),
                         kernel=kernel_s(os.path.join(logs, nm + ".out")),
                         peak=int(c["cgroup_sampled_peak_bytes"])))
    ok = all(r["exit"] == 0 and r["oom"] == 0 and r["kernel"] is not None for r in rows)
    data = cost(os.path.join(logs, "JData_0.cost"))
    cpu = sum(r["cpu"] for r in rows)
    ker = sum(r["kernel"] or 0 for r in rows)
    heavy = sum(r["heavy"] for r in rows)
    out = dict(all_pass=ok, processes=len(rows), cpu_s=round(cpu, 1), kernel_s=round(ker, 1),
               wall_s=round(sum(r["wall"] for r in rows), 1), max_charged_bytes=max(r["peak"] for r in rows),
               heavy_steps=heavy, kernel_s_per_heavy=round(ker / heavy, 2), cpu_s_per_heavy=round(cpu / heavy, 2),
               data_control_JData_0=dict(cpu_s=round(float(data["user_s"]) + float(data["sys_s"]), 1),
                                         peak=int(data["cgroup_sampled_peak_bytes"])),
               landed_cpu_s=landed["cpu_s"], landed_modules=landed["modules"],
               landed_max_charged_bytes=landed["max_charged_bytes"],
               ratio_landed_over_packed=round(landed["cpu_s"] / cpu, 1), rows=rows)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
