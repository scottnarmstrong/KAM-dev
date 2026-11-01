#!/usr/bin/env python3
"""V2-PACKED-JET-LOW: sum the receipts of the packed Low chain and compare with the landed Low stage (untrusted
tooling, read-only).

Reads LowPlan.json (the blocks), LOGDIR/<block>.{cost,out} (one process per checked block, `run_probe.sh`) and the
run20e ledger with lg00-cert's Low modules: the landed Low stage by segment kind (regular, product, character `X`,
`inv` `I`, `sqrt` `Q`; a module's cost split over its pieces) and its literal modules.
The stage (Low or Full) is the basename of LOW_DIR (lg00-cert's `KAM/LG00Cert/Low` or `…/Full`). The ledger keeps
retried runs (the last column is the exit code); the landed figure counts each module's last, successful run, and
`landed_cpu_s_with_retries` adds the failed attempts.
Usage: python3 -I scripts/packed/jet_low_sum.py LowPlan.json LOGDIR LEDGER.tsv LOW_DIR PLANS.json
"""
import collections
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


def landed(led, low, plans):
    stage = os.path.basename(os.path.normpath(low))
    rows, retries = {}, 0.0
    for line in open(led):
        p = line.rstrip("\n").split("\t")
        if len(p) >= 7:
            if p[0] in rows and p[0].startswith("KAM.LG00Cert.%s." % stage):
                retries += rows[p[0]]
            rows[p[0]] = float(p[1]) + float(p[2])
    segs = json.load(open(plans))["cfg" + stage]["segs"]
    by, lit = collections.Counter(), collections.Counter()
    for fn in os.listdir(low):
        mod = "KAM.LG00Cert.%s." % stage + fn[:-5]
        if mod not in rows:
            continue
        if not fn.startswith("T"):
            lit[re.sub(r"\d+", "", fn[:-5])] += rows[mod]
            continue
        m = re.search(r"Pieces:(.*?)-/", open(os.path.join(low, fn)).read(), re.S)
        ps = re.findall(r"([A-Za-z]+)(\d+)((?:_\d+)*) \((\w+)\)", m.group(1)) if m else []
        for p in ps:
            by[segs[int(p[1])]["kind"]] += rows[mod] / len(ps)
    return by, lit, retries


def main():
    plan, logs = json.load(open(sys.argv[1])), sys.argv[2]
    by, lit, retries = landed(*sys.argv[3:6])
    rows = []
    for b in plan["blocks"]:
        if b["kind"] == "given":
            continue
        nm = b["name"]
        c = cost(os.path.join(logs, nm + ".cost"))
        rows.append(dict(name=nm, kind=b["kind"], heavy=b.get("heavy", 0), exit=int(c["exit"]),
                         oom=int(c.get("oom_kill", 0)), cpu=float(c["user_s"]) + float(c["sys_s"]),
                         wall=float(c["wall_s"]), kernel=kernel_s(os.path.join(logs, nm + ".out")),
                         peak=int(c["cgroup_sampled_peak_bytes"])))
    ok = all(r["exit"] == 0 and r["oom"] == 0 and r["kernel"] is not None for r in rows)
    cpu = sum(r["cpu"] for r in rows)
    land_all = sum(by.values()) + sum(lit.values())
    land_given = by.get("X", 0) + by.get("I", 0) + by.get("Q", 0)
    out = dict(all_pass=ok, processes=len(rows), cpu_s=round(cpu, 1),
               kernel_s=round(sum(r["kernel"] or 0 for r in rows), 1),
               wall_s=round(sum(r["wall"] for r in rows), 1), max_charged_bytes=max(r["peak"] for r in rows),
               heavy_steps=sum(r["heavy"] for r in rows),
               max_heavy_per_process=max(r["heavy"] for r in rows),
               landed_low_cpu_s=round(land_all, 1), landed_by_kind={k: round(v, 1) for k, v in by.items()},
               landed_cpu_s_with_retries=round(land_all + retries, 1),
               ratio_with_retries=round((land_all + retries) / cpu, 1),
               landed_literal_cpu_s=round(sum(lit.values()), 1),
               landed_given_cpu_s=round(land_given, 1),
               landed_without_given_cpu_s=round(land_all - land_given, 1),
               ratio_without_given=round((land_all - land_given) / cpu, 1),
               ratio_full=round(land_all / cpu, 1),
               by_kind={k: dict(processes=sum(1 for r in rows if r["kind"] == k),
                                cpu_s=round(sum(r["cpu"] for r in rows if r["kind"] == k), 1),
                                kernel_s=round(sum(r["kernel"] or 0 for r in rows if r["kind"] == k), 1),
                                max_charged_bytes=max(r["peak"] for r in rows if r["kind"] == k))
                        for k in sorted({r["kind"] for r in rows})},
               rows=rows)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
