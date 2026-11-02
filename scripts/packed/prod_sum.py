#!/usr/bin/env python3
"""V2-PACKED-PROD (untrusted tooling, read-only): sum the receipts of a production build (`run_module.sh`'s
LOGDIR/<module>.cost) by module class: the shared certificate data, the jet bridge, and per chain the book, the
ledger parts, the chain data, the block theorems and the chain theorem.
Usage: python3 -I scripts/packed/prod_sum.py MODULES.txt LOGDIR [MODULES.txt LOGDIR ...]
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


def klass(m):
    for pat, k in ((r"\.Jet\.\w+\.Led\d+$", "ledger"), (r"\.Jet\.\w+\.B\d+$", "blocks"), (r"\.Jet\.\w+\.Book$", "book"),
                   (r"\.Jet\.\w+\.Data$", "data"), (r"\.Jet\.\w+\.Chain$", "chain"),
                   (r"\.Jet\.\w+\.ChainCert$", "chain_cert"), (r"\.JetBridge$", "bridge")):
        if re.search(pat, m):
            return k
    return "cert_data"


def main():
    a = sys.argv[1:]
    rows = []
    for lst, logs in zip(a[0::2], a[1::2]):
        for m in open(lst).read().split():
            p = os.path.join(logs, m + ".cost")
            if not os.path.exists(p):
                rows.append(dict(module=m, missing=True))
                continue
            c = cost(p)
            rows.append(dict(module=m, klass=klass(m), exit=int(c.get("exit", -1)), oom=int(c.get("oom_kill", 0)),
                             cpu=float(c["user_s"]) + float(c["sys_s"]), user=float(c["user_s"]),
                             wall=float(c["wall_s"]), peak=int(c["cgroup_sampled_peak_bytes"])))
    ok = [r for r in rows if not r.get("missing")]
    by = {}
    for r in ok:
        b = by.setdefault(r["klass"], dict(modules=0, cpu_s=0.0, wall_s=0.0, max_charged_bytes=0))
        b["modules"] += 1
        b["cpu_s"] += r["cpu"]
        b["wall_s"] += r["wall"]
        b["max_charged_bytes"] = max(b["max_charged_bytes"], r["peak"])
    for b in by.values():  # rounded once, at the end (AUDIT-V2-PACKED-PROD-1 N1)
        b["cpu_s"], b["wall_s"] = round(b["cpu_s"], 1), round(b["wall_s"], 1)
    out = dict(modules=len(rows), missing=[r["module"] for r in rows if r.get("missing")],
               all_pass=all(r["exit"] == 0 and r["oom"] == 0 for r in ok) and len(ok) == len(rows),
               cpu_s=round(sum(r["cpu"] for r in ok), 1), wall_s=round(sum(r["wall"] for r in ok), 1),
               max_charged_bytes=max(r["peak"] for r in ok), by_class=by,
               largest=sorted(({"module": r["module"], "peak": r["peak"], "cpu": r["cpu"]} for r in ok),
                              key=lambda r: -r["peak"])[:5], rows=ok)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
