#!/usr/bin/env python3
"""V2-PACKED-PROD-TPP (untrusted tooling, read-only): LG00's run18 ledger by tree and class, last run per module.

For each class (`Low`, `Full`, `Data`) of the trees `TP` (T′) and `TPP` (T″): the modules, the successful ones and
their CPU-s (user + sys); and, for T″, the same modules' CPU-s in T′ (matched by name), with their ratio. run18 was
stopped on 1 Nov (owner decision: LG00 goes by the packed route), so T″ is partial.
Usage: python3 -I scripts/packed/run18_cmp.py LEDGER.tsv      (e.g. ~/kam-data/lg00/run18/ledger.tsv)
"""
import json
import sys


def main():
    last = {}
    for line in open(sys.argv[1]):
        p = line.rstrip("\n").split("\t")
        if len(p) >= 7:
            last[p[0]] = p
    cpu = lambda r: float(r[1]) + float(r[2])
    out = {}
    for cls in ("Low", "Full", "Data"):
        tree = {t: {k[len("LG00.%s." % t):]: v for k, v in last.items() if k.startswith("LG00.%s.%s." % (t, cls))}
                for t in ("TP", "TPP")}
        ok = {t: {k: v for k, v in tree[t].items() if v[6] == "0"} for t in tree}
        both = [k for k in ok["TPP"] if k in ok["TP"]]
        out[cls] = dict(
            tp_modules=len(tree["TP"]), tp_ok=len(ok["TP"]), tp_cpu_s=round(sum(map(cpu, ok["TP"].values())), 1),
            tpp_modules=len(tree["TPP"]), tpp_ok=len(ok["TPP"]),
            tpp_cpu_s=round(sum(map(cpu, ok["TPP"].values())), 1), matched=len(both),
            matched_tpp_cpu_s=round(sum(cpu(ok["TPP"][k]) for k in both), 1),
            matched_tp_cpu_s=round(sum(cpu(ok["TP"][k]) for k in both), 1))
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
