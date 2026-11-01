#!/usr/bin/env python3
"""V2-PACKED-GEN: the whole-torus cost table of a packed route against LG00's run ledger (untrusted reporting tool).

Walks the import closure of a target module across the scratch packages (`--pkg DIR` for each package root, in
order), attributes each module's cost to the ledger that built it (`--ledger FILE` for each: the run harness's
`ledger.tsv`, LG00's run ledger, or a kamx-packed summary JSON with `rows`), and prints the totals per stage next to
LG00's own stages of the same tree. A module found in no ledger is listed (cost unknown).
Usage: python3 -I scripts/packed/run_compare.py TARGET --tree TP --pkg DIR... --ledger FILE... --lg00-ledger FILE
"""
import json
import os
import re
import sys

IMP = re.compile(r"^public import (\S+)", re.M)


def opts(name):
    out, args = [], sys.argv
    for i, a in enumerate(args):
        if a == name and i + 1 < len(args):
            out.append(args[i + 1])
    return out


def load_ledger(path):
    rows = {}
    if path.endswith(".json"):
        for r in json.load(open(path))["rows"]:
            rows[r["module"]] = dict(cpu=r["cpu"], peak=r.get("peak", 0) or 0, ok=r["exit"] == 0, reused=False)
        return rows
    for l in open(path):
        f = l.rstrip("\n").split("\t")
        if len(f) < 7:
            continue
        reused = len(f) > 7 and f[7] == "reused"
        peak = int(f[5]) if f[5].isdigit() else 0
        r = dict(cpu=float(f[1]) + float(f[2]) if f[1] not in ("?", "") else 0.0, peak=peak, ok=f[6] == "0",
                 reused=reused)
        if r["ok"] and (not reused or f[0] not in rows):
            rows[f[0]] = r
    return rows


def stage(m, tree):
    p = m.split(".")
    if p[0] == "LG00P" and len(p) > 2 and p[2] == "PK":
        x = p[3] if len(p) > 3 else ""
        return {"TorsJ": "Torsion", "Gram": "Gram", "FramesJ": "Final", "InvJ": "Full", "EnJ": "Full",
                "Front": "Data", "Data": "Data", "HamJet": "Final", "Xfer": "Final", "Asm": "Final",
                "MainJ": "Main"}.get(x, "Final")
    if len(p) > 3 and p[1] == tree and p[2] == "Jet":
        return {"Low": "Low", "Full": "Full"}[p[3]]
    if len(p) > 2 and p[1] == tree:
        return {"Data": "Data", "Balls": "Balls", "Final": "Final", "Low": "Low", "Full": "Full", "Gram": "Gram",
                "Torsion": "Torsion"}.get(p[2], "Final")
    return "Data" if p[1:2] in (["Format"], ["FormatK"], ["FormatQ"], ["Coeffs0"], ["Coeffs1"], ["Ham"]) else "Final"


def main():
    target = sys.argv[1]
    tree = (opts("--tree") or ["TP"])[0]
    pkgs = opts("--pkg")
    ledgers = [load_ledger(p) for p in opts("--ledger")]
    lg00 = load_ledger(opts("--lg00-ledger")[0])

    def src(m):
        for p in pkgs:
            f = os.path.join(p, *m.split(".")) + ".lean"
            if os.path.exists(f):
                return f
        return None
    seen, stack = set(), [target]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        for d in IMP.findall(open(src(m), encoding="utf-8").read()):
            if d.split(".")[0] in ("LG00", "LG00P") and src(d):
                stack.append(d)
    tot, unknown = {}, []
    for m in seen:
        r = None
        for L in ledgers + [lg00]:
            if m in L and not L[m]["reused"]:
                r = L[m]
                break
        st = stage(m, tree)
        t = tot.setdefault(st, dict(n=0, cpu=0.0, peak=0))
        t["n"] += 1
        if r is None:
            unknown.append(m)
            continue
        t["cpu"] += r["cpu"]
        t["peak"] = max(t["peak"], r["peak"])
    base = {}
    for m, r in lg00.items():
        p = m.split(".")
        if len(p) > 2 and p[0] == "LG00" and p[1] == tree:
            b = base.setdefault(p[2] if p[2] in ("Data", "Balls", "Gram", "Torsion", "Low", "Full", "Final")
                                else "Main", dict(n=0, cpu=0.0, peak=0))
            b["n"] += 1
            b["cpu"] += r["cpu"]
            b["peak"] = max(b["peak"], r["peak"])
    order = ["Data", "Balls", "Gram", "Torsion", "Low", "Full", "Final", "Main"]
    print("| stage | LG00 run: modules | CPU-s | peak | packed route: modules | CPU-s | peak | ratio |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|")
    T = dict(bn=0, bc=0.0, n=0, c=0.0)
    for st in order:
        b, t = base.get(st, dict(n=0, cpu=0, peak=0)), tot.get(st, dict(n=0, cpu=0, peak=0))
        ratio = ("%.1f×" % (b["cpu"] / t["cpu"])) if t["cpu"] else "—"
        print("| %s | %d | %.0f | %.2f GB | %d | %.0f | %.2f GB | %s |" % (
            st, b["n"], b["cpu"], b["peak"] / 1e9, t["n"], t["cpu"], t["peak"] / 1e9, ratio))
        T["bn"] += b["n"]; T["bc"] += b["cpu"]; T["n"] += t["n"]; T["c"] += t["cpu"]
    print("| **total** | **%d** | **%.0f** (%.2f CPU-h) | | **%d** | **%.0f** (%.2f CPU-h) | | **%.1f×** |" % (
        T["bn"], T["bc"], T["bc"] / 3600, T["n"], T["c"], T["c"] / 3600, T["bc"] / T["c"] if T["c"] else 0))
    print("modules with no ledger row (cost unknown): %d %s" % (len(unknown), sorted(unknown)[:12]))


if __name__ == "__main__":
    main()
