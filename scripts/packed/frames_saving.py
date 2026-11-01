#!/usr/bin/env python3
"""V2-PACKED-FRAMES: the LG00 end-to-end comparison (untrusted tooling, read-only).

Which landed LG00 modules does the packed route (`checkV2With (torsRBase …) (routeARefinedR …)`) make unnecessary,
and what did they cost in the final shard run?

  - Replaced: the landed modules whose theorems the packed route proves differently, i.e. `Final.Torsion` (the base
    checker's Gram and Torsion sub-checks), `Final.FrameL`, `Final.FrameN`, `Final.FrameT` and `Final.Frames` (the
    route-A-refined frame majorants).
  - Kept: the import closure of `Main` that does not pass through a replaced module, plus every import of a
    replaced module other than the Gram and Torsion stages (`Gram.*`, `Torsion.*`) and the replaced modules
    themselves. This keeps, e.g., the `Low` composition (`Low.T1908`, the torsion slots the packed boundary is
    checked against), the data, `Final.Wit` and `Kernel.StageTwo` (conservative: possibly removable too).
  - Removable = closure(Main) − kept; its cost is the sum of user + system seconds in the ledger (last row of each
    module, as `ledger_profile.py`).
The packed side is summed from the gate receipts (user + system s of each production probe; no control):
  - B2 (Gram): `V2-PACKED-B2-GATE/GramEntry_*` and `GramCore` (9 processes);
  - B3b (torsion): `V2-PACKED-B3B-GATE/entries/*` and `stages/*` (62) and the Gram link of B3,
    `V2-PACKED-B3-GATE/TorsGramVal`, `TorsEps` (2);
  - the frames: `FRL`, `FRN`, `FRT` in FRAMES_LOGS.
Usage: python3 -I scripts/packed/frames_saving.py LEDGER.tsv CERT_DIR STUDIES_DIR FRAMES_LOGS
  e.g. … <lg00-cert>/docs/campaign/handoffs/LG00-CERT-ledger/run20e.tsv <lg00-cert>/KAM/LG00Cert
         docs/campaign/studies docs/campaign/studies/V2-PACKED-FRAMES-GATE/probes
"""
import glob
import json
import os
import re
import sys

PFX = "KAM.LG00Cert"
REPLACED = ["Final.Torsion", "Final.FrameL", "Final.FrameN", "Final.FrameT", "Final.Frames"]
FRAME_PROBES = ["FRL", "FRN", "FRT"]


def ledger(path):
    rows = {}
    for line in open(path):
        p = line.rstrip("\n").split("\t")
        if len(p) >= 7:
            rows[p[0]] = float(p[1]) + float(p[2])
    return rows


def imports(cert):
    g = {}
    for d, _, fs in os.walk(cert):
        for fn in fs:
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(d, fn), cert)[:-5].replace(os.sep, ".")
                txt = open(os.path.join(d, fn), encoding="utf-8").read()
                g[PFX + "." + rel] = [m for m in re.findall(r"^(?:public )?import (\S+)", txt, re.M)
                                      if m.startswith(PFX + ".")]
    return g


def closure(g, roots, stop=()):
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m in seen or m in stop:
            continue
        seen.add(m)
        todo.extend(g.get(m, []))
    return seen


def cost(path):
    kv = {}
    for line in open(path):
        p = line.split()
        if len(p) == 2:
            kv[p[0]] = p[1]
    return float(kv["user_s"]) + float(kv["sys_s"])


def main():
    led, cert, studies, flogs = sys.argv[1:5]
    rows = ledger(led)
    g = imports(cert)
    rep = {PFX + "." + m for m in REPLACED}
    allm = closure(g, [PFX + ".Main"])
    keep_roots = [PFX + ".Main"] + [i for m in rep for i in g[m]
                                     if i not in rep and not re.match(PFX + r"\.(Gram|Torsion)\.", i)]
    kept = closure(g, keep_roots, stop=rep)
    removable = sorted(allm - kept)
    groups = {}
    for m in removable:
        k = m.split(".")[2] if m.split(".")[2] in ("Gram", "Torsion") else m
        groups[k] = groups.get(k, [0, 0.0])
        groups[k][0] += 1
        groups[k][1] += rows.get(m, 0.0)
    missing = [m for m in removable if m not in rows]
    land = sum(rows.get(m, 0.0) for m in removable)
    total = sum(rows.values())
    st = lambda *pats: sorted(f for pat in pats for f in glob.glob(os.path.join(studies, pat)))
    b2f = st("V2-PACKED-B2-GATE/GramEntry_*.cost", "V2-PACKED-B2-GATE/GramCore.cost")
    b3f = st("V2-PACKED-B3B-GATE/entries/*.cost", "V2-PACKED-B3B-GATE/stages/*.cost",
             "V2-PACKED-B3-GATE/TorsGramVal.cost", "V2-PACKED-B3-GATE/TorsEps.cost")
    gram = sum(cost(f) for f in b2f)
    tors = sum(cost(f) for f in b3f)
    fr = {p: cost(os.path.join(flogs, p + ".cost")) for p in FRAME_PROBES}
    packed = gram + tors + sum(fr.values())
    out = dict(lg00_total_cpu_s=round(total, 1), lg00_modules=len(rows), main_closure=len(allm),
               removable_modules=len(removable), removable_cpu_s=round(land, 1),
               removable_groups={k: [v[0], round(v[1], 1)] for k, v in sorted(groups.items())},
               missing_from_ledger=missing,
               packed_processes=dict(gram_B2=len(b2f), torsion_B3b=len(b3f), frames=len(fr)),
               packed_cpu_s=dict(gram_B2=round(gram, 1), torsion_B3b=round(tors, 1), **{k: round(v, 1) for k, v in fr.items()},
                                 total=round(packed, 1)),
               net_saving_cpu_s=round(land - packed, 1),
               net_saving_share_of_lg00=round((land - packed) / total, 4),
               lg00_after_cpu_h=round((total - land + packed) / 3600, 2), lg00_before_cpu_h=round(total / 3600, 2))
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
