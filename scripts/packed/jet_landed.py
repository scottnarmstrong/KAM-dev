#!/usr/bin/env python3
"""V2-PACKED-JET gate: the landed cost of a cfgLow slot range of LG00 (untrusted tooling, read-only).

The landed `Low` stage proves the chain segment by segment (`ComposeCkpt.segOk`), in theorem modules `Low.T<i>`
whose docstrings list their pieces by segment index (`S<k>` regular segment, `Sv<k>`, `Gp<k>_..` product shard
group, `Cp<k>_..` chunk, `Rp<k>_..` part, `Hp<k>_..` head, `Cvp<k>_..` decide). The segments of the range are
those of the plan (`plans.json`, cfgLow) inside [START, STOP). A module counts in full when all its pieces are in
the range, and pro rata by piece count otherwise. Costs are user + system seconds of the final shard run's ledger
(`run20e.tsv`, last row per module, as `ledger_profile.py`). The literal modules (ledger `L`, product data `D`, ...)
are reported for the whole stage, not attributed.
Usage: python3 -I scripts/packed/jet_landed.py LEDGER.tsv LOW_DIR PLANS.json START STOP
"""
import collections
import json
import os
import re
import sys


def main():
    led, low, plans, start, stop = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
    rows = {}
    for line in open(led):
        p = line.rstrip("\n").split("\t")
        if len(p) >= 7:
            rows[p[0]] = (float(p[1]) + float(p[2]), float(p[1]), int(p[5]))
    segs = json.load(open(plans))["cfgLow"]["segs"]
    idx = {i for i, s in enumerate(segs) if start <= s["start"] and s["stop"] <= stop}
    full, part, pieces = 0.0, 0.0, collections.Counter()
    mods, peak, n_full, n_mixed = [], 0, 0, 0
    lit = collections.Counter()
    for fn in sorted(os.listdir(low)):
        m0 = re.match(r"([A-Z]+)(\d*)\.lean$", fn)
        if not m0:
            continue
        mod = "KAM.LG00Cert.Low." + fn[:-5]
        if m0.group(1) != "T":
            if mod in rows:
                lit[m0.group(1)] += rows[mod][0]
            continue
        txt = open(os.path.join(low, fn)).read()
        m = re.search(r"Pieces:(.*?)-/", txt, re.S)
        if not m:
            continue
        ps = re.findall(r"([A-Za-z]+)(\d+)((?:_\d+)*) \((\w+)\)", m.group(1))
        inr = [p for p in ps if int(p[1]) in idx]
        if not inr or mod not in rows:
            continue
        frac = len(inr) / len(ps)
        cost = rows[mod][0] * frac
        if frac == 1:
            full += cost
            n_full += 1
        else:
            part += cost
            n_mixed += 1
        peak = max(peak, rows[mod][2])
        for p in inr:
            pieces[p[3]] += 1
        mods.append(mod)
    tot_T = sum(v[0] for k, v in rows.items() if k.startswith("KAM.LG00Cert.Low.T"))
    out = dict(range=[start, stop], segments=len(idx),
               segment_kinds=dict(collections.Counter(segs[i]["kind"] for i in idx)),
               modules=len(mods), modules_full=n_full, modules_mixed=n_mixed,
               cpu_s=round(full + part, 1), cpu_s_mixed_share=round(part, 1), max_charged_bytes=peak,
               pieces=dict(pieces), low_T_total_cpu_s=round(tot_T, 1),
               low_literal_modules_cpu_s={k: round(v, 1) for k, v in lit.items()})
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
