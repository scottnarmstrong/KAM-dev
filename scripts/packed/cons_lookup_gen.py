#!/usr/bin/env python3
"""V2-PACKED-CONS-LOOKUP (untrusted tooling): the kernel cost of the consumers' jet-slot reads on the whole ledgers.

The consumers read a jet slot through `jetSlots jd`: `jetNode jd i`, `jetRad jd i` and `jetNb jd i` are each
`(jd.led i).…`, and `jd.led i` is a `List.lookup` of `slotK i` on the chain's whole ledger (`JLedger`). The gate
(`cons_gate_gen.py`) used a ledger of the wanted slots only. This script writes, into the T′ package, A/B twins
of the consumer probes that read jet slots, one on kamx-packed's whole ledger (R: `LG00C.TP.jdLow`/`jdFull`,
copied from its package) and one on the wanted-only ledger (W: `LG00C.TP.Cons.jdLow`/`jdFull`), as fresh modules
measured in the same session:
  - LKXN00{R,W}: the X_N stage entry (0, 0) (reads `DX_H ∘ K`: 16 torsion slots);
  - LKY{R,W}: the averages of Y (reads `DH ∘ K`: 4 slots);
  - LKIV1{R,W}: invariance coordinate 1 (1 `d1` slot); LKEN{R,W}: the energy (`v0`);
  - LKLowLook{R,W}, LKFullLook{R,W}: every wanted slot's radius and norm bound (the lookups alone);
  - LKLowRead{R,W}, LKFullRead{R,W}: the same plus the packed value (the lookups and the node ingestion);
  - LKData{R,W}: the imports alone.
Writes PKG/LG00C/TP/Cons/L/<probe>.lean and PKG/cons_lookup_plan.json.
Usage: python3 -I scripts/packed/cons_lookup_gen.py [--pkg=DIR]
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
PKG = next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--pkg=")),
           os.path.join(ROOT, ".lake", "v2-packed-cons", "pkg"))
PRE = "LG00C"
P = os.path.join(PKG, PRE, "TP", "Cons", "P")
OUT = os.path.join(PKG, PRE, "TP", "Cons", "L")
LOW, FULL = "%s.TP.Jet.Low.Data" % PRE, "%s.TP.Jet.Full.Data" % PRE
QL = {"R": ("%s.TP.jdLow" % PRE, "%s.TP.jdFull" % PRE), "W": ("%s.TP.Cons.jdLow" % PRE, "%s.TP.Cons.jdFull" % PRE)}


def twin(src, name, ab):
    """A probe file renamed, with the jet's `JetData` qualified (R: the whole ledger, imported; W: wanted only)."""
    s = open(os.path.join(P, src + ".lean")).read()
    low, full = QL[ab]
    s = re.sub(r"\bjdLow\b", low, s)
    s = re.sub(r"\bjdFull\b", full, s)
    s = s.replace("namespace %s.TP.Cons.P.%s" % (PRE, src), "namespace %s.TP.Cons.L.%s" % (PRE, name))
    s = s.replace("end %s.TP.Cons.P.%s" % (PRE, src), "end %s.TP.Cons.L.%s" % (PRE, name))
    s = s.replace("probe `%s`" % src, "probe `%s` (V2-PACKED-CONS-LOOKUP twin of `%s`)" % (name, src))
    if ab == "R":
        imp = [LOW] + ([FULL] if "jdFull" in s else [])
        s = s.replace("\npublic import", "\n" + "".join("public import %s\n" % i for i in imp) + "public import", 1)
    return s


HEAD = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

%s

/-!
# V2-PACKED-CONS-LOOKUP probe `%s` (generated; opt-in)

%s
-/

@[expose] public noncomputable section

namespace %s.TP.Cons.L.%s

open KAM KAM.Certificate KAM.CertificateSharp.Packed

set_option profiler true
set_option profiler.threshold 1

theorem probe :
    %s := by
  decide +kernel

end %s.TP.Cons.L.%s
"""


def reads(name, ab, chain, value, doc):
    low, full = QL[ab]
    jd = low if chain == "Low" else full
    ws = "torsionSlots 2 %s.lg00Jet" % PRE if chain == "Low" else "(%s.lg00Jet.v0 :: d1Slots 2 %s.lg00Jet)" % (PRE, PRE)
    js = "(jetSlots (α := %s.LGF) %s)" % (PRE, jd)
    body = "decide (0 ≤ (%s.r i).m) && decide (0 ≤ (%s.nb i).m)" % (js, js)
    if value:
        body += " && decide ((%s.x i).re ≠ 7)" % js
    st = "(%s).all (fun i => %s) = true" % (ws, body)
    imp = ["%s.TP.Cons.Jet%s" % (PRE, chain)] + ([LOW if chain == "Low" else FULL] if ab == "R" else [])
    return HEAD % ("\n".join("public import %s" % i for i in imp), name, doc, PRE, name, st, PRE, name)


def data(name, ab):
    imp = ["%s.TP.Cons.Nodes" % PRE, "%s.TP.Cons.JetLow" % PRE, "%s.TP.Cons.JetFull" % PRE]
    if ab == "R":
        imp += [LOW, FULL]
    return HEAD % ("\n".join("public import %s" % i for i in imp), name,
                   "Data-only control: the imports of the %s probes." % ab, PRE, name, "True", PRE, name)


def main():
    os.makedirs(OUT, exist_ok=True)
    plan = []

    def put(name, txt):
        with open(os.path.join(OUT, name + ".lean"), "w") as f:
            f.write(txt)
        plan.append("%s.TP.Cons.L.%s" % (PRE, name))
    for ab in ("W", "R"):
        put("LKData" + ab, data("LKData" + ab, ab))
        for src, nm in (("TJStXN_0_0", "LKXN00"), ("TJY", "LKY"), ("IVRow_1", "LKIV1"), ("ENOk", "LKEN")):
            put(nm + ab, twin(src, nm + ab, ab))
        for chain in ("Low", "Full"):
            put("LK%sLook%s" % (chain, ab), reads("LK%sLook%s" % (chain, ab), ab, chain, False,
                                                 "Every wanted %s slot's radius and norm bound through `jetSlots` (%s "
                                                 "ledger): the lookups alone." % (chain, "whole" if ab == "R" else
                                                                                  "wanted-only")))
            put("LK%sRead%s" % (chain, ab), reads("LK%sRead%s" % (chain, ab), ab, chain, True,
                                                 "Every wanted %s slot's value, radius and norm bound through `jetSlots` "
                                                 "(%s ledger): the lookups and the node ingestion." % (
                                                     chain, "whole" if ab == "R" else "wanted-only")))
    with open(os.path.join(PKG, "cons_lookup_plan.json"), "w") as f:
        json.dump(dict(probes=plan), f, indent=1)
    print(len(plan), "probes")


if __name__ == "__main__":
    main()
