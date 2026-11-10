#!/usr/bin/env python3
"""MAG5 dry check (untrusted tooling): no generated module outside a product's own modules may evaluate a product's
full remainder bound.

    python3 mag_consumer_scan.py ROOT

Scans ROOT/KAM/Magnetic/Data/Mag/Seg/**.lean and lists every module that mentions a product equation `magM<k>`
(the bare theorem, not `magM<k>_lit`, `magM<k>T…`, `magM<k>A<n>`, …), `remainderBound` or `maxSlotDeg`, outside

  Prod/M<k>.lean, Prod/M<k>Aux<n>.lean     the product assembly and its side checks (never evaluate the bound)
  Prod/M<k>Rem*.lean                       the slot-range literal of the bound (RemSplit.lean) and `magM<k>_lit`
  Prod/M<k>Dec*.lean                       the decode (only `(targetTerms, remainderBound …).1`, a projection)

A consumer must use `magM<k>_lit` (the bound as a literal). Exit status 1 if any module is listed.
"""
import os
import re
import sys

ALLOWED = re.compile(r"^Prod/M\d+(Aux\d+|Rem(A|R\d+)?|Dec(P\d+|W)?)?\.lean$")
BARE = re.compile(r"\bmagM\d+\b(?![_T])")
BOUND = re.compile(r"\b(remainderBound|maxSlotDeg)\b")
DEC_PROJ = re.compile(r"\(\S+\.targetTerms, \S+\.remainderBound \S+ \(2 \* \d+\)\)\.1")


def main(root):
    seg = os.path.join(root, "KAM", "Magnetic", "Data", "Mag", "Seg")
    bad = []
    for d, _, fs in os.walk(seg):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(d, f), seg)
            if ALLOWED.match(rel):
                continue
            t = " ".join(open(os.path.join(d, f)).read().split())
            t = DEC_PROJ.sub("", t)
            why = sorted(set(BARE.findall(t)) | set(BOUND.findall(t)))
            if why:
                bad.append((rel, why[:4]))
    for rel, why in sorted(bad):
        print("%s: %s" % (rel, " ".join(why)))
    print("consumer scan: %d module(s) evaluate a full product bound outside the product's own modules" % len(bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
