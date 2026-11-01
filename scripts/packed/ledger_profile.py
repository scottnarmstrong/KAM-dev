#!/usr/bin/env python3
"""V2-PACKED: kernel-cost profile of a certificate shard-run ledger (untrusted tooling, read-only).

Reads an LG00-style ledger (module, user s, system s, wall, max RSS kB, charged peak bytes, exit) and the generated
theorem modules' `Pieces:` docstrings, and prints
  1. user time, max RSS and charged peak by module family;
  2. a non-negative least-squares attribution of the theorem modules' user time to piece kinds, with the import
     baseline fixed per module (default 2.0 s, the measured import-only control);
  3. per-piece medians from modules that contain a single piece kind (a model-free cross-check);
  4. the packed-product census of the advice books (`PackedAdvice` records): count, dense lengths, widths, factor
     bits and product slots.
Usage: python3 ledger_profile.py LEDGER.tsv CERT_DIR [BASE_SECONDS]
  e.g. python3 ledger_profile.py .../LG00-CERT-ledger/run20e.tsv /home/scott/KAM-dev-worktrees/lg00-cert/KAM/LG00Cert
"""
import collections
import os
import re
import statistics
import sys

import numpy as np


def ledger(path):
    rows = {}
    for line in open(path):
        p = line.rstrip("\n").split("\t")
        if len(p) >= 7:
            rows[p[0]] = (float(p[1]), float(p[2]), int(p[4]) * 1000, int(p[5]))
    return rows


def family(mod):
    return ".".join(re.sub(r"\d+", "#", t) for t in mod.split(".")[2:4])


def pieces(cert_dir, prefix):
    out = {}
    for d in ("Low", "Full", "Torsion", "Gram"):
        dd = os.path.join(cert_dir, d)
        if not os.path.isdir(dd):
            continue
        for fn in os.listdir(dd):
            if not re.match(r"T\d+\.lean$", fn):
                continue
            m = re.search(r"Pieces:(.*?)-/", open(os.path.join(dd, fn)).read(), re.S)
            if m:
                out["%s.%s.%s" % (prefix, d, fn[:-5])] = collections.Counter(
                    k for _, k in re.findall(r"(\w+) \((\w+)\)", m.group(1)))
    return out


def nnls(A, b):
    active = list(range(A.shape[1]))
    while True:
        x = np.zeros(A.shape[1])
        x[active] = np.linalg.lstsq(A[:, active], b, rcond=None)[0]
        neg = [i for i in active if x[i] < 0]
        if not neg:
            return x
        active.remove(min(neg, key=lambda i: x[i]))


def advice_census(cert_dir):
    txt = []
    dd = os.path.join(cert_dir, "Data")
    for fn in sorted(os.listdir(dd)):
        if fn.endswith(".lean"):
            txt.append(open(os.path.join(dd, fn)).read())
    lay = r"⟨\[(.*?)\], \[(.*?)\], \[(.*?)\], (\d+), (\d+)⟩"
    recs = re.findall(r": PackedAdvice where\s+la := " + lay + r"\s+lb := " + lay, "\n".join(txt))
    out = []
    for r in recs:
        da = [int(x) for x in r[1].split(",")]
        sa = [int(x) for x in r[2].split(",")]
        db = [int(x) for x in r[6].split(",")]
        na = 1 + sum((a - 1) * s for a, s in zip(da, sa))
        nb = 1 + sum((a - 1) * s for a, s in zip(db, sa))
        out.append((na, nb, int(r[3])))
    return out


def main():
    led = ledger(sys.argv[1])
    cert = sys.argv[2]
    base = float(sys.argv[3]) if len(sys.argv) > 3 else 2.0
    prefix = "KAM.LG00Cert"
    tu = sum(v[0] for v in led.values())
    ts = sum(v[1] for v in led.values())
    print("modules %d; user %.2f h, system %.2f h; max RSS %.2f GB; max charged %.2f GB" % (
        len(led), tu / 3600, ts / 3600, max(v[2] for v in led.values()) / 1e9,
        max(v[3] for v in led.values()) / 1e9))
    fam = collections.defaultdict(lambda: [0, 0.0, 0, 0])
    for m, v in led.items():
        f = fam[family(m)]
        f[0] += 1
        f[1] += v[0]
        f[2] = max(f[2], v[2])
        f[3] = max(f[3], v[3])
    print("\n%-22s %6s %9s %6s %8s %8s" % ("family", "mods", "user h", "%", "maxRSS", "maxChg"))
    for k, f in sorted(fam.items(), key=lambda x: -x[1][1])[:14]:
        print("%-22s %6d %9.2f %6.1f %8.2f %8.2f" % (k, f[0], f[1] / 3600, 100 * f[1] / tu, f[2] / 1e9,
                                                   f[3] / 1e9))
    pcs = {m: c for m, c in pieces(cert, prefix).items() if m in led}
    kinds = sorted({k for c in pcs.values() for k in c})
    names = list(pcs)
    A = np.array([[pcs[m].get(k, 0) for k in kinds] for m in names], float)
    b = np.array([led[m][0] - base for m in names])
    x = nnls(A, b)
    tt = sum(led[m][0] for m in names)
    print("\nattribution of %d theorem modules (%.2f h user), import base %.1f s/module:" % (
        len(names), tt / 3600, base))
    for i, k in enumerate(kinds):
        n = A[:, i].sum()
        if n and x[i] > 0:
            print("  %-10s %7.2f s x %5d = %6.2f h (%4.1f%%)" % (k, x[i], n, x[i] * n / 3600,
                                                              100 * x[i] * n / tt))
    print("  %-10s %7.2f s x %5d = %6.2f h (%4.1f%%)" % ("import", base, len(names), base * len(names) / 3600,
                                                      100 * base * len(names) / tt))
    print("\nsingle-kind modules (user s per piece, import included):")
    for k in ("segment", "group", "chunk"):
        per = [led[m][0] / pcs[m][k] for m in names if set(pcs[m]) == {k}]
        if per:
            print("  %-8s n=%4d median %.1f s, p10 %.1f, p90 %.1f" % (
                k, len(per), statistics.median(per), sorted(per)[len(per) // 10],
                sorted(per)[9 * len(per) // 10]))
    adv = advice_census(cert)
    if adv:
        bits = sum((a + b) * w for a, b, w in adv)
        slots = sum(a + b - 1 for a, b, _ in adv)
        big = max(adv, key=lambda t: t[0] + t[1])
        print("\nadvice census: %d real packed products; factor bits %.3g; product slots %.3g; widths %d-%d;"
              " median product length %d; largest %d x %d slots at %d bits" % (
                  len(adv), bits, slots, min(t[2] for t in adv), max(t[2] for t in adv),
                  statistics.median(a + b - 1 for a, b, _ in adv), big[0], big[1], big[2]))
        print("GMP multiply time of every factor pair at 6.6 ns per factor bit: %.1f s" % (bits * 6.6e-9))


if __name__ == "__main__":
    main()
