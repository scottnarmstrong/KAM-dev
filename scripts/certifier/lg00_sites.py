#!/usr/bin/env python3
"""V2-SITES-SIGN: certified small-divisor sites of LG00 T' (exact energy) and the resulting route-A thresholds.

Untrusted tooling.  For each site of the schedule (delta_s, b_s; kp = 3) this computes the bite witness of `biteOk` on the
short reflected box of `routeARefinedS` with the exact mirror (bite_sign.py): the cut-off l, E1, an upper bound B of
`balBound` and the constant c, all rationals, nothing float.  Then the exact route-A mirror (v2_r2.max_Xs) gives the
threshold with those constants, for every choice of the certified sites.

Reads docs/campaign/studies/v2-sites-data/dry_tp_L20.json (LG00-T2's dry run) and the box from the LG00 worktree.

Usage: python3 -B -I scripts/certifier/lg00_sites.py [--json OUT] [--lean DIR]
"""
import itertools, json, math, os, sys, time
from fractions import Fraction as F

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts", "apost_sharp"))
import bite_sign as BS            # noqa: E402
import structured_b as SB         # noqa: E402

TP = os.path.join(ROOT, "docs/campaign/studies/v2-sites-data/dry_tp_L20.json")
Q_BITS = 48                       # the short box: centre and radius at 2^-48
J, KP = 8, 3


def package():
    """T' parameters and claim, on the box of `lg00_gen.freq_box`."""
    B = SB.lg00_bounds()
    rep = json.load(open(TP))
    q = {k: F(v) for k, v in rep["params"].items()}
    B = dict(B, claim={k: F(v) for k, v in rep["claim"].items()}, params=rep["params"])
    pkg = SB.lg00_pkg(B)
    pkg["p"] = dict(q, tau=1, kappa=F(160000))
    return pkg


def schedule(p):
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    out = {}
    for s in range(KP):
        out[("d", s)] = F(1, 2) ** s * d0
        out[("b", s)] = min(p["rho"] - 6 * d0 * (1 - F(1, 2) ** s), F(1))
    return out


def short_box(box):
    """The reflected box of the sites: fibre centre and radius dyadic, the clock exact.  Returns (bw, kappa, c', r')."""
    c0, r0 = box[0]
    k0, kr = box[1]
    assert kr == 0 and k0 != 0
    neg = k0 < 0
    kap = abs(k0)
    cc = (-c0 if neg else c0) / kap
    C = round(cc * 2 ** Q_BITS)
    cs, rs = F(C, 2 ** Q_BITS), F(1, 2 ** (Q_BITS - 1))
    bw = [(cs * kap, rs * kap), (kap, F(0))]
    cover = abs(bw[0][0] - (-c0 if neg else c0)) + r0 <= bw[0][1] and bw[1] == (kap, F(0))
    assert cover
    return neg, bw, kap, cs, rs


def site_table(b, kap, gamma, cs, rs, lmin=6, lmax=15):
    """B and c at each cut-off; the least l whose c is within 0.5 % of the limit."""
    E1 = BS.E1_of(2 * b, J)
    rows = []
    for l in range(lmin, lmax + 1):
        d = BS.Data(cs, rs, gamma / kap, 2 * b, l, J, E1)
        if d.cLo() <= 0:
            continue
        v = d.bal_up()[0]
        B = BS.up_digits(v, 7)
        c = BS.c_of(B, kap, gamma, b)
        rows.append(dict(l=l, ok=d.check(), B=B, c=c, tail=float(d.tailBound() / v)))
    return E1, rows


def main():
    pkg = package()
    p, box = pkg["p"], pkg["box"]
    neg, bw, kap, cs, rs = short_box(box)
    gamma = p["gamma"]
    print("neg %s  kappa %.12f  gamma/kappa %s  fibre centre %.15f  radius 2^-%d" % (neg, float(kap), gamma / kap, float(cs), Q_BITS - 1))
    print("coverOk holds: |bw centre - reflected centre| + r <= bw radius")
    sch = schedule(p)
    clas = SB.classical_sites(p, KP)
    res, choice = {}, {}
    for key, b in sch.items():
        t = time.time()
        E1, rows = site_table(b, kap, gamma, cs, rs)
        best = min(r["c"] for r in rows if r["ok"])
        pick = next(r for r in rows if r["ok"] and r["c"] <= best * F(1005, 1000))
        choice[key] = dict(pick, E1=E1, b=b)
        print("%s%d b %.6e E1 %s classical %.5f: " % (key[0], key[1], float(b), E1, float(clas[key])) + "  ".join(
            "l%d %.5f%s" % (r["l"], float(r["c"]), "" if r["ok"] else "!") for r in rows) + "  -> l=%d c=%s (%.3fs)" % (
                pick["l"], pick["c"], time.time() - t), flush=True)
    keys = list(sch)
    errL = json.load(open(TP))["params"]["err"]
    lerr = math.log10(F(errL))
    rows = []
    for r in range(len(keys) + 1):
        for sub in itertools.combinations(keys, r):
            sites = dict(clas)
            for k in sub:
                sites[k] = choice[k]["c"]
            le = SB.route_a(pkg, sites)
            rows.append(dict(sub=["%s%d" % k for k in sub], log10_e=le, margin=10 ** (le - lerr), lmax=max([choice[k]["l"] for k in sub] + [0]),
                             cost=sum(2 ** choice[k]["l"] for k in sub)))
    rows.sort(key=lambda r: (-r["log10_e"]))
    print("-- route A refined, certified sites (exact mirror); log10 err at L = 20 %.3f" % lerr)
    for r in rows[:14]:
        print("  %-30s log10 e* %8.3f  margin %8.1f  largest l %2d  modes %6d" % (",".join(r["sub"]) or "(classical)", r["log10_e"], r["margin"], r["lmax"], 2 * r["cost"]))
    best_by_l = {}
    for r in rows:
        if r["lmax"] not in best_by_l or r["log10_e"] > best_by_l[r["lmax"]]["log10_e"]:
            best_by_l[r["lmax"]] = r
    print("-- best by largest l")
    for l in sorted(best_by_l):
        r = best_by_l[l]
        print("  l<=%2d  %-30s log10 e* %8.3f  margin %8.1f" % (l, ",".join(r["sub"]) or "(classical)", r["log10_e"], r["margin"]))
    out = dict(neg=neg, kappa=str(kap), q=Q_BITS, bw=[[str(a), str(b)] for a, b in bw], sites={"%s%d" % k: {a: str(b) for a, b in v.items()} for k, v in choice.items()},
               configs=rows, classical={"%s%d" % k: str(v) for k, v in clas.items()})
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=str)
    return 0


if __name__ == "__main__":
    sys.exit(main())
