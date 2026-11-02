#!/usr/bin/env python3
"""HD11964 phase 2 (COVERLEMMA): the exact rational cover plan of the fitted cells, for the Lean check
`CoverPlan.ok` (untrusted, Apache-2.0).

From `cover2_fit.plan` (same --d, --kappa, --nmult), this builds the rational plan of the cover lemma draft
(`docs/campaign/handoffs/HD11964-COVERLEMMA.md`):
  - slabs [lo, hi] in xi_c (endpoints rounded to 1e-6, consecutive, from 0, the last hi with hi^2 >= 2 Cmax), b's disc
    radius R >= sqrt(2 Cmax - lo^2) (rounded up to 1e-6);
  - cells: Lam centre (Lamlo + Lamhi)/2, half-width (Lamhi - Lamlo)/2 + d (exact); xi_c centre and half-width of the
    slab; eta_c centre 0, half-width 1/500; b frame (a, b) = ((1 - t^2), 2t)/(1 + t^2) (t a rational tan(phi/2), an
    exact rotation), centre (R/2)(a, b), radial half-width R/2, tangential half-width h_t >= tau R / sqrt(1 + tau^2)
    (rounded up to 1e-6), tau the largest |<v, e_t>| / <v, e_r> over the wedge's rays;
  - rays: integer vectors round(1e6 (cos, sin)) at the sector boundaries 2 pi j / n, with (1, 0) and (-1, 0) exact;
    the upper chain runs (1, 0) -> (-1, 0) and the lower (-1, 0) -> (1, 0), a sector straddling (-1, 0) appearing in
    both;
  - a slab whose plan is one square gets a disc cell (frame (1, 0), half-widths >= R).
It checks the conditions of `CoverPlan.ok` in exact rational arithmetic (fractions) and writes the plan as Lean
source (a `def fitPlan : CoverPlan`) and as JSON.

Usage: python3 -I cover2_plan_lean.py OUT.lean OUT.json --d=2e-3 --kappa=0.2 [--nmult=1]
"""
import json
import math
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cover2 as C  # noqa: E402
import cover2_fit as FT  # noqa: E402
import hd11964_model as HM  # noqa: E402

LAMLO = [Fr(116621, 2000000), Fr(4454241, 2500000)]
LAMHI = [Fr(292553, 5000000), Fr(3575393, 2000000)]
CBAR = Fr(1, 100)
Q = 10 ** 6


def up(x):
    return Fr(math.ceil(x * Q - 1e-9), Q) if x >= 0 else -Fr(math.floor(-x * Q + 1e-9), Q)


def near(x):
    return Fr(round(x * Q), Q)


def frame(phi):
    """An exact rational unit vector near (cos phi, sin phi)."""
    phi = math.remainder(phi, 2 * math.pi)
    flip = abs(phi) > math.pi / 2
    if flip:
        phi = math.remainder(phi + math.pi, 2 * math.pi)
    t = near(math.tan(phi / 2))
    a, b = (1 - t * t) / (1 + t * t), 2 * t / (1 + t * t)
    return (-a, -b) if flip else (a, b)


def ray(theta):
    c, s = math.cos(theta), math.sin(theta)
    if abs(s) < 1e-12:
        return (Fr(1 if c > 0 else -1), Fr(0))
    return (Fr(round(c * Q)), Fr(round(s * Q)))


def cross(v, p):
    return v[0] * p[1] - v[1] * p[0]


def rad(k, p):
    return k["a"] * p[0] + k["b"] * p[1]


def tng(k, p):
    return -k["b"] * p[0] + k["a"] * p[1]


def main():
    out_lean, out_json = sys.argv[1], sys.argv[2]
    d = Fr(C.opt("d", "2e-3"))
    cmax = CBAR + 2 * d
    m = HM.Model()
    cells, ivs, _ = FT.plan(m)
    # slabs
    ends = [Fr(0)] + [near(b) for (_, b) in ivs]
    while ends[-1] ** 2 < 2 * cmax:
        ends[-1] += Fr(1, Q)
    slabs = []
    for j, (a, b) in enumerate(ivs):
        lo, hi = ends[j], ends[j + 1]
        R = up(math.sqrt(float(2 * cmax - lo * lo)))
        while R * R < 2 * cmax - lo * lo:
            R += Fr(1, Q)
        cs = [c for c in cells if abs(c["xi"][0] - (a + b) / 2) < 1e-9]
        base_c = [(LAMLO[0] + LAMHI[0]) / 2, (LAMLO[1] + LAMHI[1]) / 2, (lo + hi) / 2, Fr(0)]
        base_h = [(LAMHI[0] - LAMLO[0]) / 2 + d, (LAMHI[1] - LAMLO[1]) / 2 + d, (hi - lo) / 2, Fr(1, 500)]
        if cs[0]["kind"] == "square":
            k = dict(c=base_c + [Fr(0), Fr(0)], h=base_h + [R, R], a=Fr(1), b=Fr(0))
            slabs.append(dict(lo=lo, hi=hi, R=R, disc=k, upper=[], lower=[]))
            continue
        n = len(cs)
        bounds = [2 * math.pi * j2 / n for j2 in range(n)]
        # sector j2 spans [bounds[j2], bounds[j2+1]]; its cell is the plan's cell with phi = 2 pi (j2 + 1/2) / n
        sector_cell = {}
        for c in cs:
            j2 = int(round(c["phi"] * n / (2 * math.pi) - 0.5)) % n
            a_, b_ = frame(c["phi"])
            k = dict(c=base_c + [R / 2 * a_, R / 2 * b_], h=base_h + [R / 2, None], a=a_, b=b_)
            sector_cell[j2] = k
        # chain points: the boundary rays plus (-1, 0) and (1, 0)
        pts = sorted(set([(t, j2) for j2, t in enumerate(bounds)]))
        chain = [(t, ray(t)) for t, _ in pts]
        if all(abs(t - math.pi) > 1e-12 for t, _ in chain):
            chain.append((math.pi, (Fr(-1), Fr(0))))
        chain.sort()
        chain.append((2 * math.pi, (Fr(1), Fr(0))))
        wedges = []
        for (t0, v), (t1, w) in zip(chain[:-1], chain[1:]):
            j2 = int(math.floor((t0 + t1) / 2 * n / (2 * math.pi))) % n
            k = sector_cell[j2]
            tau = max(abs(tng(k, p)) / rad(k, p) for p in (v, w))
            wedges.append(dict(v=v, w=w, cell=j2, tau=tau, upper=t1 <= math.pi + 1e-12))
        # tangential half-width of each cell: the largest over its wedges
        for j2, k in sector_cell.items():
            taus = [x["tau"] for x in wedges if x["cell"] == j2]
            tau = max(taus)
            ht = up(float(tau) * float(R) / math.sqrt(1 + float(tau) ** 2))
            while tau * tau * R * R > (1 + tau * tau) * ht * ht:
                ht += Fr(1, Q)
            k["h"][5] = ht
        up_w = [dict(x, cell=sector_cell[x["cell"]]) for x in wedges if x["upper"]]
        lo_w = [dict(x, cell=sector_cell[x["cell"]]) for x in wedges if not x["upper"]]
        slabs.append(dict(lo=lo, hi=hi, R=R, disc=None, upper=up_w, lower=lo_w))
    # exact check of CoverPlan.ok
    fails = []

    def axes_ok(s, k):
        return (all(x > 0 for x in k["h"]) and k["a"] ** 2 + k["b"] ** 2 == 1
                and all(k["c"][i] - k["h"][i] <= LAMLO[i] - d and LAMHI[i] + d <= k["c"][i] + k["h"][i]
                        for i in range(2))
                and k["c"][2] - k["h"][2] <= s["lo"] and s["hi"] <= k["c"][2] + k["h"][2] and abs(k["c"][3]) <= k["h"][3])

    for si, s in enumerate(slabs):
        if not (0 <= s["lo"] <= s["hi"] and s["R"] >= 0 and 2 * cmax - s["lo"] ** 2 <= s["R"] ** 2):
            fails.append(("slab", si))
        if s["disc"] is not None:
            k = s["disc"]
            cb = (k["c"][4], k["c"][5])
            if not (axes_ok(s, k) and s["R"] + abs(rad(k, cb)) <= k["h"][4] and s["R"] + abs(tng(k, cb)) <= k["h"][5]):
                fails.append(("disc", si))
            continue
        for name, ch, st, sp in (("upper", s["upper"], (1, 0), (-1, 0)), ("lower", s["lower"], (-1, 0), (1, 0))):
            if not ch or ch[0]["v"] != st or ch[-1]["w"] != sp or any(x["w"] != y["v"] for x, y in zip(ch, ch[1:])):
                fails.append(("chain", si, name))
            for x in ch:
                k, v, w, tau = x["cell"], x["v"], x["w"], x["tau"]
                cb = (k["c"][4], k["c"][5])
                ok = (axes_ok(s, k) and cross(v, w) > 0 and tau >= 0 and rad(k, v) >= 0 and rad(k, w) >= 0
                      and abs(tng(k, v)) <= tau * rad(k, v) and abs(tng(k, w)) <= tau * rad(k, w)
                      and rad(k, cb) - k["h"][4] <= 0 and s["R"] <= rad(k, cb) + k["h"][4]
                      and abs(tng(k, cb)) <= k["h"][5]
                      and tau ** 2 * s["R"] ** 2 <= (1 + tau ** 2) * (k["h"][5] - abs(tng(k, cb))) ** 2)
                if not ok:
                    fails.append(("wedge", si, name, x["v"], x["w"]))
    last = slabs[-1]
    if not (slabs[0]["lo"] == 0 and all(a["hi"] == b["lo"] for a, b in zip(slabs, slabs[1:]))
            and last["hi"] >= 0 and 2 * cmax <= last["hi"] ** 2):
        fails.append(("slabs-chain",))
    ncells = sum(1 if s["disc"] else len({id(x["cell"]) for x in s["upper"] + s["lower"]}) for s in slabs)
    nw = sum(len(s["upper"]) + len(s["lower"]) for s in slabs)
    reff = max([float(rad(x["cell"], (x["cell"]["c"][4], x["cell"]["c"][5])) + x["cell"]["h"][4] + x["cell"]["h"][5])
                for s in slabs for x in s["upper"] + s["lower"]] + [0.0])
    print("slabs", len(slabs), "cells", ncells, "wedges", nw, "max rho_eff %.6f" % reff, "exact check:",
          "OK" if not fails else fails)

    # Lean source
    def q(x):
        x = Fr(x)
        return "(%d / %d)" % (x.numerator, x.denominator) if x.denominator != 1 else "(%d)" % x.numerator

    def vec(v):
        return "![" + ", ".join(q(x) for x in v) + "]"

    def cell(k):
        return "⟨%s,\n      %s,\n      %s, %s⟩" % (vec(k["c"]), vec(k["h"]), q(k["a"]), q(k["b"]))

    lines = ["/-- The fitted cover plan (`cover2_plan_lean.py`, d = %s, kappa = %s, nmult = %d). -/" % (
        C.opt("d", "2e-3"), FT.KAPPA, FT.NMULT), "def fitPlan : CoverPlan :=", "  ⟨%s, [" % q(d)]
    for si, s in enumerate(slabs):
        sep = "," if si < len(slabs) - 1 else ""
        if s["disc"] is not None:
            lines.append("    ⟨%s, %s, %s, some %s, [], []⟩%s" % (q(s["lo"]), q(s["hi"]), q(s["R"]), cell(s["disc"]), sep))
            continue
        lines.append("    ⟨%s, %s, %s, none," % (q(s["lo"]), q(s["hi"]), q(s["R"])))
        for name, ch in (("upper", s["upper"]), ("lower", s["lower"])):
            items = ["      ⟨%s, %s,\n      %s, %s⟩" % (vec(x["v"]), vec(x["w"]), cell(x["cell"]), q(x["tau"])) for x in ch]
            lines.append("     [" + ",\n".join(items).lstrip() + "]" + ("," if name == "upper" else ""))
        lines.append("    ⟩" + sep)
    lines.append("  ]⟩")
    with open(out_lean, "w") as fh:
        fh.write("\n".join(lines) + "\n")
    with open(out_json, "w") as fh:
        json.dump(dict(d=str(d), kappa=FT.KAPPA, nmult=FT.NMULT, cells=ncells, wedges=nw, max_rho_eff=reff,
                       exact_check="OK" if not fails else [str(f) for f in fails],
                       slabs=[dict(lo=str(s["lo"]), hi=str(s["hi"]), R=str(s["R"]),
                                   disc=None if s["disc"] is None else {kk: [str(x) for x in vv] if isinstance(vv, list) else str(vv)
                                                                         for kk, vv in s["disc"].items()},
                                   wedges=[dict(v=[str(x) for x in w["v"]], w=[str(x) for x in w["w"]], tau=str(w["tau"]),
                                                frame=[str(w["cell"]["a"]), str(w["cell"]["b"])],
                                                h=[str(x) for x in w["cell"]["h"]], c=[str(x) for x in w["cell"]["c"]])
                                           for w in s["upper"] + s["lower"]]) for s in slabs]), fh, indent=1)


if __name__ == "__main__":
    main()
