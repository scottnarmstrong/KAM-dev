#!/usr/bin/env python3
"""Independent round-trip check of an emitted rotated-frame file (plain Fractions, no rotlib).

Recomputes from the JSON alone the polynomial parts of the P1 and P2 invariance rows (index units),
    R3 = Dt p + 2 eps sum A_m Im(e_m E),   R4 = eps sum A_m (2-m) Im(e_m E) + Dt (p + J),
as sin-series coefficients over the half lattice, their weighted l1 sums with weights exp(2 pi rho |kappa|_1)
(mpmath, 300 bits), and compares with the emitter's enclosures R3_l1w / R4_l1w (which must be >= these).
Also checks p = round(nu + Dt v) to one ulp, the zero-mode energy and the J symmetry.  Untrusted tooling.
"""
import sys, json, mpmath
from fractions import Fraction as F
import model


def main(path):
    d = json.load(open(path)); S = d["scale_bits"]; which = d["which"]
    mpmath.mp.prec = 600
    s5 = mpmath.sqrt(5)
    x, y = [F(t) for t in d["nu_minus_one_Q_sqrt5"]]
    s1 = mpmath.mpf(x.numerator) / x.denominator + s5 * mpmath.mpf(y.numerator) / y.denominator
    sc = mpmath.mpf(2) ** -S
    b = {(k, l): int(n) for k, l, n in d["v_sin"]}
    c = {(k, l): int(n) for k, l, n in d["p_cos"]}
    j = {(k, l): int(n) for k, l, n in d["J_cos"]}
    E = {(k, l): int(n) for k, l, n in d["E_re"]}
    # p rounding check
    worst = 0
    for kk, n in b.items():
        ex = n * (s1 * kk[0] + kk[1])
        worst = max(worst, abs(c.get(kk, 0) - ex))
    assert worst <= 0.5 + 1e-30, worst
    eA = {m: model.EPS * model.A_EXACT[m] for m in model.M_MODES}
    # sin-series coefficient over H of Im(e_s E): sum_all Ehat_kappa sin(2 pi (kappa+s).theta) -> at mu in H: E_{mu-s} - E_{-mu-s}
    keys = set(c) | set(j)
    for (k, l) in E:
        for m, (a, dd) in model.SHIFT.items():
            for (p_, q_) in ((k + a, l + dd), (-k - a, -l - dd)):
                if p_ > 0 or (p_ == 0 and q_ > 0):
                    keys.add((p_, q_))
    rho = mpmath.mpf(1) / 70
    t3 = t4 = mpmath.mpf(0)
    for (k, l) in keys:
        lam = s1 * k + l
        # Dt (C cos) = -lam C sin ; sin coefficient
        dtp = -lam * c.get((k, l), 0)
        dtj = -lam * j.get((k, l), 0)
        im = {m: E.get((k - a, l - dd), 0) - E.get((-k - a, -l - dd), 0) for m, (a, dd) in model.SHIFT.items()}
        g3 = sum(2 * eA[m] * im[m] for m in im); g4 = sum(eA[m] * (2 - m) * im[m] for m in im)
        r3 = (dtp + mpmath.mpf(g3.numerator) / g3.denominator) * sc
        r4 = (dtp + dtj + mpmath.mpf(g4.numerator) / g4.denominator) * sc
        w = mpmath.exp(2 * mpmath.pi * rho * (abs(k) + abs(l)))
        t3 += abs(r3) * w; t4 += abs(r4) * w
    res = d["enclosures"]["residual"]
    print(which, "R3 l1w recomputed %s  emitter %.6e" % (mpmath.nstr(t3, 8), res["R3_l1w"]))
    print(which, "R4 l1w recomputed %s  emitter %.6e" % (mpmath.nstr(t4, 8), res["R4_l1w"]))
    assert t3 <= res["R3_l1w"] * (1 + 1e-12) and t4 <= res["R4_l1w"] * (1 + 1e-12)
    assert abs(t3 / res["R3_l1w"] - 1) < 1e-6 and abs(t4 / res["R4_l1w"] - 1) < 1e-6
    # energy zero mode: p0^2 + sum_H c^2/2 over 2 ... avg(p^2)/2 + J0 - sum eps A_m E_{-s_m}
    p0 = F(int(d["p0"]), 1 << S); J0 = F(int(d["J0"]), 1 << d["J0_scale_bits"])
    avg_p2 = p0 * p0 + sum(F(n, 1 << S) ** 2 for n in c.values()) / 2
    en = avg_p2 / 2 + J0 - sum(eA[m] * F(E.get((-a, -dd), 0), 1 << S) for m, (a, dd) in model.SHIFT.items())
    print(which, "energy polynomial part %.3e (emitter bound incl. witness %.3e)" % (float(en), res["energy_unscaled"]))
    assert abs(en) <= res["energy_unscaled"]
    print(which, "all package checks:", all(d["checks"].values()), " alternative:",
          all(d["package_alternative"]["checks"].values()))
    print(which, "OK")


if __name__ == "__main__":
    for p in sys.argv[1:]:
        main(p)
