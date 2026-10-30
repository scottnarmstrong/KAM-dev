#!/usr/bin/env python3
"""SJS-PLAN experiment E3: explicit cubic-field frequency vectors near FH25's omega, with a norm-form Diophantine constant.

Untrusted design tooling (mpmath).  For a cubic field K = Q(x), f monic integer, real root x0 and other roots x1, x2, take
a_j = c_j0 + c_j1 x + c_j2 x^2 in Z[x], omega_j = a_j(x0)/D.  For k in Z^3, k != 0, b = k.a is a nonzero element of Z[x]
(a_j Q-independent), so |N(b)| >= 1 and, N(b) = b(x0) b(x1) b(x2),
    |k.omega| >= 1 / (D m1 m2 |k|_1^2),  m_i = max_j |a_j(x_i)|:
the vector is (gamma, 2)-Diophantine with gamma = 1/(D m1 m2).  This is the landed CubicDiophantine.lean argument (adjugate
Q with beta Q = N, |Q| <= C |k|_1^2), with the frequency's own conjugates in C instead of a transfer through a matrix norm,
which would lose a further factor (the size of c)^2.
The search: for a scale D, each a_j is a closest-vector problem in the Minkowski lattice of Z[x] (target (D omega_j, 0, 0)),
solved by enumeration around the rounded coordinates.  It reports the tradeoff between the frequency tolerance and gamma.
Heuristic: a lattice of covolume V has a point in {|v - t| <= e, |s| <= m} once 2 e pi m^2 ~ V, so gamma ~ (2 pi / V) tol.
Usage: python3 -I scripts/sjs/plan/sjs_dioph.py [--json OUT]
"""
import itertools, json, math, os, sys
import mpmath as mp
import numpy as np

mp.mp.dps = 60
OM = [mp.mpf("8.39549288702546301204e-2"), mp.mpf("3.38240117059304358259e-2"), mp.mpf("-1.85007988077595e-5")]
GAMMA_NUM, GAMMA_FH = 1.85007988e-5, 1.69e-6

# (name, coefficients of x^3 + c2 x^2 + c1 x + c0, discriminant)
FIELDS = [("x^3 - x - 1", [1, 0, -1, -1], -23), ("x^3 + x - 1", [1, 0, 1, -1], -31),
          ("x^3 - x^2 + x + 1", [1, -1, 1, 1], -44), ("x^3 + 2x - 1", [1, 0, 2, -1], -59),
          ("x^3 + x^2 - 2x - 1", [1, 1, -2, -1], 49), ("x^3 - 3x - 1", [1, 0, -3, -1], 81),
          ("x^3 - 2", [1, 0, 0, -2], -108)]


def field(coef):
    rts = mp.polyroots(coef, maxsteps=200, extraprec=200)
    real = sorted([r for r in rts if abs(mp.im(r)) < mp.mpf(10) ** -40], key=lambda r: mp.re(r))
    x0 = mp.re(real[-1])
    others = [r for r in rts if abs(r - x0) > mp.mpf(10) ** -30]
    return x0, others


def closest(t, x0, others, R=12, weight=1.0):
    """elements c of Z[x] with value close to t and small conjugates: list of (err, m1, m2, c)."""
    B = mp.matrix(3, 3)
    pw = lambda z, e: z ** e
    if abs(mp.im(others[0])) > 0:
        for j in range(3):
            B[0, j] = pw(x0, j); B[1, j] = mp.re(pw(others[0], j)); B[2, j] = mp.im(pw(others[0], j))
    else:
        for j in range(3):
            B[0, j] = pw(x0, j); B[1, j] = pw(others[0], j); B[2, j] = pw(others[1], j)
    c0 = mp.lu_solve(B, mp.matrix([t, 0, 0]))
    base = [int(mp.nint(c0[i])) for i in range(3)]
    Bf = np.array(B.tolist(), dtype=float)
    # offset from the rounded point, evaluated exactly once
    res0 = [t - sum(B[0, j] * base[j] for j in range(3)), -sum(B[1, j] * base[j] for j in range(3)),
            -sum(B[2, j] * base[j] for j in range(3))]
    res0 = np.array([float(r) for r in res0])
    g = np.arange(-R, R + 1)
    d = np.array(list(itertools.product(g, g, g)), dtype=float)
    v = d @ Bf.T                                     # (N, 3)
    err = np.abs(v[:, 0] - res0[0])
    s1, s2 = v[:, 1] - res0[1], v[:, 2] - res0[2]
    return d, err, s1, s2, base, res0


def cost_sets(t, x0, others, R, tol):
    d, err, s1, s2, base, res0 = closest(t, x0, others, R)
    cplx = abs(mp.im(others[0])) > 0
    if cplx:
        size = np.hypot(s1, s2)
    else:
        size = np.maximum(np.abs(s1), np.abs(s2))
    ok = np.where(err <= tol)[0]
    if len(ok) == 0:
        return None
    i = ok[np.argmin(size[ok])]
    c = [base[j] + int(d[i, j]) for j in range(3)]
    return c


def evalc(c, z):
    return sum(c[j] * z ** j for j in range(3))


def tradeoff(name, coef, disc, tols):
    x0, others = field(coef)
    rows = []
    for tol in tols:                                  # tol = absolute tolerance on omega
        best = None
        for logD in np.arange(0.0, 13.01, 0.05):
            D = int(round(10 ** logD))
            if D < 2:
                continue
            A = []
            for j in range(3):
                c = cost_sets(D * OM[j], x0, others, 7, tol * D)
                if c is None:
                    break
                A.append(c)
            if len(A) < 3:
                continue
            M = mp.matrix(A)
            if abs(mp.det(M)) < 0.5:
                continue
            ms = [max(abs(evalc(A[j], z)) for j in range(3)) for z in others]
            gamma = 1 / (D * ms[0] * ms[1])
            errs = [abs(evalc(A[j], x0) / D - OM[j]) for j in range(3)]
            if best is None or gamma > best["gamma"]:
                best = dict(D=D, gamma=float(gamma), m=[float(x) for x in ms], A=A,
                            err=[float(e) for e in errs], rel=[float(errs[j] / abs(OM[j])) for j in range(3)])
        rows.append((tol, best))
        if best:
            print("| %s | %d | %.0e | %d | %.3e | %.1f | %.1e | %.1e | %.2e |" % (
                name, disc, tol, best["D"], best["gamma"], best["m"][0], best["rel"][0], best["rel"][2],
                best["gamma"] / tol), flush=True)
        else:
            print("| %s | %d | %.0e | none |" % (name, disc, tol), flush=True)
    return rows


def numeric_inf(om, K=400):
    """inf |k|_1^2 |k.om| over |k|_1 <= K, by nearest k3 on each (k1, k2) fibre, and 2 neighbours."""
    o = np.array([float(x) for x in om])
    best = (1e9, None)
    for k1 in range(0, K + 1):
        k2s = np.arange(-(K - k1), K - k1 + 1)
        base = k1 * o[0] + k2s * o[1]
        k3 = -np.rint(base / o[2])
        for sh in (-1, 0, 1):
            kk3 = k3 + sh
            nrm = k1 + np.abs(k2s) + np.abs(kk3)
            val = np.abs(base + kk3 * o[2]) * nrm ** 2
            val[(k1 == 0) & (k2s == 0) & (kk3 == 0)] = 1e9
            mask = nrm <= K
            if mask.any():
                i = np.argmin(np.where(mask, val, 1e9))
                if val[i] < best[0]:
                    best = (float(val[i]), (k1, int(k2s[i]), int(kk3[i])))
    return best


def main():
    tols = [1e-5, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10]
    print("| field | disc | tol on omega (abs) | D | gamma (tau 2, certified by the norm) | conj size | rel err omega1 | rel err omega3 | gamma/tol |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    out = {}
    for name, coef, disc in FIELDS:
        out[name] = [(t, b) for t, b in tradeoff(name, coef, disc, tols)]
    print("\nnumerical inf |k|^2 |k.omega| for FH's omega, |k|_1 <= 400:", numeric_inf(OM))
    # the best row at tol 1e-8: its own numerical constant
    for name, rows in out.items():
        for t, b in rows:
            if b and t == 1e-8:
                x0, _ = field([c for n, c, d in FIELDS if n == name][0])
                om = [evalc(b["A"][j], x0) / b["D"] for j in range(3)]
                print(name, "tol 1e-8: numerical inf (|k|<=400)", numeric_inf(om), "certified", b["gamma"])
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
