#!/usr/bin/env python3
"""LOCK-GEN (D45): the odd synchronous periodic orbit of the seven-term model in high precision, a radii-polynomial
(Newton-Kantorovich) design check in weighted l1, and a rational trigonometric centre c(phi).

Untrusted tooling: design numbers, not certificates (no interval arithmetic; the bounds are evaluated in mpmath at
high precision with crude, explicitly stated estimates).

Model (model.py, pi-free): V = 2 pi psi(phi), odd and 1-periodic, Dt = (1/2pi) d/dphi,
    F(V) = Dt^2 V + g(phi, V) = 0,   g = 2 eps sum_m A_m sin(2 pi (2 - m) phi + 2 V).
Sine series V = sum_{l=1..K} b_l sin(2 pi l phi).  Norm (two-sided weighted l1, weight e^{2 pi nu |l|}):
    ||V||_nu = sum_l |b_l| w_l,  w_l = e^{2 pi nu l}   (|Vhat_{+-l}| = |b_l|/2).
Approximate inverse A = J_K^{-1} on modes l <= K and -1/l^2 (the inverse of the symbol of Dt^2) on the tail.
With c(phi) = dg/dV = 4 eps sum_m A_m cos(...):
    Y0 = ||A F(Vbar)||,  Z0 = ||I - A_K J_K||,
    Z1 = ||A_K|| ||c||_nu + ||c||_nu / (K+1)^2              (tail coupling, crude),
    Z2 = ||A|| 8 eps sum_m |A_m| e^{2 pi nu |2-m|} e^{2 (||Vbar|| + r_max)},
    p(r) = Z2 r^2 - (1 - Z0 - Z1) r + Y0 < 0   on [r_-, r_+]  (r_+ capped by r_max).

    python3 lock_po.py OUT.json [K=80] [M=256] [bits=256] [nu=0.2]
"""
import sys, json, time, math
from fractions import Fraction as F
import mpmath as mp
from model import A_EXACT, EPS


def setup(K, M, bits):
    mp.mp.prec = bits
    eps = mp.mpf(EPS.numerator) / EPS.denominator
    A = {m: mp.mpf(a.numerator) / a.denominator for m, a in A_EXACT.items()}
    ph = [mp.mpf(j) / M for j in range(M)]
    S = [[mp.sinpi(2 * l * p) for l in range(1, K + 1)] for p in ph]
    return eps, A, ph, S


def grid_V(b, S):
    return [mp.fsum(bl * s for bl, s in zip(b, row)) for row in S]


def g_and_c(V, ph, eps, A):
    g, c = [], []
    for v, p in zip(V, ph):
        gs, cs = 0, 0
        for m, a in A.items():
            t = 2 * mp.pi * (2 - m) * p + 2 * v
            gs += a * mp.sin(t); cs += a * mp.cos(t)
        g.append(2 * eps * gs); c.append(4 * eps * cs)
    return g, c


def sine_coeffs(f, M, L):
    """Sine coefficients l = 1..L of an odd grid function."""
    return [2 * mp.fsum(f[j] * mp.sinpi(2 * l * mp.mpf(j) / M) for j in range(M)) / M for l in range(1, L + 1)]


def cos_coeffs(f, M, L):
    """a_0 and a_l (l = 1..L) of an even grid function f = a_0 + sum a_l cos."""
    a0 = mp.fsum(f) / M
    return [a0] + [2 * mp.fsum(f[j] * mp.cospi(2 * l * mp.mpf(j) / M) for j in range(M)) / M for l in range(1, L + 1)]


def jac(c, S, K, M):
    J = mp.matrix(K, K)
    for l in range(K):
        for j in range(l, K):
            v = 2 * mp.fsum(c[i] * S[i][l] * S[i][j] for i in range(M)) / M
            J[l, j] = v; J[j, l] = v
        J[l, l] -= (l + 1) ** 2
    return J


def opnorm(B, w):
    n = B.rows
    return max(mp.fsum(abs(B[l, j]) * w[l] for l in range(n)) / w[j] for j in range(n))


def main(argv):
    out = argv[0]
    K = int(argv[1]) if len(argv) > 1 else 80
    M = int(argv[2]) if len(argv) > 2 else 256
    bits = int(argv[3]) if len(argv) > 3 else 256
    nu = F(argv[4]) if len(argv) > 4 else F(1, 5)
    t0 = time.time()
    eps, A, ph, S = setup(K, M, bits)
    b = [mp.mpf(0)] * K
    for it in range(30):
        V = grid_V(b, S)
        g, c = g_and_c(V, ph, eps, A)
        Fg = [gl - (l + 1) ** 2 * bl for l, (gl, bl) in enumerate(zip(sine_coeffs(g, M, K), b))]
        res = max(abs(x) for x in Fg)
        print("newton it %d  max|F_l| = %s  t=%.0fs" % (it, mp.nstr(res, 5), time.time() - t0), flush=True)
        if res < mp.mpf(2) ** (-bits + 24):
            break
        J = jac(c, S, K, M)
        d = mp.lu_solve(J, mp.matrix(Fg))
        b = [bl - d[l] for l, bl in enumerate(b)]
    # ---- radii polynomial
    nuf = mp.mpf(nu.numerator) / nu.denominator
    Lfull = M // 2 - 1
    w = [mp.exp(2 * mp.pi * nuf * l) for l in range(1, Lfull + 1)]
    V = grid_V(b, S)
    g, c = g_and_c(V, ph, eps, A)
    gl = sine_coeffs(g, M, Lfull)
    Ffull = [gl[l] - (l + 1) ** 2 * (b[l] if l < K else 0) for l in range(Lfull)]
    J = jac(c, S, K, M)
    AK = J ** -1
    AF = AK * mp.matrix(Ffull[:K])
    Y0 = mp.fsum(abs(AF[l]) * w[l] for l in range(K)) + mp.fsum(
        abs(Ffull[l]) * w[l] / (l + 1) ** 2 for l in range(K, Lfull))
    I = mp.eye(K)
    Z0 = opnorm(I - AK * J, w[:K])
    nAK = opnorm(AK, w[:K])
    ca = cos_coeffs(c, M, Lfull)
    nc = abs(ca[0]) + mp.fsum(abs(ca[l]) * w[l - 1] for l in range(1, Lfull + 1))
    Z1 = nAK * nc + nc / (K + 1) ** 2
    nA = max(nAK, mp.mpf(1) / (K + 1) ** 2)
    nV = mp.fsum(abs(bl) * w[l] for l, bl in enumerate(b))
    rmax = mp.mpf(1) / 100
    Z2 = nA * 8 * eps * mp.fsum(abs(a) * mp.exp(2 * mp.pi * nuf * abs(2 - m)) for m, a in A.items()) * mp.exp(
        2 * (nV + rmax))
    a2, a1 = Z2, 1 - Z0 - Z1
    disc = a1 ** 2 - 4 * a2 * Y0
    ok = a1 > 0 and disc > 0
    rlo = (a1 - mp.sqrt(disc)) / (2 * a2) if ok else None
    rhi = min((a1 + mp.sqrt(disc)) / (2 * a2), rmax) if ok else None
    # ---- rational centre c(phi) = sum_{l<=L} c_l sin(2 pi l phi) in turns
    psi = [bl / (2 * mp.pi) for bl in b]
    cents = []
    for L, rel in ((1, 1e-2), (2, 1e-2), (3, 1e-2), (3, 1e-3), (4, 1e-3)):
        cl = []
        for l in range(L):
            x = F(mp.nstr(psi[l], 30))
            den = 1
            while True:
                q = F(round(x * den), den)
                if q != 0 and abs(q - x) <= rel * abs(x):
                    break
                den *= 10 if den >= 10 else 10
            cl.append(F(q.numerator, q.denominator))
        diff = [psi[l] - (mp.mpf(cl[l].numerator) / cl[l].denominator if l < L else 0) for l in range(K)]
        nrm = mp.fsum(abs(d) * w[l] for l, d in enumerate(diff))
        sup = mp.fsum(abs(d) for d in diff)
        dsup = mp.fsum(abs(d) * 2 * mp.pi * (l + 1) for l, d in enumerate(diff))   # sup |psi*' - c'| (turns/period)
        cents.append(dict(L=L, rel=rel, coeffs=[str(q) for q in cl], l1nu=mp.nstr(nrm, 6), sup=mp.nstr(sup, 6),
                          dsup=mp.nstr(dsup, 6)))
    dec = [float(mp.log10(abs(x))) if x != 0 else -999 for x in psi]
    rec = dict(K=K, M=M, bits=bits, nu=str(nu), newton_resid=mp.nstr(res, 5), time_s=round(time.time() - t0, 1),
               psi_sine_coeffs=[mp.nstr(x, 64) for x in psi], log10_decay=dec,
               max_abs_psi=mp.nstr(max(abs(v) for v in V) / (2 * mp.pi), 10),
               Y0=mp.nstr(Y0, 6), Z0=mp.nstr(Z0, 6), Z1=mp.nstr(Z1, 6), Z2=mp.nstr(Z2, 6), normAK=mp.nstr(nAK, 6),
               norm_c=mp.nstr(nc, 6), norm_Vbar=mp.nstr(nV, 6), r_max=mp.nstr(rmax, 3), closes=bool(ok),
               r_interval_V=[mp.nstr(rlo, 6), mp.nstr(rhi, 6)] if ok else None,
               r_interval_psi_turns=[mp.nstr(rlo / (2 * mp.pi), 6), mp.nstr(rhi / (2 * mp.pi), 6)] if ok else None,
               centres=cents, F_tail_max=mp.nstr(max(abs(x) for x in Ffull[K:]), 5))
    json.dump(rec, open(out, "w"), indent=1)
    for k in ("newton_resid", "max_abs_psi", "Y0", "Z0", "Z1", "Z2", "closes", "r_interval_V", "r_interval_psi_turns",
              "F_tail_max", "time_s"):
        print(k, rec[k])
    print("decay log10|psi_l| l=1..:", " ".join("%.1f" % x for x in dec[:12]), "...", "%.1f" % dec[K - 1])
    for cc in cents:
        print("centre", cc)


if __name__ == "__main__":
    main(sys.argv[1:])
