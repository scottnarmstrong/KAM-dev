#!/usr/bin/env python3
"""SHARP-C5CORE: exact mirror of the kernel toy of the certified cohomological solve.

Mirrors, in exact rational arithmetic (the `ℚ` backend: no rounding), the Lean definitions of
`KAM/CertificateSharp/Step0/` on the toy of `KAM/CertificateSharp/Tests/Step0Coh.lean`:
  * `checkWeight` (`ratExpUp`), `SupData.check` (`Γ_∞` claim from the frequency box),
  * `solveCheck`, `CertModel.cohSolve` (coefficients −i c_k / D_k, error radius Σ e_k w^{|k|₁} plus
    2 piUpQ Γ rad), `CertModel.supBound`,
and prints the certified bound of the solution against the a-priori bound Γ · ‖g‖ (same norms:
ℓ¹ of the input at width ρ, ℓ¹ of the output at width ρ − δ), their ratio, and the true Γ_∞ and
solution norm in double precision.

Usage: python3 -I scripts/apost_sharp/step0_coh_toy.py
"""
import math
from fractions import Fraction as F

PI_UP = F(3141593, 1000000)
PI_LO = F(3141592, 1000000)


def ratExpUp(q, s, N):
    if q / 2 ** s <= 1 and 0 < N:
        y = q / 2 ** s
        r = sum(y ** m / math.factorial(m) for m in range(N)) + \
            y ** N * (F(N + 1) / (math.factorial(N) * N))
        for _ in range(s):
            r = r * r
        return r
    return F(3) ** math.ceil(q)


def checkWeight(rho, w, s, N):
    return 0 < rho and ratExpUp(2 * PI_UP * rho, s, N) <= w


def keyfun(n, key):
    return tuple(key[i] if i < len(key) else 0 for i in range(n))


def boxDot(box, k):
    return sum(F(kj) * box[j][0] for j, kj in enumerate(k))


def boxRad(box, k):
    return sum(abs(F(kj)) * box[j][1] for j, kj in enumerate(k))


def boxLb(box, k):
    return abs(boxDot(box, k)) - boxRad(box, k)


def modeBox(n, N):
    from itertools import product
    return [k for k in product(range(-N, N + 1), repeat=n) if any(k) and sum(map(abs, k)) <= N]


def sup_check(n, d):
    b, g, delta, N, J, E1, claim = d
    expLow = sum((F(628, 100) * delta) ** i / math.factorial(i) for i in range(J + 1))
    ok = (0 < g and 0 < delta and 1 <= F(628, 100) * delta * (N + 1) and 1 <= E1 * expLow and
          (N + 1) * E1 ** (N + 1) <= claim * (F(628, 100) * g))
    worst = F(0)
    for k in modeBox(n, N):
        lb = boxLb(b, k)
        ok = ok and 0 < lb and E1 ** sum(map(abs, k)) <= claim * (F(628, 100) * lb)
        if lb > 0:
            worst = max(worst, E1 ** sum(map(abs, k)) / (F(628, 100) * lb))
    return ok, worst


def keyDeg(key):
    return sum(abs(z) for z in key)


def cohSolve(n, box, Gamma, w_out, model):
    deg, terms, rad = model
    items = []
    for key, (re, im) in terms:
        k = keyfun(n, key)
        lb = boxLb(box, k)
        if not lb > 0:
            assert all(z == 0 for z in key), "solveCheck fails"
            continue
        D = boxDot(box, k)
        q = 1 / D
        div_err = boxRad(box, k) / (lb * abs(D))
        centre = (q * im, q * (-re))          # q · (−i c)
        err = (abs(re) + abs(im)) * div_err   # scaleErr = width = 0 on ℚ
        items.append((key, centre, err))
    err_rad = sum(abs(e) * w_out ** keyDeg(key) for key, _, e in items)
    out_rad = err_rad + 2 * PI_UP * Gamma * rad
    return (deg - 1, [(key, c) for key, c, _ in items], out_rad), err_rad


def degFactorUp(d):
    return (2 * PI_UP) ** d if d >= 0 else (2 * PI_LO) ** d


def supBound(w, model):
    deg, terms, rad = model
    return degFactorUp(deg) * (sum((abs(re) + abs(im)) * w ** keyDeg(key)
                                   for key, (re, im) in terms) + rad)


def main():
    n = 2
    box = [(F(-2462, 100000), F(1, 100000)), (F(1), F(0))]
    w_in, w_out = (F(1, 10), F(19, 10)), (F(1, 20), F(14, 10))
    print("checkWeight in :", checkWeight(*w_in, 0, 12), float(ratExpUp(2 * PI_UP * w_in[0], 0, 12)))
    print("checkWeight out:", checkWeight(*w_out, 0, 12), float(ratExpUp(2 * PI_UP * w_out[0], 0, 12)))
    sd = (box, F(2461, 100000), F(1, 20), 8, 8, F(731, 1000), F(5))
    ok, worst = sup_check(n, sd)
    print(f"SupData.check: {ok}; largest box entry E1^|k|/(6.28 L_k) = {float(worst):.4f}")
    model = (0, [([0, 0], (F(1, 10 ** 9), F(0))),
                 ([1, 0], (F(1, 10 ** 6), F(0))),
                 ([6, 1], (F(3, 1000), F(1, 1000))),
                 ([5, -2], (F(-2, 1000), F(1, 1000))),
                 ([7, 0], (F(1, 1000), F(-2, 1000))),
                 ([3, 4], (F(1, 1000), F(1, 1000))),
                 ([-4, 3], (F(-1, 1000), F(2, 1000))),
                 ([8, -1], (F(2, 1000), F(0)))], F(1, 10 ** 8))
    out, err_rad = cohSolve(n, box, F(5), w_out[1], model)
    cert = supBound(w_out[1], out)
    g_l1 = supBound(w_in[1], model)
    apriori = F(5) * g_l1
    print(f"solved model: deg {out[0]}, {len(out[1])} terms, error radius {float(err_rad):.3e}, "
          f"total radius {float(out[2]):.3e}")
    print(f"certified bound of the solution  : {float(cert):.4e}")
    print(f"a-priori Γ·‖g‖ (claim Γ = 5)     : {float(apriori):.4e}")
    print(f"ratio a-priori / certified       : {float(apriori / cert):.1f}")
    for r in (100, 200, 300):
        print(f"  certified · {r} ≤ a-priori: {cert * r <= apriori}")
    # true constants (double precision)
    alpha = (-79 + math.sqrt(5)) / 3118
    b = 2 * math.pi * float(sd[2])
    G = max(math.exp(-b * (abs(k1) + abs(k2))) / (2 * math.pi * abs(k1 * alpha + k2))
            for k1 in range(-400, 401) for k2 in range(-12, 13) if (k1, k2) != (0, 0))
    print(f"true Γ_∞(ω, 1/20) ≈ {G:.4f} (claim 5)")


if __name__ == "__main__":
    main()
