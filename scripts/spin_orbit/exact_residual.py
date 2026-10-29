#!/usr/bin/env python3
"""EXACT-arithmetic residual evaluator on truncated candidate data (Python Fractions; Q(sqrt5) as pairs).

Untrusted reference implementation intended to cross-check the future Lean checker.  Conventions: see model.py.

Data: v = sum_{kappa in H} b_kappa sin(2 pi kappa.(psi,phi)),  H = {k>0} u {k=0,l>0}, b_kappa = B_kappa / 2^P;
      E = exp(2 i v) = sum_kappa Ehat_kappa e_kappa with REAL coefficients (v odd), Ehat_kappa = N_kappa / 2^P.
Residual: R(v) = Dt^2 v + 2 eps sum_m A_m Im(e_{s_m} E) = sum_{kappa in H} rho_kappa * (i e_kappa - i e_{-kappa})/... i.e.
  Rhat_kappa = i * rho_kappa  (odd),   rho_kappa = (b_kappa/2) (s k + l)^2 - eps sum_m A_m (Ehat_{kappa-s_m} - Ehat_{-kappa-s_m}),
with s = nu - 1 in Q(sqrt5) and b extended oddly (b_{-kappa} = -b_kappa).  The scalar residual of the physical
equation is r = 2 pi R.  Returned: rho_kappa for kappa in H as pairs (x, y) = x + y sqrt5 (Fractions).
"""
from fractions import Fraction as F
import json, sys, math
from model import A_EXACT, EPS, SHIFT, nu_minus_one

def canon(k, l):
    """canonical representative in H and sign."""
    if k > 0 or (k == 0 and l > 0): return (k, l), 1
    return (-k, -l), -1

def residual(b, E, P, which):
    """b: {(k,l): int} for kappa in H; E: {(k,l): int} (all kappa). Returns {kappa in H: (x, y)}."""
    sx, sy = nu_minus_one(which)
    scale = F(1, 1 << P)
    c = {m: EPS * A_EXACT[m] for m in SHIFT}
    cand = set()
    cand.update(b)
    for (k, l) in E:
        for m, (a, d) in SHIFT.items():
            cand.add(canon(k + a, l + d)[0]); cand.add(canon(-k - a, -l - d)[0])
    out = {}
    for (k, l) in cand:
        bk = b.get((k, l), 0)
        # (b/2)(s k + l)^2 ; s k + l = (sx k + l) + sy k sqrt5
        u = sx * k + l; w = sy * k
        sq_r = u * u + 5 * w * w; sq_s = 2 * u * w
        x = F(bk, 2) * scale * sq_r; y = F(bk, 2) * scale * sq_s
        acc = 0
        for m, (a, d) in SHIFT.items():
            e1 = E.get((k - a, l - d), 0); e2 = E.get((-k - a, -l - d), 0)
            if e1 != e2: acc += c[m] * (e1 - e2)
        x -= acc * scale
        if x != 0 or y != 0: out[(k, l)] = (x, y)
    return out

def weighted_l1(rho, wa=0.01, wb=0.005, prec=330):
    """sum |rho_kappa| exp(2 pi (wa|k| + wb|l|)) times 2 (kappa and -kappa), as mpmath numbers; also unweighted."""
    import mpmath
    mpmath.mp.prec = prec
    s5 = mpmath.sqrt(5)
    tw = tu = mpmath.mpf(0); mx = mpmath.mpf(0)
    for (k, l), (x, y) in rho.items():
        v = abs(mpmath.mpf(x.numerator) / x.denominator + s5 * mpmath.mpf(y.numerator) / y.denominator)
        tu += 2 * v; mx = max(mx, v)
        tw += 2 * v * mpmath.exp(2 * mpmath.pi * (wa * abs(k) + wb * abs(l)))
    return tw, tu, mx

def load(path):
    d = json.load(open(path))
    return d

if __name__ == "__main__":
    # usage: exact_residual.py data.json [which]
    d = json.load(open(sys.argv[1]))
    P = d["scale_bits"]
    b = {(k, l): n for k, l, n in d["v_sin"]}
    E = {(k, l): n for k, l, n in d["E_re"]}
    rho = residual(b, E, P, d["which"])
    tw, tu, mx = weighted_l1(rho)
    import mpmath
    print("terms", len(rho), "sum|rho| = %s  weighted = %s  max = %s" % (mpmath.nstr(tu, 8), mpmath.nstr(tw, 8), mpmath.nstr(mx, 8)))
