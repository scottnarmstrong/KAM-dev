#!/usr/bin/env python3
"""LP-QUANT self-checks.  Untrusted design tooling.

 1. Chart: energy, angular momentum, symplecticity (finite differences), spatial momenta (45).
 2. Thresholds against the independent table of docs/explorations/amd-crossing/A7-practical.md section 5.
 3. Mirror test of `lp_scale_choice`: for mu <= mu0 of the literal chain, the conclusions (a)-(g) of the Lean theorem are
    checked in 60-digit arithmetic, so a transcription error in the chain would show.
 4. Envelope gradient of B against central differences.
 5. fast_lie and fast_newton agree at the first order; a Kepler-only problem has zero rate.
 6. Direct integration: the AMD identity (13), Lambda excursion against the predicted first-order amplitude.
"""
import math
import os
import sys
import numpy as np
import mpmath as mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from systems import catalogue
import geometry as G
import chart as Ch
import chain as Cn
import lambda_route as LR

mp.mp.dps = 60


def check_scale_choice(ctx, ch, muexp):
    """Evaluate (a)-(g) of lp_scale_choice at mu = 10^muexp with the chain's constants; returns the list of slacks (>= 0 is pass)."""
    mu = mp.mpf(10) ** muexp
    tau, gamma = mp.mpf(ch["tau"]), mp.mpf(ch["gamma"])
    kappa, s, w = mp.mpf(ch["kappa"]), mp.mpf(ch["s"]), mp.mpf(ch["w"])
    L, M2 = mp.mpf(ch["L"]), mp.mpf(ch["M2"])
    D0 = mp.mpf(1)
    k = ctx.n if not ctx.spatial else 2 * ctx.n
    rs = min(4 * ch["rg"], ch["R"] / 4)
    rho = mp.mpf(min(rs, ctx.Imin) / 2)
    a = 1 / (2 * (tau + 1))
    X = kappa * mu ** (-a)
    K = mp.floor(X)
    r = D0 * mp.sqrt(mu)
    alpha = gamma / (2 * mp.pi) * K ** (-tau)
    eps = M2 * mu
    c, T0 = mp.mpf(ch["c"]), mp.mpf(ch["T0"])
    T = T0 * mp.exp(c * mu ** (-a))
    Tengine = s * r / (5 * eps) * mp.exp(2 * mp.pi * K * s / 6)
    return dict(K_ge_1=K - 1, E1=alpha / 2 - K * L * r, E2=alpha * r / (256 * K) - eps, E3=w ** 2 - 64 * mp.pi * k * s * r,
                E4=2 * mp.pi * K * s - 6, r_le_rho=rho - r, time=mp.log(Tengine) - mp.log(T))


def main():
    print("1 chart", Ch.fundamental_check())
    S = catalogue()
    a7 = dict(HD109271=.1862, HD1461=.4854, HD11964=.1625, HD69830=.1373, HD96700=2.602)
    for k, v in a7.items():
        s = S[k]
        print(f"2 {k}: beta here {G.amd(s.I0, s.e) / G.B(s.I0, s.nu):.4f}, A7 {v} (axes differ: here from the periods)")
    s = S["SJ"]
    ctx = Cn.Ctx(s, Kmax=2000)
    lit = Cn.best_literal(ctx)
    print("3 mu0 literal 10^", round(lit["log10_mu0"], 2), {k: round(v, 2) for k, v in lit["limits"].items()})
    for e in (lit["log10_mu0"], lit["log10_mu0"] - 3):
        sl = check_scale_choice(ctx, lit, e)
        print("  mu=10^%.1f" % e, {k: ("pass" if v >= 0 else "FAIL") for k, v in sl.items()})
    I = ctx.I0
    g = G.grad_B(I, ctx.nu)
    h = 1e-6
    fd = np.array([(G.B(I + h * e, ctx.nu) - G.B(I - h * e, ctx.nu)) / (2 * h) for e in np.eye(2)])
    print("4 gradB envelope", g, "FD", fd)
    z = Ch._real_slow(np.random.default_rng(1), 1, 2, 1, ctx.I0, ctx.C0)[0]
    gl = LR.fast_lie(ctx, 0, 1, z[:2], z[2:], Q=2)
    nw = LR.fast_newton(ctx, 0, 1, z[:2], z[2:], s.mu, steps=1, deg=8)
    print("5 first-order rate, series", s.mu * gl[1], "newton", nw["rho"][0])
    r = LR.nbody_check(s, years=20000)
    print("6 SJ", r)
    sc = LR.scan(ctx, 1e-5, Cball=ctx.C0 * 1.02, N=256, J=30)
    print("  predicted amp (half range)", s.mu * sc["amp1"], "secular", LR.secular_rate(ctx, s.mu))
    s4 = S["JSUN"]
    r = LR.nbody_check(s4, years=20000)
    print("6 JSUN", r)


if __name__ == "__main__":
    main()
