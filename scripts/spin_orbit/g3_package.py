#!/usr/bin/env python3
"""SO-GEN3: R2-type parameter packages for the sharp test (sharp_q.py), scanned over time scale c and strip rho.

Majorants (c = 1 values, scaled): M >= c * D2H (the landed checkHamBounds sum, 1.0657 at c = 1 on the N = 40 tori,
SO-DATA-1), sigmaK - mu >= ||DK||, sigmaB - mu >= ||G^-1|| (checker l1), sigmaT - mu >= ||avg^-1||/c; the inputs are
passed per torus.  gamma = gbar = c/((N + 1) s) (gamma((nu - 1, 1)) >= 1/(N + g) > 1/(N + 1): binding k = (1, 0)).
Untrusted tooling."""
import sys, math, json
from fractions import Fraction as F
import sharp_q as SQ

def up(x, d=4):
    """decimal rational >= x with d significant digits."""
    e = math.floor(math.log10(x)) - d + 1
    return F(math.ceil(F(x) / F(10) ** e)) * F(10) ** e

def package(N, c, rho, maj, mu=F(1, 160), s=1 + F(1, 10 ** 6), margin=F(1001, 1000)):
    c = F(c); rho = F(rho)
    M = up(float(c * F(maj["D2H"]) * margin))
    sK = up(float(F(maj["DK"]) * margin + mu)); sB = up(float(F(maj["Ginv"]) * margin + mu))
    sT = up(float(F(maj["Tinv"]) / c * margin + mu))
    gam = c / s / (N + 1)
    return dict(tau=1, rho=rho, rhoInf=rho / 1000, M=M, sK=sK, sB=sB, sT=sT, mu=mu, gbar=gam, nu=F(1, 10 ** 6),
                gamma=gam, err=F(0), disp=F(0), c=c, s=s)

def scan(N, maj, rhos=(F(1, 70),), cs=None):
    cs = cs or [F(x, 100) for x in range(50, 401, 10)]
    best = None
    for rho in rhos:
        for c in cs:
            p = package(N, c, rho, maj)
            r = SQ.sharp(p)
            t = SQ.lg(r["threshold"])
            if best is None or t > best[0]:
                best = (t, c, rho, r["active"], SQ.lg(r["disp_coef"]), p)
    return best

R1MAJ = dict(D2H="1.0657", DK="1.36036", Ginv="1.979943", Tinv="1.022493")

if __name__ == "__main__":
    for N in (40, 50, 55, 60, 65):
        t, c, rho, act, dc, p = scan(N, R1MAJ, rhos=(F(1, 70), F(1, 50), F(1, 35), F(1, 20)))
        print(N, "log10 thr %.2f at c=%s rho=%s active %s log10 dispcoef %.2f  M %s sK %s sB %s sT %s" % (
            t, c, rho, act, dc, p["M"], p["sK"], p["sB"], p["sT"]))
