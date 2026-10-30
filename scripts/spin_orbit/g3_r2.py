#!/usr/bin/env python3
"""SO-GEN3: the lunar parameter package R2 (N = 65, sharp certifier) and its threshold, in one re-runnable place.

    python3 g3_r2.py [err_lower err_upper]

`R2(N)` is the package (exact rationals, the CertParams fields of KAM.SpinOrbit.lunarR1's shape).
`threshold(p)` is THE threshold function: it calls `sharp_q.sharp`, the transcription of the landed
KAM/CertificateSharp/ConstantsQ.lean.  When a new certifier version lands with new constants, update
`sharp_q.consts` / `sharp_q.sharp` (same inputs) and re-run this script: nothing else changes.

Majorants (landed-checker forms, sofx mirror on the actual N = 65 tori at L = 40, rho = 1/140, c = 2):
  checkHamBounds max 2.1191 (D2H sum) <= M = 54/25;  ||DK|| rows 1.86485 <= sK - mu;
  checkGram beta 5.36057 (l1) with margin 0.0112 at sB = 2689/500;  checkTorsion ||S|| 0.50406, delta_T 2.7e-5
  at cfgLow cutoff 160 (margin 0.0097 at sT = 13/25).
gamma = gbar = kappa/(N + 2), kappa = c/s (SO-DION: lunarRotFreq nu+- kappa is IsDiophantine (kappa/(N+2)) 1).
Untrusted tooling.
"""
import sys, math
from fractions import Fraction as F
import sharp_q as SQ

N_TARGET = 65


def R2(N=N_TARGET, err=F(0), disp=F(0)):
    c = F(2); s = 1 + F(1, 10 ** 6); kappa = c / s
    rho = F(1, 140)
    return dict(tau=1, rho=rho, rhoInf=rho / 1000, M=F(54, 25), sK=F(1873, 1000), sB=F(2689, 500),
                sT=F(13, 25), mu=F(1, 160), gbar=kappa / (N + 2), som=F(2), nu=F(1, 10 ** 6),
                gamma=kappa / (N + 2), s=s, c=c, err=F(err), E0=F(0), disp=F(disp))


def threshold(p):
    """(threshold on err, disp coefficient, active branch) of the sharp test for package p."""
    r = SQ.sharp(p)
    return r["threshold"], r["disp_coef"], r["active"]


def main(args):
    p = R2()
    thr, dc, act = threshold(p)
    print("R2 (N = %d): log10 threshold %.3f (active %s), disp >= 10^%.3f err" % (N_TARGET, SQ.lg(thr), act, SQ.lg(dc)))
    for e in args:
        e = F(e)
        disp = dc * e
        q = R2(err=e, disp=disp * F(1001, 1000))
        print("  err %.3e: err/threshold = 10^%.2f, sharpTest %s, disp %.3e" % (
            float(e), SQ.lg(e / thr), SQ.sharpTest(q), float(disp)))


if __name__ == "__main__":
    main(sys.argv[1:])
