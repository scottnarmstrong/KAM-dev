#!/usr/bin/env python3
"""SO-V2PKG: cross-check of the Python mirror v2_q.py against the kernel-checked Lean tests of SHARP2-C6
(KAM/CertificateSharp/V2/Tests/Frozen.lean and Tests/RefinedR1.lean), with their exact inputs.

    python3 -I v2_crosscheck.py

Expected (kernel): r1_frozen_passes (frozenCore true at err 1.15e-21), r1_frozen_rejects (false at 1.2e-21),
r1_wf, r1_ok, r1_tail, r1_final (true at 4.7e-12), r1_final_rejects (finalOkA false at 4.8e-12).
"""
import os, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v2_q as V   # noqa: E402

r1Kappa = F(7, 4) / (1 + F(1, 10 ** 6))


def r1Params(err, disp):
    return dict(tau=1, rho=F(1, 70), rhoInf=F(1, 70000), M=F(1924, 1000), sK=F(105, 100) * F(1303, 1000) + F(1, 160),
                sB=F(105, 100) * F(1833, 1000) + F(1, 160), sT=F(105, 100) * F(1022, 1000) / F(7, 4) + F(1, 160),
                mu=F(1, 160), gbar=r1Kappa / 42, som=F(2), nu=F(1, 10 ** 6), gamma=r1Kappa / 42, s=1 + F(1, 10 ** 6),
                err=F(err), E0=F(0), disp=F(disp))


r1Box = [(-(79 - F(2236067977, 10 ** 9)) / 3118 * r1Kappa, F(1, 10 ** 12)), (r1Kappa, F(0))]

r1FrozenWit = dict(Xs=F(120003, 10 ** 10), kp=5, th=F(1, 8),
                   c=[F(8173, 10 ** 5), F(8157, 10 ** 5), F(8149, 10 ** 5), F(1629, 20000), F(8143, 10 ** 5)],
                   cbar=[F(521, 6250), F(8239, 10 ** 5), F(819, 10 ** 4), F(1633, 20000), F(8153, 10 ** 5)],
                   ctail=F(4071, 50000), sB=F(481163, 250000), sT=F(122647, 200000), sLt=F(2736301, 500000),
                   sN=F(658303, 250000), sNt=F(10532843, 10 ** 6), t=F(13675373, 125000), J=4)

r1Claim = dict(dh=F(105, 100) * F(18228, 10000), dx=F(105, 100) * F(175, 100), d2x=F(105, 100) * F(10342, 10000),
               d2h=F(105, 100) * F(18323, 10000), bL=F(105, 100) * F(13268, 10000), bN=F(105, 100) * F(13540, 10000),
               bNt=F(105, 100) * F(13787, 10000), bT=F(105, 100) * F(33130, 10000))

r1RefinedWit = dict(Xs=F(49000), kp=3, th=F(1, 8), c=[F(2978, 10 ** 6), F(2912, 10 ** 6), F(2900, 10 ** 6)],
                    cbar=[F(6745, 10 ** 6), F(4018, 10 ** 6), F(3122, 10 ** 6)], ctail=F(1629, 20000),
                    sB=F(192597, 100000), sT=F(127829, 200000), sLt=F(348323, 250000), sN=F(284731, 200000),
                    sNt=F(362441, 250000), t=F(1767111, 500000), J=4, R=r1Claim)


def main():
    n = 2
    a = V.frozenCore(n, r1Params(F(115, 10 ** 23), F(1, 10 ** 3)), r1Box, r1FrozenWit, detail=True)
    b = V.frozenCore(n, r1Params(F(12, 10 ** 22), F(1, 10 ** 3)), r1Box, r1FrozenWit, detail=True)
    c = V.refinedCore(n, r1Params(F(47, 10 ** 13), F(1, 300)), r1Box, r1RefinedWit, detail=True)
    d = V.refinedCore(n, r1Params(F(48, 10 ** 13), F(1, 300)), r1Box, r1RefinedWit, detail=True)
    print("r1_frozen_passes (kernel: true):", a)
    print("r1_frozen_rejects (kernel: false):", b)
    print("r1_refinedCore numerical part (kernel: true; sites taken as given):", c)
    print("r1_final_rejects (kernel: finalOkA false):", d)
    ok = a[0] and not b[0] and c[0] and not d[0] and not d[1]["final"] and d[1]["okB"]
    print("MIRROR AGREES WITH THE KERNEL TESTS" if ok else "MISMATCH")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
