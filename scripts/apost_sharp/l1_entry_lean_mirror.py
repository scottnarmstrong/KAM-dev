"""The exact rational mirror of the l1 entry of route A at tau = 1, fixed frequency (SHARP2-B10C).

`entry` mirrors KAM.Sharp2.L1.entryConsts (Ent.* in KAM/Sharp2/L1/EntryA.lean) with e^-1 replaced by an upper
bound `ei`; `stepq` mirrors KAM.Sharp2.RouteA.StepInA (KAM/Sharp2/Examples/MirrorQ.lean); `Run.ok` is
NumQ.okL1 (KAM/Sharp2/Examples/MirrorL1.lean): the entry conditions at X*, B9's conditions from stage 1, the
tail decay, and every cap sum with initial values caM0 and caps cap. Untrusted design tooling: the Lean check
`l1Var_ok` (decide +kernel) is the certificate.
"""
from fractions import Fraction as F
import math, sys

def stepq(n, M1, M2, sK, sB, sT, sLt, sN, sNt, t, c, ca, gb, d, th):
    g = gb * d
    COm = 2 * (n - 1) * c * sLt
    CSym = max(F(1), sB ** 2) * COm
    CRed = n * max(sNt, sLt + 2 * sN)
    w = 2 * M1 * sLt * sK + (2 * n * sK + n * sLt)
    CS = sT * (sNt * g + t * ca * sLt)
    CXiN = CS + c * sLt
    CG = t * CXiN + sNt * g
    CDXi = max(CG, sLt * g)
    CXi = max(c * CG, g * CXiN)
    CDK = sK * c * CG + sN * g * CXiN
    CLin = CRed * CXi + CSym * CDXi
    P = sK + sN
    CE = 2 * P * (gb ** 2 * d) * CLin + M2 / 2 * CDK ** 2
    CGr = n * sLt + 2 * n * sK
    CB = sB ** 2 * CGr / (1 - th)
    CNd = n * sB + sK * CB
    CNtd = CB * sLt + 2 * n * sB
    CDab = 2 * M1 * (CNtd * sN + sNt * CNd) + 2 * M2 * sNt * sN * d
    CDc = sB ** 3 * w * (2 * n * sK + n * sLt)
    CDT = (CDab + CDc) * CDK + 2 * n * sNt * sB * (gb ** 2 * d ** 2) + 2 * sB ** 3 * w * COm * g
    rT = sT ** 2 / (1 - th) * CDT
    rate = [CDK, n * CDK, CB * CDK, rT, 2 * n * CDK, CNd * CDK, CNtd * CDK, CDT]
    def cond(x):
        return (gb ** 4 * d ** 3 * x <= 1 and CSym * (gb ** 3 * d ** 2) * x <= F(1, 2)
                and CE * x <= 1 and sT * CDT * (gb ** 2 * d) * x <= th
                and sB * CGr * CDK * (gb ** 2 * d) * x <= th)
    return dict(CE=CE, CDK=CDK, rate=rate, cond=cond, COm=COm, CRed=CRed, w=w, P=P, g=g)

def entry(n, M1, M2, sK, sB, sT, sLt, sN, sNt, t, c, ca, gb, d, th, E, ei):
    B = stepq(n, M1, M2, sK, sB, sT, sLt, sN, sNt, t, c, ca, gb, d, th)
    g = B["g"]
    aN, aL, t1, tR, G0, Gr, fr = E["aN"], E["aL"], E["t1"], E["tR"], E["G0"], E["Gr"], E.get("frame")
    tavg = min(t, tR); cavg = min(ca * sLt, Gr * aN * g)
    CS = sT * (sNt * g + tavg * cavg)
    cN1 = G0 * aN * g
    CXiN = CS + min(c * sLt, cN1); CXiN1 = CS + cN1
    CG = t * CXiN + sNt * g
    CXiL1 = G0 * g * (t1 * CXiN1 + aL * g)
    CXiL = min(c * CG, CXiL1)
    CXi = max(CXiL, g * CXiN)
    CDK = sK * CXiL + sN * g * CXiN
    COmK = min(B["COm"], n * ei * G0 * aN * g)
    CSym = max(F(1), sB ** 2) * COmK
    CDXi = max(CG, sLt * g)
    CLin = B["CRed"] * CXi + CSym * CDXi
    CE = 2 * B["P"] * (gb ** 2 * d) * CLin + M2 / 2 * CDK ** 2
    if fr:
        CDK1 = fr[0] * CXiL1 + fr[1] * g * CXiN1
        dL = min(n * CDK, ei * CDK1); dLt = min(2 * n * CDK, 2 * n * ei * CDK1)
    else:
        dL = n * CDK; dLt = 2 * n * CDK
    rB = sB ** 2 * (sLt * dL + sK * dLt) / (1 - th)
    rN = sB * dL + sK * rB
    rNt = rB * sLt + sB * dLt
    w = B["w"]
    CDT = (2 * M1 * (rNt * sN + sNt * rN) + 2 * M2 * sNt * sN * d * CDK + sB ** 3 * w * (sK * dLt + sLt * dL)
           + 2 * n * sNt * sB * (gb ** 2 * d ** 2) + sB ** 3 * w * (B["COm"] + COmK) * g)
    rT = sT ** 2 / (1 - th) * CDT
    gram = sB * (sLt * dL + sK * dLt)
    rate = [CDK, dL, rB, rT, dLt, rN, rNt, CDT]
    def cond(x):
        return (gb ** 4 * d ** 3 * x <= 1 and max(F(1), sB ** 2) * COmK * (gb ** 3 * d ** 2) * x <= F(1, 2)
                and CE * x <= 1 and sT * CDT * (gb ** 2 * d) * x <= th and gram * (gb ** 2 * d) * x <= th)
    return dict(CE=CE, CDK=CDK, rate=rate, cond=cond, parts=dict(CS=CS, CXiN=CXiN, CXiL=CXiL, CXiL1=CXiL1,
                COmK=COmK, dL=dL, dLt=dLt, sup=B))

class Run:
    def __init__(s, V, E=None, ei=F(3679, 10000)):
        s.V, s.E, s.ei = V, E, ei
        s.rho, s.rinf = F(1, 50), F(1, 50000)
        s.d0 = min(F(1), (s.rho - s.rinf) / 6)
    def delta(s, k): return F(1, 2 ** k) * s.d0
    def r(s, k): return s.rho - 6 * s.d0 * (1 - F(1, 2 ** k))
    def inp(s, k):
        V = s.V; kp = V["kp"]
        c = V["c"][k] if k < kp else V["ctail"]
        ca = V["cbar"][k] * (s.delta(k) / s.r(k)) if k < kp else V["ctail"]
        d = s.delta(min(k, kp))
        args = (2, F(3), F(3), F(993, 320), V["sB"], V["sT"], V["sLt"], V["sN"], V["sNt"], V["t"], c, ca,
                F(687, 5000), d, V["th"])
        if k == 0 and s.E is not None:
            return entry(*args, s.E, s.ei)
        return stepq(*args)
    def ok(s, Xs, diag=False):
        V = s.V; kp = V["kp"]
        cap = [F(1, 320), F(993, 320), V["sB"], V["sT"], V["sLt"], V["sN"], V["sNt"], V["t"]]
        m0 = [F(0), F(31, 10), F(2), F(50, 11), F(62, 5), F(31, 5), F(124, 5), F(496, 25)]
        jA = [0, 1, 1, 1, 1, 1, 1, 1]
        x = Xs; sums = [F(0)] * 8; fails = []
        gb = F(687, 5000)
        for k in range(kp):
            st = s.inp(k)
            if not st["cond"](x): fails.append("cond%d" % k)
            for i in range(8):
                sums[i] += st["rate"][i] * x * (gb ** 2 * s.delta(k) ** (2 - jA[i]))
            x = 16 * st["CE"] * x * x
        st = s.inp(kp)
        if not st["cond"](x): fails.append("tailcond")
        if 16 * st["CE"] * x > 1: fails.append("J2")
        for i in range(8):
            sums[i] += 2 * st["rate"][i] * x * (gb ** 2 * s.delta(kp) ** (2 - jA[i]))
            if m0[i] + sums[i] > cap[i]: fails.append("sum%d" % i)
        return fails if diag else not fails
    def thresh(s, lo=1e-9, hi=1e-1, it=50):
        lo, hi = math.log10(lo), math.log10(hi)
        for _ in range(it):
            mid = (lo + hi) / 2
            if s.ok(F(10 ** mid).limit_denominator(10 ** 15)): lo = mid
            else: hi = mid
        return lo

freqV = dict(sB=F(20002, 10000), sT=F(61, 10), sLt=F(124001, 10000), sN=F(62002, 10000),
             sNt=F(248005, 10000), t=F(1988, 100), th=F(19, 100),
             c=[F(1524, 100000), F(1512, 100000), F(1508, 100000)],
             cbar=[F(1778, 100000), F(1612, 100000), F(1540, 100000)], ctail=F(8144, 100000), kp=3)
if __name__ == "__main__":
    # The certified run of KAM.Sharp2.Examples.plasmaLean_torus_l1 (PlasmaLeanL1.lean): PLCERT's certified
    # constants (freqC, freqCbar, ctail, kp = 3), caps and theta retuned for the entry, e^-1 <= 0.3679.
    V = dict(freqV, sB=F(20001, 10000), sT=F(512, 100), sLt=F(124001, 10000), sN=F(62001, 10000),
             sNt=F(248003, 10000), t=F(19861, 1000), th=F(8, 100))
    E = dict(aN=F(62, 5), aL=F(124, 5), t1=F(496, 25), tR=F(496, 25), G0=F(551, 100), Gr=F(154, 100),
             frame=(F(31, 10), F(31, 5)))
    R = Run(V, E, ei=F(3679, 10000))
    g, d0 = F(687, 5000), F(333, 100000)
    for Xs in (F(43, 2000), F(218, 10000)):
        print("X* = %s: ok = %s %s; e* = %.4g" % (Xs, R.ok(Xs), R.ok(Xs, diag=True) or "",
                                                  float(Xs * g ** 4 * d0 ** 4)))
    Xs = F(43, 2000); kp = V["kp"]; x = Xs; sumD = F(0)
    for k in range(kp):
        st = R.inp(k); sumD += st["CDK"] * x * R.delta(k) ** 2; x = 16 * st["CE"] * x * x
    st = R.inp(kp); sumD += 2 * st["CDK"] * x * R.delta(kp) ** 2
    print("closeness constant sumD/(X* delta0^4 gamma^2) = %.1f" % float(sumD / (Xs * d0 ** 4 * g ** 2)))
    # PLCERT's sup run for comparison (route A without the entry)
    R0 = Run(freqV)
    print("sup run (PLCERT): X* = 441/10^6 ok = %s" % R0.ok(F(441, 10 ** 6)))
