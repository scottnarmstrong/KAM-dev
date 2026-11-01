#!/usr/bin/env python3
"""V2-BULK-RUNS: exact mirror of the extended bulk walk (tent runs, crossing runs, crossing split).

Untrusted tooling.  Transcribes over int/Fraction, with the Lean names of

  KAM/CertificateSharp/V2/Fiber/BulkRuns.lean   powDownK, gsumK, valK, tentK, apK
  KAM/CertificateSharp/V2/Fiber/Bulk2.lean      plainShape, crossCut, singles, sideAP, hnode, rowB2, walkB2
  KAM/CertificateSharp/V2/Fiber/Bulk2Site.lean  bulk2SiteOk

and reuses `fiber3_bulk.py` (blkK, accOk, gTab, ...) and `fiber3.py` (powUp, mulUp, ceilDiv, nearP,
fibBound, ...).  Same order, same integer rounding (every quotient rounded UP).

Usage:
  python3 -I scripts/certifier/fiber3_bulk2.py toy     # the toy site of Tests/Bulk2Toy.lean
  python3 -I scripts/certifier/fiber3_bulk2.py sjs     # counts on the SJS-plan frequencies
  python3 -I scripts/certifier/fiber3_bulk2.py check   # extended walk vs bulk walk vs landed walk
"""
import math
import pathlib
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import fiber3 as f3  # noqa: E402
import fiber3_bulk as fb  # noqa: E402

ceilDiv, mulUp, powUp, nearP = f3.ceilDiv, f3.mulUp, f3.powUp, f3.nearP


# ----------------------------------------------------------------------------- BulkRuns.lean
def mulDown(P, a, b):
    return (a * b) >> P


def powDown(e, P, f, j):
    """2^P (e/2^P)^j rounded DOWN, by binary powering (0 when the fuel runs out)."""
    if j == 0:
        return 2 ** P
    if f == 0:
        return 0
    h = powDown(e, P, f - 1, j // 2)
    h2 = mulDown(P, h, h)
    return h2 if j % 2 == 0 else mulDown(P, h2, e)


def gsumK(e, P, n):
    """2^P sum_{j<n} (e/2^P)^j, rounded up: 2^P (2^P - powDown(n)) / (2^P - e)."""
    return ceilDiv(2 ** P * (2 ** P - powDown(e, P, 64, n)), 2 ** P - e)


def valK(D, e, P, j0, g, Lam, pw, pz):
    """The mode3-shaped value with weight exponent pw and L0-parameter pz (0: no j = 0 term)."""
    Ws = mulUp(P, powUp(e, P, 64, j0), g)
    Wp = mulUp(P, powUp(e, P, 64, j0 + pw), g)
    v = ceilDiv(Wp * 2 ** (2 * D[0]), Lam * Lam)
    v += 0 if pz == 0 else ceilDiv(Ws * 4, (2 * pz - 1) * (2 * pz - 1))
    v += ceilDiv(Ws * powUp(e, P, 64, 1) * 14615, 2 ** P * 2000)
    return v


def toNat(z):
    return z if z > 0 else 0


def tentK(D, e, P, g, acc, a, sg, lo, i0, i1, st=None):
    """A run across (at most) one half-integer: x + p0 in (0, 1) on the whole run."""
    q = D[0]
    Q = 2 ** q
    X0 = fb.colX(D, a, sg, lo, i0)
    p0 = -(X0 // Q)
    Z0, Z1 = fb.colZ(D, a, sg, p0, lo, i0), fb.colZ(D, a, sg, p0, lo, i1)
    R0, R1 = fb.colR(D, a, lo, i0), fb.colR(D, a, lo, i1)
    Lam = fb.minN(fb.minN(toNat(Z0 - R0), toNat(Q - Z0 - R0)), fb.minN(toNat(Z1 - R1), toNat(Q - Z1 - R1)))
    if not 0 < Lam:
        return None
    pm = fb.minN(abs(p0), abs(p0 - 1))
    pz = fb.maxN(pm, 1)
    lazy = {}

    def v():
        if "v" not in lazy:
            lazy["v"] = valK(D, e, P, abs(a) + lo + i0, g, Lam, pm, pz)
            if st is not None:
                st.vals += 1
        return lazy["v"]
    ok, by_tol = acc(Lam, Q >> 1, v)
    if not ok:
        return None
    if st is not None:
        st.tents += 1
    return v()


def sgnZ(z):
    return 1 if z >= 0 else -1


def apK(D, e, P, g, s, rn, rd, a, sg, lo, i0, i1, st=None):
    """A run of constant p on one side of a crossing, with per-fibre lower bounds F(i)/2^q affine.
    Accepted by its quality alone; the value is computed only for an accepted run (kernel laziness)."""
    if i1 <= i0:
        return None
    q, C0, C1, Rc0, Rc1 = D
    Q = 2 ** q
    p = nearP(q, fb.colX(D, a, sg, lo, i0))
    Z0, Z1 = fb.colZ(D, a, sg, p, lo, i0), fb.colZ(D, a, sg, p, lo, i1)
    Y0, Y1 = abs(Z0), abs(Z1)
    R0, R1 = fb.colR(D, a, lo, i0), fb.colR(D, a, lo, i1)
    if not (fb.sameSign(Z0, Z1) and R0 < Y0 and R1 < Y1 and 2 * (Y0 + R0) <= Q and 2 * (Y1 + R1) <= Q):
        return None
    F0, F1 = Y0 - R0, Y1 - R1
    n = i1 - i0 + 1
    dF = sgnZ(Z0) * sg * C1 - Rc1
    j0 = abs(a) + lo + i0
    pa = abs(p)
    if dF >= 0:                       # receding: F grows with i, as the weights decay
        dn = dF
        u2 = 2 * F0 - dn
        Dp = 2 ** P - e
        den = 2 * dn * 2 ** P + Dp * u2
        if not (dn < 2 * F0 and 0 < den):
            return None
        if not s * dn <= F0:
            return None
        m = powDown(e, P, 64, n)
        num = 2 ** P * (u2 + 2 * n * dn) - m * u2
        first = ceilDiv(powUp(e, P, 64, j0 + pa) * 2 ** (2 * q + 2) * num, den * u2 * (u2 + 2 * n * dn))
    else:                             # approaching: F decays with i, toward a crossing
        ea = -dF
        if not ea < 2 * F1:
            return None
        if not (s * ea <= F1 and rd * 2 ** P <= rn * powUp(e, P, 64, n - 1)):
            return None
        first = ceilDiv(powUp(e, P, 64, j0 + pa) * 2 ** (2 * q + 2) * n,
                        (2 * F1 - ea) * (2 * F1 + (2 * n - 1) * ea))
    Ws = mulUp(P, powUp(e, P, 64, j0), g)
    v = first + (0 if pa == 0 else ceilDiv(Ws * 4, (2 * pa - 1) * (2 * pa - 1)))
    v += ceilDiv(Ws * powUp(e, P, 64, 1) * 14615, 2 ** P * 2000)
    if st is not None:
        st.vals += 1
        st.aps += 1
    return v


def plainShape(D, a, sg, lo, i0, i1):
    """The shape test shared by plain and crossing runs."""
    q = D[0]
    Q = 2 ** q
    p = nearP(q, fb.colX(D, a, sg, lo, i0))
    Z0, Z1 = fb.colZ(D, a, sg, p, lo, i0), fb.colZ(D, a, sg, p, lo, i1)
    Y0, Y1 = abs(Z0), abs(Z1)
    R0, R1 = fb.colR(D, a, lo, i0), fb.colR(D, a, lo, i1)
    return fb.sameSign(Z0, Z1) and R0 < Y0 and R1 < Y1 and 2 * (Y0 + R0) <= Q and 2 * (Y1 + R1) <= Q


def crossCut(D, a, sg, lo, s, i0, i1):
    """The cuts (c0, c1) around the integer crossed by the centre line, or None."""
    q, C0, C1, R0, R1 = D
    Q = 2 ** q
    X0, X1 = fb.colX(D, a, sg, lo, i0), fb.colX(D, a, sg, lo, i1)
    f0, f1 = X0 // Q, X1 // Q
    if f0 == f1:
        return None
    m = max(f0, f1)
    dX = abs(sg * C1)
    if dX == 0:
        return None
    k = abs(m * Q - X0) // dX
    ic = i0 + fb.minN(k, i1 - i0)
    c0 = i0 + toNat((ic - i0) - s)
    c1 = fb.minN(ic + s + 1, i1 + 1)
    return c0, c1, ic


def singles(D, e, P, a, sg, lo, i0, n, st=None):
    tot = 0
    for j in range(n):
        if st is not None:
            st.nodes += 1
        v = fb.blkK(D, e, P, 2 ** P, fb.acc_true, a, sg, lo, i0 + j, i0 + j, st)
        if v is None:
            return None
        tot += v
    return tot


class Stats(fb.Stats):
    def __init__(self):
        super().__init__()
        self.tents = 0
        self.aps = 0
        self.cuts = 0
        self.light = 0
        self.halves = 0

    def __repr__(self):
        return (super().__repr__() + ", tents %d, crossing runs %d, crossing splits %d (light %d), halvings %d"
                % (self.tents, self.aps, self.cuts, self.light, self.halves))


def oadd(u, w):
    return None if u is None or w is None else u + w


def sideAP(D, e, P, W, a, sg, lo, i0, n, st=None):
    """A crossing side as one crossing run (empty side: 0)."""
    if n == 0:
        return 0
    if n == 1:
        return fb.blkK(D, e, P, 2 ** P, fb.acc_true, a, sg, lo, i0, i0, st)
    return apK(D, e, P, gsumK(e, P, n), W["s"], W["rn"], W["rd"], a, sg, lo, i0, i0 + n - 1, st)


def hnode(D, e, P, W, a, sg, lo, fuel, i0, n, st=None):
    if n == 0:
        return 0
    if st is not None:
        st.nodes += 1
    i1 = i0 + n - 1
    if n == 1:
        return fb.blkK(D, e, P, 2 ** P, fb.acc_true, a, sg, lo, i0, i0, st)
    acc = fb.accOk(W["rn"], W["rd"], W["tol"])
    g = gsumK(e, P, n)
    if plainShape(D, a, sg, lo, i0, i1):
        v = fb.blkK(D, e, P, g, acc, a, sg, lo, i0, i1, st)
        if v is None:
            v = apK(D, e, P, g, W["s"], W["rn"], W["rd"], a, sg, lo, i0, i1, st)
    else:
        v = tentK(D, e, P, g, acc, a, sg, lo, i0, i1, st)
    if v is not None:
        return v
    if fuel == 0:
        return None
    cc = crossCut(D, a, sg, lo, W["s"], i0, i1)
    if cc is not None:
        c0, c1, ic = cc
        if st is not None:
            st.cuts += 1
        # light crossing: the crossing fibre alone and one crossing run on each side
        lt = oadd(oadd(sideAP(D, e, P, W, a, sg, lo, i0, ic - i0, st),
                       fb.blkK(D, e, P, 2 ** P, fb.acc_true, a, sg, lo, ic, ic, st)),
                  sideAP(D, e, P, W, a, sg, lo, ic + 1, i1 - ic, st))
        if lt is not None:
            if st is not None:
                st.light += 1
            return lt
        return oadd(oadd(hnode(D, e, P, W, a, sg, lo, fuel - 1, i0, c0 - i0, st),
                         singles(D, e, P, a, sg, lo, c0, c1 - c0, st)),
                    hnode(D, e, P, W, a, sg, lo, fuel - 1, c1, i1 + 1 - c1, st))
    h = (n + 1) // 2
    if st is not None:
        st.halves += 1
    return oadd(hnode(D, e, P, W, a, sg, lo, fuel - 1, i0, h, st),
                hnode(D, e, P, W, a, sg, lo, fuel - 1, i0 + h, n - h, st))


def rowB2(D, e, P, W, N, l, a, st=None):
    if N < abs(a):
        return 0
    M = N - abs(a)
    lp = fb.loP(a)
    u = hnode(D, e, P, W, a, 1, lp, W["fuel"], 0, M + 1 - lp, st)
    if u is None:
        return None
    w = hnode(D, e, P, W, a, -1, 1, W["fuel"], 0, M, st)
    return oadd(u, w)


def walkB2(D, e, P, W, N, l, st=None):
    tot = 0
    for i in range(2 ** l):
        v = rowB2(D, e, P, W, N, l, f3.rowA(N, i), st)
        if v is None:
            return None
        tot += v
    return tot


# ----------------------------------------------------------------------------- Bulk2Site.lean
def bulk2Walk(w, st=None):
    return walkB2(w["D"], w["e"], w["P"], w, w["N"], w["l"], st)


def bulk2SiteOk(n, tau, box, gamma, b, c, w, detail=False, st=None):
    """The Lean Bool (in the order of the conjunction)."""
    def no(why):
        return (False, why) if detail else False
    if n != 3:
        return no("n")
    if not (0 < c and 0 < b and 0 < gamma):
        return no("c, b, gamma")
    if not 0 < f3.clockC(box) - f3.clockR(box):
        return no("clock")
    if not f3.dboxOk(box, w["D"]):
        return no("dbox")
    if not 0 < f3.cLoQ(2 * b, tau, w["N"]):
        return no("cLoQ")
    if not (w["e"] < 2 ** w["P"] and 2 ** w["P"] <= w["e"] * f3.expLowQ(2 * b, w["J"])):
        return no("e")
    if not 2 * w["N"] + 1 <= 2 ** w["l"]:
        return no("l")
    s = bulk2Walk(w, st)
    if s is None:
        return no("mode")
    if not f3.fibBound(box, gamma, b, tau, w, s) <= w["B"]:
        return no("bound")
    kl = f3.clockC(box) - f3.clockR(box)
    if not F(2) ** n * w["B"] * f3.inv(kl ** 2) * (gamma * b ** tau) ** 2 <= (2 * F(31415, 10000) * c) ** 2:
        return no("constant")
    return (True, s) if detail else True


def produce_bulk2_site(box, gamma, b, tau, n=3, rn=5, rd=4, tol_frac=F(1, 10 ** 9), s=2, fuel=64,
                       tail_frac=F(1, 1000), P=64, q=64, J=None, N=None, S_est=None):
    """Pick the witness and the smallest 4-digit c; returns (w, c, s, stats)."""
    delta = 2 * b
    if J is None:
        J = max(8, int(3 * float(F(628, 100) * delta)) + 8)
    e = f3.ceil_q(F(2) ** P / f3.expLowQ(delta, J))
    cb = f3.clockBox2(box)
    if S_est is None:
        S_est = fb.sd_sum_fiber_np((float(cb[0][0]), float(cb[1][0])), float(delta), 64)
    if N is None:
        N = fb.choose_N(box, gamma, b, tau, e, P, S_est, tail_frac)
    l = (2 * N).bit_length()
    tol = int(float(tol_frac) * S_est * 2 ** P)
    w = {"N": N, "l": l, "J": J, "P": P, "e": e, "D": f3.dbox_for(box, q), "B": F(0),
         "rn": rn, "rd": rd, "tol": tol, "s": s, "fuel": fuel}
    st = Stats()
    sv = bulk2Walk(w, st)
    if sv is None:
        raise ValueError("a fibre fails or the fuel runs out")
    w["B"] = f3.up(f3.fibBound(box, gamma, b, tau, w, sv), 6)
    kl = f3.clockC(box) - f3.clockR(box)
    rhs = F(2) ** n * w["B"] / kl ** 2 * (gamma * b ** tau) ** 2
    c = f3.up(math.sqrt(float(rhs)) / (2 * 3.1415), 4)
    while not (rhs <= (2 * F(31415, 10000) * c) ** 2):
        c = f3.up(float(c) * 1.0001, 4)
    return w, c, sv, st


def lean_bulk2wit(w):
    q, C0, C1, R0, R1 = w["D"]
    B = w["B"]
    return ("{ N := %d, l := %d, J := %d, P := %d, e := %d,\n    D := { q := %d, C0 := %d, C1 := %d, R0 := %d, "
            "R1 := %d },\n    B := %d / %d,\n    rn := %d, rd := %d, tol := %d, s := %d, fuel := %d }"
            % (w["N"], w["l"], w["J"], w["P"], w["e"], q, C0, C1, R0, R1, B.numerator, B.denominator,
               w["rn"], w["rd"], w["tol"], w["s"], w["fuel"]))


def main(argv):
    what = argv[1] if len(argv) > 1 else "toy"
    if what == "toy":
        box, tc, tr = fb.toy_box()
        gamma = F(77, 250000)
        for b in [F(1, 16), F(1, 32), F(1, 64)]:
            w, c, sv, st = produce_bulk2_site(box, gamma, b, 2)
            w1, c1, s1, st1 = fb.produce_bulk_site(box, gamma, b, 2)
            print(f"b={b}: N={w['N']} fibres={2 * w['N'] * (w['N'] + 1)} c={c} (bulk walk c={c1}) "
                  f"value/bulk {sv / s1:.6f}; {st}; bulk walk nodes {st1.nodes}")
    elif what == "check":
        box, tc, tr = fb.toy_box()
        gamma = F(77, 250000)
        for b in [F(1, 16), F(1, 32)]:
            w, c, sv, st = produce_bulk2_site(box, gamma, b, 2)
            s2 = f3.walk2_fast(lambda a, bb: f3.mode3(w["D"], w["e"], w["P"], a, bb), w["N"])
            print(f"b={b}: extended/landed walk value {sv / s2:.6f}; site ok {bulk2SiteOk(3, 2, box, gamma, b, c, w)}")
    elif what == "sjs":
        sjs(argv[2:])


def sjs(args):
    box, W = fb.sjs_box()
    cb = f3.clockBox2(box)
    twopi = F(314159265358979323846264338327950288419716939937510, 5 * 10 ** 49)
    S3 = {F("2.649929802480e-03"): 2784427957164.413, F("1.324964901240e-03"): 21711672534550.36,
          F("6.624824506200e-04"): 230513344335294.78}
    for gname, gfh in {"cubic": F(28, 10 ** 8), "FH": F(169, 10 ** 8)}.items():
        gamma = gfh / twopi
        for b, S in S3.items():
            if gname == "FH" and b != max(S3):
                continue
            Sp = S * float(f3.clockC(box)) ** 2
            t0 = time.time()
            P = 128     # at all bites (audit AUDIT-V2-BULK-RUNS-1, E1: P = 64 gave a larger N and no gain)
            w, c, sv, st = produce_bulk2_site(box, gamma, b, 2, S_est=Sp, P=P)
            dt = time.time() - t0
            full = fb.sd_sum_fiber_np((float(cb[0][0]), float(cb[1][0])), float(2 * b), w["N"])
            infl = float(F(sv, 2 ** w["P"])) / full - 1
            fib = 2 * w['N'] * (w['N'] + 1)
            print(f"gamma={gname} b={float(b):.4g} P={P}: N={w['N']} fibres={fib:,} c={c} (+{100 * infl:.3f}% over "
                  f"the float sum) {st} [{dt:.0f}s]", flush=True)


if __name__ == "__main__":
    main(sys.argv)
