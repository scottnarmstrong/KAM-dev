#!/usr/bin/env python3
"""V2-BULK: exact mirror of the bulk walk of the three-frequency fibres, producer, and SJS counts.

Untrusted tooling.  Transcribes over int/Fraction, with the Lean names:

  KAM/CertificateSharp/V2/Fiber/Bulk.lean      gTabOk, gTabOk0, minN, maxN, sameSign, colX, colZ, colR,
                                               blkValK, blkK, accOk, hrow, loP, rowB, walkB
  KAM/CertificateSharp/V2/Fiber/BulkSite.lean  bulkSumOk, bulkSiteOk

Everything else (powUp, mulUp, ceilDiv, nearP, tailQ, clockBox2, dboxOk, fibBound, mode3, the landed
walk) comes from `fiber3.py`, the mirror of the landed modules.  The walk is mirrored node by node:
same bisection, same acceptance rule, same integer rounding (every quotient rounded UP).

`bulkSiteOk` returns the Lean Bool; `produce_bulk_site` picks a witness (N, l, J, P, e, D, B, gs,
rn, rd, tol) and the smallest short constant c it certifies; `lean_bulkwit` prints the BulkWit literal.

Usage:
  python3 -I scripts/certifier/fiber3_bulk.py toy     # the toy site of Tests/BulkToy.lean
  python3 -I scripts/certifier/fiber3_bulk.py sjs     # counts on the SJS-plan frequencies
  python3 -I scripts/certifier/fiber3_bulk.py check   # bulk vs landed walk on small boxes
"""
import math
import pathlib
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import fiber3 as f3  # noqa: E402

ceilDiv, mulUp, powUp, nearP = f3.ceilDiv, f3.mulUp, f3.powUp, f3.nearP


# ----------------------------------------------------------------------------- Bulk.lean
def gTab(e, P, L):
    """The geometric table G_0 .. G_L (G_0 = 2^P, G_{t+1} = mulUp(G_t, 2^P + powUp(2^t)))."""
    gs = [2 ** P]
    for t in range(L):
        gs.append(mulUp(P, gs[-1], 2 ** P + powUp(e, P, 64, 2 ** t)))
    return gs


def gTabOk(e, P, t, g, rest):
    for h in rest:
        if not mulUp(P, g, 2 ** P + powUp(e, P, 64, 2 ** t)) <= h:
            return False
        t, g = t + 1, h
    return True


def gTabOk0(e, P, gs):
    return len(gs) > 0 and 2 ** P <= gs[0] and gTabOk(e, P, 0, gs[0], gs[1:])


def minN(a, b):
    return a if a <= b else b


def maxN(a, b):
    return b if a <= b else a


def sameSign(u, w):
    return (u >= 0) == (w >= 0)


def colX(D, a, sg, lo, i):
    q, C0, C1, R0, R1 = D
    return a * C0 + sg * (lo + i) * C1


def colZ(D, a, sg, p, lo, i):
    return colX(D, a, sg, lo, i) + p * 2 ** D[0]


def colR(D, a, lo, i):
    return abs(a) * D[3] + (lo + i) * D[4]


def blkValK(D, e, P, j0, g, Lam, p):
    pa = abs(p)
    Ws = mulUp(P, powUp(e, P, 64, j0), g)
    Wp = mulUp(P, powUp(e, P, 64, j0 + pa), g)
    v = ceilDiv(Wp * 2 ** (2 * D[0]), Lam * Lam)
    v += 0 if pa == 0 else ceilDiv(Ws * 4, (2 * pa - 1) * (2 * pa - 1))
    v += ceilDiv(Ws * powUp(e, P, 64, 1) * 14615, 2 ** P * 2000)
    return v


class Stats:
    def __init__(self):
        self.nodes = 0      # hrow calls below the empty test
        self.leaves = 0     # accepted single fibres
        self.runs = 0       # accepted runs of length >= 2
        self.run_fibres = 0  # fibres in accepted runs
        self.tol_runs = 0   # runs accepted by the tolerance only
        self.vals = 0       # blkValK evaluations

    def __repr__(self):
        return ("nodes %d, single fibres %d, runs %d (%d fibres, %d by tol), values %d"
                % (self.nodes, self.leaves, self.runs, self.run_fibres, self.tol_runs, self.vals))


def blkK(D, e, P, g, acc, a, sg, lo, i0, i1, st=None):
    q = D[0]
    p = nearP(q, colX(D, a, sg, lo, i0))
    Z0, Z1 = colZ(D, a, sg, p, lo, i0), colZ(D, a, sg, p, lo, i1)
    Y0, Y1 = abs(Z0), abs(Z1)
    R0, R1 = colR(D, a, lo, i0), colR(D, a, lo, i1)
    if not (sameSign(Z0, Z1) and R0 < Y0 and R1 < Y1 and 2 * (Y0 + R0) <= 2 ** q
            and 2 * (Y1 + R1) <= 2 ** q):
        return None
    Lam = minN(Y0 - R0, Y1 - R1)
    Gm = maxN(Y0 + R0, Y1 + R1)
    lazy = {}

    def v():
        if "v" not in lazy:
            lazy["v"] = blkValK(D, e, P, abs(a) + lo + i0, g, Lam, p)
            if st is not None:
                st.vals += 1
        return lazy["v"]
    ok, by_tol = acc(Lam, Gm, v)
    if not ok:
        return None
    if st is not None and i1 > i0:
        st.runs += 1
        st.run_fibres += i1 - i0 + 1
        st.tol_runs += by_tol
    elif st is not None:
        st.leaves += 1
    return v()


def accOk(rn, rd, tol):
    def acc(Lam, Gm, v):
        if rd * Gm <= rn * Lam:     # Bool `||` is lazy in the kernel: v is only computed here
            return True, False
        return (v() <= tol), True
    return acc


def acc_true(Lam, Gm, v):
    return True, False


def hrow(D, e, P, G, rn, rd, tol, a, sg, lo, M, t, i0, st=None):
    if M < lo + i0:
        return 0
    if st is not None:
        st.nodes += 1
    if t == 0:
        return blkK(D, e, P, G(0), acc_true, a, sg, lo, i0, i0, st)
    v = blkK(D, e, P, G(t), accOk(rn, rd, tol), a, sg, lo, i0, minN(i0 + (2 ** t - 1), M - lo), st)
    if v is not None:
        return v
    u = hrow(D, e, P, G, rn, rd, tol, a, sg, lo, M, t - 1, i0, st)
    if u is None:
        return None
    w = hrow(D, e, P, G, rn, rd, tol, a, sg, lo, M, t - 1, i0 + 2 ** (t - 1), st)
    if w is None:
        return None
    return u + w


def loP(a):
    return 1 if abs(a) == 0 else 0


def rowB(D, e, P, G, rn, rd, tol, N, l, a, st=None):
    if N < abs(a):
        return 0
    u = hrow(D, e, P, G, rn, rd, tol, a, 1, loP(a), N - abs(a), l, 0, st)
    if u is None:
        return None
    w = hrow(D, e, P, G, rn, rd, tol, a, -1, 1, N - abs(a), l, 0, st)
    if w is None:
        return None
    return u + w


def walkB(D, e, P, G, rn, rd, tol, N, l, st=None):
    tot = 0
    for i in range(2 ** l):          # balFold over i < 2^l: the sum is order-free
        v = rowB(D, e, P, G, rn, rd, tol, N, l, f3.rowA(N, i), st)
        if v is None:
            return None
        tot += v
    return tot


# ----------------------------------------------------------------------------- BulkSite.lean
def getG(w):
    gs = w["gs"]
    return lambda t: gs[t] if t < len(gs) else 0


def bulkWalk(w, st=None):
    return walkB(w["D"], w["e"], w["P"], getG(w), w["rn"], w["rd"], w["tol"], w["N"], w["l"], st)


def bulkSiteOk(n, tau, box, gamma, b, c, w, detail=False, st=None):
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
    if not (w["e"] <= 2 ** w["P"] and 2 ** w["P"] <= w["e"] * f3.expLowQ(2 * b, w["J"])):
        return no("e")
    if not 2 * w["N"] + 1 <= 2 ** w["l"]:
        return no("l")
    if not (w["l"] < len(w["gs"]) and gTabOk0(w["e"], w["P"], w["gs"])):
        return no("gs")
    s = bulkWalk(w, st)
    if s is None:
        return no("mode")
    if not f3.fibBound(box, gamma, b, tau, w, s) <= w["B"]:
        return no("bound")
    kl = f3.clockC(box) - f3.clockR(box)
    if not F(2) ** n * w["B"] * f3.inv(kl ** 2) * (gamma * b ** tau) ** 2 <= (2 * F(31415, 10000) * c) ** 2:
        return no("constant")
    return (True, s) if detail else True


# ----------------------------------------------------------------------------- producer
def choose_N(box, gamma, b, tau, e, P, S_est, tail_frac=F(1, 1000), Nmax=100000):
    delta = 2 * b
    gp = f3.fibGamma(box, gamma)
    N = max(2, math.ceil(tau / (3.14 * float(delta))))
    while True:
        if f3.cLoQ(delta, tau, N) > 0:
            Ep = F(powUp(e, P, 64, N + 1), 2 ** P)
            if float(f3.tailQ(gp, delta, tau, N, Ep)) <= float(tail_frac) * S_est:
                return N
        N += max(1, N // 64)
        if N > Nmax:
            raise ValueError("N too large")


def produce_bulk_site(box, gamma, b, tau, n=3, rn=5, rd=4, tol_frac=F(1, 10 ** 9), tail_frac=F(1, 1000),
                      P=64, q=64, J=None, N=None, S_est=None):
    """Pick (N, l, J, P, e, D, B, gs, rn, rd, tol) and the smallest 4-digit c; returns (w, c, s, stats)."""
    delta = 2 * b
    if J is None:
        J = max(8, int(3 * float(F(628, 100) * delta)) + 8)
    e = f3.ceil_q(F(2) ** P / f3.expLowQ(delta, J))
    cb = f3.clockBox2(box)
    if S_est is None:
        S_est = sd_sum_fiber_np((float(cb[0][0]), float(cb[1][0])), float(delta), 64)
    if N is None:
        N = choose_N(box, gamma, b, tau, e, P, S_est, tail_frac)
    l = (2 * N).bit_length()
    tol = int(float(tol_frac) * S_est * 2 ** P)
    w = {"N": N, "l": l, "J": J, "P": P, "e": e, "D": f3.dbox_for(box, q), "B": F(0),
         "gs": gTab(e, P, l), "rn": rn, "rd": rd, "tol": tol}
    st = Stats()
    s = bulkWalk(w, st)
    if s is None:
        raise ValueError("a fibre fails")
    w["B"] = f3.up(f3.fibBound(box, gamma, b, tau, w, s), 6)
    kl = f3.clockC(box) - f3.clockR(box)
    rhs = F(2) ** n * w["B"] / kl ** 2 * (gamma * b ** tau) ** 2
    c = f3.up(math.sqrt(float(rhs)) / (2 * 3.1415), 4)
    while not (rhs <= (2 * F(31415, 10000) * c) ** 2):
        c = f3.up(float(c) * 1.0001, 4)
    return w, c, s, st


def lean_bulkwit(w):
    """The BulkWit literal."""
    q, C0, C1, R0, R1 = w["D"]
    B = w["B"]
    gs = ",\n      ".join(str(g) for g in w["gs"])
    return ("{ N := %d, l := %d, J := %d, P := %d, e := %d,\n    D := { q := %d, C0 := %d, C1 := %d, R0 := %d, "
            "R1 := %d },\n    B := %d / %d,\n    gs := [%s],\n    rn := %d, rd := %d, tol := %d }"
            % (w["N"], w["l"], w["J"], w["P"], w["e"], q, C0, C1, R0, R1, B.numerator, B.denominator, gs,
               w["rn"], w["rd"], w["tol"]))


# ----------------------------------------------------------------------------- floats
def sd_sum_fiber_np(cs, delta, N):
    """Float value of the landed walk's sum (no rounding, no tail): the fibered bound over 0<|k'|<=N."""
    import numpy as np
    c0, c1 = cs
    k = 2 * math.pi * delta
    E = math.exp(-k)
    tot = E * math.pi ** 2 / 3
    for a in range(-N, N + 1):
        M = N - abs(a)
        b = np.arange(-M, M + 1)
        if a == 0:
            b = b[b != 0]
        x = a * c0 + b * c1
        p = np.floor(0.5 - x)
        y = np.abs(x + p)
        w = np.exp(-k * (abs(a) + np.abs(b)))
        pa = np.abs(p)
        tot += float(np.sum(w * np.exp(-k * pa) / y ** 2
                            + w * (np.where(pa > 0, 1 / np.maximum(pa - 0.5, 0.5) ** 2, 0) + E * (4 + math.pi ** 2 / 3))))
    return tot


# ----------------------------------------------------------------------------- data
def cubic_vec(A, D, th):
    v = [1, th, th * th]
    return [sum(A[i][j] * v[j] for j in range(3)) / D for i in range(3)]


TOY_A = [[-1, 1, 0], [-35, 24, 3], [1, 0, 0]]   # (theta - 1, -35 + 24 theta + 3 theta^2, 1), theta^3 = 2


TOY_LO = F(12599210498948731647672106072782283505702514647015079800819751121, 10 ** 64)   # toyT3RootLo
TOY_HI = F(6299605249474365823836053036391141752851257323507539900409875561, 5 * 10 ** 63)  # toyT3RootHi


def toy_box():
    """The toy frequency (theta - 1, 3 theta^2 + 24 theta - 35, 1), theta = 2^(1/3): the FreqBox of
    Tests/BulkToy.lean (centres to 40 digits, radii 10^-38, exact clock 1), and (theta_c, theta_r)."""
    tc, tr = (TOY_LO + TOY_HI) / 2, (TOY_HI - TOY_LO) / 2
    om = cubic_vec(TOY_A, 1, tc)
    box = [(F(round(om[0] * 10 ** 40), 10 ** 40), F(1, 10 ** 38)),
           (F(round(om[1] * 10 ** 40), 10 ** 40), F(1, 10 ** 38)), (F(1), F(0))]
    for i in range(2):   # the enclosure test of BulkToy.lean (polyAbsUp)
        w0 = TOY_A[i][0] - box[i][0]
        assert f3.polyAbsUp(w0, TOY_A[i][1], TOY_A[i][2], tc, tr) <= box[i][1]
    return box, tc, tr


def sjs_box():
    """SJS (FH25 planar) frequencies, period-1 units, ordered so that the fast frequency is the clock."""
    W = [F("0.0839549288702546301204"), F("0.0338240117059304358259"), F("-0.0000185007988077595")]
    twopi = F(314159265358979323846264338327950288419716939937510, 5 * 10 ** 49)
    om = [w / twopi for w in W]
    r = F(1, 10 ** 30)
    return [(om[1], r), (om[2], r), (om[0], r)], W


def main(argv):
    what = argv[1] if len(argv) > 1 else "toy"
    if what == "check":
        # bulk vs landed walk (same witness data): the bulk value is >= the landed one, within the loss
        box = toy_box()[0]
        gamma = F(77, 250000)
        for b in [F(1, 16), F(1, 32), F(1, 64)]:
            w, c, s, st = produce_bulk_site(box, gamma, b, 2)
            s2 = f3.walk2_fast(lambda a, bb: f3.mode3(w["D"], w["e"], w["P"], a, bb), w["N"])
            fw = {k: w[k] for k in ("N", "l", "J", "P", "e", "D")}
            fw["B"] = f3.up(f3.fibBound(box, gamma, b, 2, fw, s2), 6)
            print(f"b={b} N={w['N']}: bulk s/landed s = {s / s2:.6f}; B bulk {float(w['B']):.6g} landed "
                  f"{float(fw['B']):.6g}; landed fiberSiteOk at the bulk c: "
                  f"{f3.fiberSiteOk(3, 2, box, gamma, b, c, fw)}; {st}")
    elif what == "toy":
        box, tc, tr = toy_box()
        cb = f3.clockBox2(box)
        print("toy box:", [(float(c), float(r)) for c, r in box], " omega' =", [float(c) for c, _ in cb])
        g, Wb = f3.cubic_gamma(-2, 0, 0, tc, tr, TOY_A, 1)
        print("cubic: Wbar = %.6g, gamma = %.6g" % (float(Wb), float(g)))
        gamma = F(math.floor(float(g) * 0.999 * 1e7), 10 ** 7)
        print("gamma used:", gamma, f3.cubicDioOk(-2, 0, 0, tc, tr, TOY_A, 1, gamma))
        for b in [F(1, 16), F(1, 32), F(1, 64)]:
            t0 = time.time()
            w, c, s, st = produce_bulk_site(box, gamma, b, 2)
            dt = time.time() - t0
            ok = bulkSiteOk(3, 2, box, gamma, b, c, w)
            print(f"b={b}: N={w['N']} l={w['l']} fibres={2 * w['N'] * (w['N'] + 1)} c={c} ok={ok} {st} ({dt:.1f}s)")
            print("   classical c = %.4g" % f3.classical_c_float(3, 2, float(b)))
    elif what == "sjs":
        sjs_counts(argv[2:])


def sjs_counts(args):
    box, W = sjs_box()
    cb = f3.clockBox2(box)
    print("omega' =", [float(c) for c, _ in cb])
    gam_fh = {"cubic": F(28, 10 ** 8), "FH": F(169, 10 ** 8)}
    twopi = F(314159265358979323846264338327950288419716939937510, 5 * 10 ** 49)
    S3 = {F("2.649929802480e-03"): 2784427957164.413, F("1.324964901240e-03"): 21711672534550.36,
          F("6.624824506200e-04"): 230513344335294.78}
    rows = []
    for gname, gfh in gam_fh.items():
        gamma = gfh / twopi
        for b, S in S3.items():
            if gname == "FH" and b != max(S3):
                continue
            Sp = S * float(f3.clockC(box)) ** 2
            for rn, rd, tf in ((5, 4, F(1, 10 ** 9)),):
                t0 = time.time()
                w, c, s, st = produce_bulk_site(box, gamma, b, 2, rn=rn, rd=rd, tol_frac=tf, S_est=Sp, P=128)
                dt = time.time() - t0
                full = sd_sum_fiber_np((float(cb[0][0]), float(cb[1][0])), float(2 * b), w["N"])
                infl = float(F(s, 2 ** w["P"])) / full - 1
                fib = 2 * w['N'] * (w['N'] + 1)
                print(f"gamma={gname} b={float(b):.4g}: N={w['N']} fibres={fib:,} "
                      f"S'~{Sp:.4g} walk {full:.6g} bulk {float(F(s, 2 ** w['P'])):.6g} (+{100 * infl:.3f}%) "
                      f"{st} [{dt:.0f}s]", flush=True)
                # kernel laws (handoff V2-BULK): module base 1.6 GB, 4 GB cap; bulk 1.4 ms and 180 KB
                # per node (13k nodes per shard), landed walk 1.2 ms and 215 KB per fibre (11k per shard)
                print(f"    kernel: bulk {st.nodes * 1.4e-3 / 60:.1f} min in {math.ceil(st.nodes / 13000)} shards; "
                      f"landed walk {fib * 1.2e-3 / 3600:.1f} h in {math.ceil(fib / 11000):,} shards", flush=True)
                rows.append((gname, float(b), w["N"], 2 * w["N"] * (w["N"] + 1), st.nodes, st.leaves, st.runs,
                             st.vals, infl))
    return rows


if __name__ == "__main__":
    main(sys.argv)
