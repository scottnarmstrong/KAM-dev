#!/usr/bin/env python3
"""SO-DATA-1: mirror of the LANDED packed product route and the advice generator (untrusted tooling).

Literal transcriptions (landed bodies, not the SO-DATA-PY proposals):
  Poly/Packed.lean     packSum/packShift (fast, = packShift_eq), intSlotsBound (balanced digits, tested equal to
                       the loop in sodata_packed), maxAbs
  Poly/Layout.lean     PackLayout, packDot, packDigits, packNoWrap, keyInBox, denseLen, packSlotAux, dense,
                       prodKey, compat
  Poly/Advice.lean     PackedAdvice, reconFitsAux, shardFits (max over the first s+1 blocks), blockLen, cut,
                       prodLen, packDigitsIn, boxLow/boxHigh, inBox, shardLogs, combined, windowZeroOK,
                       adviceZeroOK, targetSubBox, shapeOK, shardPacked, checkShard, checkPackedProduct
  Poly/MulPacked.lean  certMantPair/toMants (CertFixed: mantCheck at P = soPrecision), slotDeg, slotErr,
                       maxSlotDeg, remainderBound (exact), targetEntry/targetTerms, packedRealProduct,
                       ofDyadicScaled, dyadicTerms, CertPoly.mulPacked

Differences from the SO-DATA-PY mirror (sodata_packed.py), all in the landed bodies:
  * shardFits bounds max|.| over the first s+1 blocks of A and B only (proposed: all blocks);
  * shapeOK does not compare lb.blockRows; compat is packNoWrap (s1·(dA1+dB1-1) <= s0, s1 >= 1);
  * inBox is the digit test packDigitsIn (no `i < prodLen` conjunct; window slots >= prodLen must be zero by
    windowZeroOK);
  * an empty real part costs nothing (packedRealProduct returns ([], 0) before any check), so the advice of a
    zero part is never read: the generator emits a one-slot placeholder for it.
"""
import math
from fractions import Fraction as F

import sofx_arith as A
from sodata_packed import pack_sum, balanced_digits

R_DEFAULT = 32


def nsub(a, b):
    return a - b if a > b else 0


class Layout:
    __slots__ = ("lo", "dims", "stride", "width", "blockRows")

    def __init__(self, lo, dims, stride, width, blockRows):
        self.lo, self.dims, self.stride = tuple(lo), tuple(dims), tuple(stride)
        self.width, self.blockRows = width, blockRows

    def json(self):
        return [list(self.lo), list(self.dims), list(self.stride), self.width, self.blockRows]


class Advice:
    __slots__ = ("la", "lb", "target", "scale", "rounded", "outLog")

    def __init__(self, la, lb, target, scale, rounded, outLog):
        self.la, self.lb, self.target, self.scale, self.rounded, self.outLog = la, lb, target, scale, rounded, outLog


def getD(L, j, d=0):
    return L[j] if j < len(L) else d


def packDot(u, s):
    return sum(a * b for a, b in zip(u, s))


def packDigits(ss, i):
    out = []
    for s in ss:
        out.append(i // s if s else 0)
        i = i % s if s else i
    return out


def packNoWrap(ss, es):
    if len(ss) != len(es) or not ss:
        return len(ss) == 0 and len(es) == 0
    if len(ss) == 1:
        return 1 <= ss[0]
    return ss[1] * es[1] <= ss[0] and packNoWrap(ss[1:], es[1:])


def denseLen(L):
    if all(0 < d for d in L.dims):
        return 1 + packDot([d - 1 for d in L.dims], L.stride)
    return 0


def packSlotAux(k, lo, ds, ss):
    if len(k) != len(ds):
        return None
    acc = 0
    for j, x in enumerate(k):
        u = x - getD(lo, j)
        if u < 0 or u >= ds[j]:
            return None
        acc += u * getD(ss, j)
    return acc


def dense(L, cs):
    slots = []
    for k, v in cs:
        q = packSlotAux(k, L.lo, L.dims, L.stride)
        if q is None:
            return None
        slots.append((q, v))
    n = denseLen(L)
    out = [0] * n
    for q, v in slots:
        if q < n:
            out[q] += v
    return out


def prodKey(La, Lb, i):
    dg = packDigits(La.stride, i)
    return tuple(getD(La.lo, j) + getD(Lb.lo, j) + getD(dg, j) for j in range(len(La.dims)))


def compat(n, La, Lb):
    return (len(La.dims) == n and len(Lb.dims) == n and len(La.stride) == n and La.stride == Lb.stride
            and La.width == Lb.width
            and packNoWrap(list(La.stride), [a + b - 1 for a, b in zip(La.dims, Lb.dims)]))


def blockLen(adv):
    return adv.la.blockRows * (adv.la.stride[0] if adv.la.stride else 1)


def cut(adv, d):
    L = blockLen(adv)
    out = []
    if L == 0:
        return out      # packCutAux with an empty block never empties d; fuel = length d (rejected by shapeOK)
    for s in range(0, len(d), L):
        blk = d[s:s + L]
        out.append(blk + [0] * (L - len(blk)))
    return out


def prodLen(adv):
    return nsub(denseLen(adv.la) + denseLen(adv.lb), 1)


def boxLow(adv):
    return [max(0, getD(adv.target.lo, j) - getD(adv.la.lo, j) - getD(adv.lb.lo, j)) for j in range(len(adv.la.dims))]


def boxHigh(adv):
    return [max(0, getD(adv.target.lo, j) + getD(adv.target.dims, j) - getD(adv.la.lo, j) - getD(adv.lb.lo, j))
            for j in range(len(adv.la.dims))]


class InBox:
    """PackedAdvice.inBox for all window slots (cached; the digit test packDigitsIn)."""

    def __init__(self, adv):
        self.ok_axes = len(adv.target.dims) == len(adv.la.dims) and len(adv.la.stride) == len(adv.la.dims)
        self.ss, self.lo, self.hi = list(adv.la.stride), boxLow(adv), boxHigh(adv)

    def __call__(self, i):
        if not self.ok_axes:
            return False
        for s, a, b in zip(self.ss, self.lo, self.hi):
            d = i // s if s else 0
            if not (a <= d < b):
                return False
            i = i % s if s else i
        return True


def shardLogs(adv, s, box):
    L = blockLen(adv)
    hi = nsub(adv.scale, 1)
    return [hi if box(s * L + i) else adv.outLog for i in range(nsub(2 * L, 1))]


def combined(adv):
    L = blockLen(adv)
    n = prodLen(adv)
    out = [0] * n
    for s, r in enumerate(adv.rounded):
        base = s * L
        for i, x in enumerate(r):
            if x and base + i < n:
                out[base + i] += x
    return out


def targetSubBox(adv):
    la, lb, t = adv.la, adv.lb, adv.target
    if len(t.dims) != len(la.dims):
        return False
    for j in range(len(la.dims)):
        lo = getD(la.lo, j) + getD(lb.lo, j)
        if not (lo <= getD(t.lo, j)):
            return False
        if not (getD(t.lo, j) + getD(t.dims, j) <= lo + nsub(getD(la.dims, j) + getD(lb.dims, j), 1)):
            return False
    return True


def shapeOK(adv, box, why=None):
    def fail(m):
        if why is not None:
            why.append(m)
        return False
    L = blockLen(adv)
    if not (1 <= adv.scale and 0 < adv.la.width and 0 < adv.la.blockRows and 0 < L):
        return fail("scale/width/blockRows/blockLen")
    if not compat(len(adv.la.dims), adv.la, adv.lb):
        return fail("compat")
    if not (adv.lb.width == adv.la.width and adv.target.width == adv.la.width):
        return fail("widths")
    if not targetSubBox(adv):
        return fail("targetSubBox")
    pl = prodLen(adv)
    for s, r in enumerate(adv.rounded):
        if len(r) != 2 * L - 1:
            return fail("window length")
        base = s * L
        for i, c in enumerate(r):
            if c != 0 and (base + i >= pl or not box(base + i)):
                return fail("adviceZeroOK window %d slot %d" % (s, i))
    return True


def maxAbsFlat(blocks):
    m = 0
    for x in blocks:
        for c in x:
            a = c if c >= 0 else -c
            if a > m:
                m = a
    return m


def checkShard(adv, Ablk, Bblk, s, box, PA, PB, why=None):
    def fail(m):
        if why is not None:
            why.append(m)
        return False
    L = blockLen(adv)
    w = adv.la.width
    if any(len(x) != L for x in Ablk) or any(len(x) != L for x in Bblk):
        return fail("block length")
    r = adv.rounded[s] if s < len(adv.rounded) else []
    if len(r) != 2 * L - 1:
        return fail("window length")
    At, Bt = Ablk[:s + 1], Bblk[:s + 1]
    if any(len(x) > L for x in At) or any(len(x) > L for x in Bt):
        return fail("shardFits lengths")
    if not (2 * (s + 1) * L * maxAbsFlat(At) * maxAbsFlat(Bt) < (1 << w)):
        return fail("shardFits")
    logs = shardLogs(adv, s, box)
    lim = 1 << w
    for c, g in zip(r, logs):
        if not (2 * ((abs(c) << adv.scale) + (1 << g)) < lim):
            return fail("reconFits")
    X = 0
    for i in range(s + 1):
        a = PA[i] if i < len(PA) else 0
        b = PB[s - i] if s - i < len(PB) else 0
        X += a * b
    X -= pack_sum(w, r) << adv.scale
    e = balanced_digits(w, 2 * L - 1, X)
    if e is None:
        return fail("intSlotsBound leftover (window %d)" % s)
    for x, g in zip(e, logs):
        if abs(x) > (1 << g):
            return fail("intSlotsBound (window %d)" % s)
    return True


def checkPackedProduct(adv, da, db, why=None):
    box = InBox(adv)
    if not shapeOK(adv, box, why):
        return False
    if len(da) != denseLen(adv.la) or len(db) != denseLen(adv.lb) or not da or not db:
        if why is not None:
            why.append("raw lengths")
        return False
    Ab, Bb = cut(adv, da), cut(adv, db)
    ns = nsub(len(Ab) + len(Bb), 1)
    if len(adv.rounded) != ns:
        if why is not None:
            why.append("shard count")
        return False
    w = adv.la.width
    PA = [pack_sum(w, x) for x in Ab]
    PB = [pack_sum(w, x) for x in Bb]
    for s in range(ns):
        if not checkShard(adv, Ab, Bb, s, box, PA, PB, why):
            return False
    return True


# ---------------------------------------------------------------------------------------------- MulPacked
def slotDegs(adv):
    n = prodLen(adv)
    st = adv.la.stride
    lo = [getD(adv.la.lo, j) + getD(adv.lb.lo, j) for j in range(len(adv.la.dims))]
    out = []
    for i in range(n):
        d, x = 0, i
        for j, s in enumerate(st):
            q = x // s if s else 0
            x = x % s if s else x
            v = lo[j] + q
            d += v if v >= 0 else -v
        out.append(d)
    return out


def remainderBound(adv, W, P2, degs=None, box=None):
    degs = slotDegs(adv) if degs is None else degs
    box = InBox(adv) if box is None else box
    if not degs:
        return F(0)
    D = max(degs)
    num, den = W.w.numerator, W.w.denominator
    pn = {}
    tot = 0
    hi_in, hi_out = 1 << adv.scale, 1 << (adv.outLog + 1)
    for i, d in enumerate(degs):
        if d not in pn:
            pn[d] = num ** d * den ** (D - d)
        tot += (hi_in if box(i) else hi_out) * pn[d]
    return F(tot, den ** D * 2 ** P2)


def targetTerms(adv):
    out = []
    for i, c in enumerate(combined(adv)):
        if c != 0:
            out.append((prodKey(adv.la, adv.lb, i), c))
    return out


def toMants(B, P, poly):
    """CertPoly.toMants (B.toMant P, verified by mantCheck): (re part, im part) or None."""
    re, im = [], []
    for k, c in poly:
        zr, zi = B.toMant(P, c[0]), B.toMant(P, c[1])
        if zr is None or zi is None or not A.mantCheck(B, P, c[0], zr) or not A.mantCheck(B, P, c[1], zi):
            return None
        if zr != 0:
            re.append((k, zr))
        if zi != 0:
            im.append((k, zi))
    return re, im


def ofDyadicScaled(B, P2, sc, c):
    return A.ofDyadic(B, nsub(P2, sc), c * 2 ** nsub(sc, P2))


class PackedEngine:
    """Generator + landed checker of `ProductAdvice.packed` products (CertFixed backends only)."""

    def __init__(self, budgets, blockRows=R_DEFAULT, log=None):
        self.budgets = budgets          # cfg name -> rational budget of the packed remainder
        self.blockRows = blockRows
        self.log = log if log is not None else []
        self.last_info = None
        self.stats = []

    # ---- landed route
    def packedRealProduct(self, adv, W, P2, x, y, why=None):
        if not x or not y:
            return [], F(0)
        da, db = dense(adv.la, x), dense(adv.lb, y)
        if da is None or db is None:
            if why is not None:
                why.append("dense")
            return None
        if not checkPackedProduct(adv, da, db, why):
            return None
        return targetTerms(adv), remainderBound(adv, W, P2)

    def mulPacked(self, B, W, padv, a, b):
        _, P, rr, ii, ri, ir = padv
        ma, mb = toMants(B, P, a), toMants(B, P, b)
        why = []
        self.last_info = dict(P=P, why=why)
        if ma is None or mb is None:
            why.append("toMants")
            return None
        res = []
        for adv, x, y in ((rr, ma[0], mb[0]), (ii, ma[1], mb[1]), (ri, ma[0], mb[1]), (ir, ma[1], mb[0])):
            p = self.packedRealProduct(adv, W, 2 * P, x, y, why)
            if p is None:
                return None
            res.append((adv, p))
        terms = []
        z = B.ofInt(0)
        for idx, (adv, (ts, _)) in enumerate(res):
            sgn = -1 if idx == 1 else 1
            for k, c in ts:
                v = ofDyadicScaled(B, 2 * P, adv.scale, sgn * c)
                if v is None:
                    why.append("ofDyadic")
                    return None
                terms.append((k, (v, z) if idx < 2 else (z, v)))
        rem = sum((p[1] for _, p in res), F(0))
        self.last_info["rem"] = rem
        return terms, B.ofRatUp(rem)

    # ---- generator
    def generate(self, B, W, root, fk, a, b):
        P = B.P
        ma, mb = toMants(B, P, a), toMants(B, P, b)
        assert ma is not None and mb is not None
        budget = F(self.budgets[root.name])
        nz = sum(1 for x, y in ((ma[0], mb[0]), (ma[1], mb[1]), (ma[0], mb[1]), (ma[1], mb[0])) if x and y)
        advs, infos = [], []
        for x, y in ((ma[0], mb[0]), (ma[1], mb[1]), (ma[0], mb[1]), (ma[1], mb[0])):
            if x and y:
                adv, info = self.build_real(x, y, W, P, budget / max(nz, 1))
            else:
                adv, info = placeholder(), dict(zero=True)
            advs.append(adv)
            infos.append(info)
        self.stats.append((fk, infos))
        return ("packed", P, advs[0], advs[1], advs[2], advs[3])

    def build_real(self, x, y, W, P, budget):
        R = self.blockRows

        def box_of(cs):
            k0 = [k[0] for k, _ in cs]
            k1 = [k[1] for k, _ in cs]
            return (min(k0), min(k1)), (max(k0) - min(k0) + 1, max(k1) - min(k1) + 1)
        (loa, dA), (lob, dB) = box_of(x), box_of(y)
        st = (dA[1] + dB[1] - 1, 1)
        la, lb = Layout(loa, dA, st, 0, R), Layout(lob, dB, st, 0, R)
        da, db = dense(la, x), dense(lb, y)
        adv0 = Advice(la, lb, la, 1, [], 0)
        L = blockLen(adv0)
        Ab, Bb = cut(adv0, da), cut(adv0, db)
        ns = len(Ab) + len(Bb) - 1
        mA, mB = maxAbsFlat(Ab), maxAbsFlat(Bb)
        w0 = (2 * len(Ab) * L * mA * mB).bit_length() + 1
        PA = [pack_sum(w0, v) for v in Ab]
        PB = [pack_sum(w0, v) for v in Bb]
        T = []
        for s in range(ns):
            X = 0
            for i in range(max(0, s - len(Bb) + 1), min(len(Ab), s + 1)):
                X += PA[i] * PB[s - i]
            e = balanced_digits(w0, 2 * L - 1, X)
            assert e is not None
            T.append(e)
        plen = len(da) + len(db) - 1
        r0, c0 = loa[0] + lob[0], loa[1] + lob[1]
        sst = st[0]
        lw = math.log2(float(W.w))
        # per product slot: degree, and the max over windows of |T| (outLog) and the combined value
        deg = [abs(r0 + q // sst) + abs(c0 + q % sst) for q in range(plen)]
        wmax = [0] * plen
        for s, Ts in enumerate(T):
            base = s * L
            for i, v in enumerate(Ts):
                if v:
                    q = base + i
                    av = abs(v)
                    if q < plen and av > wmax[q]:
                        wmax[q] = av
        # box sweep: include the slots whose log2(|T| W) is within e of the top
        mag = [(math.log2(wmax[q]) + deg[q] * lw, q) for q in range(plen) if wmax[q]]
        mag.sort(reverse=True)
        logb = math.log2(float(budget / 2)) + 2 * P
        Wq = [deg[q] * lw for q in range(plen)]
        totW = _logsumexp2(Wq)
        best = None
        bx = None
        # grow the box by thresholds (coarse sweep by 1 bit of magnitude)
        idx = 0
        rows_lo = rows_hi = cols_lo = cols_hi = None
        thresholds = sorted(set(int(m) for m, _ in mag), reverse=True)
        mi = 0
        for th in thresholds:
            while mi < len(mag) and mag[mi][0] >= th:
                q = mag[mi][1]
                rr, cc = q // sst, q % sst
                if rows_lo is None:
                    rows_lo = rows_hi = rr; cols_lo = cols_hi = cc
                else:
                    rows_lo, rows_hi = min(rows_lo, rr), max(rows_hi, rr)
                    cols_lo, cols_hi = min(cols_lo, cc), max(cols_hi, cc)
                mi += 1
            # out-of-box max |T| and weight mass (float estimate)
            outlog, wout = 0, []
            for q in range(plen):
                rr, cc = q // sst, q % sst
                if not (rows_lo <= rr <= rows_hi and cols_lo <= cc <= cols_hi):
                    wout.append(Wq[q])
                    if wmax[q]:
                        g = _lg(wmax[q])
                        if g > outlog:
                            outlog = g
            lw_out = _logsumexp2(wout) if wout else -1e300
            if outlog + 1 + lw_out <= logb - 0.01:
                bx = (rows_lo, rows_hi, cols_lo, cols_hi, outlog)
                break
        assert bx is not None, "no target box"
        rows_lo, rows_hi, cols_lo, cols_hi, outlog = bx
        target = Layout((r0 + rows_lo, c0 + cols_lo), (rows_hi - rows_lo + 1, cols_hi - cols_lo + 1), st, 0, R)
        adv = Advice(la, lb, target, 1, [], outlog)
        box = InBox(adv)
        degs = deg
        # largest scale with the exact remainder <= budget
        win_log = _logsumexp2([Wq[q] for q in range(plen) if box(q)])
        scale = max(1, int(math.floor(logb - win_log)) + 2)
        while True:
            adv.scale = scale
            if remainderBound(adv, W, 2 * P, degs, box) <= budget or scale == 1:
                break
            scale -= 1
        assert remainderBound(adv, W, 2 * P, degs, box) <= budget, "budget below resolution"
        half = 1 << (scale - 1)
        rounded = []
        for s, Ts in enumerate(T):
            base = s * L
            rounded.append([((v + half) >> scale) if (box(base + i) and base + i < plen) else 0
                            for i, v in enumerate(Ts)])
        adv.rounded = rounded
        w = w0
        for s in range(ns):
            logs = shardLogs(adv, s, box)
            for c, g in zip(rounded[s], logs):
                w = max(w, (2 * ((abs(c) << scale) + (1 << g))).bit_length())
        for Lx in (la, lb, target):
            Lx.width = w
        info = dict(w=w, shards=ns, blockLen=L, blocks=[len(Ab), len(Bb)], scale=scale, outLog=outlog,
                    target=[list(target.lo), list(target.dims)], nonzero=sum(1 for r in rounded for c in r if c),
                    terms=[len(x), len(y)], rem=float(remainderBound(adv, W, 2 * P, degs, box)))
        return adv, info


def _lg(v):
    a = abs(v)
    return 0 if a <= 1 else (a - 1).bit_length()


def _logsumexp2(xs):
    if not xs:
        return -1e300
    m = max(xs)
    return m + math.log2(sum(2.0 ** (x - m) for x in xs))


def placeholder():
    """Advice of a zero real part: never read by the landed route (packedRealProduct returns early)."""
    L = Layout((0, 0), (1, 1), (1, 1), 1, 1)
    return Advice(L, L, L, 1, [], 0)
