#!/usr/bin/env python3
"""V2-PACKED-B3B gate: the rounded and truncated packed torsion stage on LG00's data (untrusted tooling; the
kernel re-checks everything).

Reads LG00's data and the boundary memos as `tors_gate_gen.load()` does (lg00-cert, bit-exact mirror), then
computes, exactly in Python (Kronecker products of big integers, as the kernel does):
  - every node of `KAM/CertificateSharp/Packed/TorsR.lean` (`N`, `D L`, `DG`, `C`, `D(G^-1)`, `DN`, `X_N`):
    the exact product of its memoized inputs on the window, rounded to scale 2^P (ties up) and truncated to the
    box (modes below `--drop` bits are dropped too: the residual carries them);
  - its radius and norm bound with the bit-exact mirror of the kernel's backend arithmetic (`sofx_arith.FixedB`,
    `sumUp`), so the memo's bounds equal what the kernel recomputes;
  - the exact centres and radii of the averages of `T` and `Y`, and a mirror of the final test (`tabFinal`).
Writes the probes (into $V2P_GATE_DIR, default .lake/v2-packed-gate), each with the data it reads:
  TRData (control), TRLay, TRPack, TRSt<node> (one node, every entry), TRStDN_i_j and TRStXN_i_j (one entry
  each: the two largest nodes), TRT, TRY, TRFinal, the boundary entries under the box book (TRE_*), and the
  controls TRFinalNeg (bound 1/100), TRStNMut (a node mantissa off by 2^120), TRStCRadUlp (one ulp of radius),
  TRStCDrop (the largest term dropped), TRFinalEdge_hi / TRFinalEdge_lo (sigma around the threshold).
`--toy` prints the book and the memo of `TorsRTests.lean` instead.
Usage: python3 -I scripts/packed/torsr_gate_gen.py [--toy] [--drop=BITS]
"""
import json
import os
import re
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tors_gate_gen as T     # noqa: E402
G, A, C, M, SP = T.G, T.A, T.C, T.M, T.SP

OUT = T.OUT
P, Q, n = 128, 24, 2
WPY = 1024                   # the Python packing width (bits), far above every product
DROP = next((int(a.split("=")[1]) for a in sys.argv if a.startswith("--drop=")), 0)


# ---------------------------------------------------------------------------------------------- exact packing
def pack(poly, lo, s0, nslots):
    nb = WPY // 8
    pos, neg = bytearray(nslots * nb), bytearray(nslots * nb)
    for (k0, k1), v in poly.items():
        i = (k0 - lo[0]) * s0 + (k1 - lo[1])
        assert 0 <= i < nslots and 0 <= k1 - lo[1] < s0
        if v > 0:
            pos[i * nb:(i + 1) * nb] = v.to_bytes(nb, "little")
        elif v < 0:
            neg[i * nb:(i + 1) * nb] = (-v).to_bytes(nb, "little")
    return int.from_bytes(pos, "little") - int.from_bytes(neg, "little")


def unpack(z, lo, dims, s0):
    nb = WPY // 8
    N = (dims[0] - 1) * s0 + dims[1]
    half = 1 << (WPY - 1)
    y = z + int.from_bytes((bytes(nb - 1) + b"\x80") * N, "little")
    assert 0 <= y < 1 << (WPY * N)
    bs = y.to_bytes(N * nb, "little")
    out = {}
    for i in range(N):
        v = int.from_bytes(bs[i * nb:(i + 1) * nb], "little") - half
        if v:
            a, b = divmod(i, s0)
            assert b < dims[1], "wrap"
            out[(lo[0] + a, lo[1] + b)] = v
    return out


class Geo:
    def __init__(self, hb, s0):
        self.lo, self.dims = (-hb, -hb), (2 * hb + 1, 2 * hb + 1)
        self.wlo, self.wdims = (-2 * hb, -2 * hb), (4 * hb + 1, 4 * hb + 1)
        self.s0 = s0
        self.nb = (self.dims[0] - 1) * s0 + self.dims[1]

    def inbox(self, k):
        return all(self.lo[j] <= k[j] < self.lo[j] + self.dims[j] for j in range(2))

    def rmul(self, x, y):
        if not x or not y:
            return {}
        return unpack(pack(x, self.lo, self.s0, self.nb) * pack(y, self.lo, self.s0, self.nb), self.wlo,
                      self.wdims, self.s0)


def part(p, which):
    return {k: v[which] for k, v in p.items() if v[which]}


def join(re_, im_):
    out = {}
    for k, v in re_.items():
        out[k] = (v, 0)
    for k, v in im_.items():
        out[k] = (out.get(k, (0, 0))[0], v)
    return {k: v for k, v in out.items() if v != (0, 0)}


def cmul(geo, a, b):
    ar, ai, br, bi = part(a, 0), part(a, 1), part(b, 0), part(b, 1)
    rr, ii, ri, ir = geo.rmul(ar, br), geo.rmul(ai, bi), geo.rmul(ar, bi), geo.rmul(ai, br)
    re_ = dict(rr)
    for k, v in ii.items():
        re_[k] = re_.get(k, 0) - v
    im_ = dict(ri)
    for k, v in ir.items():
        im_[k] = im_.get(k, 0) + v
    return join({k: v for k, v in re_.items() if v}, {k: v for k, v in im_.items() if v})


def cadd(a, b):
    out = dict(a)
    for k, (r, i) in b.items():
        r0, i0 = out.get(k, (0, 0))
        out[k] = (r0 + r, i0 + i)
    return {k: v for k, v in out.items() if v != (0, 0)}


def cscale(a, c):
    return {k: (r * c, i * c) for k, (r, i) in a.items()}


# ---------------------------------------------------------------------------------------------- packed models
class Ctx:
    def __init__(self, w, q, PP):
        self.B = A.FixedB(PP)
        self.w, self.q, self.P = w, q, PP

    def pnorm(self, poly, e):
        return self.B.ofRatUp(F(T.wnorm(poly, self.w, self.q), 2 ** (e + 2 * self.q)))

    def pmulRad(self, na, r, nb, s):
        B = self.B
        return B.upAdd(B.upAdd(B.upMul(na, s), B.upMul(r, nb)), B.upMul(r, s))


def matmul(ctx, geo, X, Y, m, rows, cols):
    out = {}
    for i in rows:
        for j in cols:
            acc = {}
            for k in range(m):
                acc = cadd(acc, cmul(geo, X[(i, k)][0], Y[(k, j)][0]))
            r = M.sumUp(ctx.B, [ctx.pmulRad(X[(i, k)][2], X[(i, k)][1], Y[(k, j)][2], Y[(k, j)][1])
                                for k in range(m)])
            nb = M.sumUp(ctx.B, [ctx.B.upMul(X[(i, k)][2], Y[(k, j)][2]) for k in range(m)])
            out[(i, j)] = (acc, r, nb)
    return out


def madd(ctx, X, Y):
    return {k: (cadd(X[k][0], Y[k][0]), ctx.B.upAdd(X[k][1], Y[k][1]), ctx.B.upAdd(X[k][2], Y[k][2])) for k in X}


def mneg(X):
    return {k: (cscale(v[0], -1), v[1], v[2]) for k, v in X.items()}


def mtr(X):
    return {(j, i): v for (i, j), v in X.items()}


def momega(X, nn):
    out = {}
    for (i, j), v in X.items():
        if i < nn:
            out[(nn + i, j)] = v
        else:
            out[(i - nn, j)] = (cscale(v[0], -1), v[1], v[2])
    return out


def reduce_node(ctx, geo, Mx, PP):
    """Round to scale 2^P (ties up), truncate to the box, drop modes below `DROP` bits; the memo entry and
    the node's packed model (the radius and norm bound the kernel recomputes)."""
    out, memo = {}, {}
    for key, (poly, r, _) in Mx.items():
        red = {}
        for k, (re_, im_) in poly.items():
            if geo.inbox(k):
                a, b = (re_ + (1 << (PP - 1))) >> PP, (im_ + (1 << (PP - 1))) >> PP
                if DROP:
                    a = a if abs(a) >= (1 << DROP) else 0
                    b = b if abs(b) >= (1 << DROP) else 0
                if a or b:
                    red[k] = (a, b)
        res = cadd(poly, cscale(red, -(1 << PP)))
        rad = ctx.B.upAdd(r, ctx.pnorm(res, 2 * PP))
        nb = ctx.pnorm(red, PP)
        memo[key] = red
        out[key] = (red, rad, nb)
    return out, memo


def chain(ctx, geo, K, Bm, D2, Fl, Am, D1, nn, PP, lay_l0=None):
    """The rounded chain of `TorsR.lean`: nodes, `T`, `Y`."""
    rows2, rows1 = range(2 * nn), range(nn)
    MN = matmul(ctx, geo, K, Bm, nn, rows2, rows1)
    Nm, memoN = reduce_node(ctx, geo, MN, PP)
    N = momega(Nm, nn)
    DL0 = {}
    for r in rows2:
        for j in rows1:
            acc = {}
            for l in range(nn):
                acc = cadd(acc, cscale(D2[l][(r, j)][0], Fl[l][0][(0, 0)][0]))
            rr = M.sumUp(ctx.B, [ctx.pmulRad(D2[l][(r, j)][2], D2[l][(r, j)][1], Fl[l][2], Fl[l][1])
                                 for l in range(nn)])
            DL0[(r, j)] = (acc, rr, None)
    DLm, memoDL = reduce_node(ctx, geo, DL0, PP)
    MDG = madd(ctx, matmul(ctx, geo, mtr(DLm), K, 2 * nn, rows1, rows1), matmul(ctx, geo, mtr(K), DLm, 2 * nn, rows1,
                                                                             rows1))
    DGm, memoDG = reduce_node(ctx, geo, MDG, PP)
    Cm, memoC = reduce_node(ctx, geo, matmul(ctx, geo, Bm, DGm, nn, rows1, rows1), PP)
    DGim, memoDGi = reduce_node(ctx, geo, matmul(ctx, geo, Cm, Bm, nn, rows1, rows1), PP)
    DGi = mneg(DGim)
    MDN = madd(ctx, matmul(ctx, geo, DLm, Bm, nn, rows2, rows1), matmul(ctx, geo, K, DGi, nn, rows2, rows1))
    DNm, memoDN = reduce_node(ctx, geo, MDN, PP)
    DN = momega(DNm, nn)
    sh = {k: (cscale(v[0], -(1 << PP)), v[1], v[2]) for k, v in DN.items()}
    MXN = madd(ctx, matmul(ctx, geo, Am, N, 2 * nn, rows2, rows1), sh)
    XNm, memoXN = reduce_node(ctx, geo, MXN, PP)
    Tm = matmul(ctx, geo, mtr(N), momega(XNm, nn), 2 * nn, rows1, rows1)
    Ym = matmul(ctx, geo, D1, N, 2 * nn, [0], rows1)
    memos = dict(N=(memoN, Nm), DL=(memoDL, DLm), DG=(memoDG, DGm), C=(memoC, Cm), DGi=(memoDGi, DGim),
                 DN=(memoDN, DNm), XN=(memoXN, XNm))
    loads = dict(MN=MN, DL0=DL0, MDG=MDG, MXN=MXN)
    return memos, Tm, Ym, loads


def centre(poly, e):
    re_, im_ = poly.get((0, 0), (0, 0))
    return (F(re_, 2 ** e), F(im_, 2 ** e))


# ---------------------------------------------------------------------------------------------- the book
def dense(lo_dims, s0):
    return (lo_dims[1][0] - 1) * s0 + lo_dims[1][1]


def r_book(PP, q, w, hb, b):
    """`PRBook`: one box of half-width `hb`, its window, the unit layout, the 1 x 1 zero key; loads and norm
    exponents (Lean formulas of `TorsR.lean`), the width."""
    s0 = 4 * hb + 1
    Lb = ((-hb, -hb), (2 * hb + 1, 2 * hb + 1))
    Lw = ((-2 * hb, -2 * hb), (4 * hb + 1, 4 * hb + 1))
    Lu = Lb
    LU0 = ((0, 0), (1, 1))
    Nb, Nu, N0 = dense(Lb, s0), dense(Lu, s0), 1
    ml = lambda Na, Nb_, x, y: 2 * min(Na, Nb_) * x * y
    nn = n
    bK, bB, bD, bA, bF, bR = b["bK"], b["bB"], b["bD"], b["bA"], b["bF"], b["bR"]
    ld = dict(aN=nn * ml(Nb, Nb, bK, bB), aDL=nn * ml(Nb, N0, bD, bF),
              aDG=2 * nn * ml(Nb, Nb, bR, bK) + 2 * nn * ml(Nb, Nb, bK, bR), aC=nn * ml(Nb, Nb, bB, bR),
              aDGi=nn * ml(Nb, Nb, bR, bB), aDN=nn * ml(Nb, Nb, bR, bB) + nn * ml(Nb, Nb, bK, bR),
              aXN=2 * nn * ml(Nb, Nb, bA, bR) + ml(Nb, Nu, bR, 2 ** PP), aT=2 * nn * ml(Nb, Nb, bR, bR),
              aY=2 * nn * ml(Nb, Nb, bA, bR))
    aW = max(ld[k] for k in ("aN", "aDG", "aC", "aDGi", "aDN", "aXN"))
    aL = ld["aDL"]
    resW = aW + ml(Nb, Nu, bR, 2 ** PP)
    resL = aL + ml(Nb, N0, bR, 2 ** PP)
    ls = dict(lK=bK.bit_length(), lB=bB.bit_length(), lD=bD.bit_length(), lA=bA.bit_length(),
              lR=bR.bit_length(), lW=resW.bit_length(), lL=resL.bit_length())
    guards = [(Lb, ls[k]) for k in ("lK", "lB", "lD", "lA", "lR")] + [(Lw, ls["lW"]), (Lb, ls["lL"])]
    need = [(2 * ld["aT"]).bit_length(), (2 * ld["aY"]).bit_length()]
    for L, l in guards:
        r, c = G.maxes(w, q, L[0], L[1], s0)
        need += [l + 2, (L[1][0] * s0 * 2 ** l * r * c).bit_length()]
    width = max(need)
    width += (-width) % 8
    return dict(P=PP, q=q, s0=s0, width=width, Lb=Lb, Lw=Lw, Lu=Lu, LU0=LU0, b=b, aW=aW, aL=aL, ls=ls, loads=ld)


def lean_rbook(name, rb):
    lay = lambda L: "⟨[%d, %d], [%d, %d], [%d, 1], %d, 1⟩" % (L[0][0], L[0][1], L[1][0], L[1][1], rb["s0"],
                                                           rb["width"])
    p2 = T.pow2
    out = "noncomputable def %s : PRBook where\n  P := %d\n" % (name, rb["P"])
    out += "  Lb := %s\n  Lu := %s\n  LU0 := %s\n" % (lay(rb["Lb"]), lay(rb["Lu"]), lay(rb["LU0"]))
    for k in ("bK", "bB", "bD", "bA", "bF", "bR"):
        out += "  %s := %s\n" % (k, p2(rb["b"][k]))
    out += "  aW := %d\n  aL := %d\n  q := %d\n" % (rb["aW"], rb["aL"], rb["q"])
    for k in ("lK", "lB", "lD", "lA", "lR", "lW", "lL"):
        out += "  %s := %d\n" % (k, rb["ls"][k])
    return out


# ---------------------------------------------------------------------------------------------- the inputs
def inputs(ctx, D, PP):
    """The packed models of the boundary (as `ptK`, `ptB`, `ptD2`, `ptF`, `ptA`, `ptD1`)."""
    B = ctx.B
    gm, d2, ax, d1, eps, box, s = D["gm"], D["d2"], D["ax"], D["d1"], D["eps"], D["box"], D["s"]
    K = {}
    for (r, a), e in gm.items():
        p = T.pdict(e[0], e[1])
        K[(r, a)] = (p, B.ofRatUp(e[2]), ctx.pnorm(p, PP))
    Bm = {}
    for i in range(n):
        for k in range(n):
            mt = SP.toMants(B, PP, C.gramInvPoly(D["Bpolys"], i, k))
            p = T.pdict(mt[0], mt[1])
            Bm[(i, k)] = (p, eps, ctx.pnorm(p, PP))
    D2 = []
    for l in range(n):
        Dl = {}
        for r in range(2 * n):
            for j in range(n):
                e = d2[(r * n + j) * n + l]
                p = T.pdict(e[0], e[1])
                Dl[(r, j)] = (p, B.ofRatUp(e[2]), ctx.pnorm(p, PP))
        D2.append(Dl)
    Fl = []
    for l in range(n):
        c, rad = box[l]
        fc = T.C_round(s * c * 2 ** PP)
        fr = abs(s) * rad + abs(s * c - F(fc, 2 ** PP))
        Fl.append(({(0, 0): (fc, 0)}, B.ofRatUp(fr), B.ofRatUp(F(abs(fc), 2 ** PP))))
    Am = {}
    for a in range(2 * n):
        for b in range(2 * n):
            e = ax[a * 2 * n + b]
            p = T.pdict(e[0], e[1])
            Am[(a, b)] = (p, B.ofRatUp(e[2]), ctx.pnorm(p, PP))
    D1 = {}
    for a in range(2 * n):
        e = d1[a]
        p = T.pdict(e[0], e[1])
        D1[(0, a)] = (p, B.ofRatUp(e[2]), ctx.pnorm(p, PP))
    return K, Bm, D2, Fl, Am, D1


def final_mirror(ctx, D, CT, RT, CY, RY, S, sig, PP):
    """Mirror of `tabFinal` (exact defect, backend rows): the four quantities of the landed test."""
    B = ctx.B
    box, s = D["box"], D["s"]
    k = n + 1

    def cen(i, j):
        if i < n:
            return CT[i][j] if j < n else (s * box[i][0], F(0))
        return CY[j] if j < n else (F(0), F(0))

    def rad(i, j):
        if i < n:
            return RT[i][j] if j < n else abs(s) * box[i][1]
        return RY[j] if j < n else F(0)
    Sq = [[(F(S[i][l][0], 2 ** PP), F(S[i][l][1], 2 ** PP)) for l in range(k)] for i in range(k)]
    dRows, rRows = [], []
    for i in range(k):
        tot = F(0)
        for j in range(k):
            re_ = (1 if i == j else 0) - sum(Sq[i][l][0] * cen(l, j)[0] - Sq[i][l][1] * cen(l, j)[1] for l in range(k))
            im_ = -sum(Sq[i][l][0] * cen(l, j)[1] + Sq[i][l][1] * cen(l, j)[0] for l in range(k))
            tot += abs(re_) + abs(im_)
        dRows.append(B.ofRatUp(tot))
        rRows.append(B.ofRatUp(sum(rad(i, j) for j in range(k))))
    bRows = [M.sumUp(B, [A.normUp(B, (S[i][j][0], S[i][j][1])) for j in range(k)]) for i in range(k)]
    a, b, r = C.maxCandidate(B, dRows), C.maxCandidate(B, bRows), C.maxCandidate(B, rRows)
    d = B.upAdd(a, B.upMul(b, r))
    ok = (all(B.ble(x, a) for x in dRows) and all(B.ble(x, r) for x in rRows) and B.ble(B.ofInt(0), r)
          and C.gramBoundsOk(B, [d], bRows, d, b, sig))
    return ok, dict(a=float(F(a, 2 ** PP)), b=float(F(b, 2 ** PP)), r=float(F(r, 2 ** PP)),
                    deltaT=float(F(d, 2 ** PP)), margin=float(sig - (F(b, 2 ** PP) + sig * F(d, 2 ** PP))))


def lit_int(t):
    m = re.fullmatch(r"\(?Int\.negSucc (\d+)\)?", t.strip())
    return -int(m.group(1)) - 1 if m else int(t)


def parse_cc_matrix(text, k):
    """A literal `List (List (CC LGF))` (entries `⟨⟨re⟩, ⟨im⟩⟩`) as mantissa pairs."""
    flat = re.sub(r"\s+", " ", text.split(":=", 1)[1])
    vals = re.findall(r"⟨⟨\s*(\(?Int\.negSucc \d+\)?|-?\d+)\s*⟩, ⟨\s*(\(?Int\.negSucc \d+\)?|-?\d+)\s*⟩⟩", flat)
    assert len(vals) == k * k, len(vals)
    pairs = [(lit_int(a), lit_int(b)) for a, b in vals]
    return [pairs[i * k:(i + 1) * k] for i in range(k)]


def toy():
    """The book and the memo of `TorsRTests.lean`: `K` the identity, `B = I`, `D²K = 0`,
    `DX_H = [[0, I], [0, 0]]`, `DH = (0, ω)`, `ω = (1, 0)`, `s = 1`, `P = 64`, box half-width 1."""
    PP, q, w = 64, 8, F(2)
    ctx, geo = Ctx(w, q, PP), Geo(1, 5)
    one = 2 ** PP
    unit = lambda c: ({(0, 0): (c, 0)} if c else {})
    mk = lambda p, r: (p, r, ctx.pnorm(p, PP))
    K = {(r, a): mk(unit(one if r == a else 0), 0) for r in range(2 * n) for a in range(n)}
    Bm = {(i, k): (unit(one if i == k else 0), 0, ctx.pnorm(unit(one if i == k else 0), PP))
          for i in range(n) for k in range(n)}
    D2 = [{(r, j): mk({}, 0) for r in range(2 * n) for j in range(n)} for _ in range(n)]
    Fl = [(unit(one), 0, ctx.B.ofRatUp(F(1))), (unit(0), 0, 0)]
    Fl[1] = ({(0, 0): (0, 0)}, 0, 0)
    Am = {(a, b): mk(unit(one if (a, b) in ((0, 2), (1, 3)) else 0), 0) for a in range(2 * n) for b in range(2 * n)}
    D1 = {(0, a): mk(unit(one if a == 2 else 0), 0) for a in range(2 * n)}
    memos, Tm, Ym, _ = chain(ctx, geo, K, Bm, D2, Fl, Am, D1, n, PP)
    mx = max([1] + [abs(x) for m in memos.values() for p_ in m[0].values() for v in p_.values() for x in v])
    rb = r_book(PP, q, w, 1, dict(bK=2 ** 65, bB=2 ** 65, bD=1, bA=2 ** 65, bF=2 ** 65, bR=2 ** (mx.bit_length() + 1)))
    print(lean_rbook("tRb", rb))
    shape = dict(N=(2 * n, n), DL=(2 * n, n), DG=(n, n), C=(n, n), DGi=(n, n), DN=(2 * n, n), XN=(2 * n, n))
    zk = lambda x: "[" + ", ".join("([%d, %d], %d)" % (k[0], k[1], v) for k, v in x) + "]"
    print("def tRm : PRMemo where")
    for nm, (R, Cc) in shape.items():
        memo, mats = memos[nm]
        rows = []
        for i in range(R):
            ents = []
            for j in range(Cc):
                re_, im_ = node_lists(memo[(i, j)])
                ents.append("(%s, %s, %s, %s)" % (zk(re_), zk(im_), T.qlit(F(mats[(i, j)][1], 2 ** PP)),
                                                  T.qlit(F(mats[(i, j)][2], 2 ** PP))))
            rows.append("[" + ", ".join(ents) + "]")
        print("  %s := [%s]" % (nm, ", ".join(rows)))
    CT = [[centre(Tm[(i, j)][0], 2 * PP) for j in range(n)] for i in range(n)]
    print("  CT := [%s]" % ", ".join("[" + ", ".join(qpair(c) for c in row) + "]" for row in CT))
    print("  RT := [%s]" % ", ".join("[" + ", ".join(T.qlit(F(Tm[(i, j)][1], 2 ** PP)) for j in range(n)) + "]"
                                     for i in range(n)))
    print("  CY := [%s]" % ", ".join(qpair(centre(Ym[(0, j)][0], 2 * PP)) for j in range(n)))
    print("  RY := [%s]" % ", ".join(T.qlit(F(Ym[(0, j)][1], 2 ** PP)) for j in range(n)))


def compute():
    """LG00's data, the rounded chain, the tables and the book (shared with `frames_gate_gen.py`)."""
    D = T.load()
    w, s = D["w"], D["s"]
    ctx = Ctx(w, Q, P)
    geo = Geo(25, 101)
    K, Bm, D2, Fl, Am, D1 = inputs(ctx, D, P)
    memos, Tm, Ym, _ = chain(ctx, geo, K, Bm, D2, Fl, Am, D1, n, P)
    sizes = {k: sum(len(v) for v in m[0].values()) for k, m in memos.items()}
    mx = max(abs(x) for m in memos.values() for p in m[0].values() for v in p.values() for x in v)
    print("node terms", sizes, "max mantissa bits", mx.bit_length())
    CT = [[centre(Tm[(i, j)][0], 2 * P) for j in range(n)] for i in range(n)]
    RT = [[F(Tm[(i, j)][1], 2 ** P) for j in range(n)] for i in range(n)]
    CY = [centre(Ym[(0, j)][0], 2 * P) for j in range(n)]
    RY = [F(Ym[(0, j)][1], 2 ** P) for j in range(n)]
    S = parse_cc_matrix(D["tinv"], n + 1)
    ok, info = final_mirror(ctx, D, CT, RT, CY, RY, S, D["sigT_mu"], P)
    print("T centres", [[(float(c[0]), float(c[1])) for c in row] for row in CT])
    print("T radii", [[float(r) for r in row] for row in RT], "Y", [float(r) for r in RY])
    print("final (mirror)", ok, info)
    assert ok, "the mirror of the final test fails"
    p2 = lambda x: 2 ** max(1, x.bit_length())
    mxv = lambda es: max([1] + [abs(v) for e in es for _, v in e[0] + e[1]])
    bR = p2(mx)
    bk = D["bk"]["b"]
    rb = r_book(P, Q, w, 25, dict(bK=2 ** 136, bB=2 ** 132, bD=bk["bD"], bA=bk["bA"], bF=bk["bF"], bR=bR))
    return dict(D=D, ctx=ctx, rb=rb, memos=memos, K=K, Tm=Tm, CT=CT, RT=RT, CY=CY, RY=RY, info=info)


def main():
    if "--toy" in sys.argv:
        toy()
        return
    S = compute()
    write_probes(S["D"], S["rb"], S["memos"], S["CT"], S["RT"], S["CY"], S["RY"], S["info"])


def qpair(z):
    return "(%s, %s)" % (T.qlit(F(z[0])), T.qlit(F(z[1])))


def node_lists(poly):
    re_ = sorted((k, v[0]) for k, v in poly.items() if v[0])
    im_ = sorted((k, v[1]) for k, v in poly.items() if v[1])
    return re_, im_


def parts(D, rb, memos, CT, RT, CY, RY):
    """The probe data: the shared base text and the memo writers (shared with `frames_gate_gen.py`)."""
    fmt = ("abbrev lgP : ℕ := 128\n\nabbrev LGF : Type := CertFixed lgP\n\n"
           "def dz (n : ℕ) : ℤ := if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)\n\n"
           "abbrev tm (k₀ k₁ re im : ℕ) : CertKey × CC LGF := ([dz k₀, dz k₁], ⟨⟨dz re⟩, ⟨dz im⟩⟩)\n\n"
           "abbrev tr (k₀ k₁ re : ℕ) : CertKey × CC LGF := ([dz k₀, dz k₁], ⟨⟨dz re⟩, ⟨0⟩⟩)\n\n"
           "abbrev tz (k₀ k₁ v : ℕ) : CertKey × ℤ := ([dz k₀, dz k₁], dz v)\n\n"
           "noncomputable def gW : CertWeight := ⟨(29 / 5000 : ℚ), lgD4⟩\n\n"
           "noncomputable def gCfg : ModelConfig LGF := ⟨24, 30, 12, CertFixed.toMant lgP, []⟩\n\n")
    wrap, tl, qlit = T.wrap, T.tl, T.qlit
    gm, d2, ax, d1 = D["gm"], D["d2"], D["ax"], D["d1"]
    nodes = ("N", "DL", "DG", "C", "DGi", "DN", "XN")
    shape = dict(N=(2 * n, n), DL=(2 * n, n), DG=(n, n), C=(n, n), DGi=(n, n), DN=(2 * n, n), XN=(2 * n, n))

    def node_defs(nm, sub=None, radsub=None):
        memo, mats = memos[nm]
        out = ""
        R, Cc = shape[nm]
        for i in range(R):
            for j in range(Cc):
                poly = (sub or {}).get((i, j), memo[(i, j)])
                re_, im_ = node_lists(poly)
                rad, nb = mats[(i, j)][1] - (radsub or {}).get((i, j), 0), mats[(i, j)][2]
                nmij = "r%s_%d_%d" % (nm, i, j)
                out += ("noncomputable def %s_re : List (CertKey × ℤ) :=\n%s\n\n"
                        "noncomputable def %s_im : List (CertKey × ℤ) :=\n%s\n\n"
                        "noncomputable def %s : NodeEntry := (%s_re, %s_im, %s, %s)\n\n") % (
                            nmij, wrap(tl(re_)), nmij, wrap(tl(im_)), nmij, nmij, nmij,
                            qlit(F(rad, 2 ** P)), qlit(F(nb, 2 ** P)))
        return out

    def node_tab(nm):
        R, Cc = shape[nm]
        return "[" + ", ".join("[" + ", ".join("r%s_%d_%d" % (nm, i, j) for j in range(Cc)) + "]"
                               for i in range(R)) + "]"

    def rmemo(have):
        out = "noncomputable def rMemo : PRMemo where\n"
        for nm in nodes:
            out += "  %s :=\n%s\n" % (nm, wrap(node_tab(nm)) if nm in have else "    []")
        out += "  CT := %s\n" % ("[" + ", ".join("[" + ", ".join(qpair(c) for c in row) + "]" for row in CT) + "]")
        out += "  RT := %s\n" % ("[" + ", ".join("[" + ", ".join(qlit(r) for r in row) + "]" for row in RT) + "]")
        out += "  CY := %s\n" % ("[" + ", ".join(qpair(c) for c in CY) + "]")
        out += "  RY := %s\n" % ("[" + ", ".join(qlit(r) for r in RY) + "]")
        return out.replace("CT := [", "CT :=\n    [").replace("RT := [", "RT :=\n    [")

    def tmemo():
        def edef(name, e):
            return ("noncomputable def %s_re : List (CertKey × ℤ) :=\n%s\n\n"
                    "noncomputable def %s_im : List (CertKey × ℤ) :=\n%s\n\n"
                    "noncomputable def %s : MemoEntry := (%s_re, %s_im, %s)\n\n") % (
                        name, wrap(tl(e[0])), name, wrap(tl(e[1])), name, name, name, qlit(e[2]))
        out, lists = "", {}
        for kind, es in (("d2", d2), ("ax", ax), ("d1", d1)):
            names = []
            for i, e in enumerate(es):
                out += edef("t%s_%d" % (kind, i), e)
                names.append("t%s_%d" % (kind, i))
            lists[kind] = names
        out += "noncomputable def tMemo : PTorsMemo where\n"
        for kind in ("d2", "ax", "d1"):
            out += "  %s :=\n%s\n" % (kind, wrap("[" + ", ".join(lists[kind]) + "]"))
        return out
    gmemo = ""
    for (r, a), e in sorted(gm.items()):
        gmemo += "noncomputable def gMre_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (r, a, wrap(tl(e[0])))
        gmemo += "noncomputable def gMim_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (r, a, wrap(tl(e[1])))
    rows = lambda pf: "[" + ", ".join("[" + ", ".join("%s_%d_%d" % (pf, r, a) for a in range(n)) + "]"
                                      for r in range(2 * n)) + "]"
    rads = "[" + ", ".join("[" + ", ".join(qlit(gm[(r, a)][2]) for a in range(n)) + "]" for r in range(2 * n)) + "]"
    gmemo += "noncomputable def gMemo : PGramMemo where\n  re := %s\n  im := %s\n  rad :=\n%s\n\n" % (
        rows("gMre"), rows("gMim"), wrap(rads))
    grams = D["grams"]
    base = (D["d4"] + "\n" + D["d1t"] + "\n" + D["d2t"] + "\n" + fmt + D["pi"] + "\n" + D["boxt"] + "\n" + D["tinv"] +
            "\n" + "".join(D["texts"][nm] + "\n" for nm in grams) + D["ginv"] + "\n" + gmemo +
            "noncomputable def tEps : LGF := ⟨%d⟩\n\n" % D["eps"] + lean_rbook("rBook", rb) + "\n")
    return dict(base=base, tmemo=tmemo, node_defs=node_defs, rmemo=rmemo, nodes=nodes)


HEAD = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.%s

/-!
# %s gate probe `%s` (opt-in, not built)

%s

The data are LG00's (branch `lg00-cert`, read-only copies). Generated by
`scripts/packed/%s`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.%s.%s

open KAM KAM.Certificate KAM.CertificateSharp.Packed

"""


def emit(probes, imp="TorsRBase", task="V2-PACKED-B3B", script="torsr_gate_gen.py", ns="RGate"):
    """Write each probe `name: (doc, body, statement)` as a module proving the statement by `decide +kernel`."""
    os.makedirs(OUT, exist_ok=True)
    for name, (doc, body, st) in probes.items():
        words, lines, cur = doc.split(), [], ""
        for wd in words:
            if cur and len(cur) + 1 + len(wd) > 98:
                lines.append(cur)
                cur = wd
            else:
                cur = (cur + " " + wd) if cur else wd
        lines.append(cur)
        txt = HEAD % (imp, task, name, "\n".join(lines), script, ns, name) + body
        txt += "\nset_option profiler true\nset_option profiler.threshold 1\n\ntheorem probe :\n    %s := by\n" \
               "  decide +kernel\n\nend KAM.CertificateSharp.Packed.%s.%s\n" % (st, ns, name)
        with open(os.path.join(OUT, name + ".lean"), "w") as f:
            f.write(txt)


def write_probes(D, rb, memos, CT, RT, CY, RY, info):
    pt = parts(D, rb, memos, CT, RT, CY, RY)
    base, tmemo, node_defs, rmemo, nodes = pt["base"], pt["tmemo"], pt["node_defs"], pt["rmemo"], pt["nodes"]
    qlit = T.qlit
    sv = "(1000001 / 1000000 : ℚ)"
    sig = "((21 / 100 : ℚ) - 1 / 100000)"
    needs = dict(N=["N"], DL=["DL"], DG=["DL", "DG"], C=["DG", "C"], DGi=["C", "DGi"], DN=["DL", "DGi", "DN"],
                 XN=["N", "DN", "XN"])
    stmt = dict(N="trStN 2 lg00GramInv gW gCfg rBook gMemo rMemo tEps",
                DL="trStDL (α := LGF) 2 gW lg00Box %s rBook tMemo rMemo" % sv,
                DG="trStDG (α := LGF) 2 gW rBook gMemo rMemo",
                C="trStC 2 lg00GramInv gW gCfg rBook rMemo tEps",
                DGi="trStDGi 2 lg00GramInv gW gCfg rBook rMemo tEps",
                DN="trStDN 2 lg00GramInv gW gCfg rBook gMemo rMemo tEps",
                XN="trStXN (α := LGF) 2 gW rBook tMemo rMemo")
    probes = {}
    allnodes = "".join(node_defs(nm) for nm in nodes)
    probes["TRData"] = ("Data-only control (all data of the core).", base + tmemo() + allnodes + rmemo(nodes), "True")
    probes["TRLay"] = ("The layout and load guards (`trLayOk`, `trNormOk`).", base + tmemo() + rmemo(()),
                       "(trLayOk 2 rBook && trNormOk 2 gW lg00Box %s rBook) = true" % sv)
    probes["TRPack"] = ("The packing of every boundary entry on the box (`ptPackOk`).", base + tmemo() + rmemo(()),
                        "ptPackOk 2 lg00GramInv gCfg rBook.toT gMemo tMemo = true")
    for nm in nodes:
        probes["TRSt" + nm] = ("The node %s against the exact product of its inputs (`stageAll`)." % nm,
                               base + tmemo() + "".join(node_defs(x) for x in needs[nm]) + rmemo(needs[nm]),
                               stmt[nm] + " = true")
    mats = dict(DN="trMDN 2 lg00GramInv gW gCfg rBook gMemo rMemo tEps",
                XN="trMXN (α := LGF) 2 gW rBook tMemo rMemo")
    for nm in ("DN", "XN"):
        body = base + tmemo() + "".join(node_defs(x) for x in needs[nm]) + rmemo(needs[nm])
        for i in range(2 * n):
            for j in range(n):
                probes["TRSt%s_%d_%d" % (nm, i, j)] = (
                    "One entry (%d, %d) of the node %s against the exact product of its inputs (`stageOk`)."
                    % (i, j, nm), body,
                    "stageOk 2 gW rBook.q rBook.lW rBook.lR rBook.Lw rBook.Lb rBook.Lu rBook.bR (2 * rBook.P)\n"
                    "      rBook.P ((%s).x %d %d) ((%s).r %d %d)\n      (nodeAt rMemo.%s %d %d) = true"
                    % (mats[nm], i, j, mats[nm], i, j, nm, i, j))
    probes["TRT"] = ("The averages of T against the tables (`trTCheck`).",
                     base + tmemo() + node_defs("N") + node_defs("XN") + rmemo(["N", "XN"]),
                     "trTCheck (α := LGF) 2 rBook rMemo = true")
    probes["TRY"] = ("The averages of Y against the tables (`trYCheck`).",
                     base + tmemo() + node_defs("N") + rmemo(["N"]), "trYCheck (α := LGF) 2 gW rBook tMemo rMemo = true")
    fin = "tabFinal 2 gCfg 128 (trCentre 2 lg00Box %s rMemo) (trRad 2 lg00Box %s rMemo) lg00TorsInv\n      %%s = %%s" % (
        sv, sv)
    probes["TRFinal"] = ("The landed averaged test on the tables (`tabFinal`).", base + rmemo(()), fin % (sig, "true"))
    probes["TRFinalNeg"] = ("Negative control: the averaged test with the bound 1/100 is false.", base + rmemo(()),
                            fin % ("(1 / 100 : ℚ)", "false"))
    m00 = dict(memos["N"][0][(0, 0)])
    k0 = sorted(m00)[0]
    m00[k0] = (m00[k0][0] + (1 << 120), m00[k0][1])
    probes["TRStNMut"] = ("Negative control (data): the node N with one mantissa off by 2^120 is rejected.",
                          base + tmemo() + node_defs("N", sub={(0, 0): m00}) + rmemo(["N"]),
                          stmt["N"] + " = false")
    # sharp controls (AUDIT-V2-PACKED-B3-1 L2): one ulp of radius, the largest term dropped, the sigma edges
    probes["TRStCRadUlp"] = ("Negative control (sharp): the radius of C(0, 0) lowered by one ulp (2^-128) is rejected.",
                             base + tmemo() + node_defs("DG") + node_defs("C", radsub={(0, 0): 1}) +
                             rmemo(["DG", "C"]), stmt["C"] + " = false")
    c00 = dict(memos["C"][0][(0, 0)])
    kbig = max(c00, key=lambda k: max(abs(c00[k][0]), abs(c00[k][1])))
    part_ = 0 if abs(c00[kbig][0]) >= abs(c00[kbig][1]) else 1
    c00[kbig] = (0, c00[kbig][1]) if part_ == 0 else (c00[kbig][0], 0)
    c00 = {k: v for k, v in c00.items() if v != (0, 0)}
    probes["TRStCDrop"] = ("Negative control (sharp): the largest term of C(0, 0) dropped, radius kept, is rejected.",
                           base + tmemo() + node_defs("DG") + node_defs("C", sub={(0, 0): c00}) +
                           rmemo(["DG", "C"]), stmt["C"] + " = false")
    probes["TRFinalEdge_hi"] = ("Control: the averaged test just above its threshold (sigma = 0.2088116) is true.",
                                base + rmemo(()), fin % ("(2088116 / 10000000 : ℚ)", "true"))
    probes["TRFinalEdge_lo"] = ("Negative control (sharp): the averaged test just below its threshold "
                                "(sigma = 0.2088114) is false.", base + rmemo(()),
                                fin % ("(2088114 / 10000000 : ℚ)", "false"))
    for r in range(2 * n):
        for j in range(n):
            for l in range(n):
                probes["TRE_D2_%d_%d_%d" % (r, j, l)] = (
                    "One boundary entry: the landed d2kModel (%d, %d, %d) against the memo." % (r, j, l),
                    base + "".join(D["texts"][nm] + "\n" for nm in D["comps"]) + D["emb"] + "\n" + tmemo() +
                    rmemo(()), "ptD2Ok 2 lg00Emb gW gCfg lg00Pi rBook.toT tMemo %d %d %d = true" % (r, j, l))
    for a in range(2 * n):
        for b in range(2 * n):
            probes["TRE_A_%d_%d" % (a, b)] = (
                "One boundary entry: the landed DX_H ∘ K entry (%d, %d) at degree 0 against the memo." % (a, b),
                base + D["tms_defs"] + tmemo() + rmemo(()),
                "ptAOk 2 gW gCfg lg00Pi rBook.toT tMemo lg00TMs %d %d = true" % (a, b))
        probes["TRE_D1_%d" % a] = (
            "One boundary entry: the landed DH ∘ K entry %d at degree 0 against the memo." % a,
            base + D["tms_defs"] + tmemo() + rmemo(()), "ptD1Ok 2 gW gCfg lg00Pi rBook.toT tMemo lg00TMs %d = true" % a)
    emit(probes)
    import subprocess
    try:
        commit = subprocess.run(["git", "-C", T.CERT, "rev-parse", "HEAD"], capture_output=True, text=True,
                                check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        commit = "unknown"
    meta = dict(lg00_cert_commit=commit, box_half_width=25, stride=rb["s0"],
                width=rb["width"], window_mbit=round(((rb["Lw"][1][0] - 1) * rb["s0"] + rb["Lw"][1][1]) * rb["width"]
                                                     / 1e6, 2),
                loads_log2={k: v.bit_length() for k, v in rb["loads"].items()}, aW_log2=rb["aW"].bit_length(),
                l=rb["ls"], node_terms={k: sum(len(v) for v in memos[k][0].values()) for k in nodes},
                T_centres=[[[float(c[0]), float(c[1])] for c in row] for row in CT],
                T_radii=[[float(r) for r in row] for row in RT], Y_radii=[float(r) for r in RY], final=info)
    with open(os.path.join(OUT, "TorsRGate.json"), "w") as f:
        json.dump(meta, f, indent=1)
    print(json.dumps(meta, indent=1))


if __name__ == "__main__":
    main()
