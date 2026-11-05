#!/usr/bin/env python3
"""V2-PACKED-JET first gate: one packed cfgLow segment of LG00's jet chain (untrusted tooling; the kernel re-checks
everything).

Reads the slot range extracted by `jet_extract.py` (LG00's program, the live slots, the landed cfgLow models of the
imports) and runs the packed segment of `KAM/CertificateSharp/Packed/JetSeg.lean` in Python, bit for bit:
  - the imports: each landed model `(2π)^deg Σ c_k e^{ik·θ} ± rad` rounded to scale 2^P on the box `Lb` (a
    constant on the one-slot layout `LU0`); its radius (landed radius plus the rounding, exact) and its norm bound
    `pnorm` (these are the hypotheses of `jSegOk_sound`; the kernel does not check them);
  - every live slot: `jAdd` (unit shifts to the larger scale, exact sum), `jMul` (exact product; a box-by-box
    product on the window is reduced at once to the box at scale 2^P: `zPC`, `boxOk`, the residual's `pnorm`),
    and a reduce in place to 2^P after a product by a constant (`jRed`);
  - the book (`JBook`): loads, offsets, norm guards, the slot width, from the run (two passes);
  - the exports: the nodes of the live slots read after the range.
Every mirror function names its Lean counterpart. Literals: balanced `natJoin` trees of 1024-bit chunks; a box part
as its narrow digits (width rounded up to a multiple of 8, so few width classes share the spreading masks), read by
`jSpread`; a zero part as `0`. The program is emitted with right-nested appends (`++` associates to the left).
The steps are cut into sub-segments of at most `--heavy` heavy steps (box-by-box products and reduces in place),
one probe each; `--split=i,j;k` halves chosen sub-segments (rounds separated by `;`).
V2-PACKED-JET-MEM: `--heavy=34` (two processes, <= 2.65 GB) is the measured setting for LG00's Low range; the
whole range (68 heavy steps) also passes in one process at 3.90 GB.
Historical since V2-PACKED-JET-LOW: its own probes predate `jSegOk`'s pi-enclosure and configuration arguments and
the book's leaf fields (receipts of V2-PACKED-JET-GATE / -MEM); its mirror functions are used by `jet_low_gen.py`.
Usage: python3 -I scripts/packed/jet_gate_gen.py SEG.json [--stats] [--heavy=N] [--split=...]
Writes the probes into $V2P_GATE_DIR (default .lake/v2-packed-jet/gate).
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
import gram_gate_gen as G     # noqa: E402  (wceil, maxes)
import gate_gen as GG         # noqa: E402  (nat_tree, lean_rat)
import sofx_arith as A        # noqa: E402  (FixedB: the backend mirror)
import functools              # noqa: E402

_wceil = functools.lru_cache(maxsize=None)(G.wceil)

OUT = os.environ.get("V2P_GATE_DIR", os.path.join(ROOT, ".lake", "v2-packed-jet", "gate"))
P, Q, H, n = 128, 24, 25, 2
PI = F("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798")
TWO_PI = 2 * PI


# ------------------------------------------------------------------------------------------------- layouts
class Lay:
    def __init__(self, lo, dims, S, w):
        self.lo, self.dims, self.S, self.w = lo, dims, S, w

    def dl(self):                                       # PackLayout.denseLen (two axes, stride [S, 1])
        return (self.dims[0] - 1) * self.S + self.dims[1]

    def slot(self, k):
        return (k[0] - self.lo[0]) * self.S + (k[1] - self.lo[1])

    def key(self, i):
        return (self.lo[0] + i // self.S, self.lo[1] + i % self.S)


def periodic(w, N, m):                                  # Digits.periodic
    return m * ((2 ** (w * N) - 1) // (2 ** w - 1))


def box_pat(w, S, D0, D1, v):                           # Box.boxPat
    return periodic(w * S, D0, periodic(w, D1, v))


def digit_shift(w, N, s, Y):                            # Round.digitShift
    return (Y - (Y & periodic(w, N, 2 ** s - 1))) >> s


def to_nat(z):
    return z if z > 0 else 0


def z_part(w, Ns, ls, s, S, D0, D1, off, Z):            # StageZ.zPart
    Y = to_nat(Z + periodic(w, Ns, 2 ** ls) + periodic(w, Ns, 2 ** (s - 1)))
    T = (digit_shift(w, Ns, s, Y) & (box_pat(w, S, D0, D1, 2 ** w - 1) << (w * off))) >> (w * off)
    return T - box_pat(w, S, D0, D1, 2 ** max(ls - s, 0))


def box_ok(L, l, Z):                                    # Box.boxOk
    w, S, D0, D1 = L.w, L.S, L.dims[0], L.dims[1]
    if not (0 < D0 and 0 < D1 and D1 <= S and 0 < w and l + 1 <= w):
        return False
    Y = Z + box_pat(w, S, D0, D1, 2 ** l)
    return Y >= 0 and Y < 2 ** (w * ((D0 - 1) * S + D1)) and (Y & box_pat(w, S, D0, D1, 2 ** (l + 1) - 1)) == Y


def pack(L, d):
    """The packed integer of slot data `{key: c}`."""
    return sum(c << (L.w * L.slot(k)) for k, c in d.items() if c)


def unpack(L, Z):
    """The slot data of a packed integer (digits in (-2^(w-1), 2^(w-1)))."""
    N, w = L.dl(), L.w
    off = periodic(w, N, 2 ** (w - 1))
    Y = Z + off
    assert 0 <= Y < 2 ** (w * N)
    bs = Y.to_bytes(N * w // 8, "little")
    out = {}
    nb = w // 8
    for i in range(N):
        c = int.from_bytes(bs[i * nb:(i + 1) * nb], "little") - 2 ** (w - 1)
        if c:
            out[L.key(i)] = c
    return out


def mul_load(La, Lb, A_, B_):                           # Complex.mulLoad
    return 2 * (min(La.dl(), Lb.dl()) * A_ * B_)


class Ctx:
    def __init__(self, W, w):
        self.B = A.FixedB(P)
        self.W = W
        self.Lb = Lay((-H, -H), (2 * H + 1, 2 * H + 1), 4 * H + 1, w)
        self.Lw = Lay((-2 * H, -2 * H), (4 * H + 1, 4 * H + 1), 4 * H + 1, w)
        self.LU0 = Lay((0, 0), (1, 1), 4 * H + 1, w)
        self.off = self.Lb.slot((0, 0))                 # zslot n Lb, the box in the window
        assert self.off == self.Lw.slot((-H, -H))

    def wnorm(self, d):                                 # Norm.pcNorm (exact, no carry)
        return sum(abs(c) * _wceil(self.W, Q, abs(k[0])) * _wceil(self.W, Q, abs(k[1])) for k, c in d.items())

    def pnorm(self, L, e, x):                           # Enc.pnorm
        nrm = self.wnorm(unpack(L, x[0])) + self.wnorm(unpack(L, x[1]))
        return self.B.ofRatUp(F(nrm, 2 ** (e + 2 * Q)))

    def pmul_rad(self, na, r, nb, s):                   # Enc.pmulRad
        B = self.B
        return B.upAdd(B.upAdd(B.upMul(na, s), B.upMul(r, nb)), B.upMul(r, s))

    def lay(self, u):                                   # JetNode.jLay
        return self.LU0 if u else self.Lb


def pc_mul(x, y):                                       # Complex.pcMul
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


# ------------------------------------------------------------------------------------------------- nodes
class Node:
    __slots__ = ("u", "A", "e", "x", "r", "nb")

    def __init__(self, u, A_, e, x, r, nb):
        self.u, self.A, self.e, self.x, self.r, self.nb = u, A_, e, x, r, nb


class Book:
    def __init__(self, **kw):
        self.__dict__.update(kw)


def j_unit(L, k):                                       # JetNode.jUnit
    return (2 ** k << (L.w * L.slot((0, 0))), 0)


def j_up(C, nd, u2, e2):                                # JetNode.jUp
    if nd.u == u2 and nd.e == e2:
        return nd
    assert nd.e <= e2
    k = e2 - nd.e
    if nd.u and not u2:
        return Node(False, mul_load(C.LU0, C.Lb, nd.A, 2 ** k), e2, pc_mul(nd.x, j_unit(C.Lb, k)), nd.r, nd.nb)
    assert nd.u == u2
    return Node(u2, mul_load(C.lay(u2), C.LU0, nd.A, 2 ** k), e2, pc_mul(nd.x, j_unit(C.LU0, k)), nd.r, nd.nb)


def j_add(C, a, b):                                     # JetNode.jAdd
    u, e = a.u and b.u, max(a.e, b.e)
    a2, b2 = j_up(C, a, u, e), j_up(C, b, u, e)
    B = C.B
    return Node(u, a2.A + b2.A, e, (a2.x[0] + b2.x[0], a2.x[1] + b2.x[1]), B.upAdd(a2.r, b2.r),
                B.upAdd(a2.nb, b2.nb))


def z_pc(C, Ls, ls, s, off, x, Ld=None):                # StageZ.zPC (onto `Ld`, the box by default)
    Lb = Ld or C.Lb
    f = lambda Z: z_part(Ls.w, Ls.dl(), ls, s, Lb.S, Lb.dims[0], Lb.dims[1], off, Z)
    return (f(x[0]), f(x[1]))


def z_res(Lu, s, x, x2):                                # StageZ.zRes
    u = (2 ** s << (Lu.w * Lu.slot((0, 0))), 0)
    m = pc_mul(x2, u)
    return (x[0] - m[0], x[1] - m[1])


def j_red_w(C, bk, A_, e, x, r, eT, st):                # JetNode.jRedW
    s = e - eT
    st["aW"] = max(st["aW"], A_)
    st["smax"] = max(st["smax"], s)
    assert eT < e
    if bk is None:
        x2 = z_pc(C, C.Lw, A_.bit_length(), s, C.off, x)
        st["lb"] = max(st["lb"], max(abs(c) for z in x2 for c in unpack(C.Lb, z).values()).bit_length())
        return Node(False, None, eT, x2, None, None)
    assert A_ <= bk.aW and s <= bk.smax
    x2 = z_pc(C, C.Lw, bk.ls, s, bk.off, x)
    assert box_ok(C.Lb, bk.lb, x2[0]) and box_ok(C.Lb, bk.lb, x2[1]), "boxOk fails"
    rr = C.B.upAdd(r, C.pnorm(C.Lw, e, z_res(C.Lb, s, x, x2)))
    return Node(False, 2 ** bk.lb, eT, x2, rr, C.pnorm(C.Lb, eT, x2))


def j_red(C, bk, nd, eT, st):                           # JetNode.jRed (on the node's layout)
    s = nd.e - eT
    L = C.lay(nd.u)
    assert eT < nd.e
    st["aB"] = max(st["aB"], nd.A)
    st["smax"] = max(st["smax"], s)
    if bk is None:
        x2 = z_pc(C, L, nd.A.bit_length(), s, 0, nd.x, L)
        st["lb"] = max(st["lb"], max([abs(c) for z in x2 for c in unpack(L, z).values()] + [1]).bit_length())
        return Node(nd.u, None, eT, x2, None, None)
    assert nd.A <= bk.aB and s <= bk.smax
    x2 = z_pc(C, L, bk.lsb, s, 0, nd.x, L)
    assert box_ok(L, bk.lb, x2[0]) and box_ok(L, bk.lb, x2[1]), "boxOk fails (in place)"
    rr = C.B.upAdd(nd.r, C.pnorm(L, nd.e, z_res(C.LU0, s, nd.x, x2)))
    return Node(nd.u, 2 ** bk.lb, eT, x2, rr, C.pnorm(L, eT, x2))


def j_mul(C, bk, a, b, eT, st):                         # JetNode.jMul
    if a.u or b.u:
        return Node(a.u and b.u, mul_load(C.lay(a.u), C.lay(b.u), a.A, b.A), a.e + b.e, pc_mul(a.x, b.x),
                    None if bk is None else C.pmul_rad(a.nb, a.r, b.nb, b.r),
                    None if bk is None else C.B.upMul(a.nb, b.nb))
    rad = None if bk is None else C.pmul_rad(a.nb, a.r, b.nb, b.r)
    return j_red_w(C, bk, mul_load(C.Lb, C.Lb, a.A, b.A), a.e + b.e, pc_mul(a.x, b.x), rad, eT, st)


# ------------------------------------------------------------------------------------------------- imports
def const_val(op):
    _, re_, im_, deg = op
    return F(re_[0], re_[1]) * TWO_PI ** deg, F(im_[0], im_[1]) * TWO_PI ** deg


def rnd(q):
    return (q.numerator * 2 + q.denominator) // (2 * q.denominator)


def import_node(C, j, imp):
    """The packed node of an imported slot (a hypothesis of `jSegOk_sound`): the landed model rounded."""
    op, m = imp["op"], imp["model"]
    B = C.B
    if op[0] == "const":
        cr, ci = const_val(op)
        xr, xi = rnd(cr * 2 ** P), rnd(ci * 2 ** P)
        err = abs(cr - F(xr, 2 ** P)) + abs(ci - F(xi, 2 ** P))
        x = (xr, xi)
        A_ = 2 ** max(abs(xr), abs(xi), 1).bit_length()
        return Node(True, A_, P, x, B.ofRatUp(err), B.ofRatUp(F(abs(xr) + abs(xi), 2 ** P)))
    fac = TWO_PI ** m["deg"]
    dr, di, err = {}, {}, F(0)
    for k, (cr, ci) in m["poly"]:
        k = tuple(k)
        assert max(abs(k[0]), abs(k[1])) <= H, ("import key outside the box", j, k)
        vr, vi = F(cr) * fac, F(ci) * fac                # mantissas at 2^128 = 2^P
        xr, xi = rnd(vr), rnd(vi)
        dr[k], di[k] = xr, xi
        err += (abs(vr - xr) + abs(vi - xi)) * _wceil(C.W, Q, abs(k[0])) * _wceil(C.W, Q, abs(k[1]))
    x = (pack(C.Lb, dr), pack(C.Lb, di))
    mx = max([abs(v) for v in list(dr.values()) + list(di.values())] + [1])
    rad = F(m["rad"], 2 ** P) * (2 * F(314159265358979323846264338327950288420, 10 ** 38)) ** m["deg"] + \
        err / 2 ** (P + 2 * Q)
    return Node(False, 2 ** mx.bit_length(), P, x, B.ofRatUp(rad), C.pnorm(C.Lb, P, x))


# ------------------------------------------------------------------------------------------------- the run
def steps_of(D):
    """`JStep`s: a box-by-box product reduced to 2^P; a reduce in place to 2^P after a product by a constant."""
    ops = D["ops"]
    is_const = {int(j) for j, v in D["imports"].items() if v["op"][0] == "const"}
    out = []
    for i in D["live"]:
        op = ops[i]
        if op[0] == "mul" and not (op[1] in is_const or op[2] in is_const):
            out.append((i, P, 0))
        elif op[0] == "mul":
            out.append((i, 0, P))
        else:
            out.append((i, 0, 0))
    return out


def run(C, bk, D, imports, steps):
    st = {"aW": 0, "aB": 0, "smax": 0, "lb": 0}
    S = dict(imports)
    ops = D["ops"]
    for i, eT, red in steps:
        op = ops[i]
        a, b = S[op[1]], S[op[2]]
        assert op[1] < i and op[2] < i
        if op[0] == "add":
            nd = j_add(C, a, b) if bk is not None else Node(a.u and b.u, None, max(a.e, b.e), None, None, None)
            if bk is None:
                nd = j_add_pass1(C, a, b)
        else:
            nd = j_mul(C, bk, a, b, eT, st) if bk is not None else j_mul_pass1(C, a, b, eT, st)
        if red:
            nd = j_red(C, bk, nd, red, st) if bk is not None else j_red_pass1(C, nd, red, st)
        S[i] = nd
    return S, st


# pass 1: loads and digits only (no radii), with the loads of `lb` unknown: reduced nodes take the load of their
# largest digit; the book is then fixed and pass 2 runs the exact mirror.
def j_add_pass1(C, a, b):
    u, e = a.u and b.u, max(a.e, b.e)
    a2, b2 = j_up(C, a, u, e), j_up(C, b, u, e)
    return Node(u, a2.A + b2.A, e, (a2.x[0] + b2.x[0], a2.x[1] + b2.x[1]), None, None)


def lb_of(C, x2):
    return max([abs(c) for z in x2 for c in unpack(C.Lb, z).values()] + [1]).bit_length()


def j_mul_pass1(C, a, b, eT, st):
    if a.u or b.u:
        return Node(a.u and b.u, mul_load(C.lay(a.u), C.lay(b.u), a.A, b.A), a.e + b.e, pc_mul(a.x, b.x), None, None)
    A_, e = mul_load(C.Lb, C.Lb, a.A, b.A), a.e + b.e
    x2 = z_pc(C, C.Lw, A_.bit_length(), e - eT, C.off, pc_mul(a.x, b.x))
    st["aW"], st["smax"] = max(st["aW"], A_), max(st["smax"], e - eT)
    st["lb"] = max(st["lb"], lb_of(C, x2))
    return Node(False, 2 ** st["lbfix"], eT, x2, None, None)


def j_red_pass1(C, nd, eT, st):
    L = C.lay(nd.u)
    x2 = z_pc(C, L, nd.A.bit_length(), nd.e - eT, 0, nd.x, L)
    st["aB"], st["smax"] = max(st["aB"], nd.A), max(st["smax"], nd.e - eT)
    st["lb"] = max(st["lb"], max([abs(c) for z in x2 for c in unpack(L, z).values()] + [1]).bit_length())
    return Node(nd.u, 2 ** st["lbfix"], eT, x2, None, None)


def book_of(C, st):
    """`JBook` from the pass-1 loads (`jBookOk`'s guards)."""
    lb, aW, aB, smax = st["lb"], st["aW"], st["aB"], st["smax"]
    lr = (aW + mul_load(C.Lb, C.Lb, 2 ** lb, 2 ** smax)).bit_length()
    lrb = (aB + mul_load(C.Lb, C.LU0, 2 ** lb, 2 ** smax)).bit_length()
    ln = lb + 1
    ls, lsb = aW.bit_length(), aB.bit_length()
    need = [ls + 2, lsb + 2, lb + 2]
    for L, l in ((C.Lw, lr), (C.Lb, lrb), (C.Lb, ln)):
        r, c = G.maxes(C.W, Q, L.lo, L.dims, L.S)
        need += [l + 2, (L.dims[0] * L.S * 2 ** l * r * c).bit_length()]
    w = max(need)
    w += (-w) % 8
    return Book(lb=lb, lr=lr, lrb=lrb, ln=ln, aW=aW, aB=aB, smax=smax, ls=ls, lsb=lsb, off=C.off, w=w)


# ------------------------------------------------------------------------------------------------- ingestion
def spread_step(a, b, h, k, Y):                         # JetIngest.spreadStep
    return Y + (Y & periodic(b * (2 * h), k, (2 ** (a * h) - 1) << (a * h))) * (2 ** ((b - a) * h) - 1)


def spread_aux(a, b, L, k, Y):                          # JetIngest.spreadAux
    while L:
        L -= 1
        Y = spread_step(a, b, 2 ** L, k, Y)
        k *= 2
    return Y


def ceil_log2(x):
    return max(0, (x - 1).bit_length())


def j_spread(D0, D1, S, w, wn, L1, L2, Y):              # JetIngest.jSpread
    return spread_aux(D1 * w, S * w, L2, 1, spread_aux(wn, w, L1, 1, Y)) - box_pat(w, S, D0, D1, 2 ** (wn - 1))


def narrow(C, Z):
    """The narrow literal of a box part: its width rounded up to a multiple of 8 (few width classes, so the
    spreading masks are shared), checked against the mirror of `jSpread`."""
    L = C.Lb
    d = unpack(L, Z)
    wn = max([abs(c) for c in d.values()] + [1]).bit_length() + 1
    wn += (-wn) % 8
    Y = 0
    for r in range(L.dims[0]):
        for c in range(L.dims[1]):
            v = d.get((L.lo[0] + r, L.lo[1] + c), 0) + 2 ** (wn - 1)
            assert 0 <= v < 2 ** wn
            Y |= v << (wn * (r * L.dims[1] + c))
    L1, L2 = ceil_log2(L.dims[0] * L.dims[1]), ceil_log2(L.dims[0])
    assert j_spread(L.dims[0], L.dims[1], L.S, L.w, wn, L1, L2, Y) == Z, "jSpread mirror"
    return wn, Y, L1, L2


# ------------------------------------------------------------------------------------------------- Lean text
CHUNK = 1024                                            # bits per hexadecimal chunk of a literal


def nat_tree(z, bits=CHUNK):
    """A balanced `natJoin` tree of `bits`-bit chunks XOR-ed with `natRamp bits m` (as `gate_gen.nat_tree`)."""
    m = max(1, -(-z.bit_length() // bits))
    z ^= GG.nat_ramp(bits, m)
    ch = [(z >> (bits * i)) & ((1 << bits) - 1) for i in range(m)]
    lines = []

    def emit(lo, hi):
        if hi - lo == 1:
            lines.append("0x%X" % ch[lo])
            return
        mid = (lo + hi) // 2
        lines.append("(natJoin %d" % (bits * (mid - lo)))
        emit(lo, mid)
        emit(mid, hi)
        lines[-1] += ")"
    emit(0, m)
    return "((\n%s)\n  ^^^ natRamp %d %d)" % ("\n".join(lines), bits, m), m


def q_lit(q):
    q = F(q)
    return "(%d / %d : ℚ)" % (q.numerator, q.denominator)


def op_lit(op):
    k = op[0]
    if k == "const":
        return ".const %s %s (%d)" % (q_lit(F(*op[1])), q_lit(F(*op[2])), op[3])
    if k == "char":
        return ".char [%s]" % ", ".join("(%d)" % x for x in op[1])
    if k in ("add", "mul"):
        return ".%s %d %d" % (k, op[1], op[2])
    return ".%s %d" % (k, op[1])


def lay_lit(L):
    return "⟨[%d, %d], [%d, %d], [%d, 1], %d, 1⟩" % (L.lo[0], L.lo[1], L.dims[0], L.dims[1], L.S, L.w)


class Emit:
    def __init__(self, C):
        self.C, self.defs, self.chunks = C, [], 0

    def node(self, name, nd):
        C = self.C
        if nd.u:
            x = "⟨(%d), (%d)⟩" % nd.x
        else:
            parts = []
            for pi, z in enumerate(nd.x):
                if z == 0:
                    parts.append("0")
                    continue
                wn, Y, L1, L2 = narrow(C, z)
                body, m = nat_tree(Y)
                self.chunks += m
                self.defs.append("def %s_%d : ℕ :=\n%s\n" % (name, pi, body))
                parts.append("jSpread %d %d %d %d %d %d %d %s_%d" % (C.Lb.dims[0], C.Lb.dims[1], C.Lb.S, C.Lb.w,
                                                                       wn, L1, L2, name, pi))
            x = "⟨%s,\n    %s⟩" % tuple(parts)
        al = ("2 ^ %d" % (nd.A.bit_length() - 1)) if nd.A == 2 ** (nd.A.bit_length() - 1) else "%d" % nd.A
        self.defs.append("def %s : JNode LGF :=\n  ⟨%s, %s, %d, %s, ⟨%d⟩, ⟨%d⟩⟩\n" % (
            name, "true" if nd.u else "false", al, nd.e, x, nd.r, nd.nb))


HEAD = """module

public import KAM.CertificateSharp.Packed.JetIngest

/-!
# V2-PACKED-JET gate probe `%s` (generated, opt-in, not built)

%s

LG00's cfgLow jet chain, slots [%d, %d) (lg00-cert `%s`); generated by `scripts/packed/jet_gate_gen.py`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed.JGate.%s

open KAM KAM.Certificate KAM.CertificateSharp.Packed

abbrev LGF : Type := CertFixed 128

"""


def main():
    D = json.load(open(sys.argv[1]))
    W = F(D["weight"]["w"][0], D["weight"]["w"][1])
    steps = steps_of(D)
    # pass 1 at a wide slot (loads and digits do not depend on the width); `lbfix` iterated to a fixed point
    C1 = Ctx(W, 1024)
    imps1 = {int(j): import_node(C1, int(j), v) for j, v in D["imports"].items()}
    lbfix = 140
    for _ in range(6):
        st = {"aW": 0, "aB": 0, "smax": 0, "lb": 0, "lbfix": lbfix}
        S = dict(imps1)
        for i, eT, red in steps:
            op = D["ops"][i]
            a, b = S[op[1]], S[op[2]]
            nd = j_add_pass1(C1, a, b) if op[0] == "add" else j_mul_pass1(C1, a, b, eT, st)
            if red:
                nd = j_red_pass1(C1, nd, red, st)
            S[i] = nd
        if st["lb"] <= lbfix:
            break
        lbfix = st["lb"]
    st["lb"] = lbfix
    bk = book_of(C1, st)
    print("book", {k: (v if k in ("lb", "lr", "lrb", "ln", "smax", "ls", "lsb", "off", "w") else v.bit_length())
                   for k, v in bk.__dict__.items()})
    if "--stats" in sys.argv:
        return
    C = Ctx(W, bk.w)
    imps = {int(j): import_node(C, int(j), v) for j, v in D["imports"].items()}
    S, _ = run(C, bk, D, imps, steps)
    E = Emit(C)
    rho = F(*D["weight"]["rho"])
    E.defs.append("def gW : CertWeight := ⟨%s, %s⟩\n" % (q_lit(rho), GG.lean_rat(W).strip()))
    E.defs.append("def jbk : JBook where\n  Lb := %s\n  LU0 := %s\n  Lw := %s\n  q := %d\n  lb := %d\n  lr := %d\n"
                  "  lrb := %d\n  ln := %d\n  aW := %d\n  aB := %d\n  smax := %d\n  ls := %d\n  lsb := %d\n  off := %d\n"
                  % (lay_lit(C.Lb), lay_lit(C.LU0), lay_lit(C.Lw), Q, bk.lb, bk.lr, bk.lrb, bk.ln, bk.aW, bk.aB,
                     bk.smax, bk.ls, bk.lsb, bk.off))
    ops = D["ops"]
    nch = 200
    names = []
    for c0 in range(0, len(ops), nch):
        nm = "ops_%d" % (c0 // nch)
        names.append(nm)
        E.defs.append("def %s : List SlpOp :=\n  [%s]\n" % (nm, ",\n   ".join(op_lit(op) for op in ops[c0:c0 + nch])))
    # right-nested appends: `++` associates to the left, and a left-nested chain makes every cell of the first
    # chunk pass through every append (V2-PACKED-JET-MEM: 4.6 s and 1.1 GB for one walk to slot 7291)
    E.defs.append("def lgProg : Slp := ⟨%s%s⟩\n" % (" ++\n    (".join(names), ")" * (len(names) - 1)))
    for j in sorted(imps):
        E.node("imp_%d" % j, imps[j])
    E.defs.append("def imports : List (ℕ × JNode LGF) :=\n  [%s]\n" % ",\n   ".join(
        "(%d, imp_%d)" % (j, j) for j in sorted(imps)))
    E.defs.append("def steps : List JStep :=\n  [%s]\n" % ",\n   ".join("(%d, %d, %d)" % t for t in steps))
    head_defs = list(E.defs[:3 + len(names)])        # gW, jbk, the program chunks, lgProg
    heavy_max = int(next((x.split("=")[1] for x in sys.argv if x.startswith("--heavy=")), "34"))
    # sub-segments of at most `heavy_max` heavy steps (box-by-box products and reduces in place): the kernel keeps
    # every intermediate of a declaration, so one sub-segment per probe
    chunks, cur, hv = [], [], 0
    for t in steps:
        h = (1 if t[1] else 0) + (1 if t[2] else 0)
        if cur and hv + h > heavy_max:
            chunks.append(cur)
            cur, hv = [], 0
        cur.append(t)
        hv += h
    chunks.append(cur)
    # `--split=i,j`: halve these sub-segments (by heavy steps) where the data of four heavy steps does not fit
    # rounds separated by `;`, each on the numbering left by the previous round
    for rnd_ in next((a.split("=")[1] for a in sys.argv if a.startswith("--split=")), "").split(";"):
        split = {int(x) for x in rnd_.split(",") if x}
        out_ch = []
        for c, ch in enumerate(chunks):
            if c not in split:
                out_ch.append(ch)
                continue
            hv, cut = 0, len(ch)
            tot = sum((1 if t[1] else 0) + (1 if t[2] else 0) for t in ch)
            for k, t in enumerate(ch):
                hv += (1 if t[1] else 0) + (1 if t[2] else 0)
                if hv >= (tot + 1) // 2:
                    cut = k + 1
                    break
            if tot <= 1:                            # a data-bound piece: halve by steps
                cut = max(1, len(ch) // 2)
            out_ch += [ch[:cut], ch[cut:]] if ch[cut:] else [ch]
        chunks = out_ch
    final = set(D["exports"])
    node_of = dict(imps)
    node_of.update(S)
    probes, plan = {}, []
    for c, ch in enumerate(chunks):
        defined = {t[0] for t in ch}
        reads = {x for t in ch for x in D["ops"][t[0]][1:3]}
        imp_c = sorted(reads - defined)
        later = {x for ch2 in chunks[c + 1:] for t in ch2 for x in D["ops"][t[0]][1:3]}
        exp_c = sorted(j for j in defined if j in later or j in final)
        E.defs, E.chunks = list(head_defs), 0
        for j in imp_c:
            E.node("imp_%d" % j, node_of[j])
        E.defs.append("def imports : List (ℕ × JNode LGF) :=\n  [%s]\n" % ",\n   ".join(
            "(%d, imp_%d)" % (j, j) for j in imp_c))
        E.defs.append("def steps : List JStep :=\n  [%s]\n" % ",\n   ".join("(%d, %d, %d)" % t for t in ch))
        base = "".join(d + "\n" for d in E.defs)
        E.defs = []
        for j in exp_c:
            E.node("exp_%d" % j, node_of[j])
        expo = "".join(d + "\n" for d in E.defs)
        exp_list = "def exports : List (ℕ × JNode LGF) :=\n  [%s]\n\n" % ",\n   ".join(
            "(%d, exp_%d)" % (j, j) for j in exp_c)
        nm = "JSeg_%d" % c
        stmt = "jSegOk 2 gW jbk lgProg %d imports steps exports = %%s" % ch[0][0]
        hv_c = sum((1 if t[1] else 0) + (1 if t[2] else 0) for t in ch)
        doc = ("Sub-segment %d of %d (`jSegOk`): slots %d..%d, %d steps (%d box-by-box products, %d reduces in place), "
               "%d imports, %d exports." % (c, len(chunks), ch[0][0], ch[-1][0], len(ch), sum(1 for t in ch if t[1]),
                                           sum(1 for t in ch if t[2]), len(imp_c), len(exp_c)))
        probes[nm] = (doc, base + expo + exp_list, stmt % "true")
        plan.append(dict(name=nm, steps=len(ch), heavy=hv_c, imports=len(imp_c), exports=len(exp_c),
                         first=ch[0][0], last=ch[-1][0]))
        if c == 0:
            probes["JData_0"] = ("Data-only control of sub-segment 0.", base + expo + exp_list, "True")
        if c == len(chunks) - 1:
            # controls: the last export's radius one ulp (2^-128) lower; its lowest box digit off by one
            jl = exp_c[-1]
            nd = node_of[jl]
            k0 = sorted(unpack(C.Lb, nd.x[0]))[0]
            for tag, m in (("R", Node(nd.u, nd.A, nd.e, nd.x, nd.r - 1, nd.nb)),
                           ("X", Node(nd.u, nd.A, nd.e, (nd.x[0] + (1 << (C.Lb.w * C.Lb.slot(k0))), nd.x[1]),
                                      nd.r, nd.nb))):
                E.defs = []
                E.node("exp_%d" % jl, m)
                ex2 = expo[:expo.index("def exp_%d_0" % jl)] + "".join(d + "\n" for d in E.defs)
                probes["JSegMut%s_%d" % (tag, c)] = (
                    ("Negative control (sharp): the radius of export %d one ulp (2^-128) lower." % jl) if tag == "R"
                    else ("Negative control (data): the lowest box digit of export %d off by one." % jl),
                    base + ex2 + exp_list, stmt % "false")
    os.makedirs(OUT, exist_ok=True)
    for name, (doc, body, stx) in probes.items():
        txt = HEAD % (name, doc, D["start"], D["stop"], D["lg00_cert_commit"][:8], name) + body
        txt += "set_option profiler true\nset_option profiler.threshold 1\n\ntheorem probe :\n    %s := by\n" \
               "  decide +kernel\n\nend KAM.CertificateSharp.Packed.JGate.%s\n" % (stx, name)
        with open(os.path.join(OUT, name + ".lean"), "w") as f:
            f.write(txt)
    exps = {j: S[j] for j in D["exports"]}
    meta = dict(start=D["start"], stop=D["stop"], lg00_cert_commit=D["lg00_cert_commit"], steps=len(steps),
                products=sum(1 for t in steps if t[1]), in_place=sum(1 for t in steps if t[2]),
                adds=sum(1 for t in steps if D["ops"][t[0]][0] == "add"), imports=len(imps), exports=len(exps),
                landed_segments=len(D["segs"]), landed_kinds={k: sum(1 for s_ in D["segs"] if s_["kind"] == k)
                                                             for k in ("P", "R")},
                book={k: (v if k in ("lb", "lr", "lrb", "ln", "smax", "ls", "lsb", "off", "w") else
                          "2^%d" % v.bit_length()) for k, v in bk.__dict__.items()},
                heavy_max=heavy_max, sub_segments=plan, chunk_bits=CHUNK,
                export_radius_max=float(max(F(x.r, 2 ** P) for x in exps.values())),
                export_nb_max=float(max(F(x.nb, 2 ** P) for x in exps.values())))
    with open(os.path.join(OUT, "JetGate.json"), "w") as f:
        json.dump(meta, f, indent=1)
    print(json.dumps(meta, indent=1))


if __name__ == "__main__":
    main()
