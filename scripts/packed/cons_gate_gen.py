#!/usr/bin/env python3
"""V2-PACKED-CONS gate (untrusted tooling; the kernel re-checks everything): the consumers of the packed jet
(`checkTorsionJ`, `checkInvarianceJ`, `checkEnergyJ`, and the frames' `sup |T|` on the jet's torsion) on LG00 T'
data, as modules of a scratch Lake package (opt-in, outside the default build).

Inputs (read only):
  - T''s certificate data, lg00-app `applications/lg00/LG00/<TREE>/Data` (`DCoeffs`, `E0`, `W8`, `Cert`);
  - the jet's T' nodes: the mirror caches of `jet_low_gen.py --mirror-only --cache=...` for cfgLow and cfgFull
    (`--low=`, `--full=`; the wanted slots' nodes are read, nothing else);
  - the package PKG holds T''s certificate modules under the prefix PRE (`prod_cert_gen.py PKG --prefix=PRE`).
Computes, exactly in Python (bit-exact mirrors of the backend `CertFixed 128` and of the packed norms):
  - the Gram memo and core (delta, beta, eps) and the D2K memo (as `tors_gate_gen.load`);
  - the rounded torsion chain of `TorsR.lean` with `DX_H o K` and `DH o K` from the jet nodes (`trAJ`, `trD1J`):
    the seven nodes (rounded to 2^128, truncated to the box), the tables of the averages, the final test; on the
    jet's cfgLow box and slot width (`jetLowOk` checks `layoutEq jd.jb.Lb rb.Lb`);
  - the invariance arrays (`ivX`), their radii (`ivR`) and the bound of `ivRowOk`, on the jet's cfgFull box;
  - the energy read-out of `enOk`; the frames' `sup |T|` row sums (`trFrameTOk`).
Writes PKG/PRE/Cons/{Base,Nodes,Jet}.lean (the shared data: books, memos, the wanted jet nodes as an alpha-free
ledger `JetData`) and PKG/PRE/Cons/P/<probe>.lean (one conjunct each, `decide +kernel`), and PKG/cons_plan.json
(the probes in build order and the mirror's figures).
Usage: python3 -I scripts/packed/cons_gate_gen.py --low=PKL --full=PKL [--app=APP] [--tree=TP] [--pkg=DIR]
       [--prefix=LG00C]
"""
import json
import os
import pickle
import re
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import torsr_gate_gen as R    # noqa: E402  (imports tors_gate_gen, gram_gate_gen and the sofx mirror)
import jet_gate_gen as JG     # noqa: E402

T, G, A, C, M, SP = R.T, R.G, R.A, R.C, R.M, R.SP
P, Q, n = 128, 24, 2
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))


def opt(name, default):
    return next((a.split("=", 1)[1] for a in sys.argv if a.startswith("--%s=" % name)), default)


APP = opt("app", "/home/scott/KAM-dev-worktrees/lg00-app/applications/lg00/LG00")
TREE = opt("tree", "TP")
PKG = opt("pkg", os.path.join(ROOT, ".lake", "v2-packed-cons", "pkg"))
PRE = opt("prefix", "LG00C")
LOW = opt("low", None)
FULL = opt("full", None)
HL, HF = 25, 48                                       # the boxes of the cfgLow and cfgFull chains


# ---------------------------------------------------------------------------------------------- T' data
def rat_of(txt):
    """A generated rational `((num : ℤ) : ℚ) / ((den : ℕ) : ℚ)` (digits, `+ - * ^ ( )` only)."""
    def arith(expr):
        expr = re.sub(r"\s+", "", expr).replace("^", "**")
        assert re.fullmatch(r"[0-9+\-*()]+", expr), expr
        return int(eval(expr, {"__builtins__": {}}))  # digits and + - * ( ) only
    flat = re.sub(r"\s+", " ", txt)
    num = re.search(r":= \(\((.*?) : ℤ\) : ℚ\)", flat).group(1)
    den = re.search(r"/ \(\((.*?) : ℕ\) : ℚ\)", flat).group(1)
    return F(arith(num), arith(den))


def qfield(text, name):
    """A field `name := (a / b : ℚ)` or `name := lgDk` of a `where` block, as a rational."""
    m = re.search(r"\b%s := \((-?\d+) / (\d+) : ℚ\)" % re.escape(name), text)
    if m:
        return F(int(m.group(1)), int(m.group(2)))
    m = re.search(r"\b%s := (lgD\d+)\b" % re.escape(name), text)
    assert m, name
    return m.group(1)


def mant(t):
    t = t.strip()
    m = re.fullmatch(r"\(?Int\.negSucc\s+(\d+)\)?", t)
    return -int(m.group(1)) - 1 if m else int(t)


def load():
    data = os.path.join(APP, TREE, "Data")
    comps = ["lg00Angle0_0", "lg00Angle1_0", "lg00Action0_0", "lg00Action1_0"]
    grams = ["lg00Gram00_0", "lg00Gram01_0", "lg00Gram10_0", "lg00Gram11_0"]
    texts = {nm: G.grab(os.path.join(data, "E0.lean"), nm) for nm in comps}
    texts.update({nm: G.grab(os.path.join(data, "W8.lean"), nm) for nm in grams})
    dco = os.path.join(data, "DCoeffs.lean")
    lgD = {}
    for k in range(10):
        try:
            lgD["lgD%d" % k] = rat_of(G.grab(dco, "lgD%d" % k))
        except ValueError:
            break
    cert = open(os.path.join(data, "Cert.lean")).read()
    val = lambda x: lgD[x] if isinstance(x, str) else x
    params = cert[cert.index("def lg00Params"):cert.index("def lg00Box")]
    s, E0, err = val(qfield(params, "s")), val(qfield(params, "E0")), val(qfield(params, "err"))
    sigT, sigB, mu = val(qfield(params, "σT")), val(qfield(params, "σB")), val(qfield(params, "μ"))
    mb = re.search(r"def lg00Box : FreqBox := \[\((lgD\d+), (lgD\d+)\), \(\((-?\d+) / (\d+) : ℚ\), 0\)\]", cert)
    box = [(lgD[mb.group(1)], lgD[mb.group(2)]), (F(int(mb.group(3)), int(mb.group(4))), F(0))]
    mw = re.search(r"weight := ⟨\((\d+) / (\d+) : ℚ\), (lgD\d+)⟩", cert)
    rho, w = F(int(mw.group(1)), int(mw.group(2))), lgD[mw.group(3)]
    me = re.search(r"def lg00Emb : CertEmbedding LGF where(.*?)\n\n", cert, re.S).group(1)
    assert "angleDeg := [-1, -1]" in me and "actionDeg := [0, 0]" in me
    zs = [mant(z) for z in re.findall(r"⟨⟨\s*(\(?Int\.negSucc\s+\d+\)?|-?\d+)\s*⟩,\s*lg00(?:Angle|Action)\d_0⟩",
                                      re.sub(r"\s+", " ", me))]
    assert len(zs) == 4, zs
    mp = re.search(r"def lg00Pi : PiEnclosure LGF := ⟨⟨(\d+)⟩, ⟨(\d+)⟩, (\d+), (\d+)⟩", cert)
    pe = A.PiEnclosure(*(int(mp.group(i)) for i in range(1, 5)))
    tinv = cert[cert.index("def lg00TorsInv"):cert.index("/-- The model configuration Full")]
    B = A.FixedB(P)

    def half(nm):
        return [(k, (re_, im_)) for k, (re_, im_) in T.parse_cc_terms(texts[nm])]
    K = M.Embedding([-1, -1], [M.RealPoly(zs[0], half(comps[0])), M.RealPoly(zs[1], half(comps[1]))],
                    [0, 0], [M.RealPoly(zs[2], half(comps[2])), M.RealPoly(zs[3], half(comps[3]))])
    Wm = M.Weight(rho, w)

    def entry(m):
        assert m.deg == 0
        mt = SP.toMants(B, P, m.poly)
        assert mt is not None
        return mt[0], mt[1], F(m.rad, 2 ** P)
    gm = {}
    for r in range(2 * n):
        for a in range(n):
            gm[(r, a)] = entry(C.dkAngleModel(B, n, K, Wm, pe, r, a) if r < n
                               else C.dkActionModel(B, n, K, Wm, pe, r - n, a))
    d2 = [entry(C.d2kModel(B, n, K, Wm, pe, r, j, l)) for r in range(2 * n) for j in range(n) for l in range(n)]
    Bpolys = [[half(grams[0]), half(grams[1])], [half(grams[2]), half(grams[3])]]
    S = R.parse_cc_matrix(tinv, n + 1)
    return dict(texts=texts, comps=comps, grams=grams, lgD=lgD, s=s, E0=E0, err=err, sigT_mu=sigT - mu,
                sigB_mu=sigB - mu, box=box, rho=rho, w=w, K=K, Wm=Wm, pe=pe, B=B, gm=gm, d2=d2, Bpolys=Bpolys, S=S)


def gram_book(D):
    """`PGramBook` as `gram_gate_gen.py`: the boxes of the `DK` and `B` keys, their window, the width."""
    kk = [(0, 0)]
    for nm in D["comps"]:
        for k in G.keys(D["texts"][nm]):
            kk += [k, (-k[0], -k[1])]
    loK, dK = G.box(kk)
    loB, dB = G.box([k for nm in D["grams"] for k in G.keys(D["texts"][nm])] + [(0, 0)])
    d2_ = (2 * dK[0] - 1, 2 * dK[1] - 1)
    lo2 = (2 * loK[0], 2 * loK[1])
    d3 = (dB[0] + d2_[0] - 1, dB[1] + d2_[1] - 1)
    lo3 = (loB[0] + lo2[0], loB[1] + lo2[1])
    s0 = d3[1]
    st = (s0, 1)
    N1, NB, N2 = G.dense_len(dK, st), G.dense_len(dB, st), G.dense_len(d2_, st)
    BK, BB = 2 ** 136, 2 ** 132
    bG = 2 * n * G.mul_load(N1, N1, BK, BK)
    bE = n * G.mul_load(NB, N2, BB, bG)
    bD = 2 ** (3 * P) + bE
    lK, lB, lD = BK.bit_length(), BB.bit_length(), bD.bit_length()
    need = []
    for lo, dims, l in ((loK, dK, lK), (loB, dB, lB), (lo3, d3, lD)):
        r, c = G.maxes(D["w"], Q, lo, dims, s0)
        need.append(max(l + 2, (dims[0] * s0 * 2 ** l * r * c).bit_length() + 1))
    width = max(need)
    lay = lambda lo, dims: "⟨[%d, %d], [%d, %d], [%d, 1], %d, 1⟩" % (lo[0], lo[1], dims[0], dims[1], s0, width)
    return ("def cBk : PGramBook where\n  P := %d\n  L1 := %s\n  LB := %s\n  bK := 2 ^ 136\n  bB := 2 ^ 132\n"
            "  q := %d\n  lK := %d\n  lB := %d\n  lD := %d\n" % (P, lay(loK, dK), lay(loB, dB), Q, lK, lB, lD)), \
        dict(loK=loK, dK=dK, loB=loB, dB=dB)


# ---------------------------------------------------------------------------------------------- the jet nodes
class _Ctx:
    def __init__(self, Lb):
        self.Lb = Lb


def jet_nodes(path, H, wanted):
    """The wanted slots' nodes of a mirror run (on the box of half-width H, at the run's slot width)."""
    with open(path, "rb") as f:
        ck = pickle.load(f)
    assert ck["H"] == H, (ck["H"], H)
    bk, S = ck["bk"], ck["S"]
    Lb = JG.Lay((-H, -H), (2 * H + 1, 2 * H + 1), 4 * H + 1, bk.w)
    nodes = {}
    for i in wanted:
        nd = S[i]
        assert not nd.u and nd.e == P, ("wanted node not reduced to the box", i, nd.u, nd.e)
        nodes[i] = nd
    return dict(bk=bk, Lb=Lb, nodes=nodes, source=ck.get("source"))


def node_poly(Lb, nd):
    re_, im_ = JG.unpack(Lb, nd.x[0]), JG.unpack(Lb, nd.x[1])
    return R.join(re_, im_)


def swap(a):
    return a + n if a < n else a - n


# ---------------------------------------------------------------------------------------------- the torsion
def tors(D, jl, J):
    """The rounded torsion chain with `A`, `DH` from the jet (mirror of `torsRCoreJ`)."""
    B, w = D["B"], D["w"]
    ctx = R.Ctx(w, Q, P)
    geo = R.Geo(HL, 4 * HL + 1)
    # the boundary (as `torsr_gate_gen.inputs`, with A and DH from the jet)
    K = {}
    for (r, a), e in D["gm"].items():
        p = T.pdict(e[0], e[1])
        assert all(geo.inbox(k) for k in p), "a DK key outside the box"
        K[(r, a)] = (p, B.ofRatUp(e[2]), ctx.pnorm(p, P))
    Bm = {}
    for i in range(n):
        for k in range(n):
            mt = SP.toMants(B, P, C.gramInvPoly(D["Bpolys"], i, k))
            p = T.pdict(mt[0], mt[1])
            assert all(geo.inbox(kk) for kk in p), "a B key outside the box"
            Bm[(i, k)] = (p, D["eps"], ctx.pnorm(p, P))
    D2 = []
    for l in range(n):
        Dl = {}
        for r in range(2 * n):
            for j in range(n):
                e = D["d2"][(r * n + j) * n + l]
                p = T.pdict(e[0], e[1])
                assert all(geo.inbox(k) for k in p), "a D2K key outside the box"
                Dl[(r, j)] = (p, B.ofRatUp(e[2]), ctx.pnorm(p, P))
        D2.append(Dl)
    Fl = []
    for l in range(n):
        c, rad = D["box"][l]
        fc = T.C_round(D["s"] * c * 2 ** P)
        fr = abs(D["s"]) * rad + abs(D["s"] * c - F(fc, 2 ** P))
        Fl.append(({(0, 0): (fc, 0)}, B.ofRatUp(fr), B.ofRatUp(F(abs(fc), 2 ** P))))
    Lb = jl["Lb"]
    Am = {}
    for a in range(2 * n):
        for b in range(2 * n):
            nd = jl["nodes"][J["d2"][swap(a)][b]]
            p = node_poly(Lb, nd)
            Am[(a, b)] = (p if a < n else R.cscale(p, -1), nd.r, nd.nb)
    D1 = {(0, a): (node_poly(Lb, jl["nodes"][J["d1"][a]]), jl["nodes"][J["d1"][a]].r,
                   jl["nodes"][J["d1"][a]].nb) for a in range(2 * n)}
    memos, Tm, Ym, _ = R.chain(ctx, geo, K, Bm, D2, Fl, Am, D1, n, P)
    CT = [[R.centre(Tm[(i, j)][0], 2 * P) for j in range(n)] for i in range(n)]
    RT = [[F(Tm[(i, j)][1], 2 ** P) for j in range(n)] for i in range(n)]
    CY = [R.centre(Ym[(0, j)][0], 2 * P) for j in range(n)]
    RY = [F(Ym[(0, j)][1], 2 ** P) for j in range(n)]
    ok, info = R.final_mirror(ctx, dict(box=D["box"], s=D["s"]), CT, RT, CY, RY, D["S"], D["sigT_mu"], P)
    assert ok, ("the mirror of the final test fails", info)
    mx = max(abs(x) for m in memos.values() for p in m[0].values() for v in p.values() for x in v)
    p2 = lambda x: 2 ** max(1, x.bit_length())
    mxv = lambda es: max([1] + [abs(v) for e in es for _, v in e[0] + e[1]])
    bA = max(nd.A for nd in jl["nodes"].values())
    assert bA == 2 ** (bA.bit_length() - 1)
    rb = R.r_book(P, Q, w, HL, dict(bK=2 ** 136, bB=2 ** 132, bD=p2(mxv(D["d2"])), bA=bA,
                                    bF=p2(max(abs(f[0][(0, 0)][0]) for f in Fl)), bR=p2(mx)))
    assert rb["width"] <= Lb.w, ("the torsion needs a wider slot than the jet's", rb["width"], Lb.w)
    rb["width"] = Lb.w
    assert rb["s0"] == Lb.S and rb["Lb"] == (Lb.lo, Lb.dims)
    assert rb["loads"]["aT"] <= rb["aW"], "trFrameTOk's guard aT ≤ aW"
    # the frames' `sup |T|` row sums (`trFrameTOk`: pnorm on the window at scale 2^(2P) plus the radius)
    rows = []
    for i in range(n):
        vals = [B.upAdd(ctx.pnorm(Tm[(i, j)][0], 2 * P), Tm[(i, j)][1]) for j in range(n)]
        rows.append(M.sumUp(B, vals))
    return dict(ctx=ctx, K=K, Fl=Fl, memos=memos, Tm=Tm, Ym=Ym, CT=CT, RT=RT, CY=CY, RY=RY, rb=rb, info=info,
                frameT=rows, Am=Am)


# ---------------------------------------------------------------------------------------------- invariance
def invariance(D, jf, J, Kmm, Fl):
    """Mirror of `ivRowOk` for every coordinate: the array, its packed norm and its radius."""
    B, w = D["B"], D["w"]
    ctx = R.Ctx(w, Q, P)
    Lb = jf["Lb"]
    inb = lambda k: all(Lb.lo[j] <= k[j] < Lb.lo[j] + Lb.dims[j] for j in range(2))
    out = []
    for a in range(2 * n):
        nd = jf["nodes"][J["d1"][swap(a)]]
        xh = node_poly(Lb, nd)
        if a >= n:
            xh = R.cscale(xh, -1)
        arr = R.cscale(xh, 2 ** P)
        rads = []
        for l in range(n):
            kp, kr, knb = Kmm[(a, l)]
            assert all(inb(k) for k in kp)
            fc, fr, fnb = Fl[l][0][(0, 0)][0], Fl[l][1], Fl[l][2]
            arr = R.cadd(arr, R.cscale(kp, -fc))
            rads.append(ctx.pmulRad(knb, kr, fnb, fr))
        rad = B.upAdd(nd.r, M.sumUp(B, rads))
        nrm = ctx.pnorm(arr, 2 * P)
        tot = B.upAdd(nrm, rad)
        out.append(dict(norm=nrm, rad=rad, tot=tot, jet_r=nd.r))
    return out


def dk_full(D, jf):
    """The `DK` entries packed on the cfgFull box (`ptK` on `ib.toT`): polynomial, radius, norm bound."""
    B, ctx = D["B"], R.Ctx(D["w"], Q, P)
    return {k: (T.pdict(e[0], e[1]), B.ofRatUp(e[2]), ctx.pnorm(T.pdict(e[0], e[1]), P)) for k, e in D["gm"].items()}


def i_book(D, jf, Fl):
    Lb = jf["Lb"]
    bJ = max(nd.A for nd in jf["nodes"].values())
    bF = 2 ** max(1, max(abs(f[0][(0, 0)][0]) for f in Fl).bit_length())
    N = Lb.dl()
    ml = lambda x, y: 2 * min(N, 1) * x * y
    aI = ml(bJ, 2 ** P) + n * ml(2 ** 136, bF)
    lK, lI = 137, aI.bit_length()
    for l, lo, dims in ((lK, Lb.lo, Lb.dims), (lI, Lb.lo, Lb.dims)):
        r, c = G.maxes(D["w"], Q, lo, dims, Lb.S)
        assert l + 2 <= Lb.w and dims[0] * Lb.S * 2 ** l * r * c < 2 ** Lb.w, "an invariance norm guard fails"
    return dict(P=P, Lb=Lb, bJ=bJ, bK=2 ** 136, bF=bF, q=Q, lK=lK, lI=lI, aI=aI)


# ---------------------------------------------------------------------------------------------- energy
def energy(D, jf, J):
    B = D["B"]
    nd = jf["nodes"][J["v0"]]
    p = node_poly(jf["Lb"], nd)
    z = p.get((0, 0), (0, 0))
    zr, zi = F(z[0], 2 ** P), F(z[1], 2 ** P)
    q = abs(zr - D["E0"]) + abs(zi)
    tot = B.upAdd(B.ofRatUp(q), nd.r)
    return dict(z=(zr, zi), q=q, tot=tot, r=nd.r)


# ---------------------------------------------------------------------------------------------- Lean text
COPY = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

%s

/-!
# %s

%s

Generated by `scripts/packed/cons_gate_gen.py` (V2-PACKED-CONS; opt-in, outside the default build).
-/

@[expose] public noncomputable section

namespace %s.TP.Cons

open KAM KAM.Certificate KAM.CertificateSharp.Packed

"""


def module(path, imports, title, doc, body):
    txt = COPY % ("\n".join("public import %s" % i for i in imports), title, doc, PRE) + body + \
        "\nend %s.TP.Cons\n" % PRE
    full = os.path.join(PKG, *path.split(".")) + ".lean"
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "w") as f:
        f.write(txt)


def lay_lit(lo, dims, s0, w):
    return "⟨[%d, %d], [%d, %d], [%d, 1], %d, 1⟩" % (lo[0], lo[1], dims[0], dims[1], s0, w)


def memo_entry(name, e, kind="MemoEntry"):
    return ("def %s_re : List (CertKey × ℤ) :=\n%s\n\ndef %s_im : List (CertKey × ℤ) :=\n%s\n\n"
            "def %s : %s := (%s_re, %s_im, %s)\n\n") % (name, T.wrap(T.tl(e[0])), name, T.wrap(T.tl(e[1])), name,
                                                         kind, name, name, T.qlit(e[2]))


def base_text(D, X, gbook):
    fmt = ("def dz (n : ℕ) : ℤ := if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)\n\n"
           "abbrev tz (k₀ k₁ v : ℕ) : CertKey × ℤ := ([dz k₀, dz k₁], dz v)\n\n")
    out = fmt + gbook + "\n"
    for (r, a), e in sorted(D["gm"].items()):
        out += "def gMre_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (r, a, T.wrap(T.tl(e[0])))
        out += "def gMim_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (r, a, T.wrap(T.tl(e[1])))
    rows = lambda pf: "[" + ", ".join("[" + ", ".join("%s_%d_%d" % (pf, r, a) for a in range(n)) + "]"
                                      for r in range(2 * n)) + "]"
    rads = "[" + ", ".join("[" + ", ".join(T.qlit(D["gm"][(r, a)][2]) for a in range(n)) + "]"
                           for r in range(2 * n)) + "]"
    out += "def cMm : PGramMemo where\n  re := %s\n  im := %s\n  rad :=\n%s\n\n" % (rows("gMre"), rows("gMim"),
                                                                                  T.wrap(rads))
    names = []
    for i, e in enumerate(D["d2"]):
        out += memo_entry("td2_%d" % i, e)
        names.append("td2_%d" % i)
    out += "/-- The torsion boundary memo: `D²K` only (`DX_H ∘ K`, `DH ∘ K` come from the jet). -/\n"
    out += "def cTm : PTorsMemo where\n  d2 :=\n%s\n  ax := []\n  d1 := []\n\n" % T.wrap("[" + ", ".join(names) + "]")
    out += "/-- The Gram core's `(δ, β)` and the radius of `G⁻¹`. -/\n"
    out += "def cDb : LGF × LGF := (⟨%d⟩, ⟨%d⟩)\n\ndef cEps : LGF := ⟨%d⟩\n\n" % (D["db"][0], D["db"][1], D["eps"])
    out += R.lean_rbook("cRb", X["rb"]).replace("noncomputable def", "def") + "\n"
    return out


def ibook_text(ib):
    L = ib["Lb"]
    return ("/-- The invariance and energy book on the cfgFull box. -/\n"
            "def cIb : PIBook where\n  P := %d\n  Lb := %s\n  LU0 := %s\n  bJ := %s\n  bK := 2 ^ 136\n  bF := %s\n"
            "  q := %d\n  lK := %d\n  lI := %d\n\n") % (
                P, lay_lit(L.lo, L.dims, L.S, L.w), lay_lit((0, 0), (1, 1), L.S, L.w), T.pow2(ib["bJ"]),
                T.pow2(ib["bF"]), Q, ib["lK"], ib["lI"])


SHAPE = dict(N=(2 * n, n), DL=(2 * n, n), DG=(n, n), C=(n, n), DGi=(n, n), DN=(2 * n, n), XN=(2 * n, n))
NODES = ("N", "DL", "DG", "C", "DGi", "DN", "XN")


def nodes_text(X, radsub=None):
    memos = X["memos"]
    out = ""
    for nm in NODES:
        memo, mats = memos[nm]
        R_, Cc = SHAPE[nm]
        for i in range(R_):
            for j in range(Cc):
                re_, im_ = R.node_lists(memo[(i, j)])
                rad = mats[(i, j)][1] - (radsub or {}).get((nm, i, j), 0)
                nij = "r%s_%d_%d" % (nm, i, j)
                out += ("def %s_re : List (CertKey × ℤ) :=\n%s\n\ndef %s_im : List (CertKey × ℤ) :=\n%s\n\n"
                        "def %s : NodeEntry := (%s_re, %s_im, %s, %s)\n\n") % (
                            nij, T.wrap(T.tl(re_)), nij, T.wrap(T.tl(im_)), nij, nij, nij,
                            T.qlit(F(rad, 2 ** P)), T.qlit(F(mats[(i, j)][2], 2 ** P)))
    return out


def rmemo_text(X, name="cRm", ry=None):
    tab = lambda nm: "[" + ", ".join("[" + ", ".join("r%s_%d_%d" % (nm, i, j) for j in range(SHAPE[nm][1])) + "]"
                                     for i in range(SHAPE[nm][0])) + "]"
    out = "def %s : PRMemo where\n" % name
    for nm in NODES:
        out += "  %s :=\n%s\n" % (nm, T.wrap(tab(nm)))
    RY = ry if ry is not None else X["RY"]
    out += "  CT :=\n    [%s]\n" % ", ".join("[" + ", ".join(R.qpair(c) for c in row) + "]" for row in X["CT"])
    out += "  RT :=\n    [%s]\n" % ", ".join("[" + ", ".join(T.qlit(r) for r in row) + "]" for row in X["RT"])
    out += "  CY := [%s]\n" % ", ".join(R.qpair(c) for c in X["CY"])
    out += "  RY := [%s]\n\n" % ", ".join(T.qlit(r) for r in RY)
    return out


def jled_text(name, jl, nd, rplus=0):
    E = JG.Emit(_Ctx(jl["Lb"]))
    E.node(name + "_n", nd)
    body = "".join(E.defs)
    # the JNode literal `⟨u, A, e, x, ⟨r⟩, ⟨nb⟩⟩` becomes an α-free `JLed` with dyadic radius and norm bound
    m = re.search(r"def %s_n : JNode LGF :=\n  ⟨(.*), ⟨(-?\d+)⟩, ⟨(-?\d+)⟩⟩\n" % re.escape(name), body, re.S)
    head = body[:m.start()]
    lit = m.group(1)
    r, nb = int(m.group(2)) + rplus, int(m.group(3))
    return head + "def %s : JLed :=\n  ⟨%s, %s, %s⟩\n\n" % (name, lit, T.qlit(F(r, 2 ** P)), T.qlit(F(nb, 2 ** P)))


def jbook_text(name, jl):
    bk, L = jl["bk"], jl["Lb"]
    H = (L.dims[0] - 1) // 2
    Lw = JG.Lay((-2 * H, -2 * H), (4 * H + 1, 4 * H + 1), L.S, L.w)
    LU0 = JG.Lay((0, 0), (1, 1), L.S, L.w)
    return ("def %s : JBook where\n  Lb := %s\n  LU0 := %s\n  Lw := %s\n  q := %d\n  lb := %d\n  lr := %d\n"
            "  lrb := %d\n  ln := %d\n  aW := %d\n  aB := %d\n  smax := %d\n  ls := %d\n  lsb := %d\n  off := %d\n"
            "  P := %d\n  aC := %d\n  lc := %d\n  lrc := %d\n  lnc := %d\n\n"
            % (name, JG.lay_lit(L), JG.lay_lit(LU0), JG.lay_lit(Lw), Q, bk.lb, bk.lr, bk.lrb, bk.ln, bk.aW, bk.aB,
               bk.smax, bk.ls, bk.lsb, bk.off, bk.P, bk.aC, bk.lc, bk.lrc, bk.lnc))


def jet_text(tag, jx):
    out = jbook_text("jb%s" % tag, jx)
    if True:
        names = []
        for i in sorted(jx["nodes"]):
            nm = "n%s_%d" % (tag, i)
            out += jled_text(nm, jx, jx["nodes"][i])
            names.append("(slotK %d, %s)" % (i, nm))
        out += ("/-- The %s chain's wanted slots on one ledger (the chain itself, its blocks and order, is the "
                "jet check's). -/\ndef jd%s : JetData := ⟨jb%s,\n%s, [], []⟩\n\n") % (
                    tag, tag, tag, T.wrap("[" + ", ".join(names) + "]"))
    return out


# ---------------------------------------------------------------------------------------------- probes
PHEAD = """/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

%s

/-!
# V2-PACKED-CONS gate probe `%s` (generated; opt-in)

%s
-/

@[expose] public noncomputable section

namespace %s.TP.Cons.P.%s

open KAM KAM.Certificate KAM.CertificateSharp.Packed %s.TP %s.TP.Cons

"""


def probe(name, imports, doc, stmt, extra=""):
    txt = PHEAD % ("\n".join("public import %s" % i for i in imports), name, doc, PRE, name, PRE, PRE) + extra + \
        ("set_option profiler true\nset_option profiler.threshold 1\n\ntheorem probe :\n    %s := by\n"
         "  decide +kernel\n\nend %s.TP.Cons.P.%s\n") % (stmt, PRE, name)
    full = os.path.join(PKG, PRE, "TP", "Cons", "P", name + ".lean")
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "w") as f:
        f.write(txt)
    return "%s.TP.Cons.P.%s" % (PRE, name)


def main():
    assert LOW, "--low= (the cfgLow jet mirror cache; --full= adds the invariance and energy)"
    D = load()
    J = dict(v0=7731, d1=[7732, 7733, 7734, 7735], d2=[[7736 + 4 * a + b for b in range(4)] for a in range(4)])
    jet_src = open(os.path.join(APP, "Jet.lean")).read()
    assert "v0 := %d" % J["v0"] in jet_src and "d1 := [7732, 7733, 7734, 7735]" in jet_src
    # the Gram core
    gtext, _ = gram_book(D)
    db = T.gram_core(D["B"], n, P, Q, D["w"], D["gm"], D["Bpolys"], D["sigB_mu"])
    assert db is not None, "the packed Gram core fails"
    D["db"], D["eps"] = db, C.gramInvRadius(D["B"], db)
    assert D["eps"] is not None
    B = D["B"]
    errM = B.ofRatDown(D["err"])
    # the jet's wanted nodes and the torsion
    jl = jet_nodes(LOW, HL, J["d1"] + [x for row in J["d2"] for x in row])
    X = tors(D, jl, J)
    print("Gram (delta, beta)", float(F(db[0], 2 ** P)), float(F(db[1], 2 ** P)), "eps", float(F(D["eps"], 2 ** P)))
    print("torsion final (mirror)", X["info"])
    jf = IV = EN = ib = None
    if FULL:
        jf = jet_nodes(FULL, HF, [J["v0"]] + J["d1"])
        Kf = dk_full(D, jf)
        ib = i_book(D, jf, X["Fl"])
        IV = invariance(D, jf, J, Kf, X["Fl"])
        EN = energy(D, jf, J)
        print("invariance", [(float(F(v["norm"], 2 ** P)), float(F(v["rad"], 2 ** P))) for v in IV],
              "err", float(D["err"]), "pass", all(v["tot"] <= errM for v in IV))
        print("energy", float(EN["q"]), float(F(EN["r"], 2 ** P)), "pass", EN["tot"] <= errM)
        assert all(v["tot"] <= errM for v in IV) and EN["tot"] <= errM
    # the shared data
    base_imp = ["%s.TP.Data.Cert" % PRE, "%s.Jet" % PRE, "KAM.CertificateSharp.Packed.JetBase"]
    module("%s.TP.Cons.Base" % PRE, base_imp, "LG00 T′: the consumers' books and memos",
           "The Gram book and memo (B2), the torsion boundary memo (`D²K`), the Gram core's `(δ, β)` and `eps`, the "
           "torsion book on the jet's cfgLow box.",
           "open %s.TP\n\n" % PRE + base_text(D, X, gtext))
    module("%s.TP.Cons.Nodes" % PRE, ["%s.TP.Cons.Base" % PRE], "LG00 T′: the rounded torsion nodes",
           "The seven nodes of `TorsR.lean` (rounded to `2^128`, truncated to the box), with `DX_H ∘ K` from the jet, "
           "and the tables of the averages.", nodes_text(X) + rmemo_text(X))
    module("%s.TP.Cons.JetLow" % PRE, ["%s.TP.Cons.Base" % PRE], "LG00 T′: the cfgLow chain's wanted slots",
           "The cfgLow chain's torsion slots as α-free ledger nodes (`JLed`) of a `JetData` without blocks: the "
           "consumers read `jetSlots`.", jet_text("Low", jl))
    if FULL:
        module("%s.TP.Cons.JetFull" % PRE, ["%s.TP.Cons.Base" % PRE], "LG00 T′: the cfgFull chain's wanted slots",
               "The cfgFull chain's `v0` and `d1` slots as α-free ledger nodes (`JLed`) of a `JetData` without "
               "blocks, and the invariance and energy book on the cfgFull box.", jet_text("Full", jf) + ibook_text(ib))
    # the probes
    NI = ["%s.TP.Cons.Nodes" % PRE]
    JI = ["%s.TP.Cons.JetFull" % PRE]
    NJ = NI + ["%s.TP.Cons.JetLow" % PRE]
    W, cfg, gi = "lg00Cert.weight", "lg00Cert.cfgLow", "lg00Cert.gramInv"
    box, s = "lg00Cert.freqBox", "lg00Cert.params.s"
    sigB = "(lg00Cert.params.σB - lg00Cert.params.μ)"
    js = "(jetSlots (α := LGF) jdLow)"
    jsf = "(jetSlots (α := LGF) jdFull)"
    plan = []
    add = lambda nm, imp, doc, st, extra="": plan.append(dict(module=probe(nm, imp, doc, st, extra), group=nm))
    add("ConsData", NJ, "Data-only control: the imports of the torsion probes.", "True")
    # the Gram link (B2's check, a shared conjunct of the three consumers)
    for r in range(2 * n):
        for a in range(n):
            add("CGEntry_%d_%d" % (r, a), ["%s.TP.Cons.Base" % PRE],
                "Shared: one boundary entry of the packed Gram check (the landed DK model (%d, %d))." % (r, a),
                "pgEntryOk 2 lg00Cert.emb %s %s lg00Cert.piEnc cBk cMm %d %d = true" % (W, cfg, r, a))
    add("CGCore", ["%s.TP.Cons.Base" % PRE], "Shared: the core of the packed Gram check gives `(δ, β)`.",
        "(gramPackedCore 2 %s %s %s cBk cMm %s).map (fun p => (p.1.m, p.2.m)) =\n"
        "      some (cDb.1.m, cDb.2.m)" % (gi, W, cfg, sigB))
    add("CGEps", ["%s.TP.Cons.Base" % PRE], "Shared: the radius of `G⁻¹` from `(δ, β)`.",
        "(gramInvRadius cDb).map (fun e => e.m) = some cEps.m")
    # the torsion
    add("TJJet", NJ, "Torsion: the jet's cfgLow box and scale are the torsion's (the guard part of `jetLowOk`).",
        "(layoutEq jdLow.jb.Lb cRb.Lb && jdLow.jb.P == cRb.P) = true")
    for r in range(2 * n):
        for j in range(n):
            for l in range(n):
                add("TJD2_%d_%d_%d" % (r, j, l), ["%s.TP.Cons.Base" % PRE],
                    "Torsion: one D²K boundary entry (%d, %d, %d) against the memo (`ptD2All`)." % (r, j, l),
                    "ptD2Ok 2 lg00Cert.emb %s %s lg00Cert.piEnc cRb.toT cTm %d %d %d = true" % (W, cfg, r, j, l))
    add("TJLay", NI, "Torsion: the layout and load guards.", "(trLayOk 2 cRb && trNormOk 2 %s %s %s cRb) = true"
        % (W, box, s))
    add("TJPack", NI, "Torsion: the packing of the boundary on the box.",
        "ptPackOk 2 %s %s cRb.toT cMm cTm = true" % (gi, cfg))
    st = dict(N="trStN 2 %s %s %s cRb cMm cRm cEps" % (gi, W, cfg),
              DL="trStDL (α := LGF) 2 %s %s %s cRb cTm cRm" % (W, box, s),
              DG="trStDG (α := LGF) 2 %s cRb cMm cRm" % W,
              C="trStC 2 %s %s %s cRb cRm cEps" % (gi, W, cfg),
              DGi="trStDGi 2 %s %s %s cRb cRm cEps" % (gi, W, cfg))
    for nm in ("N", "DL", "DG", "C", "DGi"):
        add("TJSt" + nm, NI, "Torsion: the node %s against the exact product of its inputs." % nm, st[nm] + " = true")
    mats = dict(DN="trMDN 2 %s %s %s cRb cMm cRm cEps" % (gi, W, cfg),
                XN="trMXNJ 2 lg00Jet %s cRb cRm" % js)
    for nm in ("DN", "XN"):
        for i in range(2 * n):
            for j in range(n):
                add("TJSt%s_%d_%d" % (nm, i, j), NJ if nm == "XN" else NI,
                    "Torsion: one entry (%d, %d) of the node %s against the exact product of its inputs%s." % (
                        i, j, nm, " (`A` from the jet)" if nm == "XN" else ""),
                    "stageOk 2 %s cRb.q cRb.lW cRb.lR cRb.Lw cRb.Lb cRb.Lu cRb.bR (2 * cRb.P)\n"
                    "      cRb.P ((%s).x %d %d) ((%s).r %d %d)\n      (nodeAt cRm.%s %d %d) = true"
                    % (W, mats[nm], i, j, mats[nm], i, j, nm, i, j))
    add("TJT", NI, "Torsion: the averages of T against the tables.", "trTCheck (α := LGF) 2 cRb cRm = true")
    add("TJY", NJ, "Torsion: the averages of Y = DH N against the tables (`DH` from the jet).",
        "trYCheckJ 2 lg00Jet %s cRb cRm = true" % js)
    sigT = "(lg00Cert.params.σT - lg00Cert.params.μ)"
    add("TJFinal", NI, "Torsion: the landed averaged test on the tables.",
        "tabFinal 2 %s 128 (trCentre 2 %s %s cRm) (trRad 2 %s %s cRm) lg00Cert.torsInv\n      %s = true"
        % (cfg, box, s, box, s, sigT))
    # torsion controls: one ulp below the computed radius (the XN memo, the Y table), one ulp above (a jet radius)
    mx00 = X["memos"]["XN"][1][(0, 0)]
    xtab = "[" + ", ".join("[" + ", ".join("xXN00" if (i, j) == (0, 0) else "rXN_%d_%d" % (i, j)
                                           for j in range(n)) + "]" for i in range(2 * n)) + "]"
    add("TJCtlXNUlp", NJ,
        "Negative control: the memo radius of X_N (0, 0) one ulp (2^-128) below the computed one is rejected.",
        "stageOk 2 %s cRb.q cRb.lW cRb.lR cRb.Lw cRb.Lb cRb.Lu cRb.bR (2 * cRb.P)\n      cRb.P ((trMXNJ 2 lg00Jet "
        "%s cRb cRm).x 0 0) ((trMXNJ 2 lg00Jet %s cRb cRm).r 0 0)\n      (nodeAt xRm.XN 0 0) = false" % (W, js, js),
        "def xXN00 : NodeEntry := (rXN_0_0_re, rXN_0_0_im, %s, %s)\n\ndef xRm : PRMemo := { cRm with XN :=\n%s }\n\n"
        % (T.qlit(F(mx00[1] - 1, 2 ** P)), T.qlit(F(mx00[2], 2 ** P)), T.wrap(xtab)))
    ry = list(X["RY"])
    ry[0] = ry[0] - F(1, 2 ** P)
    add("TJCtlYUlp", NJ, "Negative control: the radius table of Y one ulp below the computed one is rejected.",
        "trYCheckJ 2 lg00Jet %s cRb yRm = false" % js,
        "def yRm : PRMemo := { cRm with RY := [%s] }\n\n" % ", ".join(T.qlit(r) for r in ry))
    slotA = J["d2"][swap(0)][0]
    nd = jl["nodes"][slotA]
    xst = ("stageOk 2 %s cRb.q cRb.lW cRb.lR cRb.Lw cRb.Lb cRb.Lu cRb.bR (2 * cRb.P)\n      cRb.P ((trMXNJ 2 lg00Jet "
           "(jetSlots (α := LGF) %%s) cRb cRm).x 0 0)\n      ((trMXNJ 2 lg00Jet (jetSlots (α := LGF) %%s) cRb cRm).r "
           "0 0) (nodeAt cRm.XN 0 0) = %%s" % W)
    ledx = lambda nm, jd: "def %s : JetData := ⟨jdLow.jb, (slotK %d, %s) :: jdLow.L, [], []⟩\n\n" % (jd, slotA, nm)
    add("TJObsJetUlp", NJ, "Observation (not a control): the jet's radius of slot %d (DX_H (0, 0)) one ulp above the "
        "ledger's still passes the X_N stage (0, 0): the outward rounding of `upMul` in the propagated radius absorbs "
        "it (the jet radius itself is certified by the jet check's export test)." % slotA,
        xst % ("jdLowX", "jdLowX", "true"), jled_text("xA", jl, nd, rplus=1) + ledx("xA", "jdLowX"))
    add("TJCtlJetRad", NJ, "Negative control: the jet's radius of slot %d (DX_H (0, 0)) 2^20 ulp above the ledger's is "
        "rejected by the X_N stage (0, 0)." % slotA,
        xst % ("jdLowR", "jdLowR", "false"), jled_text("xR", jl, nd, rplus=2 ** 20) + ledx("xR", "jdLowR"))
    parts = [JG.unpack(jl["Lb"], nd.x[t]) for t in range(2)]
    pt = max(range(2), key=lambda t: max([abs(v) for v in parts[t].values()] + [0]))
    kmax = max(parts[pt], key=lambda k: abs(parts[pt][k]))
    assert abs(parts[pt][kmax]) + 2 ** 20 < nd.A
    bump = 2 ** 20 << (jl["Lb"].w * jl["Lb"].slot(kmax))
    xv = (nd.x[0] + bump, nd.x[1]) if pt == 0 else (nd.x[0], nd.x[1] + bump)
    ndv = JG.Node(nd.u, nd.A, nd.e, xv, nd.r, nd.nb)
    add("TJCtlJetVal", NJ, "Negative control: the jet's value of slot %d (DX_H (0, 0)) with its largest coefficient "
        "(%s part, key %s) off by 2^20 (2^-108) is rejected by the X_N stage (0, 0)." % (
            slotA, ("real", "imaginary")[pt], list(kmax)),
        xst % ("jdLowV", "jdLowV", "false"), jled_text("xV", jl, ndv) + ledx("xV", "jdLowV"))
    # the frames' `sup |T|` on the jet's torsion (tight bound: the computed row sums; and one ulp below)
    bT = max(X["frameT"])
    wit = open(os.path.join(APP, TREE, "Final", "Wit.lean")).read()
    mT = re.search(r"\bbT := (\d+)(?: / (\d+))?\b", wit)
    claimT = F(int(mT.group(1)), int(mT.group(2) or 1))
    assert bT <= B.ofRatDown(claimT), "sup |T| above the claim"
    add("FRTJClaim", NI, "Frames: `sup |T| ≤ bT` on the jet's torsion at T′'s claim `bT` (`RefClaim.bT`).",
        "trFrameTOk (α := LGF) 2 %s cRb cRm %s = true" % (W, T.qlit(claimT)))
    add("FRTJ", NI, "Frames: `sup |T| ≤ bT` on the jet's torsion at the tight bound (the largest computed row sum).",
        "trFrameTOk (α := LGF) 2 %s cRb cRm %s = true" % (W, T.qlit(F(bT, 2 ** P))))
    add("FRTJCtl", NI, "Negative control: `sup |T|` one ulp below the tight bound is rejected.",
        "trFrameTOk (α := LGF) 2 %s cRb cRm %s = false" % (W, T.qlit(F(bT - 1, 2 ** P))))
    if FULL:
        add("ConsDataFull", JI, "Data-only control: the imports of the invariance and energy probes.", "True")
        # the invariance
        errs = "lg00Cert.params.err"
        add("IVJet", JI, "Invariance: the jet's cfgFull box and scale are the book's (the guard part of `jetFullOk`).",
            "(layoutEq jdFull.jb.Lb cIb.Lb && jdFull.jb.P == cIb.P) = true")
        add("IVGuard", JI, "Invariance: the layouts, norm guards, packing and frequency loads.",
            "ivGuard 2 %s %s %s cIb cMm = true" % (W, box, s))
        for a in range(2 * n):
            add("IVRow_%d" % a, JI, "Invariance: coordinate %d, one packed norm plus the radii at most `err`." % a,
                "ivRowOk 2 %s %s %s lg00Jet %s cIb cMm %s %d = true" % (W, box, s, jsf, errs, a))
        a0 = max(range(2 * n), key=lambda a: IV[a]["tot"])
        tight = T.qlit(F(IV[a0]["tot"], 2 ** P))
        add("IVTight", JI, "Control: coordinate %d at the tight bound (its computed norm plus radius) passes." % a0,
            "ivRowOk 2 %s %s %s lg00Jet %s cIb cMm %s %d = true" % (W, box, s, jsf, tight, a0))
        add("IVCtlUlp", JI, "Negative control: coordinate %d one ulp below the tight bound is rejected." % a0,
            "ivRowOk 2 %s %s %s lg00Jet %s cIb cMm %s %d = false" % (W, box, s, jsf, T.qlit(F(IV[a0]["tot"] - 1, 2 ** P)),
                                                                     a0))
        slotI = J["d1"][swap(a0)]
        add("IVCtlJetUlp", JI, "Negative control: the jet's radius of slot %d one ulp above the ledger's is rejected at "
            "the tight bound." % slotI,
            "ivRowOk 2 %s %s %s lg00Jet (jetSlots (α := LGF) jdFullX) cIb cMm %s %d = false" % (W, box, s, tight, a0),
            jled_text("xI", jf, jf["nodes"][slotI], rplus=1) +
            "def jdFullX : JetData := ⟨jdFull.jb, (slotK %d, xI) :: jdFull.L, [], []⟩\n\n" % slotI)
        # the energy
        add("ENGuard", JI, "Energy: the zero-key read-out guards.", "enGuard 2 cIb = true")
        add("ENOk", JI, "Energy: the zero mode of the v0 node plus its radius at most `err`.",
            "enOk 2 lg00Jet %s cIb lg00Cert.params.E0 %s = true" % (jsf, errs))
        tightE = T.qlit(F(EN["tot"], 2 ** P))
        add("ENTight", JI, "Control: the energy bound at its tight value passes.",
            "enOk 2 lg00Jet %s cIb lg00Cert.params.E0 %s = true" % (jsf, tightE))
        add("ENCtlUlp", JI, "Negative control: the energy bound one ulp below its tight value is rejected.",
            "enOk 2 lg00Jet %s cIb lg00Cert.params.E0 %s = false" % (jsf, T.qlit(F(EN["tot"] - 1, 2 ** P))))
        add("ENCtlJetUlp", JI, "Negative control: the jet's radius of v0 one ulp above the ledger's is rejected at the "
            "tight bound.",
            "enOk 2 lg00Jet (jetSlots (α := LGF) jdFullE) cIb lg00Cert.params.E0 %s = false" % tightE,
            jled_text("xE", jf, jf["nodes"][J["v0"]], rplus=1) +
            "def jdFullE : JetData := ⟨jdFull.jb, (slotK %d, xE) :: jdFull.L, [], []⟩\n\n" % J["v0"])
    meta = dict(
        source=dict(app=APP, tree=TREE, low=LOW, full=FULL, low_src=jl["source"], full_src=jf and jf["source"]),
        gram=dict(delta=float(F(db[0], 2 ** P)), beta=float(F(db[1], 2 ** P)), eps=float(F(D["eps"], 2 ** P))),
        torsion=dict(final=X["info"], width=X["rb"]["width"], aW_log2=X["rb"]["aW"].bit_length(),
                     node_terms={k: sum(len(v) for v in X["memos"][k][0].values()) for k in NODES},
                     T_radii=[[float(r) for r in row] for row in X["RT"]], Y_radii=[float(r) for r in X["RY"]],
                     jet_radii={str(i): float(F(nd_.r, 2 ** P)) for i, nd_ in sorted(jl["nodes"].items())},
                     frameT=[float(F(v, 2 ** P)) for v in X["frameT"]], frameT_claim=str(claimT)),
        data=["%s.TP.Cons.Base" % PRE, "%s.TP.Cons.Nodes" % PRE, "%s.TP.Cons.JetLow" % PRE] +
        (["%s.TP.Cons.JetFull" % PRE] if FULL else []),
        probes=plan)
    if FULL:
        meta["invariance"] = dict(err=float(D["err"]), rows=[dict(norm=float(F(v["norm"], 2 ** P)),
                                                                  rad=float(F(v["rad"], 2 ** P)),
                                                                  jet_r=float(F(v["jet_r"], 2 ** P))) for v in IV],
                                  width=jf["Lb"].w, lI=ib["lI"], margin=float(D["err"] - F(max(v["tot"] for v in IV),
                                                                                             2 ** P)))
        meta["energy"] = dict(z=[float(EN["z"][0]), float(EN["z"][1])], E0=float(D["E0"]), dev=float(EN["q"]),
                              r=float(F(EN["r"], 2 ** P)), err=float(D["err"]),
                              margin=float(D["err"] - F(EN["tot"], 2 ** P)))
    with open(os.path.join(PKG, "cons_plan.json"), "w") as f:
        json.dump(meta, f, indent=1)
    print(json.dumps({k: v for k, v in meta.items() if k != "probes"}, indent=1))
    print("probes", len(plan))


if __name__ == "__main__":
    main()
