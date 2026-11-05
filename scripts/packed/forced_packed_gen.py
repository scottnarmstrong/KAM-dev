#!/usr/bin/env python3
"""V2-CONSOL: the packed route A refined on a whole forced-toy certificate (untrusted tooling; the kernel re-checks
everything).

    python3 -I scripts/packed/forced_packed_gen.py [TAG] [--out DIR] [--json FILE]

TAG is a forced toy of `scripts/certifier/forced/forced_build.py` (default `Micro`). The certificate is regenerated
with the forced producer (`forced_cert.generate`, deterministic) and asserted to emit exactly the landed
`KAM/CertificateSharp/V2/Tests/Forced/<TAG>Data.lean`, so the mirror objects are those of `<TAG>.cert`.

The packed boundary decodes mantissas exactly (`memoOk`, `pcOfPolyOk`: `CertPoly.toMants cfgLow.toMant P`), and the
forced toys carry the decoder `fun _ _ => none` (their landed checks never use it: every product advice is
`direct`). The packed certificate `<TAG>P.cert` is therefore `<TAG>.cert` with the production decoder
`CertFixed.toMant P` in `cfgLow` and nothing else changed; its landed sub-checks other than Gram and torsion do not
read `cfgLow`, so their landed proofs transfer by `rfl`.

Computed here, with the existing packed generators' functions (read-only: `torsr_gate_gen` (`Ctx`, `Geo`, `inputs`,
`chain`, `r_book`, `final_mirror`, `centre`), `tors_gate_gen` (`gram_core`, `wnorm`, `C_round`), `gram_gate_gen`
(`box`, `maxes`, `dense_len`, `mul_load`)) and the landed bit-exact mirror `scripts/spin_orbit/sofx_*.py`:
  - the packed Gram book and memo (`PGramBook`, `PGramMemo`: the landed `DK` models' mantissas and radii), the
    packed Gram core's `(δ, β)` and `eps = gramInvRadius (δ, β)`;
  - the rounded packed torsion book (`PRBook`: one box `Lb` of half-width the largest key of the boundary), the
    boundary memo (`PTorsMemo`: the landed `D²K`, `DX_H ∘ K`, `DH ∘ K` entries at degree 0) and the node memos and
    tables (`PRMemo`), with the mirror of the final test (`tabFinal`);
  - the packed frame sums (`trFrameLOk`, `trFrameNOk`, `trFrameTOk`), mirrored as in `frames_gate_gen.mirror`
    at the toy's scale `P`;
  - the refined claim R: the disc-pass sums (`sodata3_v2checks.ham_values`) and the packed frame sums, rounded up
    by a relative 10^-4 (as `forced_witness.refined_claim`), and a route-A-refined witness with classical sites
    (`siteOk … none`), X* the largest 3-digit value passing the exact mirror of `refinedCore` (`v2_r2.max_Xs`).
Writes `<TAG>PackedData.lean` (the data) into --out (default `KAM/CertificateSharp/V2/Tests/Forced/`) and the
numbers into --json (default `scripts/certifier/fixtures/forced-toy/<TAG>_packed.json`).
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
FORCED = os.path.join(ROOT, "scripts", "certifier", "forced")
sys.path.insert(0, HERE)
sys.path.insert(1, FORCED)
sys.path.insert(2, os.path.join(ROOT, "scripts", "spin_orbit"))
sys.path.insert(3, os.path.join(ROOT, "scripts", "apost_sharp"))
sys.setrecursionlimit(100000)

import torsr_gate_gen as R          # noqa: E402  (imports tors_gate_gen, gram_gate_gen, the sofx mirror)
import forced_build as FB           # noqa: E402
import forced_cert as FC            # noqa: E402
import forced_emit as FE            # noqa: E402
import forced_stages as FS          # noqa: E402
import forced_witness as FW         # noqa: E402
import sodata3_v2checks as V2C      # noqa: E402
import v2_q as V                    # noqa: E402
import v2_r2 as R2                  # noqa: E402

T, G, A, C, M, SP = R.T, R.G, R.A, R.C, R.M, R.SP
n = 2
Q = 24                              # norm precision of both books
LEAN_DIR = os.path.join(ROOT, "KAM", "CertificateSharp", "V2", "Tests", "Forced")
JSON_DIR = os.path.join(ROOT, "scripts", "certifier", "fixtures", "forced-toy")


# ---------------------------------------------------------------------------------------------- the certificate
def toy_cert(tag):
    """The forced producer's certificate `tag` (with its stages), asserted to be the landed `<tag>Data.lean`."""
    spec = dict(FB.SPECS[tag])
    spec["name"] = tag
    c = FC.generate(spec, log=lambda *a: None)
    assert c.report["passes_base"], c.report["checks"]
    c.stages = FS.stages(c)
    doc = ("The periodically forced toy `%s` of the V2-TOOLS regression suite,\n"
           "`H = c (J + β p²/2 + Σ ε_j cos 2π k_j·θ)`, reference vector `κ (ν₋(%d) - 1, 1)`, `κ = c/s`.\n"
           "Emitted by `scripts/certifier/forced/forced_build.py %s`; the producer's report is\n"
           "`scripts/certifier/fixtures/forced-toy/%s.json`.") % (tag, c.toy.N, tag, tag)
    txt = FE.emit_data(c, tag, "The forced toy `%s` (data)" % tag, doc)
    with open(os.path.join(LEAN_DIR, "%sData.lean" % tag), encoding="utf-8") as fh:
        assert fh.read() == txt, "the regenerated certificate differs from the landed %sData.lean" % tag
    return c


# ---------------------------------------------------------------------------------------------- the boundary
def boundary(c):
    """The memo entries of the packed boundary: the landed models through the bit-exact mirror."""
    B, K, Wm, pe, P = c.B, c.emb, c.weight, c.piEnc, c.B.P

    def entry(m):
        assert m.deg == 0
        mt = SP.toMants(B, P, m.poly)
        assert mt is not None
        return ([(tuple(k), v) for k, v in mt[0]], [(tuple(k), v) for k, v in mt[1]], F(m.rad, 2 ** P))
    gm = {}
    for r in range(2 * n):
        for a in range(n):
            gm[(r, a)] = entry(C.dkAngleModel(B, n, K, Wm, pe, r, a) if r < n
                               else C.dkActionModel(B, n, K, Wm, pe, r - n, a))
    tms = c.stages["ms"]
    d2 = [entry(C.d2kModel(B, n, K, Wm, pe, r, j, l)) for r in range(2 * n) for j in range(n) for l in range(n)]
    X = C.dxhModels(B, n, tms)
    ax = [entry(M.toDeg(B, Wm, pe, 0, C.entry(X, a, b, B))) for a in range(2 * n) for b in range(2 * n)]
    d1 = [entry(M.toDeg(B, Wm, pe, 0, C.msGet(tms, a, B))) for a in range(2 * n)]
    Bpolys = c.gramInv
    Bm = [[SP.toMants(B, P, C.gramInvPoly(Bpolys, i, k)) for k in range(n)] for i in range(n)]
    assert all(x is not None for row in Bm for x in row)
    return dict(gm=gm, d2=d2, ax=ax, d1=d1, Bpolys=Bpolys, Bm=Bm)


def maxm(es):
    return max([1] + [abs(v) for e in es for _, v in list(e[0]) + list(e[1])])


def p2(x):
    return 2 ** max(1, x.bit_length())


def gram_book(P, w, gm, Bm, bK, bB):
    """`PGramBook` (the formulas of `gram_gate_gen.main`): boxes of the memo's keys and of B's keys (with the zero
    key), one row stride (that of the window of `B G`), loads, norm exponents and the width from `normOk`."""
    kk = [(0, 0)] + [tuple(k) for e in gm.values() for k, _ in e[0] + e[1]]
    loK, dK = G.box(kk)
    kb = [(0, 0)] + [tuple(k) for row in Bm for mt in row for k, _ in mt[0] + mt[1]]
    loB, dB = G.box(kb)
    d2 = (2 * dK[0] - 1, 2 * dK[1] - 1)
    lo2 = (2 * loK[0], 2 * loK[1])
    d3 = (dB[0] + d2[0] - 1, dB[1] + d2[1] - 1)
    lo3 = (loB[0] + lo2[0], loB[1] + lo2[1])
    s0 = d3[1]
    st = (s0, 1)
    N1, NB, N2, N3 = (G.dense_len(dK, st), G.dense_len(dB, st), G.dense_len(d2, st), G.dense_len(d3, st))
    bG = 2 * n * G.mul_load(N1, N1, bK, bK)
    bE = n * G.mul_load(NB, N2, bB, bG)
    bD = 2 ** (3 * P) + bE
    lK, lB, lD = bK.bit_length(), bB.bit_length(), bD.bit_length()
    need = []
    for lo, dims, l in ((loK, dK, lK), (loB, dB, lB), (lo3, d3, lD)):
        r, cc = G.maxes(w, Q, lo, dims, s0)
        need.append(max(l + 2, (dims[0] * s0 * 2 ** l * r * cc).bit_length() + 1))
    return dict(P=P, L1=(loK, dK), LB=(loB, dB), s0=s0, width=max(need), bK=bK, bB=bB, q=Q, lK=lK, lB=lB, lD=lD)


# ---------------------------------------------------------------------------------------------- the frames
def frames_mirror(ctx, K, memos, Tm, rb, P):
    """`frames_gate_gen.mirror` at the scale `P`: the sums the kernel computes (backend mantissas at 2^P)."""
    B = ctx.B
    colL = [M.sumUp(B, [B.upAdd(K[(r, j)][2], K[(r, j)][1]) for r in range(2 * n)]) for j in range(n)]
    Nm = memos["N"][1]
    trN = {(r, j): (Nm[(n + r, j)] if r < n else Nm[(r - n, j)]) for r in range(2 * n) for j in range(n)}
    rowN = [M.sumUp(B, [B.upAdd(trN[(r, j)][2], trN[(r, j)][1]) for j in range(n)]) for r in range(2 * n)]
    colN = [M.sumUp(B, [B.upAdd(trN[(r, j)][2], trN[(r, j)][1]) for r in range(2 * n)]) for j in range(n)]
    rowT = [M.sumUp(B, [B.upAdd(ctx.pnorm(Tm[(i, j)][0], 2 * P), Tm[(i, j)][1]) for j in range(n)])
            for i in range(n)]
    return dict(colL=colL, rowN=rowN, colN=colN, rowT=rowT, guardT=rb["loads"]["aT"] <= rb["aW"])


# ---------------------------------------------------------------------------------------------- compute
def compute(tag):
    c = toy_cert(tag)
    B, P, w = c.B, c.B.P, c.weight.w
    p = c.params
    bd = boundary(c)
    gm, d2, ax, d1 = bd["gm"], bd["d2"], bd["ax"], bd["d1"]
    bK, bB = p2(maxm(gm.values())), p2(maxm([(mt[0], mt[1]) for row in bd["Bm"] for mt in row]))
    gb = gram_book(P, w, gm, bd["Bm"], bK, bB)
    sigB_mu, sigT_mu = p["sB"] - p["mu"], p["sT"] - p["mu"]
    db = T.gram_core(B, n, P, Q, w, gm, bd["Bpolys"], sigB_mu)
    assert db is not None, "the packed Gram core fails in the mirror"
    eps = C.gramInvRadius(B, db)
    assert eps is not None
    # the rounded packed torsion: one box containing every boundary key
    keys = [k for e in list(gm.values()) + d2 + ax + d1 for k, _ in e[0] + e[1]]
    keys += [k for row in bd["Bm"] for mt in row for k, _ in mt[0] + mt[1]]
    hb = max([1] + [abs(x) for k in keys for x in k])
    D = dict(gm=gm, d2=d2, ax=ax, d1=d1, eps=eps, box=c.freqBox, s=p["s"], Bpolys=bd["Bpolys"])
    ctx = R.Ctx(w, Q, P)
    geo = R.Geo(hb, 4 * hb + 1)
    K, Bmat, D2, Fl, Am, D1 = R.inputs(ctx, D, P)
    memos, Tm, Ym, _ = R.chain(ctx, geo, K, Bmat, D2, Fl, Am, D1, n, P)
    mx = max([1] + [abs(x) for m in memos.values() for pp in m[0].values() for v in pp.values() for x in v])
    CT = [[R.centre(Tm[(i, j)][0], 2 * P) for j in range(n)] for i in range(n)]
    RT = [[F(Tm[(i, j)][1], 2 ** P) for j in range(n)] for i in range(n)]
    CY = [R.centre(Ym[(0, j)][0], 2 * P) for j in range(n)]
    RY = [F(Ym[(0, j)][1], 2 ** P) for j in range(n)]
    S = c.torsInv
    ok, info = R.final_mirror(ctx, D, CT, RT, CY, RY, S, sigT_mu, P)
    assert ok, ("the mirror of the final test fails", info)
    fc = [T.C_round(p["s"] * c.freqBox[l][0] * 2 ** P) for l in range(n)]
    rb = R.r_book(P, Q, w, hb, dict(bK=bK, bB=bB, bD=p2(maxm(d2)), bA=p2(maxm(ax + d1)),
                                    bF=p2(max(abs(v) for v in fc)), bR=p2(mx)))
    # the packed frames and the claim
    fv = frames_mirror(ctx, K, memos, Tm, rb, P)
    assert fv["guardT"], "aT > aW"
    val = lambda x: F(x, 2 ** P)
    packed = dict(L=max(val(x) for x in fv["colL"]), N=max(val(x) for x in fv["rowN"]),
                  Nt=max(val(x) for x in fv["colN"]), T=max(val(x) for x in fv["rowT"]))
    hv = V2C.ham_values(c)
    Rc = dict(dh=FW.up_rel(hv["dh"]), dx=FW.up_rel(hv["dx"]), d2x=FW.up_rel(hv["d2x"]), d2h=FW.up_rel(hv["d2h"]),
              bL=FW.up_rel(packed["L"]), bN=FW.up_rel(packed["N"]), bNt=FW.up_rel(packed["Nt"]),
              bT=FW.up_rel(packed["T"]))
    assert V2C.checkHamClaim(c, Rc)
    assert all(B.ble(x, B.ofRatDown(Rc["bL"])) for x in fv["colL"])
    assert all(B.ble(x, B.ofRatDown(Rc["bN"])) for x in fv["rowN"])
    assert all(B.ble(x, B.ofRatDown(Rc["bNt"])) for x in fv["colN"])
    assert all(B.ble(x, B.ofRatDown(Rc["bT"])) for x in fv["rowT"])
    landed = V2C.frame_values(B, c)
    W = refined_A(c, Rc)
    return dict(c=c, P=P, gb=gb, gm=gm, d2=d2, ax=ax, d1=d1, db=db, eps=eps, hb=hb, rb=rb, memos=memos, CT=CT,
                RT=RT, CY=CY, RY=RY, final=info, fv=fv, packed=packed, landed=landed, R=Rc, W=W, ham=hv)


def refined_A(c, Rc, kp=3, th=F(1, 8), J=20):
    """`forced_witness.refined_A` with classical sites at every bite (`siteOk … none`) and the claim `Rc`."""
    p = dict(c.params)
    box = c.freqBox
    kappa = box[1][0]
    Q0 = V.Num(n=2, tau=1, rho=p["rho"], rhoInf=p["rhoInf"], kp=kp)
    sd = {}
    for s in range(kp):
        sd[("d", s)] = V.classical_c(2, 1, J, Q0.delta(s))
        sd[("b", s)] = V.classical_c(2, 1, J, Q0.b(s))
    Xs = R2.max_Xs("refined", p, box, kp, th, J, Rc, sd, lo=-30.0, hi=8.0, steps=40)
    ok, why, w = R2.okB_at("refined", p, box, kp, th, J, Xs, Rc, sd, detail=True)
    assert ok, why
    w = dict(w, R=Rc)
    full = V.refinedCore(2, p, box, w, detail=True)
    assert full[0], full
    return dict(core=w, R=Rc, kappa=kappa, sites=[(None, None)] * kp, Xs=Xs, mirror=full, kp=kp, th=th, J=J,
                estar=Xs * p["gamma"] ** 4 * Q0.d0 ** 4)


# ---------------------------------------------------------------------------------------------- emission
WIDTH = 100


def zi(x):
    return FE.z(x)


def qlit(x):
    x = F(x)
    return "(%d : ℚ)" % x.numerator if x.denominator == 1 else "(%d / %d : ℚ)" % (x.numerator, x.denominator)


def qsplit(x, ind):
    """A ℚ literal, split after `/` when it does not fit."""
    t = qlit(x)
    if len(ind) + len(t) + 2 <= WIDTH:
        return t
    x = F(x)
    return "(%d /\n%s  %d : ℚ)" % (x.numerator, ind, x.denominator)


def pz_list(ts):
    """The terms in their given order (a boundary memo must equal `toMants` term by term), which must be strictly
    ascending (`packRepOk`: strictly increasing slots)."""
    ks = [tuple(k) for k, _ in ts]
    assert all(a < b for a, b in zip(ks, ks[1:])), "memo keys not strictly ascending"
    return ["pz %s %s %s" % (zi(k[0]), zi(k[1]), zi(v)) for k, v in ts]


def wrap(head, items, indent="    ", close="]"):
    if not items:
        return head + close
    out = FE.wrap(head, items, indent=indent, close=close)
    for ln in out.split("\n"):
        assert len(ln) <= WIDTH, ln
    return out


def lay(L, s0, width):
    return "⟨[%d, %d], [%d, %d], [%d, 1], %d, 1⟩" % (L[0][0], L[0][1], L[1][0], L[1][1], s0, width)


def p2lit(x):
    return "2 ^ %d" % (x.bit_length() - 1) if x > 0 and x & (x - 1) == 0 else str(x)


def node_lists(poly):
    return (sorted((k, v[0]) for k, v in poly.items() if v[0]), sorted((k, v[1]) for k, v in poly.items() if v[1]))


SHAPE = dict(N=(2 * n, n), DL=(2 * n, n), DG=(n, n), C=(n, n), DGi=(n, n), DN=(2 * n, n), XN=(2 * n, n))
NODES = ("N", "DL", "DG", "C", "DGi", "DN", "XN")


def emit_data(tag, S):
    """The data module `<tag>PackedData.lean`."""
    P, gb, rb, W = S["P"], S["gb"], S["rb"], S["W"]
    out = [FE.HEADER, "public import KAM.CertificateSharp.V2.Tests.Forced.%sData\n" % tag,
           "public import KAM.CertificateSharp.Packed.Frames\n\n"]
    out.append(DOC % dict(T=tag, P=P, hb=S["hb"]))
    out.append("@[expose] public section\n\nnamespace KAM.CertificateSharp.V2.Forced.%sP\n\n" % tag)
    out.append("open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.Packed KAM.CertificateSharp.V2\n\n")
    out.append("/-- `%s.cert` with the production decoder `CertFixed.toMant %d` in `cfgLow`; nothing else\n"
               "changes. -/\ndef cert : TorusCertificate 2 FB :=\n"
               "  { %s.cert with cfgLow := { %s.cert.cfgLow with toMant := CertFixed.toMant %d } }\n\n"
               % (tag, P, tag, tag, P))
    out.append("/-- A memo term: the key `[k₀, k₁]` and a mantissa. -/\n"
               "def pz (k₀ k₁ v : ℤ) : CertKey × ℤ := ([k₀, k₁], v)\n\n")
    # the packed Gram book and memo
    s0, wd = gb["s0"], gb["width"]
    out.append("/-- The packed Gram book. -/\ndef bk : PGramBook where\n  P := %d\n  L1 := %s\n  LB := %s\n"
               "  bK := %s\n  bB := %s\n  q := %d\n  lK := %d\n  lB := %d\n  lD := %d\n\n" % (
                   P, lay(gb["L1"], s0, wd), lay(gb["LB"], s0, wd), p2lit(gb["bK"]), p2lit(gb["bB"]), gb["q"],
                   gb["lK"], gb["lB"], gb["lD"]))
    gm = S["gm"]
    for (r, a), e in sorted(gm.items()):
        out.append("/-- `DK` entry `(%d, %d)`, real part. -/\ndef gRe_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (
            r, a, r, a, wrap("  [", pz_list(e[0]))))
        out.append("/-- `DK` entry `(%d, %d)`, imaginary part. -/\ndef gIm_%d_%d : List (CertKey × ℤ) :=\n%s\n\n" % (
            r, a, r, a, wrap("  [", pz_list(e[1]))))
    rows = lambda pf: ["[%s]" % ", ".join("%s_%d_%d" % (pf, r, a) for a in range(n)) for r in range(2 * n)]
    rads = ["[%s]" % ", ".join(qlit(gm[(r, a)][2]) for a in range(n)) for r in range(2 * n)]
    out.append("/-- The packed Gram memo. -/\ndef mm : PGramMemo where\n  re :=\n%s\n  im :=\n%s\n  rad :=\n%s\n\n" % (
        wrap("    [", rows("gRe")), wrap("    [", rows("gIm")), wrap("    [", rads)))
    d, b = S["db"]
    out.append("/-- `(δ, β)` of the packed Gram core. -/\ndef db : FB × FB := (⟨%d⟩, ⟨%d⟩)\n\n" % (d, b))
    out.append("/-- `gramInvRadius db`. -/\ndef eps : FB := ⟨%d⟩\n\n" % S["eps"])
    # the rounded packed torsion book
    s0, wd = rb["s0"], rb["width"]
    out.append("/-- The book of the rounded packed torsion stage (box half-width %d). -/\n"
               "def rb : PRBook where\n  P := %d\n  Lb := %s\n  Lu := %s\n  LU0 := %s\n" % (
                   S["hb"], rb["P"], lay(rb["Lb"], s0, wd), lay(rb["Lu"], s0, wd), lay(rb["LU0"], s0, wd)))
    for k in ("bK", "bB", "bD", "bA", "bF", "bR"):
        out.append("  %s := %s\n" % (k, p2lit(rb["b"][k])))
    out.append("  aW := %d\n  aL := %d\n  q := %d\n" % (rb["aW"], rb["aL"], rb["q"]))
    for k in ("lK", "lB", "lD", "lA", "lR", "lW", "lL"):
        out.append("  %s := %d\n" % (k, rb["ls"][k]))
    out.append("\n")
    # the boundary memo
    names = {}
    for kind, es, doc in (("d2", S["d2"], "The landed `D²K` entry at index %d (`(r n + j) n + l`)."),
                          ("ax", S["ax"], "The landed `DX_H ∘ K` entry at index %d (`a (2n) + b`), degree 0."),
                          ("d1", S["d1"], "The landed `DH ∘ K` entry %d, degree 0.")):
        names[kind] = []
        for i, e in enumerate(es):
            nm = "t%s_%d" % (kind, i)
            out.append("/-- %s -/\ndef %s : MemoEntry :=\n%s,\n%s,\n    %s)\n\n" % (
                doc % i, nm, wrap("  ([", pz_list(e[0])), wrap("    [", pz_list(e[1])), qsplit(e[2], "    ")))
            names[kind].append(nm)
    out.append("/-- The boundary memo of the torsion. -/\ndef tm : PTorsMemo where\n")
    for kind in ("d2", "ax", "d1"):
        out.append("  %s :=\n%s\n" % (kind, wrap("    [", names[kind])))
    out.append("\n")
    # the nodes and the tables
    for nm in NODES:
        memo, mats = S["memos"][nm]
        R_, C_ = SHAPE[nm]
        for i in range(R_):
            for j in range(C_):
                re_, im_ = node_lists(memo[(i, j)])
                out.append("/-- Node `%s`, entry `(%d, %d)`. -/\ndef n%s_%d_%d : NodeEntry :=\n"
                           "%s,\n%s,\n    %s,\n    %s)\n\n"
                           % (nm, i, j, nm, i, j, wrap("  ([", pz_list(re_)), wrap("    [", pz_list(im_)),
                              qsplit(F(mats[(i, j)][1], 2 ** P), "    "),
                              qsplit(F(mats[(i, j)][2], 2 ** P), "    ")))
    for i in range(n):
        for j in range(n):
            out.append("/-- Table: the centre of the average of `T (%d, %d)`. -/\ndef cT_%d_%d : ℚ × ℚ :=\n"
                       "  (%s,\n   %s)\n\n" % (i, j, i, j, qsplit(S["CT"][i][j][0], "   "),
                                             qsplit(S["CT"][i][j][1], "   ")))
            out.append("/-- Table: the radius of the average of `T (%d, %d)`. -/\ndef rT_%d_%d : ℚ :=\n  %s\n\n"
                       % (i, j, i, j, qsplit(S["RT"][i][j], "  ")))
    for j in range(n):
        out.append("/-- Table: the centre of the average of `Y %d`. -/\ndef cY_%d : ℚ × ℚ :=\n  (%s,\n   %s)\n\n"
                   % (j, j, qsplit(S["CY"][j][0], "   "), qsplit(S["CY"][j][1], "   ")))
        out.append("/-- Table: the radius of the average of `Y %d`. -/\ndef rY_%d : ℚ :=\n  %s\n\n"
                   % (j, j, qsplit(S["RY"][j], "  ")))
    out.append("/-- The node memos and the tables of the averages. -/\ndef rm : PRMemo where\n")
    for nm in NODES:
        R_, C_ = SHAPE[nm]
        rws = ["[%s]" % ", ".join("n%s_%d_%d" % (nm, i, j) for j in range(C_)) for i in range(R_)]
        out.append("  %s :=\n%s\n" % (nm, wrap("    [", rws)))
    out.append("  CT := [%s]\n" % ", ".join("[%s]" % ", ".join("cT_%d_%d" % (i, j) for j in range(n))
                                            for i in range(n)))
    out.append("  RT := [%s]\n" % ", ".join("[%s]" % ", ".join("rT_%d_%d" % (i, j) for j in range(n))
                                            for i in range(n)))
    out.append("  CY := [%s]\n" % ", ".join("cY_%d" % j for j in range(n)))
    out.append("  RY := [%s]\n\n" % ", ".join("rY_%d" % j for j in range(n)))
    # the witness
    w, Rc = W["core"], W["R"]
    out.append("/-- The route-A-refined witness: the claim `R` (disc pass, packed frame sums), classical sites. -/\n"
               "def wit : RefinedWit where\n  core :=\n")
    core = ["Xs := %s" % qlit(w["Xs"]), "kp := %d" % w["kp"], "th := %s" % qlit(w["th"])]
    core += ["c := [%s]" % ", ".join(qlit(x) for x in w["c"]), "cbar := [%s]" % ", ".join(qlit(x) for x in w["cbar"])]
    core += ["%s := %s" % (k, qlit(w[k])) for k in ("ctail", "sB", "sT", "sLt", "sN", "sNt", "t")]
    core += ["J := %d" % w["J"]]
    out.append(wrap("    { ", core, indent="      ", close=" }") + "\n")
    out.append("  R :=\n" + wrap("    { ", ["%s := %s" % (k, qlit(Rc[k])) for k in
                                          ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt", "bT")],
                                   indent="      ", close=" }") + "\n")
    out.append("  κ := %s\n  sites := [%s]\n\n" % (qlit(W["kappa"]), ", ".join(["(none, none)"] * W["kp"])))
    # the controls
    g00 = sorted(gm[(0, 0)][0])
    mut = [(g00[0][0], g00[0][1] + 1)] + g00[1:]
    out.append("/-- Control data: the real part of `DK (0, 0)` with its first mantissa plus one. -/\n"
               "def gRe_0_0_mut : List (CertKey × ℤ) :=\n%s\n\n" % wrap("  [", pz_list(mut)))
    mrows = ["[%s]" % ", ".join(("gRe_0_0_mut" if (r, a) == (0, 0) else "gRe_%d_%d" % (r, a)) for a in range(n))
             for r in range(2 * n)]
    out.append("/-- Control data: the Gram memo with `gRe_0_0_mut`. -/\ndef mmMut : PGramMemo :=\n"
               "  { mm with re :=\n%s }\n\n" % wrap("    [", mrows))
    mT = max(S["fv"]["rowT"])
    out.append("/-- Control data: the largest packed row sum of `T` (the edge of `trFrameTOk`). -/\n"
               "def edgeT : ℚ := %s\n\n" % qlit(F(mT, 2 ** P)))
    out.append("end KAM.CertificateSharp.V2.Forced.%sP\n\nend\n" % tag)
    txt = "".join(out)
    for ln in txt.split("\n"):
        assert len(ln) <= WIDTH, ln
    return txt


DOC = """/-!
# The packed books and memos of the forced toy `%(T)s` (data)

`%(T)sP.cert` is `%(T)s.cert` with the production mantissa decoder `CertFixed.toMant %(P)d` in
`cfgLow`. The packed boundary decodes mantissas exactly (`memoOk`, `pcOfPolyOk`); the producer of
the forced toys emits the decoder `fun _ _ => none`, which no landed check of `%(T)s` reads (every
product advice is `direct`; of the landed base, only `checkGram` and `checkTorsion` read `cfgLow`
at all). Nothing else changes.

The untrusted data of the packed route A refined (`KAM/CertificateSharp/Packed/`), computed by
`scripts/packed/forced_packed_gen.py %(T)s` with the bit-exact mirror of the landed checker; every
entry is re-checked by the kernel (`%(T)sPacked*`):
* `bk`, `mm`: the packed Gram book and memo (the landed `DK` models' mantissas at `2^-%(P)d` and
  radii); `db`, `eps`: the packed Gram core's `(δ, β)` and `gramInvRadius (δ, β)`;
* `rb`: the book of the rounded packed torsion stage (one box of half-width %(hb)d and its window);
  `tm`: the boundary memo (the landed `D²K`, `DX_H ∘ K`, `DH ∘ K` entries at degree 0); `rm`: the
  node memos (`N`, `D L`, `DG`, `C`, `D(G⁻¹)`, `DN`, `X_N`) and the tables of the averages;
* `wit`: a route-A-refined witness, its claim `R` from the disc pass and the packed frame sums
  (rounded up by a relative `10⁻⁴`), classical sites;
* control data: `mmMut` (one mantissa of `DK (0, 0)` plus one) and `edgeT` (the largest packed row
  sum of `T`).
-/

"""


def summary(S):
    return dict(hb=S["hb"], gram_book={k: str(v) for k, v in S["gb"].items()},
                torsion_book=dict(s0=S["rb"]["s0"], width=S["rb"]["width"], aW_log2=S["rb"]["aW"].bit_length(),
                                  loads_log2={k: v.bit_length() for k, v in S["rb"]["loads"].items()},
                                  l=S["rb"]["ls"]),
                db=[str(F(x, 2 ** S["P"])) for x in S["db"]], eps=str(F(S["eps"], 2 ** S["P"])),
                boundary_terms=dict(gm=sum(len(e[0]) + len(e[1]) for e in S["gm"].values()),
                                    d2=sum(len(e[0]) + len(e[1]) for e in S["d2"]),
                                    ax=sum(len(e[0]) + len(e[1]) for e in S["ax"]),
                                    d1=sum(len(e[0]) + len(e[1]) for e in S["d1"])),
                node_terms={k: sum(len(v) for v in m[0].values()) for k, m in S["memos"].items()},
                final=S["final"], packed_frames={k: str(v) for k, v in S["packed"].items()},
                landed_frames={k: [float(x) for x in v] for k, v in S["landed"].items()},
                ham={k: str(v) for k, v in S["ham"].items()},
                R={k: str(v) for k, v in S["R"].items()}, Xs=str(S["W"]["Xs"]), estar=float(S["W"]["estar"]),
                core={k: (str(v) if not isinstance(v, list) else [str(x) for x in v])
                      for k, v in S["W"]["core"].items() if k != "R"},
                edgeT=str(F(max(S["fv"]["rowT"]), 2 ** S["P"])))


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    opt = lambda k, d: next((sys.argv[i + 1] for i, a in enumerate(sys.argv[:-1]) if a == k), d)
    tag = args[0] if args else "Micro"
    S = compute(tag)
    out = opt("--out", LEAN_DIR)
    js = opt("--json", os.path.join(JSON_DIR, "%s_packed.json" % tag))
    with open(os.path.join(out, "%sPackedData.lean" % tag), "w", encoding="utf-8") as fh:
        fh.write(emit_data(tag, S))
    info = summary(S)
    with open(js, "w") as fh:
        json.dump(info, fh, indent=1, sort_keys=True)
    print(json.dumps(dict(hb=info["hb"], node_terms=info["node_terms"], final=info["final"], R=info["R"],
                          Xs=info["Xs"], estar=info["estar"]), indent=1))
