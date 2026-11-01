#!/usr/bin/env python3
"""V2-PACKED-GEN: the reader of an LG00-format certificate tree, and the packed Gram, torsion and frame data of the
certificate (untrusted tooling; the kernel re-checks everything).

`Cert(root)` reads a generated certificate tree:
  - `<root>/Data/{Cert, DCoeffs, E0, W8}.lean` (the certificate, its long rationals, the embedding, the Gram witness);
  - `<root>/Torsion/{D0, V*}.lean` (the 20 jet slot models `lg00TMs` read by the torsion: the landed `cfgLow`
    composition, proved by the tree's `Low` stage);
  - `<root>/Final/Wit.lean` (the route witness: the claimed frame bounds).
Trees: LG00's first certificate `KAM/LG00Cert` (branch `lg00-cert`) and the tori of the LG00 package
(`applications/lg00/LG00/TP`, `TPP`, branch `lg00-app`). Every number the packed stages need is read from the tree
(the parameters, the frequency box, the weight, the embedding's zero modes and degrees, the pi enclosure, `cfgLow`,
the claims), none is assumed. The legacy gate generators (`gram_gate_gen.py`, `tors_gate_gen.py`) hard-code the
first certificate's values; this reader replaces their `load()` and reuses their arithmetic unchanged.

  load(cert)    the inputs of the packed torsion chain (the dict of `tors_gate_gen.load()`, plus the reader's data);
  compute(cert) the rounded packed torsion chain, its book and tables (`torsr_gate_gen.compute()`, for any tree);
  frames(S)     the bit-exact mirror of the three packed frame tests (`frames_gate_gen.mirror`) and their verdicts.

Regression: `python3 -I scripts/packed/gen_cert.py --check-legacy` recomputes the first certificate's frame edges
and compares them with the receipts of V2-PACKED-FRAMES (`docs/campaign/studies/V2-PACKED-FRAMES-GATE/FramesGate.json`).
Usage: python3 -I scripts/packed/gen_cert.py [CERT_ROOT] [--check-legacy]
"""
import json
import os
import re
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
_argv, sys.argv = sys.argv, sys.argv[:1]      # the legacy modules read sys.argv at import
import tors_gate_gen as T      # noqa: E402
import torsr_gate_gen as R     # noqa: E402
import frames_gate_gen as FR   # noqa: E402
sys.argv = _argv
G, A, C, M, SP = T.G, T.A, T.C, T.M, T.SP

ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
P, Q, n = 128, 24, 2
LEGACY = "/home/scott/KAM-dev-worktrees/lg00-cert/KAM/LG00Cert"
TP = "/home/scott/KAM-dev-worktrees/lg00-app/applications/lg00/LG00/TP"


# ---------------------------------------------------------------------------------------------- Lean literals
def _arith(expr):
    expr = re.sub(r"\s+", "", expr).replace("^", "**")
    assert re.fullmatch(r"[0-9+\-*()]+", expr), expr
    return int(eval(expr, {"__builtins__": {}}))      # digits and + - * ( ) only


def lit_int(t):
    t = t.strip()
    m = re.fullmatch(r"\(?Int\.negSucc (\d+)\)?", t)
    return -int(m.group(1)) - 1 if m else int(t)


def flat(s):
    return re.sub(r"\s+", " ", s).strip()


class Cert:
    """A generated LG00-format certificate tree (read only)."""

    def __init__(self, root):
        self.root = os.path.abspath(root)
        self.data = os.path.join(self.root, "Data")
        self.tors = os.path.join(self.root, "Torsion")
        self.cert_path = os.path.join(self.data, "Cert.lean")
        self.dco_path = os.path.join(self.data, "DCoeffs.lean")
        self.cert_txt = open(self.cert_path, encoding="utf-8").read()
        dco = open(self.dco_path, encoding="utf-8").read()
        self.ns = re.search(r"^namespace (\S+)", self.cert_txt, re.M).group(1)
        # the long rationals `lgD<i>` and their Lean text
        self.lgD, self.lgD_text = {}, ""
        for m in re.finditer(r"^def (lgD\d+) : ℚ :=\n(.*?)(?=\n\n|\nend )", dco, re.M | re.S):
            body = flat(m.group(2))
            mm = re.fullmatch(r"\(\((.*) : ℤ\) : ℚ\) / \(\((.*) : ℕ\) : ℚ\)", body)
            assert mm, body[:80]
            self.lgD[m.group(1)] = F(_arith(mm.group(1)), _arith(mm.group(2)))
            self.lgD_text += m.group(0) + "\n\n"
        # the parameters
        ptxt = self.defn("lg00Params")
        self.params = {}
        for k, v in re.findall(r"^  (\S+) := (.*)$", ptxt, re.M):
            self.params[k] = self.rat(v)
        # the frequency box
        btxt = flat(self.defn("lg00Box").split(":=", 1)[1])
        items = re.findall(r"\(([^,()]+|\([^()]*\)), ([^,()]+|\([^()]*\))\)", btxt)
        self.box = [(self.rat(a), self.rat(b)) for a, b in items]
        # the certificate's fields: the weight, the configurations
        ctxt = self.defn("lg00Cert")
        wm = re.search(r"^  weight := ⟨(.*), (lgD\d+)⟩$", ctxt, re.M)
        self.rho_w, self.wname = self.rat(wm.group(1)), wm.group(2)
        self.w = self.lgD[self.wname]
        cl = self.defn(re.search(r"^  cfgLow := (\S+)$", ctxt, re.M).group(1))
        self.cfgLow = tuple(int(re.search(r"^  %s := (\d+)$" % k, cl, re.M).group(1))
                            for k in ("cutoff", "taylorN", "halvings"))
        # the embedding: degrees and zero modes
        etxt = flat(self.defn("lg00Emb"))
        deg = lambda k: [int(x) for x in re.search(r"%sDeg := \[([^\]]*)\]" % k, etxt).group(1).split(", ")]
        self.angleDeg, self.actionDeg = deg("angle"), deg("action")
        zs = lambda k: [lit_int(x) for x in re.findall(
            r"⟨⟨(\(?Int\.negSucc \d+\)?|-?\d+)⟩, lg00%s\d_0⟩" % k, etxt)]
        self.angleZero, self.actionZero = zs("Angle"), zs("Action")
        assert len(self.angleZero) == n and len(self.actionZero) == n, etxt[:200]
        # the pi enclosure
        pm = re.search(r"⟨⟨(\d+)⟩, ⟨(\d+)⟩, (\d+), (\d+)⟩", self.defn("lg00Pi"))
        self.pi = tuple(int(x) for x in pm.groups())

    def defn(self, name, path=None):
        return G.grab(path or self.cert_path, name)

    def rat(self, v):
        """A rational field: `(a / b : ℚ)`, `(-a / b : ℚ)`, an integer, or a long rational `lgD<i>`."""
        v = v.strip()
        if v in self.lgD:
            return self.lgD[v]
        m = re.fullmatch(r"\((-?\d+) / (\d+) : ℚ\)", v)
        if m:
            return F(int(m.group(1)), int(m.group(2)))
        m = re.fullmatch(r"-?\d+", v)
        if m:
            return F(int(v))
        raise ValueError("not a rational literal: %r" % v)

    def claims(self):
        """The claimed frame bounds `bL`, `bN`, `bNt`, `bT` of the route witness (`Final/Wit.lean`)."""
        txt = flat(open(os.path.join(self.root, "Final", "Wit.lean"), encoding="utf-8").read())
        out = {}
        for k in ("bL", "bN", "bNt", "bT"):
            m = re.search(r"\b%s := (\((\d+) / (\d+) : ℚ\)|(\d+))" % k, txt)
            out[k] = F(int(m.group(2)), int(m.group(3))) if m.group(2) else F(int(m.group(4)))
        return out

    def lean_weight(self):
        return "⟨%s, %s⟩" % (T.qlit(self.rho_w), self.wname)

    def lean_cfg(self):
        return "⟨%d, %d, %d, CertFixed.toMant lgP, []⟩" % self.cfgLow


# ---------------------------------------------------------------------------------------------- the inputs
def load(cert):
    """The inputs of the packed Gram and torsion stages (`tors_gate_gen.load()` with the tree's numbers)."""
    data, tors = cert.data, cert.tors
    comps = ["lg00Angle0_0", "lg00Angle1_0", "lg00Action0_0", "lg00Action1_0"]
    grams = ["lg00Gram00_0", "lg00Gram01_0", "lg00Gram10_0", "lg00Gram11_0"]
    texts = {nm: G.grab(os.path.join(data, "E0.lean"), nm) for nm in comps}
    texts.update({nm: G.grab(os.path.join(data, "W8.lean"), nm) for nm in grams})
    emb, ginv, pi = cert.defn("lg00Emb"), cert.defn("lg00GramInv"), cert.defn("lg00Pi")
    tinv, boxt = cert.defn("lg00TorsInv"), cert.defn("lg00Box")
    tms, tms_defs = [], ""
    d0 = os.path.join(tors, "D0.lean")
    for i in range(20):
        mdef = G.grab(d0, "lg00TMs_%d" % i)
        deg, lst, rad = re.search(r"⟨(\d+), ⟨(lg00TMs_\d+t_\d+)⟩, ⟨(\d+)⟩⟩", flat(mdef)).groups()
        ttext = T.grab_any(tors, r"V\d+\.lean", lst)
        tms.append(M.Model(int(deg), T.parse_cc_terms(ttext), int(rad)))
        tms_defs += ttext + "\n" + mdef + "\n"
    tms_defs += G.grab(d0, "lg00TMs") + "\n"
    box, s, w = cert.box, cert.params["s"], cert.w
    sigT_mu = cert.params["σT"] - cert.params["μ"]
    sigB_mu = cert.params["σB"] - cert.params["μ"]
    B = A.FixedB(P)

    def half(nm):
        return [(k, (re_, im_)) for k, (re_, im_) in T.parse_cc_terms(texts[nm])]
    K = M.Embedding(cert.angleDeg, [M.RealPoly(cert.angleZero[i], half(comps[i])) for i in range(n)],
                    cert.actionDeg, [M.RealPoly(cert.actionZero[i], half(comps[n + i])) for i in range(n)])
    Wm = M.Weight(cert.rho_w, w)
    pe = A.PiEnclosure(*cert.pi)

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
    X = C.dxhModels(B, n, tms)
    ax = [entry(M.toDeg(B, Wm, pe, 0, C.entry(X, a, b, B))) for a in range(2 * n) for b in range(2 * n)]
    d1 = [entry(M.toDeg(B, Wm, pe, 0, C.msGet(tms, a, B))) for a in range(2 * n)]
    mx = lambda es: max([1] + [abs(v) for e in es for _, v in e[0] + e[1]])
    kk = [(0, 0)]
    for nm in comps:
        for k, _ in T.parse_cc_terms(texts[nm]):
            kk += [k, (-k[0], -k[1])]
    L1 = G.box(kk)
    LB = G.box([k for nm in grams for k, _ in T.parse_cc_terms(texts[nm])] + [(0, 0)])
    LA = G.box([k for e in ax + d1 for k, _ in e[0] + e[1]] + [(0, 0)])
    assert all(L1[0][j] <= k[j] < L1[0][j] + L1[1][j] for e in d2 for k, _ in e[0] + e[1] for j in range(2))
    fc = [T.C_round(s * box[l][0] * 2 ** P) for l in range(n)]
    p2 = lambda x: 2 ** x.bit_length()
    bk = T.tors_book(n, P, Q, w, L1, LB, LA, 2 ** 136, 2 ** 132, p2(mx(d2)), p2(mx(ax + d1)),
                     p2(max(abs(v) for v in fc)))
    assert mx(gm.values()) <= 2 ** 136
    Bpolys = [[half(grams[0]), half(grams[1])], [half(grams[2]), half(grams[3])]]
    db = T.gram_core(B, n, P, Q, w, gm, Bpolys, sigB_mu)
    assert db is not None, "the packed Gram core fails"
    eps = C.gramInvRadius(B, db)
    assert eps is not None
    return dict(cert=cert, comps=comps, grams=grams, texts=texts, emb=emb, ginv=ginv, pi=pi, tinv=tinv, boxt=boxt,
                tms=tms, tms_defs=tms_defs, box=box, s=s, w=w, sigT_mu=sigT_mu, sigB_mu=sigB_mu, B=B, K=K, Wm=Wm,
                pe=pe, gm=gm, d2=d2, ax=ax, d1=d1, L1=L1, LB=LB, LA=LA, fc=fc, bk=bk, Bpolys=Bpolys, db=db, eps=eps,
                d4=cert.lgD_text, d1t="", d2t="")


def compute(cert, hb=25, quiet=False):
    """The rounded packed torsion chain of the tree (`torsr_gate_gen.compute()` on `load(cert)`)."""
    D = load(cert)
    w = D["w"]
    ctx = R.Ctx(w, Q, P)
    geo = R.Geo(hb, 4 * hb + 1)
    K, Bm, D2, Fl, Am, D1 = R.inputs(ctx, D, P)
    memos, Tm, Ym, _ = R.chain(ctx, geo, K, Bm, D2, Fl, Am, D1, n, P)
    mx = max(abs(x) for m in memos.values() for p in m[0].values() for v in p.values() for x in v)
    CT = [[R.centre(Tm[(i, j)][0], 2 * P) for j in range(n)] for i in range(n)]
    RT = [[F(Tm[(i, j)][1], 2 ** P) for j in range(n)] for i in range(n)]
    CY = [R.centre(Ym[(0, j)][0], 2 * P) for j in range(n)]
    RY = [F(Ym[(0, j)][1], 2 ** P) for j in range(n)]
    S = R.parse_cc_matrix(D["tinv"], n + 1)
    ok, info = R.final_mirror(ctx, D, CT, RT, CY, RY, S, D["sigT_mu"], P)
    if not quiet:
        print("node terms", {k: sum(len(v) for v in m[0].values()) for k, m in memos.items()},
              "max mantissa bits", mx.bit_length())
        print("final (mirror)", ok, info)
    assert ok, "the mirror of the final torsion test fails"
    bR = 2 ** max(1, mx.bit_length())
    bk = D["bk"]["b"]
    rb = R.r_book(P, Q, w, hb, dict(bK=2 ** 136, bB=2 ** 132, bD=bk["bD"], bA=bk["bA"], bF=bk["bF"], bR=bR))
    return dict(D=D, ctx=ctx, rb=rb, memos=memos, K=K, Tm=Tm, CT=CT, RT=RT, CY=CY, RY=RY, info=info)


def ham_jet(cert):
    """The jet's slot indices `v0`, `d1`, `d2` (`LG00/Jet.lean` of the certificate's package)."""
    path = os.path.join(os.path.dirname(cert.root), "Jet.lean")
    txt = flat(open(path, encoding="utf-8").read())
    v0 = int(re.search(r"v0 := (\d+)", txt).group(1))
    d1 = [int(x) for x in re.search(r"d1 := \[([\d, ]*)\]", txt).group(1).split(", ")]
    d2s = re.search(r"d2 := \[(\[[\d, ]*\](?:, \[[\d, ]*\])*)\]", txt).group(1)
    d2 = [[int(x) for x in row.split(", ")] for row in re.findall(r"\[([\d, ]*)\]", d2s)]
    return v0, d1, d2


def jet_nodes(cache, slots, hb):
    """The wanted nodes of a packed jet chain from kamx-packed's mirror cache (`jet_low_gen.py --mirror-only
    --cache`): slot -> (poly {key: (re, im)} at scale 2^P on the box, radius and norm-bound mantissas, load), and
    the chain's slot width."""
    import pickle
    import jet_gate_gen as JG
    ck = pickle.load(open(cache, "rb"))
    assert ck["H"] == hb, (ck["H"], hb)
    bk, S = ck["bk"], ck["S"]
    L = JG.Lay((-hb, -hb), (2 * hb + 1, 2 * hb + 1), 4 * hb + 1, bk.w)
    out = {}
    for j in slots:
        nd = S[j]
        assert not nd.u and nd.e == P, (j, nd.u, nd.e)
        out[j] = (R.join(JG.unpack(L, nd.x[0]), JG.unpack(L, nd.x[1])), nd.r, nd.nb, nd.A)
    return out, bk.w


def compute_j(cert, low_cache, hb=25, quiet=False):
    """The rounded packed torsion chain on the jet's torsion (`checkTorsionJ`, kamx-pk-cons): `DX_H ∘ K` and `DH ∘ K`
    are the jet's wanted nodes (`trAJ`, `trD1J`: the sign `-` on the rows `a ≥ n`), the book's `bA` is the jet's
    largest wanted load (`jetLowOk` reads `jetCheck … rb.bA`), its width at least the jet's (`layoutEq`)."""
    D = load(cert)
    w = D["w"]
    v0, d1, d2 = ham_jet(cert)
    swap = lambda a: a + n if a < n else a - n
    dxh = lambda a, b: d2[swap(a)][b]
    wanted = d1 + [x for row in d2 for x in row]
    nodes, wj = jet_nodes(low_cache, wanted, hb)
    ctx = R.Ctx(w, Q, P)
    geo = R.Geo(hb, 4 * hb + 1)
    K, Bm, D2, Fl, _, _ = R.inputs(ctx, D, P)
    Am = {}
    for a in range(2 * n):
        for b in range(2 * n):
            p, r, nb, _ = nodes[dxh(a, b)]
            Am[(a, b)] = (p if a < n else R.cscale(p, -1), r, nb)
    D1 = {(0, a): nodes[d1[a]][:3] for a in range(2 * n)}
    memos, Tm, Ym, _ = R.chain(ctx, geo, K, Bm, D2, Fl, Am, D1, n, P)
    mx = max(abs(x) for m in memos.values() for p in m[0].values() for v in p.values() for x in v)
    CT = [[R.centre(Tm[(i, j)][0], 2 * P) for j in range(n)] for i in range(n)]
    RT = [[F(Tm[(i, j)][1], 2 ** P) for j in range(n)] for i in range(n)]
    CY = [R.centre(Ym[(0, j)][0], 2 * P) for j in range(n)]
    RY = [F(Ym[(0, j)][1], 2 ** P) for j in range(n)]
    S = R.parse_cc_matrix(D["tinv"], n + 1)
    ok, info = R.final_mirror(ctx, D, CT, RT, CY, RY, S, D["sigT_mu"], P)
    if not quiet:
        print("J: node terms", {k: sum(len(v) for v in m[0].values()) for k, m in memos.items()},
              "max mantissa bits", mx.bit_length())
        print("J: final (mirror)", ok, info)
    assert ok, "the mirror of the final torsion test fails (jet's torsion)"
    bA = max(nodes[j][3] for j in wanted)
    bk = D["bk"]["b"]
    rb = R.r_book(P, Q, w, hb, dict(bK=2 ** 136, bB=2 ** 132, bD=bk["bD"], bA=bA, bF=bk["bF"],
                                     bR=2 ** max(1, mx.bit_length())))
    if rb["width"] < wj:
        rb["width"] = wj
    assert all(nodes[j][3] <= rb["b"]["bA"] for j in wanted)
    return dict(D=D, ctx=ctx, rb=rb, memos=memos, K=K, Tm=Tm, CT=CT, RT=RT, CY=CY, RY=RY, info=info,
                jet=dict(v0=v0, d1=d1, d2=d2, wanted=wanted, bA=bA, width=wj))


def inv_energy(S, full_cache, hb=48):
    """The mirror of the jet route's invariance and energy tests (kamx-pk-cons, `JetConsInv.lean`,
    `JetConsEnergy.lean`): per coordinate `a`, `ivRowOk` = the packed weighted norm of
    `X_a = (X_H ∘ K)_a 2^P - Σ_l DK_{al} fc_l` (scale `2^(2P)`; `X_H` from the Full chain's `d1` nodes, sign `-`
    on `a ≥ n`) plus `r_jet + Σ_l pmulRad(nb_K, r_K, |fc_l|/2^P, fr_l)` is at most `err`; `enOk` = the zero mode of
    the `v0` node minus `E0`, plus its radius, is at most `err`. Returns the values and verdicts."""
    D, ctx = S["D"], S["ctx"]
    B = ctx.B
    cert = D["cert"]
    v0, d1, _ = ham_jet(cert)
    nodes, _ = jet_nodes(full_cache, [v0] + d1, hb)
    box, s, K = D["box"], D["s"], S["K"]
    err, E0 = cert.params["err"], cert.params["E0"]
    fc = [T.C_round(s * box[l][0] * 2 ** P) for l in range(n)]
    fr = [abs(s) * box[l][1] + abs(s * box[l][0] - F(fc[l], 2 ** P)) for l in range(n)]
    swap = lambda a: a + n if a < n else a - n
    rows = []
    for a in range(2 * n):
        p, r, _, _ = nodes[d1[swap(a)]]
        x = R.cscale(p if a < n else R.cscale(p, -1), 2 ** P)
        for l in range(n):
            x = R.cadd(x, R.cscale(K[(a, l)][0], -fc[l]))
        rad = B.upAdd(r, M.sumUp(B, [ctx.pmulRad(K[(a, l)][2], K[(a, l)][1], B.ofRatUp(F(abs(fc[l]), 2 ** P)),
                                                 B.ofRatUp(fr[l])) for l in range(n)]))
        tot = B.upAdd(ctx.pnorm(x, 2 * P), rad)
        rows.append(dict(value=float(F(tot, 2 ** P)), ok=B.ble(tot, B.ofRatDown(err))))
    p0, r0, _, _ = nodes[v0]
    re0, im0 = p0.get((0, 0), (0, 0))
    ev = B.upAdd(B.ofRatUp(abs(F(re0, 2 ** P) - E0) + abs(F(im0, 2 ** P))), r0)
    return dict(err=float(err), rows=rows, energy=dict(value=float(F(ev, 2 ** P)), ok=B.ble(ev, B.ofRatDown(err))))


def frames(S):
    """The mirror of the three packed frame tests at the tree's claims: sums, verdicts, edges."""
    cert = S["D"]["cert"]
    cl = cert.claims()
    mv = FR.mirror(S)
    B = S["ctx"].B
    ok = dict(L=all(B.ble(x, B.ofRatDown(cl["bL"])) for x in mv["colL"]),
              N=all(B.ble(x, B.ofRatDown(cl["bN"])) for x in mv["rowN"]) and
              all(B.ble(x, B.ofRatDown(cl["bNt"])) for x in mv["colN"]),
              T=mv["guardT"] and all(B.ble(x, B.ofRatDown(cl["bT"])) for x in mv["rowT"]))
    val = lambda x: F(x, 2 ** P)
    edges = dict(L=val(max(mv["colL"])), N=val(max(mv["rowN"])), Nt=val(max(mv["colN"])), T=val(max(mv["rowT"])))
    return dict(claims=cl, mirror=mv, ok=ok, edges=edges)


def check_legacy():
    """The first certificate through this reader: the frame edges of V2-PACKED-FRAMES' receipts, bit for bit."""
    S = compute(Cert(LEGACY), quiet=True)
    fr = frames(S)
    ref = json.load(open(os.path.join(ROOT, "docs", "campaign", "studies", "V2-PACKED-FRAMES-GATE",
                                      "FramesGate.json")))
    got = {k: str(fr["edges"][k]) for k in ("L", "N", "T")}
    print("edges", got)
    assert got == ref["edges"], (got, ref["edges"])
    assert all(fr["ok"].values())
    print("LEGACY OK: the reader reproduces the first certificate's frame edges bit for bit")


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if "--check-legacy" in sys.argv:
        check_legacy()
        return
    cert = Cert(args[0] if args else TP)
    print("ns", cert.ns, "s", cert.params["s"], "weight", cert.rho_w, cert.wname, float(cert.w), "cfgLow", cert.cfgLow)
    print("box", [(float(a), float(b)) for a, b in cert.box], "zeros", cert.angleZero, cert.actionZero)
    S = compute(cert)
    fr = frames(S)
    print(json.dumps(dict(claims={k: str(v) for k, v in fr["claims"].items()}, ok=fr["ok"],
                          edges={k: float(v) for k, v in fr["edges"].items()}), indent=1))


if __name__ == "__main__":
    main()
