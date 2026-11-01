#!/usr/bin/env python3
"""V2-TOOLS #6: the memoized stages of the Gram and torsion checks of a forced-toy certificate, computed by the
backend-generic mirror (scripts/spin_orbit/sofx_check.py) in exactly the order, keys and shapes of
`KAM.Certificate.torsionModels_eq_of_stages` and `gramCheck_eq_of_rows` (KAM/CertificateSharp/Kernel/Stage.lean),
and their Lean emission.  Untrusted tooling: each literal is re-proved by its own kernel run (`decide +kernel`
on a Boolean equality), so a mirror that drifted from the landed checker makes the build fail.  That makes every
stage literal a cross-language agreement test of the Python mirror against the Lean checker.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(1, os.path.join(HERE, "..", "..", "spin_orbit"))

import sofx_model as M              # noqa: E402
import sofx_check as C              # noqa: E402
import forced_emit as FE            # noqa: E402


def stages(c):
    """dict of the literal stages (mirror values) of certificate c (sofx Cert with CHECK books)."""
    B, n, W, pe, p = c.B, c.n, c.weight, c.piEnc, c.params
    cfg = c.cfgLow
    m = n + n
    G = C.gramModels(B, n, c.emb, W, cfg, pe, c.DKc)
    dRows = [M.sumUp(B, [C.gramDefectUp(B, W, i, j, C.gramBGModel(B, n, c.gramInv, G, W, cfg, pe, i, j))
                         for j in range(n)]) for i in range(n)]
    db = C.gramCheck(B, n, c.emb, c.gramInv, W, cfg, pe, p["sB"] - p["mu"], c.DKc)
    assert db is not None
    eps = C.gramInvRadius(B, db)
    ms = M.compose(B, n, c.jet["prog"], c.emb, c.wit, W, cfg, pe, C.torsionSlots(n, c.jet))
    assert eps is not None and ms is not None
    mul = lambda key, r, k, col, X, Y: C.modelMatMul(B, W, cfg, pe, key, r, k, col, X, Y)
    add = lambda r, col, X, Y: C.modelMatAdd(B, W, pe, r, col, X, Y)
    neg = lambda r, col, X: C.modelMatNeg(B, r, col, X)
    tr = lambda r, col, X: C.modelMatTranspose(B, r, col, X)
    om = lambda col, X: C.modelMatOmega(B, n, col, X)
    L = C.dkModels(B, n, c.DKc)
    Gi = C.buildMat(n, n, lambda k, j: M.Model(0, C.gramInvPoly(c.gramInv, k, j), eps))
    DL = C.dkwModels(B, n, c.emb, c.freqBox, p["s"], W, cfg, pe)
    N0 = mul((4, 0), m, n, n, L, Gi)
    DG1 = mul((4, 1), n, m, n, tr(m, n, DL), L)
    DG2 = mul((4, 2), n, m, n, tr(m, n, L), DL)
    DGi0 = mul((4, 3), n, n, n, Gi, add(n, n, DG1, DG2))
    DGi1 = mul((4, 4), n, n, n, DGi0, Gi)
    DN1 = mul((4, 5), m, n, n, DL, Gi)
    DN2 = mul((4, 6), m, n, n, L, neg(n, n, DGi1))
    XN1 = mul((4, 7), m, m, n, C.dxhModels(B, n, ms), om(n, N0))
    Tb = mul((4, 8), n, m, n, tr(m, n, om(n, N0)),
             om(n, add(m, n, XN1, neg(m, n, om(n, add(m, n, DN1, DN2))))))
    Y = mul((4, 9), 1, m, n, [[C.msGet(ms, a, B) for a in range(m)]], om(n, N0))
    T = C.torsionModels(B, n, c.jet, c.emb, c.wit, c.gramInv, db, c.freqBox, p["s"], W, cfg, pe, c.DKc)
    # self-check: the staged T equals the mirror's one-shot T
    for i in range(n):
        for j in range(n):
            assert same(C.entry(T, i, j, B), C.entry(Tb, i, j, B))
    return dict(G=G, dRows=dRows, db=db, eps=eps, ms=ms, L=L, Gi=Gi, DL=DL, N0=N0, DG1=DG1, DG2=DG2, DGi0=DGi0,
                DGi1=DGi1, DN1=DN1, DN2=DN2, XN1=XN1, Tb=Tb, Y=Y, T=T)


def same(a, b):
    return a.deg == b.deg and a.rad == b.rad and [(tuple(k), v) for k, v in a.poly] == [(tuple(k), v)
                                                                                     for k, v in b.poly]


# ---------------------------------------------------------------------------------------------- emission
def model_def(name, mdl, doc=None):
    terms = [FE.term(k, v) for k, v in mdl.poly]
    head = "def %s : CertModel FB :=\n" % name
    if not terms:
        body = "  ⟨%d, ⟨[]⟩, ⟨%d⟩⟩" % (mdl.deg, mdl.rad)
    else:
        body = FE.wrap("  ⟨%d, ⟨[" % mdl.deg, terms, indent="    ", close="]⟩,") + "\n    ⟨%d⟩⟩" % mdl.rad
    out = ("/-- %s -/\n" % doc if doc else "") + head + body + "\n"
    for ln in out.split("\n"):
        assert len(ln) <= FE.WIDTH, ln
    return out


def matrix_defs(name, Mx, doc):
    out = []
    names = []
    for i, row in enumerate(Mx):
        rn = []
        for j, mdl in enumerate(row):
            nm = "%s_%d_%d" % (name, i, j)
            out.append(model_def(nm, mdl))
            rn.append(nm)
        names.append(rn)
    rows = ["[%s]" % ", ".join(r) for r in names]
    out.append("/-- %s -/\ndef %s : ModelMatrix FB :=\n%s\n" % (doc, name, FE.wrap("  [", rows, indent="   ")))
    return "\n".join(out)


def models_def(name, ms, doc):
    out = []
    names = []
    for i, mdl in enumerate(ms):
        nm = "%s_%d" % (name, i)
        out.append(model_def(nm, mdl))
        names.append(nm)
    out.append("/-- %s -/\ndef %s : List (CertModel FB) :=\n%s\n" % (doc, name, FE.wrap("  [", names)))
    return "\n".join(out)


STAGE_DOCS = [
    ("G", "the Gram models `gramModels` (low stage)"), ("L", "`dkModels`"), ("Gi", "`gramInvModels B eps`"),
    ("DL", "`dkwModels`"), ("N0", "stage `[4, 0]`"), ("DG1", "stage `[4, 1]`"), ("DG2", "stage `[4, 2]`"),
    ("DGi0", "stage `[4, 3]`"), ("DGi1", "stage `[4, 4]`"), ("DN1", "stage `[4, 5]`"), ("DN2", "stage `[4, 6]`"),
    ("XN1", "stage `[4, 7]`"), ("Tb", "stage `[4, 8]`"), ("Y", "stage `[4, 9]`")]


def emit_stages(c, st, tag, datamod):
    out = [FE.HEADER, "public import %s\n" % datamod, "public import KAM.CertificateSharp.Kernel.SegDefs\n\n"]
    out.append("/-!\n# The memoized Gram and torsion stages of `%s.cert` (data)\n\n" % tag)
    out.append("Computed by `scripts/certifier/forced/forced_stages.py` (the mirror of the landed checker) in the\n"
               "order and with the keys of `torsionModels_eq_of_stages`; each literal is re-proved in\n"
               "`%sStagesCheck` by its own kernel run.\n-/\n\n" % tag)
    out.append("@[expose] public section\n\nnamespace KAM.CertificateSharp.V2.Forced\n\nopen KAM.Certificate\n\n")
    out.append("namespace %s\n\n" % tag)
    d, b = st["db"]
    out.append("/-- `δβ` of `gramCheck`. -/\ndef db : FB × FB := (⟨%d⟩, ⟨%d⟩)\n\n" % (d, b))
    out.append("/-- `gramInvRadius db`. -/\ndef eps : FB := ⟨%d⟩\n\n" % st["eps"])
    out.append("/-- The defect rows of `gramCheck`. -/\ndef dRows : List FB :=\n%s\n\n" % FE.wrap(
        "  [", ["⟨%d⟩" % x for x in st["dRows"]]))
    out.append(models_def("ms", st["ms"], "the composed torsion slots (low stage)") + "\n")
    for nm, doc in STAGE_DOCS:
        out.append(matrix_defs(nm, st[nm], doc) + "\n")
    out.append("end %s\n\nend KAM.CertificateSharp.V2.Forced\n\nend\n" % tag)
    return "".join(out)
