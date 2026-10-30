#!/usr/bin/env python3
"""SO-CSPLIT: structural and workload census of the heavy sub-checks (untrusted tooling; design evidence only).

Runs SO-DATA3's mirror (`sofx_*`, the N = 65 v2 sizing: CertFixed 96, L = 20, cut-offs 100000 / 160) on one torus
and records, for every operation that the segmented proof would place in some theorem:

* compose (cfgFull, the program of `checkInvariance`/`checkEnergy`; cfgLow, the program of `torsionModels`):
  per slot the op, its operands' term counts, the output's term count, backend-primitive counts (a proxy of kernel
  reduction work), packed-product shards;
* Gram (`gramModels` entries, `gramBGModel` entries) and torsion (`modelMatMul` stages [4,0]..[4,9]):
  per product the operand / output term counts and the backend-primitive counts;
* `checkEmbedding` as a whole (the calibration point: 28 s user, 3.2 GB in the kernel, SO-DATA3 kpass).

The backend-primitive count ("ops") counts every call of a `FixedB` method; packed products are counted
separately (shards, block-pair multiplications), since the mirror computes them with numpy.

Usage (read-only on the mirror; run with -B -I so nothing is written beside it):
  SO_MIRROR=<dir of sofx_*.py> python3 -B -I csplit_census.py lower OUT.json
"""
import json
import os
import sys
import time
from collections import Counter
from fractions import Fraction as F

MIRROR = os.environ.get("SO_MIRROR", "/root/code/KAM-inp-sodata3/scripts/spin_orbit")
D3 = "/mnt/HC_Volume_106379410/kam-data/so-data3"
os.environ.setdefault("OMP_NUM_THREADS", "1")
for k, v in dict(SO_N="65", SO_DATA_DIR=D3 + "/L20", SO_PREC="96", SO_PKG=D3 + "/pkgR2.json", SO_SHARP="1",
                 SO_BUDGET_FULL="20", SO_CUT_LOW="160", SO_DISP_COEF="420000").items():
    os.environ.setdefault(k, v)
sys.path.insert(0, MIRROR)

import sofx_arith as A  # noqa: E402
import sofx_model as M  # noqa: E402
import sofx_check as C  # noqa: E402
import sofx_lunar as L  # noqa: E402
import sofx_packed as PK  # noqa: E402
import sofx_gen as G  # noqa: E402
import sofx_lean as SL  # noqa: E402
import sodata3_v2checks as V2  # noqa: E402
import hashlib  # noqa: E402

CNT = Counter()


def _wrap(cls):
    for name in ("ofInt", "ofRatUp", "ofRatDown", "add", "neg", "mul", "abs", "addErr", "mulErr", "upAdd",
                 "upMul", "ble", "blt", "beq"):
        f = getattr(cls, name)

        def g(self, *a, _f=f, _n=name):
            CNT["ops"] += 1
            CNT[_n] += 1
            return _f(self, *a)
        setattr(cls, name, g)


_wrap(A.FixedB)

PACK = []          # packed products seen: (key, terms a, terms b, shards)
_orig_poly = M.polyProduct


def _polyProduct(B, W, cfg, key, a, b):
    out = _orig_poly(B, W, cfg, key, a, b)
    if not (M.isConst(a) or M.isConst(b)):
        # the memoized decoded product (L1c (b)): one `tm` row per output term, plus a 200-byte def header
        ob = 200 + (sum(len("  tm %s %s %s %s,\n" % (SL.num(t[0][0]), SL.num(t[0][1]), SL.num(t[1][0]),
                                                      SL.num(t[1][1]))) for t in out[0]) if out else 0)
        PACK.append((cfg.name, tuple(cfg.full_key(key)) if hasattr(cfg, "full_key") else tuple(key), len(a), len(b),
                     ob))
    return out


M.polyProduct = _polyProduct


def terms(m):
    return len(m.poly) if m is not None else 0


def row_bytes(m):
    """bytes of the term rows `  tm k0 k1 re im,` (sofx_lean's format)."""
    return sum(len("  tm %s %s %s %s,\n" % (SL.num(k[0]), SL.num(k[1]), SL.num(c[0]), SL.num(c[1])))
               for k, c in m.poly)


def def_text(name, m, norm=None):
    """the complete emitted definition of a ledger model (and its cached norm), as SO-CSEG-GEN would write it:
    `def <name> : CertModel SoBackendV2 := ⟨deg, ⟨[rows]⟩, ⟨rad⟩⟩` and `def <name>.norm : SoBackendV2 := ⟨norm⟩`."""
    rows = "".join("  tm %s %s %s %s,\n" % (SL.num(k[0]), SL.num(k[1]), SL.num(c[0]), SL.num(c[1]))
                   for k, c in m.poly)
    rows = rows[:-2] + "\n" if rows else ""
    t = "/-- ledger model %s (generated) -/\ndef %s : CertModel SoBackendV2 :=\n  ⟨%s, ⟨[\n%s  ]⟩, ⟨%s⟩⟩\n\n" % (
        name, name, SL.num(m.deg), rows, SL.num(m.rad))
    if norm is not None:
        t += "def %s.norm : SoBackendV2 := ⟨%s⟩\n\n" % (name, SL.num(norm))
    return t


def lit_bytes(m, norm=None, name="lowerFull.s000"):
    """complete emitted bytes (UTF-8) of the definition(s) of one model."""
    return len(def_text(name, m, norm).encode())


def mhash(m):
    return hashlib.sha256(repr((m.deg, m.poly, m.rad)).encode()).hexdigest()[:16]


def snap():
    return CNT["ops"], len(PACK)


def census_compose(B, c, cfg, wanted):
    """Instrumented copy of `M.compose`: one record per slot."""
    n, W, pe = c.n, c.weight, c.piEnc
    st = M.ComposeState()
    recs = []
    for i, op in enumerate(c.jetOps):
        o0, p0 = snap()
        t = op[0]
        ins = []
        if t in ("add", "mul"):
            ins = [terms(st.slot(B, W, op[1])[0]), terms(st.slot(B, W, op[2])[0])]
        elif t in ("exp", "inv"):
            ins = [terms(st.slot(B, W, op[1])[0])]
        t0 = time.time()
        if M.composeStep(B, n, c.emb, c.wit, W, cfg, pe, st, op) is None:
            raise SystemExit("compose failed at slot %d" % i)
        o1, p1 = snap()
        m = st.slots[-1][0]
        reads = [op[1], op[2]] if t in ("add", "mul") else ([op[1]] if t in ("exp", "inv") else [])
        recs.append(dict(slot=i, op=t, reads=reads, ins=ins, out=terms(m), deg=m.deg, ops=o1 - o0,
                         bytes=lit_bytes(m, st.slots[-1][1]), rowBytes=row_bytes(m), hash=mhash(m),
                         packed=[list(x[1:]) for x in PACK[p0:p1]], sec=round(time.time() - t0, 4)))
    return recs, [st.slots[j][0] for j in wanted], st


def main(which, out):
    eng = PK.PackedEngine({"cfgFull": G.BUDGET["cfgFull"], "cfgLow": G.BUDGET["cfgLow"]})
    adv = json.load(open(os.path.join(D3, "g2", "%s_advice.json" % which)))
    cert = json.load(open(os.path.join(D3, "g2", "%s_cert.json" % which)))
    cf, cl = G.make_cfgs(eng)
    c = L.build(which, F(cert["params"]["err"]) if "params" in cert else F(1, 10 ** 16), F(1), cf, cl,
                G.HALV, G.TAYLOR)
    B = c.B
    rep = dict(which=which, advice_keys={k: len(v) for k, v in adv.items()})
    # --- calibration: checkEmbedding
    o0 = CNT["ops"]
    t0 = time.time()
    ok = C.checkEmbedding(B, c, {})
    rep["embedding"] = dict(ok=ok, ops=CNT["ops"] - o0, sec=round(time.time() - t0, 2))
    # --- compose, cfgFull (invariance + energy)
    J = c.jet
    d1 = [M.getD(J["d1"], a) for a in range(4)]
    recs, msF, _ = census_compose(B, c, cf, d1 + [J["v0"]])
    rep["composeFull"] = recs
    # --- the tails after the composition: invariance rows, energy
    n, W, pe = c.n, c.weight, c.piEnc
    DKm = C.dkModels(B, n, c.DKc)
    rows = []
    for a in range(n + n):
        o0, p0 = snap()
        x = C.msGet(msF[:4], C.swapNat(n, a), B)
        lhs = x if a < n else M.negM(B, x)
        m = M.addMixed(B, W, pe, lhs, M.negM(B, C.dkFreqModel(B, n, DKm, c.freqBox, c.params["s"], W, cf, pe, a)))
        M.supBound(B, W, m)
        o1, p1 = snap()
        rows.append(dict(row=a, ops=o1 - o0, packed=p1 - p0))
    rep["invarianceRows"] = rows
    o0 = CNT["ops"]
    d = M.addMixed(B, W, pe, M.toDeg(B, W, pe, 0, msF[4]), M.constModel(B, n, -F(0), 0, 0))
    C.zeroModeBall(B, n, d)
    rep["energyTail"] = dict(ops=CNT["ops"] - o0)
    # --- compose, cfgLow (torsionSlots)
    recsL, _, _ = census_compose(B, c, cl, C.torsionSlots(2, J))
    rep["composeLow"] = recsL
    rep["wanted"] = dict(d1=d1, v0=J["v0"], torsion=C.torsionSlots(2, J))
    # --- Gram: entries and BG entries
    W, pe = c.weight, c.piEnc
    gram = []
    G_ = [[None] * 2 for _ in range(2)]
    for a in range(2):
        for b in range(2):
            if a > b:
                G_[a][b] = G_[b][a]
                continue
            o0, p0 = snap()
            m = C.gramEntryModel(B, 2, c.emb, W, cl, pe, a, b, c.DKc)
            o1, p1 = snap()
            G_[a][b] = m
            gram.append(dict(stage="gramEntry", idx=[a, b], out=terms(m), ops=o1 - o0, bytes=lit_bytes(m),
                             packed=[list(x[1:]) for x in PACK[p0:p1]]))
    for i in range(2):
        for j in range(2):
            o0, p0 = snap()
            m = C.gramBGModel(B, 2, c.gramInv, G_, W, cl, pe, i, j)
            o1, p1 = snap()
            gram.append(dict(stage="gramBG", idx=[i, j], out=terms(m), ops=o1 - o0, bytes=lit_bytes(m),
                             packed=[list(x[1:]) for x in PACK[p0:p1]]))
    rep["gram"] = gram
    p = c.params
    o0 = CNT["ops"]
    db = C.gramCheck(B, 2, c.emb, c.gramInv, W, cl, pe, p["sB"] - p["mu"], c.DKc)
    rep["gramCheckWhole"] = dict(ok=db is not None, ops=CNT["ops"] - o0)
    # --- torsion stages: instrument modelMatMul / modelMatAdd
    stages = []
    _mm, _ma = C.modelMatMul, C.modelMatAdd

    def mm(B_, W_, cfg_, pe_, key, r, m_, cc, X, Y):
        o0, p0 = snap()
        R = _mm(B_, W_, cfg_, pe_, key, r, m_, cc, X, Y)
        o1, p1 = snap()
        stages.append(dict(stage="mul", key=list(key), shape=[r, m_, cc], ops=o1 - o0,
                           inTerms=[[terms(x) for x in row] for row in X] + [[terms(x) for x in row] for row in Y],
                           out=[[terms(x) for x in row] for row in R], packed=len(PACK[p0:p1]),
                           packedBytes=sum(x[4] for x in PACK[p0:p1]),
                           bytes=sum(lit_bytes(x) for row in R for x in row)))
        return R

    def ma(B_, W_, pe_, r, cc, X, Y):
        o0 = CNT["ops"]
        R = _ma(B_, W_, pe_, r, cc, X, Y)
        stages.append(dict(stage="add", shape=[r, cc], ops=CNT["ops"] - o0,
                           out=[[terms(x) for x in row] for row in R],
                           bytes=sum(lit_bytes(x) for row in R for x in row)))
        return R
    C.modelMatMul, C.modelMatAdd = mm, ma
    o0 = CNT["ops"]
    T = C.torsionModels(B, 2, J, c.emb, c.wit, c.gramInv, db, c.freqBox, p["s"], W, cl, pe, c.DKc)
    rep["torsionWhole"] = dict(ok=T is not None, ops=CNT["ops"] - o0)
    rep["torsionStages"] = stages
    C.modelMatMul, C.modelMatAdd = _mm, _ma
    # --- frames: the corner bounds on literal rows (FrameL, FrameN/Nt, FrameT)
    o0 = CNT["ops"]
    fr = V2.frame_rows(B, c)
    rep["frameRowsBuildOps"] = CNT["ops"] - o0
    wlo = V2.wloOf(W, c.expOrder)
    fops = {}
    for k, v in fr.items():
        o0 = CNT["ops"]
        for ms in v:
            V2.rowCornerMax(B, W, wlo, n, ms)
        fops[k] = CNT["ops"] - o0
    rep["frameCornerOps"] = fops
    # --- stage literal bytes (Gram entries, torsion matrices): out term counts x measured bytes per term
    allb = [r["bytes"] for r in recs if r["out"]]
    allt = [r["out"] for r in recs if r["out"]]
    rep["bytesPerTerm"] = sum(allb) / max(1, sum(allt))
    rep["counter"] = dict(CNT)
    with open(out, "w") as fh:
        json.dump(rep, fh, default=str)
    print("done", which, out)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
