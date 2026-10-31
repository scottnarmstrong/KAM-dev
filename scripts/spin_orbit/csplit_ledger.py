#!/usr/bin/env python3
"""SO-CSEG-GEN: the ledger of the segmented proof, from SO-DATA3's bit-exact mirror (untrusted tooling).

    python3 -B csplit_ledger.py lower|upper GENDIR PLAN.json OUT.pkl

For the certificate of GENDIR (sofx_gen output) and the plan of `csplit_plan.py`:

* the two composition chains (cfgFull, wanted `d1 ++ [v0]`; cfgLow, wanted `torsionSlots`), run whole: every slot
  pair `(model, supNormUp)` and the meta `(len, nExp, nInv, cache)` at every boundary of the plan;
* **self-check**: every segment re-run by the shadow fold of `SegDefs.lean` (`shadowStep`: the landed step on live or
  fallible ops, a zero placeholder otherwise) from its seed (ledger pairs at the imports, the zero entry elsewhere,
  the boundary meta); its output meta and every export must equal the whole run's, bit for bit;
* the Gram stage literals (`gramEntryModel` a <= b, `gramBGModel`, the defect rows, `(δ, β)`, `eps`) and the torsion
  stage literals (`dkModels` .. `[4,9]`, the torsion slots, `T`), each as `gramCheck`/`torsionModels` compute them;
* the packed-product memos: every packed product of the chains and the stages, with its operands, the advice key,
  the four parts (empty or not), each part's decoded terms and remainder, and the product's `(terms, err)`.

The pickle holds backend numbers as the mantissa integers of `CertFixed 96`.
"""
import os
import pickle
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)
D3 = "/mnt/HC_Volume_106379410/kam-data/so-data3"
for k, v in dict(OMP_NUM_THREADS="1", SO_N="65", SO_DATA_DIR=D3 + "/L20", SO_PREC="96", SO_PKG=D3 + "/pkgR2.json",
                 SO_SHARP="1", SO_BUDGET_FULL="20", SO_CUT_LOW="160").items():
    os.environ.setdefault(k, v)

import json  # noqa: E402
import sofx_model as M  # noqa: E402
import sofx_check as C  # noqa: E402
import sofx_packed as PK  # noqa: E402
import sodata3_witness as SW  # noqa: E402
import sofx_arith as A  # noqa: E402

FALLIBLE = ("char", "exp", "inv", "sqrt")
MEMOS = []          # packed-product memos, in evaluation order
CTX = ["?"]         # the context label of the products being evaluated ("dup": a recomputation, not recorded)
KEY = [None]        # (cfg name, full key) of the product being evaluated


def _wrap_engine():
    orig_pp = M.polyProduct

    def pp(B, W, cfg, key, a, b):
        KEY[0] = (cfg.name, tuple(cfg.full_key(key)), tuple(key))
        return orig_pp(B, W, cfg, key, a, b)
    M.polyProduct = pp
    orig = PK.PackedEngine.mulPacked

    def mp(self, B, W, padv, a, b):
        out = orig(self, B, W, padv, a, b)
        _, P, rr, ii, ri, ir = padv
        ma, mb = PK.toMants(B, P, a), PK.toMants(B, P, b)
        parts = []
        for nm, adv, x, y in (("rr", rr, ma[0], mb[0]), ("ii", ii, ma[1], mb[1]), ("ri", ri, ma[0], mb[1]),
                              ("ir", ir, ma[1], mb[0])):
            parts.append(dict(part=nm, empty=not (x and y), x=len(x), y=len(y)))
        if CTX[0] == "dup":
            return out
        MEMOS.append(dict(ctx=CTX[0], cfg=KEY[0][0], fullKey=KEY[0][1], key=KEY[0][2], P=P, a=list(a), b=list(b), parts=parts,
                          out=None if out is None else (list(out[0]), out[1])))
        return out
    PK.PackedEngine.mulPacked = mp


def wanted_of(c):
    J = c.jet
    d1 = [M.getD(J["d1"], a) for a in range(2 * c.n)]
    return dict(cfgFull=d1 + [J["v0"]], cfgLow=C.torsionSlots(c.n, J))


def meta_of(st):
    return (len(st.slots), st.nExp, st.nInv, [(tuple(k), (list(e[0]), e[1])) for k, e in st.cache])


def run_chain(B, c, cfg, tag, bounds):
    st = M.ComposeState()
    metas = {0: meta_of(st)}
    for i, op in enumerate(c.jetOps):
        CTX[0] = "%s/slot%d" % (tag, i)
        if M.composeStep(B, c.n, c.emb, c.wit, c.weight, cfg, c.piEnc, st, op) is None:
            raise SystemExit("compose failed at %s slot %d" % (tag, i))
        if i + 1 in bounds:
            metas[i + 1] = meta_of(st)
    return st, metas


def zero_pair(B, W):
    z = M.zeroModel(B)
    return (z, M.supNormUp(B, W, z.poly))


def same_pair(p, q):
    return (p[0].deg == q[0].deg and p[0].rad == q[0].rad and list(p[0].poly) == list(q[0].poly) and p[1] == q[1])


def self_check(B, c, cfg, plan, pairs, metas):
    """shadow re-run of every segment from its seed; returns the number of segments checked."""
    W = c.weight
    ledger = set(plan["ledger"])
    for s in plan["segs"]:
        lo, hi, live = s["start"], s["stop"], set(s["live"])
        st = M.ComposeState()
        L, nE, nI, cache = metas[lo]
        st.slots = [pairs[i] if i in s["imports"] else zero_pair(B, W) for i in range(L)]
        st.nExp, st.nInv = nE, nI
        st.cache = [(k, (list(e[0]), e[1])) for k, e in cache]
        for i in range(lo, hi):
            op = c.jetOps[i]
            if i in live or op[0] in FALLIBLE:
                CTX[0] = "dup"
                if M.composeStep(B, c.n, c.emb, c.wit, W, cfg, c.piEnc, st, op) is None:
                    raise SystemExit("self-check: shadow step failed at %d" % i)
            else:
                st.push(B, W, M.zeroModel(B))
        if meta_of(st) != metas[hi]:
            raise SystemExit("self-check: meta mismatch after segment [%d,%d)" % (lo, hi))
        for e in s["exports"]:
            assert e in ledger
            if not same_pair(st.slots[e], pairs[e]):
                raise SystemExit("self-check: export %d of [%d,%d) differs" % (e, lo, hi))
    return len(plan["segs"])


def char_values(B, c, cfg):
    """the character slot (the first `char` op, a cache miss on its own key): the values that its one-op segment
    proof memoizes (charResolve_eq_of_radius, expWitnessRadius_eq_of_pin, expWitnessRadiusOf_eq_of_residuals)."""
    n, W, pe = c.n, c.weight, c.piEnc
    slot = next(i for i, op in enumerate(c.jetOps) if op[0] == "char")
    op = c.jetOps[slot]
    k2 = tuple(M.normKey(B, n, c.emb, op[1]))
    cidx, E = M.findKeyIdx(k2, c.wit.charWit)
    cfgw = cfg.forWitness(1, len(c.wit.expWit) + cidx)
    CTX[0] = "dup"
    g = M.charPhaseModel(B, n, c.emb, W, pe, k2)
    z, zr = M.expPinBall(B, g)
    out = A.certCExpReduced(B, z, zr, E[1], E[2])
    info = {}
    r = M.expWitnessRadiusOf(B, n, W, cfgw, g, E[0], out, info)
    return dict(slot=slot, opKey=tuple(op[1]), k2=k2, cidx=cidx, pinHalvings=E[1], pinOrder=E[2], out=out,
                mB=info["mB"], mEta=info["mEta"], res=info["res"], r=r)


def gram_stages(B, c):
    n, K, W, cfg, pe = c.n, c.emb, c.weight, c.cfgLow, c.piEnc
    CTX[0] = "gram/entries"
    G = C.gramModels(B, n, K, W, cfg, pe, c.DKc)
    E = {(a, b): G[a][b] for a in range(n) for b in range(n) if a <= b}
    T = {}
    for i in range(n):
        for j in range(n):
            CTX[0] = "gram/bg%d%d" % (i, j)
            T[(i, j)] = C.gramBGModel(B, n, c.gramInv, G, W, cfg, pe, i, j)
    rows = [M.sumUp(B, [C.gramDefectUp(B, W, i, j, T[(i, j)]) for j in range(n)]) for i in range(n)]
    p = c.params
    CTX[0] = "dup"
    db = C.gramCheck(B, n, K, c.gramInv, W, cfg, pe, p["sB"] - p["mu"], c.DKc)
    assert db is not None
    eps = C.gramInvRadius(B, db)
    return dict(E=E, T=T, rows=rows, db=db, eps=eps)


def torsion_stages(B, c, db):
    """the stages of `torsionModels` in the landed order (Torsion/Models.lean), each named as in
    `torsionModels_eq_of_stages`."""
    n, W, cfg, pe = c.n, c.weight, c.cfgLow, c.piEnc
    m = n + n
    eps = C.gramInvRadius(B, db)
    CTX[0] = "dup"
    ms = M.compose(B, n, c.jetOps, c.emb, c.wit, W, cfg, pe, C.torsionSlots(n, c.jet))
    L = C.dkModels(B, n, c.DKc)
    Gi = C.buildMat(n, n, lambda k, j: M.Model(0, C.gramInvPoly(c.gramInv, k, j), eps))
    CTX[0] = "torsion/DL"
    DL = C.dkwModels(B, n, c.emb, c.freqBox, c.params["s"], W, cfg, pe)

    def mm(key, r, k, cc, X, Y):
        CTX[0] = "torsion/%d" % key[1]
        return C.modelMatMul(B, W, cfg, pe, key, r, k, cc, X, Y)
    N0 = mm((4, 0), m, n, n, L, Gi)
    DG1 = mm((4, 1), n, m, n, C.modelMatTranspose(B, m, n, DL), L)
    DG2 = mm((4, 2), n, m, n, C.modelMatTranspose(B, m, n, L), DL)
    DGi0 = mm((4, 3), n, n, n, Gi, C.modelMatAdd(B, W, pe, n, n, DG1, DG2))
    DGi1 = mm((4, 4), n, n, n, DGi0, Gi)
    DN1 = mm((4, 5), m, n, n, DL, Gi)
    DN2 = mm((4, 6), m, n, n, L, C.modelMatNeg(B, n, n, DGi1))
    XN1 = mm((4, 7), m, m, n, C.dxhModels(B, n, ms), C.modelMatOmega(B, n, n, N0))
    inner = C.modelMatOmega(B, n, n, C.modelMatAdd(B, W, pe, m, n, XN1, C.modelMatNeg(
        B, m, n, C.modelMatOmega(B, n, n, C.modelMatAdd(B, W, pe, m, n, DN1, DN2)))))
    Tb = mm((4, 8), n, m, n, C.modelMatTranspose(B, m, n, C.modelMatOmega(B, n, n, N0)), inner)
    Y = mm((4, 9), 1, m, n, [[C.msGet(ms, a, B) for a in range(m)]], C.modelMatOmega(B, n, n, N0))
    CTX[0] = "dup"
    whole = C.torsionModels(B, n, c.jet, c.emb, c.wit, c.gramInv, db, c.freqBox, c.params["s"], W, cfg, pe, c.DKc)
    st = dict(eps=eps, ms=ms, L=L, Gi=Gi, DL=DL, N0=N0, DG1=DG1, DG2=DG2, DGi0=DGi0, DGi1=DGi1, DN1=DN1, DN2=DN2,
              XN1=XN1, Tb=Tb, Y=Y, T=whole)
    # the staged recomputation equals the landed whole (self-check of the stage order)
    for i in range(n):
        for j in range(n):
            a, b = whole[i][j], Tb[i][j]
            assert a.deg == b.deg and a.rad == b.rad and list(a.poly) == list(b.poly), ("T", i, j)
    return st


def main(which, gdir, plan_path, out):
    _wrap_engine()
    c, d = SW.load(gdir, which)
    B = c.B
    plan = json.load(open(plan_path))
    res = dict(which=which, prec=B.P, wanted=wanted_of(c), chains={},
               jet=dict(ops=[tuple(tuple(x) if isinstance(x, list) else x for x in o) for o in c.jetOps_toy],
                        v0=c.jet["v0"], d1=c.jet["d1"], d2=c.jet["d2"], d3=c.jet["d3"]),
               ops=[tuple(tuple(x) if isinstance(x, list) else x for x in o) for o in c.jetOps])
    for tag, cfg in (("cfgFull", c.cfgFull), ("cfgLow", c.cfgLow)):
        p = plan[tag]
        assert p["wanted"] == res["wanted"][tag], (tag, p["wanted"], res["wanted"][tag])
        bounds = {s["start"] for s in p["segs"]} | {p["segs"][-1]["stop"]}
        st, metas = run_chain(B, c, cfg, tag, bounds)
        pairs = st.slots
        nseg = self_check(B, c, cfg, p, pairs, metas)
        res["chains"][tag] = dict(ledger={i: pairs[i] for i in p["ledger"]}, metas=metas, nsegs=nseg)
        print(tag, "slots", len(pairs), "segments self-checked", nseg, "ledger", len(p["ledger"]), flush=True)
    res["char"] = {}
    for tag, cfg in (("cfgFull", c.cfgFull), ("cfgLow", c.cfgLow)):
        res["char"][tag] = char_values(B, c, cfg)
    gs = gram_stages(B, c)
    res["gram"] = gs
    res["torsion"] = torsion_stages(B, c, gs["db"])
    res["memos"] = MEMOS
    print("memos", len(MEMOS), "by context", sorted({m["ctx"].split("/")[0] for m in MEMOS}), flush=True)
    pickle.dump(res, open(out, "wb"))


if __name__ == "__main__":
    main(*sys.argv[1:5])
