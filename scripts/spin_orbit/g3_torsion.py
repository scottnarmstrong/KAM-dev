#!/usr/bin/env python3
"""SO-GEN3: run checkGram + checkTorsion alone (sofx mirror) at a given cfgLow cutoff, err/disp irrelevant.
    SO_N=.. SO_DATA_DIR=.. SO_PREC=.. SO_PKG=.. python3 g3_torsion.py which CUT_LOW"""
import sys, json, time
from fractions import Fraction as F
import sofx_gen as G, sofx_lunar as L, sofx_check as C, sofx_packed as PK, sofx_model as M

def main(which, cut):
    t = time.time()
    eng = PK.PackedEngine({"cfgFull": F(1, 10 ** 36), "cfgLow": F(1, 10 ** 8)})
    cf = M.Cfg("cfgFull", G.CUT_FULL, G.TAYLOR, G.HALV, None, eng)
    cl = M.Cfg("cfgLow", int(cut), G.TAYLOR, G.HALV, None, eng)
    c = L.build(which, F(1), F(1), cf, cl, G.HALV, G.TAYLOR)
    B = c.B
    ig = {}
    assert C.checkGram(B, c, ig)
    _mm = C.modelMatMul
    def mm(B_, W, cfg, pe, key, *a):
        r = _mm(B_, W, cfg, pe, key, *a)
        print("matmul", key, [[float(B_.val(x.rad)) for x in row] for row in r][:4], flush=True)
        return r
    C.modelMatMul = mm
    _cm = M.compose
    def cm(*a, **k):
        r = _cm(*a, **k)
        if r is not None:
            print("compose", [float(B.val(x.rad)) for x in r], flush=True)
        return r
    M.compose = cm
    print("gramInvRadius", float(B.val(C.gramInvRadius(B, c._gram))), flush=True)
    T = C.torsionModels(B, 2, c.jet, c.emb, c.wit, c.gramInv, c._gram, c.freqBox, c.params["s"], c.weight, c.cfgLow,
                        c.piEnc, c.DKc)
    for i in range(3):
        print("T row", i, [(float(B.val(C.entry(T, i, j, B).rad)), len(C.entry(T, i, j, B).poly) if hasattr(C.entry(T, i, j, B), "poly") else None) for j in range(3)], flush=True)
    S, Cm = G.torsion_witness(B, c, T)
    c.torsInv = S
    info = {}
    ok = C.checkTorsion(B, c, info)
    s = G.summ(info)
    print(json.dumps(dict(which=which, cut=int(cut), ok=ok, a=s.get("a"), b=s.get("b"), r=s.get("r"),
                          deltaT=s.get("deltaT"), margin=s.get("margin"), seconds=round(time.time() - t))), flush=True)

if __name__ == "__main__":
    main(*sys.argv[1:])
