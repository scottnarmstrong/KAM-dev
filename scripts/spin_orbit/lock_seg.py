#!/usr/bin/env python3
"""LOCK-DATA: SO-CSEG-GEN (csplit_census.py, csplit_plan.py, csplit_ledger.py) on the N = 65 lock certificate,
unchanged: this shim only replaces their lunar loaders by the lock certificate of `lock_gen.py` (untrusted tooling).

    python3 lock_seg.py census GENDIR OUT.json       # csplit_census.main on the lock
    python3 lock_seg.py ledger GENDIR PLAN.json OUT.pkl

GENDIR is a `lock_gen.py generate` output (gen.pkl: books, torsInv, graph, domain); the certificate is rebuilt in
CHECK mode with exactly those books.  Run with SO_LOCK_DATA (the emission JSON) and SO_LOCK_SIZE set as for
`lock_gen.py`.
"""
import os
import pickle
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
os.environ["SO_MIRROR"] = HERE
for k, v in dict(OMP_NUM_THREADS="1", SO_CUT_LOW="250", SO_BUDGET_FULL="24").items():
    os.environ.setdefault(k, v)
sys.path.insert(0, HERE)
sys.set_int_max_str_digits(0)


def lock_cert(gdir):
    import lock_gen as LG
    import sofx_gen as G
    import sofx_packed as PK
    import lock_sofx as LS
    import json
    g = pickle.load(open(os.path.join(gdir, "gen.pkl"), "rb"))
    d = LS.load()
    d["params"] = LG.final_params(d)
    eng = PK.PackedEngine({"cfgFull": F(1, 10 ** 24), "cfgLow": F(1, 10 ** 8)})
    cf, cl = G.make_cfgs(eng, g["books"])
    c = LS.build(LG.FINAL["err"], g["v2"]["disp"], cf, cl, d=d, S=g["torsInv"], graph=g["graph"])
    dom = g["domain"]
    c.centre, c.radius = [F(x) for x in dom["centre"]], [F(x) for x in dom["radius"]]
    LG.set_weightH(c, F(dom["rhoH"]))
    c.jetOps_toy = LG.toy_ops(c.jetOps)
    c.claims = g["claims"]
    return c, d


class _Shim:
    def __init__(self, c):
        self.c = c

    def build(self, *a, **k):
        return self.c


if __name__ == "__main__":
    mode, gdir = sys.argv[1], sys.argv[2]
    c, d = lock_cert(gdir)
    if mode == "census":
        import json
        import tempfile
        import csplit_census as CC
        tmp = tempfile.mkdtemp(dir=os.path.dirname(sys.argv[3]))
        os.makedirs(os.path.join(tmp, "g2"))
        g = pickle.load(open(os.path.join(gdir, "gen.pkl"), "rb"))
        json.dump({k: [list(map(str, x[0])) for x in v] for k, v in g["books"].items()},
                  open(os.path.join(tmp, "g2", "lock_advice.json"), "w"))
        json.dump({}, open(os.path.join(tmp, "g2", "lock_cert.json"), "w"))
        CC.D3, CC.L = tmp, _Shim(c)
        CC.main("lock", sys.argv[3])
    elif mode == "ledger":
        import csplit_ledger as CL
        CL.SW.load = lambda gdir_, which: (c, d)
        CL.main("lock", gdir, sys.argv[3], sys.argv[4])
