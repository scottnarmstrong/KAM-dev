#!/usr/bin/env python3
"""LOCK-GEN part 2: invariance error of the truncated lock embedding against the support (untrusted tooling).

    SO_HP_BITS=192 python3 lock_trunc.py OUT.json shape:Ks:Ls ...

Uses lock_emit's cached grid Fourier data; for each support, the weighted norms Σ|R̂_k| e^{2πρ|k|₁} of the residual
rows (α, I, J̃) and the energy error at several ρ (κ = 1; every row scales with κ), and the half-term counts.
"""
import sys, json, time
from fractions import Fraction as F
import lock_emit as LE
import pickle, os

RHOS = ("1/280", "1/140", "1/100", "1/70")


def main(out, specs):
    g = LE.Grid()
    co = pickle.load(open(os.path.join(LE.DATA, "lock_emit_grid_P%d.pkl" % LE.P), "rb"))
    res = []
    for sp in specs:
        shape, Ks, Ls = sp.split(":")
        Ks, Ls = int(Ks), int(Ls)
        S = 3.33 * 26 + 24
        S = int(S)
        tr = {k: LE.truncate(co[k], Ks, Ls, shape, S) for k in ("U", "P", "J")}
        t = time.time()
        r = LE.residual(g, tr, S, F(1, 140), F(1), rhos=RHOS)
        row = dict(shape=shape, Ks=Ks, Ls=Ls, half={k: len(LE.half(v)) for k, v in tr.items()},
                   err={rr: max(r[x]["weighted_%s" % rr] for x in ("a", "I", "J")) for rr in RHOS},
                   energy={rr: r["E"]["weighted_%s" % rr] for rr in RHOS}, rows=r, seconds=round(time.time() - t))
        res.append(row)
        print(sp, row["half"]["U"], {k: "%.2e" % v for k, v in row["err"].items()}, flush=True)
        json.dump(res, open(out, "w"), indent=1)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
