#!/usr/bin/env python3
"""HD11964-PILOT: census of the jet products of the normal form at orders 1-4 (untrusted, Apache-2.0).
Counts the grid-valued jet products (and their monomial pairs) in the setup and the full Lie series at one interior
centre on a 64 x 32 grid, unpruned.  The product and pair counts do not depend on the grid.  Writes
validation/product-census.json."""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gate  # noqa: E402
import hd11964_model as HM  # noqa: E402
import jets  # noqa: E402
import normal_form  # noqa: E402

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
cnt = {"mul": 0, "pairs": 0}
orig = jets.mul


def cmul(A, B, chunk=4096, bmask_key=None, bmask=None):
    d = min(A.deg, B.deg)
    I, J, K, st = A.S.pairs(d, bmask_key, bmask)
    if A.c.ndim == 3 and A.c.shape[1] > 1 and A.c.shape[2] > 1:
        cnt["mul"] += 1
        cnt["pairs"] += len(I)
    return orig(A, B, chunk, bmask_key, bmask)


normal_form.mul = cmul
jets.mul = cmul
m = HM.Model()
reg = gate.region(m)
nu = [float(HM.R(x)) for x in m.nu]
mu = float(HM.R(m.mu))
out = {}
for N in (1, 2, 3, 4):
    for k in cnt:
        cnt[k] = 0
    nf = normal_form.NormalForm(nu, mu, N1=64, N2=32, N=N)
    nf.setup(*gate.centre(reg["Lhat"], [0.004, 0.006], [0.5, 0.0]))
    setup = dict(cnt)
    nf.run()
    out[N] = dict(setup_mul=setup["mul"], setup_pairs=setup["pairs"], total_mul=cnt["mul"],
                  total_pairs=cnt["pairs"], D=nf.D, M=nf.S6.M(nf.D))
    print(N, out[N], flush=True)
with open(os.path.join(root, "validation", "product-census.json"), "w") as fh:
    json.dump(out, fh, indent=1)
