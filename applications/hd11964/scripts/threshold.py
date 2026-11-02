#!/usr/bin/env python3
"""HD11964-PILOT: the threshold and budget check of the baseline region, in exact rationals (untrusted,
Apache-2.0).  Calls `threshold_ok` (the mirror of the planned Lean check) on the baseline action box, Cbar = 1/100,
r = 4/1000, d = 1/1000, and writes validation/threshold.json."""
import json
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hd11964_model as HM  # noqa: E402

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
m = HM.Model()
lo, hi = HM.baseline_box(m)
Cbar, r, d = Fr(1, 100), Fr(4, 1000), Fr(1, 1000)
ok, det = HM.threshold_ok(m, lo, hi, Cbar, r, d)
inbox = all(float(lo[i]) <= float(m.Lam(i)) <= float(hi[i]) for i in range(2))
C = float(sum(m.Gam(i) for i in range(2)))
out = dict(ok=ok, box_lo=[str(x) for x in lo], box_hi=[str(x) for x in hi], Cbar=str(Cbar), r_exact=str(r),
           d_exact=str(d), nominal_in_box=inbox, C_nominal=C)
out.update(det)
with open(os.path.join(root, "validation", "threshold.json"), "w") as fh:
    json.dump(out, fh, indent=1)
print(ok, inbox, C)
