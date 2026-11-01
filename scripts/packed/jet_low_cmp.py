#!/usr/bin/env python3
"""V2-PACKED-JET-LOW (untrusted tooling, read-only): the radii of the packed Low chain's wanted slots against the
landed Low stage's.

For each wanted slot (`J.d1`, `J.d2`) prints the packed node's radius and norm bound (LowPlan.json, written by
`jet_low_gen.py` from the bit-exact mirror) next to the landed model's radius and weighted sup norm, both at
degree 0 (the landed model is converted by lg00-cert's mirror of `toDeg`, as `jLeaf` does).
Run with lg00-cert's tooling on the path (unpickling). Usage:
  python3 -I scripts/packed/jet_low_cmp.py STATE.pkl LowPlan.json [LG00_CERT_ROOT]
"""
import json
import os
import pickle
import sys
from fractions import Fraction as Fr

P = 128


def main():
    state, plan = sys.argv[1], json.load(open(sys.argv[2]))
    cert = sys.argv[3] if len(sys.argv) > 3 else "/home/scott/KAM-dev-worktrees/lg00-cert"
    sys.path.insert(0, os.path.join(cert, "scripts", "sjs", "lg00cert"))
    import lg00_emit_stage  # noqa: F401  (lg00-cert's classes and mirror on the path)
    import sofx_model as SM
    import sofx_arith as SA
    st = pickle.load(open(state, "rb"))
    pairs, c = st["pairs"]["cfgLow"], st["c"]
    B, W, pe = SA.FixedB(P), c.weight, c.piEnc
    fl = lambda v: float(Fr(v, 2 ** P))
    rows = []
    for j, (r, nb) in sorted(plan["wanted"].items(), key=lambda t: int(t[0])):
        m0 = SM.toDeg(B, W, pe, 0, pairs[int(j)][0])
        lr, ln = fl(m0.rad), fl(SM.supNormUp(B, W, m0.poly))
        rows.append(dict(slot=int(j), packed_rad=r, landed_rad=lr, rad_ratio=r / lr if lr else None,
                         packed_nb=nb, landed_norm=ln))
        print("%5s  packed r %.3e  landed r %.3e  ratio %.3g   packed nb %.4g  landed norm %.4g"
              % (j, r, lr, r / lr if lr else float("nan"), nb, ln))
    rs = [x["rad_ratio"] for x in rows if x["rad_ratio"] is not None]
    print(json.dumps(dict(wanted=len(rows), max_rad_ratio=max(rs), min_rad_ratio=min(rs),
                          max_packed_rad=max(x["packed_rad"] for x in rows),
                          max_landed_rad=max(x["landed_rad"] for x in rows), rows=rows)))


if __name__ == "__main__":
    main()
