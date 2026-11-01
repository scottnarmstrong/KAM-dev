#!/usr/bin/env python3
"""V2-PACKED-JET-LOW, step 1 (untrusted tooling, read-only): extract LG00's whole cfgLow jet chain from the LG00-CERT
generator state into JSON, with every leaf node computed by lg00-cert's bit-exact mirror exactly as `jLeaf`
(`KAM/CertificateSharp/Packed/JetLeaf.lean`) computes it in the kernel:
  model -> `toDeg` to degree 0 (pi enclosure) -> `jBoxTrunc` (the terms without a slot on the node's layout dropped
  into the radius at `supNormUp`) -> `toMants` at scale 2^P.
  - constants (`constModel`, on the one-slot layout: key (0, 0));
  - actions (`realCompModel`, the landed slot model), characters, `inv`, `sqrt` (the landed slot models; in
    V2-PACKED-JET-LOW M1 the last three are given blocks), on the box of half-width H.
Writes the program prefix, the live slots, the wanted slots, the weight, and the leaves.
Run with lg00-cert's tooling on the path (unpickling). Usage:
  python3 -I scripts/packed/jet_extract_low.py STATE.pkl OUT.json [LG00_CERT_ROOT]
"""
import json
import os
import pickle
import subprocess
import sys

P, H = 128, 25


def main():
    state, out = sys.argv[1], sys.argv[2]
    cert = sys.argv[3] if len(sys.argv) > 3 else "/home/scott/KAM-dev-worktrees/lg00-cert"
    sys.path.insert(0, os.path.join(cert, "scripts", "sjs", "lg00cert"))
    import lg00_emit_stage  # noqa: F401  (lg00-cert's classes and mirror on the path)
    import sofx_model as SM
    import sofx_packed as SP
    import sofx_arith as SA
    st = pickle.load(open(state, "rb"))
    prog, pairs = st["prog"], st["pairs"]["cfgLow"]
    live = sorted(st["live"]["cfgLow"])
    J = st["J"]
    wanted = J["d1"] + [x for row in J["d2"] for x in row]
    stop = max(live + wanted) + 1
    c = st["c"]
    B = SA.FixedB(P)
    W, pe, n = c.weight, c.piEnc, 2

    def leaf(m, inbox):
        m0 = SM.toDeg(B, W, pe, 0, m)
        kept = [t for t in m0.poly if inbox(t[0])]
        drop = [t for t in m0.poly if not inbox(t[0])]
        rad = B.upAdd(m0.rad, SM.supNormUp(B, W, drop))
        tm = SP.toMants(B, P, kept)
        assert tm is not None
        re, im = tm
        return dict(re=[[list(k), v] for k, v in re], im=[[list(k), v] for k, v in im], rad=rad,
                    dropped=len(drop))

    box = lambda k: max(abs(k[0]), abs(k[1])) <= H
    unit = lambda k: tuple(k) == (0, 0)
    leaves = {}
    for j in live:
        op = prog[j]
        if op[0] == "const":
            leaves[j] = dict(kind="const", **leaf(SM.constModel(B, n, op[1], op[2], op[3]), unit))
        elif op[0] in ("action", "char", "inv", "sqrt", "exp"):
            leaves[j] = dict(kind=op[0], **leaf(pairs[j][0], box))

    # V2-PACKED-JET-LOW M3: the angle leaves and the constants of the packed characters
    from fractions import Fraction as Fr
    angles = {str(j): dict(kind="angle", **leaf(SM.realCompModel(B, n, K.angleDeg[j], K.angle[j]), box))
              for j in range(n)} if (K := c.emb) is not None else {}
    consts = {}
    for re_, im_, deg in [(Fr(0), Fr(-1), 1), (Fr(0), Fr(1), 1), (Fr(1), Fr(0), 0)] + \
            [(Fr(1, m + 1), Fr(0), 0) for m in range(48)]:
        consts["%s/%s/%d" % (re_, im_, deg)] = dict(kind="const", **leaf(SM.constModel(B, n, re_, im_, deg), unit))

    def fr(q):
        return [q.numerator, q.denominator]

    def op_json(op):
        if op[0] == "const":
            return ["const", fr(op[1]), fr(op[2]), op[3]]
        if op[0] == "char":
            return ["char", list(op[1])]
        return list(op)
    try:
        commit = subprocess.run(["git", "-C", cert, "rev-parse", "HEAD"], capture_output=True, text=True,
                                check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        commit = "unknown"
    data = dict(ops=[op_json(op) for op in prog[:stop]], live=live, wanted=wanted,
                leaves={str(j): v for j, v in leaves.items()}, angles=angles, consts=consts,
                weight=dict(rho=fr(W.rho), w=fr(W.w)), lg00_cert_commit=commit, args=st["args"])
    with open(out, "w") as f:
        json.dump(data, f)
    from collections import Counter
    print("live", len(live), "stop", stop, Counter(v["kind"] for v in leaves.values()),
          "dropped", sum(v["dropped"] for v in leaves.values()))


if __name__ == "__main__":
    main()
