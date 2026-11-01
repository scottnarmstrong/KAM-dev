#!/usr/bin/env python3
"""V2-PACKED-JET gate, step 1 (untrusted tooling, read-only): extract one cfgLow slot range of LG00's jet chain
from the LG00-CERT generator state into JSON, for `jet_gate_gen.py`.

Run with lg00-cert's tooling on the path (it unpickles the state with lg00-cert's classes); this keeps the two
repositories' `scripts/spin_orbit` modules apart. Writes, for the slots [START, STOP):
  - the program prefix (ops 0 .. STOP-1), the plan's live slots of the segments inside the range;
  - the operands read from before START (the imports) with their landed cfgLow models (deg, poly, rad: the
    mantissas at scale 2^128) and their operations;
  - the live slots read after STOP (the exports) and the chain's wanted slots;
  - the weight (rho, w) and the lg00-cert commit.
The state is LG00-CERT's L = 20 generator state (`lg00_cert_gen.py`, docs/campaign/handoffs/LG00-CERT.md on
lg00-cert: `gen_L20/state.pkl`, `plans.json`); a copy lives in .lake/v2-packed-jet/lg00-gen-L20/.
Usage: python3 -I scripts/packed/jet_extract.py STATE.pkl PLANS.json START STOP OUT.json [LG00_CERT_ROOT]
"""
import json
import os
import pickle
import subprocess
import sys


def main():
    state, plans, start, stop, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    cert = sys.argv[6] if len(sys.argv) > 6 else "/home/scott/KAM-dev-worktrees/lg00-cert"
    sys.path.insert(0, os.path.join(cert, "scripts", "sjs", "lg00cert"))
    import lg00_emit_stage  # noqa: F401  (lg00-cert's classes on the path, for unpickling)
    st = pickle.load(open(state, "rb"))
    prog = st["prog"]
    pairs = st["pairs"]["cfgLow"]
    plan = json.load(open(plans))["cfgLow"]
    segs = [s for s in plan["segs"] if s["start"] >= start and s["stop"] <= stop]
    live = sorted(set(x for s in segs for x in s["live"]))
    imports, used_later = set(), set()
    for j in live:
        op = prog[j]
        assert op[0] in ("add", "mul"), (j, op)
        for x in op[1:3]:
            if x < start:
                imports.add(x)
            else:
                assert x in live, (j, x)
    for j, op in enumerate(prog[stop:], stop):
        if op[0] in ("add", "mul"):
            used_later |= {op[1], op[2]}
        elif op[0] in ("exp", "inv", "sqrt"):
            used_later.add(op[1])
    wanted = [st["J"]["v0"]] + st["J"]["d1"] + [x for row in st["J"]["d2"] for x in row]
    exports = sorted((used_later | set(wanted)) & set(live))

    def fr(q):
        return [q.numerator, q.denominator]

    def op_json(op):
        if op[0] == "const":
            return ["const", fr(op[1]), fr(op[2]), op[3]]
        if op[0] == "char":
            return ["char", list(op[1])]
        return list(op)

    def model(j):
        m = pairs[j][0]
        return dict(deg=m.deg, rad=m.rad, poly=[[list(k), [v[0], v[1]]] for k, v in m.poly])
    W = st["c"].weight
    try:
        commit = subprocess.run(["git", "-C", cert, "rev-parse", "HEAD"], capture_output=True, text=True,
                                check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        commit = "unknown"
    rho = W.rho if hasattr(W, "rho") else W[0]
    w = W.w if hasattr(W, "w") else W[1]
    data = dict(start=start, stop=stop, ops=[op_json(op) for op in prog[:stop]], live=live,
                imports={str(j): dict(op=op_json(prog[j]), model=model(j)) for j in sorted(imports)},
                exports=exports, wanted=wanted, segs=[dict(s) for s in segs],
                weight=dict(rho=fr(rho), w=fr(w)), lg00_cert_commit=commit, args=st["args"])
    with open(out, "w") as f:
        json.dump(data, f)
    print("live", len(live), "imports", len(imports), "exports", len(exports), "segments", len(segs))


if __name__ == "__main__":
    main()
