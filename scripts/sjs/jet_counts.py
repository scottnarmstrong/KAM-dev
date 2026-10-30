#!/usr/bin/env python3
"""SJS-FEAS: operation counts of jet programs (total vs live per check), lunar and planetary-type.

usage: jet_counts.py [OUT.json]

Uses the Python mirror of the LANDED jet compiler `scripts/spin_orbit/adv_jet.py` (read-only import; it mirrors
`KAM/Certificate/Expr/{DiffBuild,DiffNode,Diff}.lean` op by op) and its slot-kind classifier (C: constant, M: a
Fourier model; a `mul` is CC, CM (scalar x model) or MM (model x model, a genuine packed product)).

* lunar: `soRotHamExprScaled` (adv_jet.report), n = 2.
* planetary-type toys (n = 4: two Delaunay/Poincare-like action-angle pairs per planet in the planar SJS
  reduction): H = sum_i (a_i A_i^2 + b_i A_i^3) + sum_m c_m (1 + A_2 + A_3) cos(k_m . theta), the modes k_m the
  M smallest |k|_1 nonzero half-lattice indices in Z^4 (a stand-in for a truncated disturbing function; the
  real planetary Hamiltonian has rational/sqrt dependence on the actions, i.e. inv/exp nodes, which only adds
  ops). For each: program length, op histogram, mul classes, and the closure (live slots, MM products, char
  slots) of: invariance (d1 slots), energy (v0), invariance + energy shared (v0 :: d1), torsion (d1 + d2).
Untrusted tooling; no Lean is run.
"""
import itertools
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
SO = os.path.join(os.path.dirname(HERE), "spin_orbit")
sys.path.insert(0, SO)
import adv_jet  # noqa: E402


def counts(J):
    prog = J["prog"]
    kd, src, cls = adv_jet.kinds(prog)
    d1 = [x for x in J["d1"] if x]
    d2 = [x for r in J["d2"] for x in r if x]
    wanted = {"invariance (d1)": d1, "energy (v0)": [J["v0"]], "inv+energy shared (v0::d1)": [J["v0"]] + d1,
              "torsion (d1,d2)": d1 + d2, "whole program": list(range(len(prog)))}
    out = dict(program_length=len(prog),
               ops={t: sum(1 for o in prog if o[0] == t) for t in ("const", "action", "char", "add", "mul")},
               model_slots=sum(1 for k in kd if k == "M"), per_call={})
    for name, w in wanted.items():
        sl = adv_jet.closure(prog, w)
        c = adv_jet.count(prog, sl, cls)
        heavy = sum(1 for i in sl if kd[i] == "M" and prog[i][0] in ("add", "mul"))
        out["per_call"][name] = dict(slots=len(sl), model_ops=heavy, chars=sum(1 for i in sl if prog[i][0] == "char"),
                                     **c)
    sep = out["per_call"]["invariance (d1)"]["model_ops"] + out["per_call"]["energy (v0)"]["model_ops"]
    out["landed_two_composes_model_ops_upper"] = 2 * out["per_call"]["whole program"]["model_ops"]
    out["separate_decls_inv_plus_energy_model_ops"] = sep
    out["shared_one_decl_model_ops"] = out["per_call"]["inv+energy shared (v0::d1)"]["model_ops"]
    return out


def planetary(M, n=4):
    modes = []
    for r in range(1, 12):
        for k in itertools.product(range(-r, r + 1), repeat=n):
            if sum(abs(x) for x in k) == r and k > tuple([0] * n):
                modes.append(k)
        if len(modes) >= M:
            break
    modes = modes[:M]
    kep = ("const", 0)
    for i in (0, 1):
        kep = ("add", ("add", ("mul", ("const", F(-3, 2 + i)), ("pow", ("action", i), 2)),
                       ("mul", ("const", F(1, 3 + i)), ("pow", ("action", i), 3))), kep)
    amp = ("add", ("const", 1), ("add", ("action", 2), ("action", 3)))
    pert = ("const", 0)
    for m, k in enumerate(modes):
        pert = ("add", ("mul", ("const", F(1, 1000 + m)), ("mul", amp, ("cosMode", k))), pert)
    return ("add", kep, pert), modes


def main():
    res = {}
    out, J, *_ = adv_jet.report()
    res["lunar"] = counts(J)
    for M in (1, 4, 16, 64):
        e, modes = planetary(M)
        J = adv_jet.jet(4, e)
        r = counts(J)
        r["modes"] = M
        res["planetary_M%d" % M] = r
    txt = json.dumps(res, indent=1)
    if len(sys.argv) > 1:
        with open(sys.argv[1], "w") as f:
            f.write(txt + "\n")
    print(txt)


if __name__ == "__main__":
    main()
