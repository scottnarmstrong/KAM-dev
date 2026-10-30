#!/usr/bin/env python3
"""SHARP-CERTSIDE: how loose is the checker's invariance bound against the true sup on the strip?

Untrusted design tooling (numbers for docs/campaign/design/CERTIFIER-SHARPNESS.md, not a certificate).

For the rotated-frame lunar candidates (SO-GEN2, owner ruling O5) this rebuilds the exact residual rows
R3 (P1 row) and R4 (P2 row) of `scripts/spin_orbit/rot_build.py` (read-only import; same truncation as the
emitted `*_rot.json`: Lv = LE = LJ = 88, S = 318) and compares, on the strip T_rho (rho = 1/70):

  l1w     sum_k |c_k| w^{|k|_1}                     (the checker's `supBound`, CertModel semantics)
  corner  max_{sigma in {+-1}^2} sum_k |c_k| e^{2 pi rho sigma.k}   (vertex bound: y -> sum |c_k| e^{-2 pi k.y}
          is convex on the box |y_i| <= rho, so its max is at a vertex; rigorous, same data)
  l2      max_sigma (sum_k |c_k|^2 e^{4 pi rho sigma.k})^{1/2}    (Parseval on the distinguished torus; a LOWER
          bound of the sup there, and the quantity the Parseval/frequency-specific cohomological estimates consume)
  sup     sampled max of |R| on the two distinguished tori (|Im psi| = |Im phi| = rho, up to conjugation),
          FFT grid N1 x N2 (heuristic: no interpolation error added; a lower bound of the true sup)

Usage: python3 -I scripts/certifier/measure_residual.py [lower|upper] [--json OUT]
"""
import sys, os, math, json, time
import numpy as np
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "spin_orbit"))
import rot_build as RB                                     # noqa: E402  (read-only use)
from rotlib import _obj                                    # noqa: E402

RHO = float(RB.RHO)
TP = 2 * math.pi


def q5_float(X, Y, den):
    """float values of (X + Y sqrt5)/den for object arrays X, Y (exact ints), den int."""
    T = RB.SQ5_T
    num = X * (1 << T) + Y * RB.SQ5_LO
    return np.array([float(F(int(a), den << T)) for a in num])


def residual_rows(cand):
    """(k, l, c3, c4): full-lattice keys and the coefficients of R3, R4 (index units, phase 1 values: the
    function is sum_kappa i c_kappa e_kappa).  Mirrors rot_build.bounds (rows P1, P2)."""
    which, S = cand["which"], cand["S"]
    p, E, J = cand["p"], cand["E"], cand["J"]
    pd = {(int(k), int(l)): int(x) for k, l, x in zip(p.k, p.l, p.v)}
    Ed = {(int(k), int(l)): int(x) for k, l, x in zip(E.k, E.l, E.v)}
    Jd = {(int(k), int(l)): int(x) for k, l, x in zip(J.k, J.l, J.v)}
    keys = set(pd) | set(Jd)
    for m, (a, d) in RB.SH.items():
        for (k, l) in Ed:
            keys.add((k + a, l + d)); keys.add((-k - a, -l - d))
    keys.discard((0, 0))
    keys = sorted(keys)
    kk = np.array([x for x, _ in keys], dtype=np.int64); ll = np.array([y for _, y in keys], dtype=np.int64)
    la, lb = RB.lam_pair(which, _obj(kk.tolist()), _obj(ll.tolist()))
    Pv = _obj([pd.get(x, 0) for x in keys]); Jv = _obj([Jd.get(x, 0) for x in keys])
    G3 = _obj([0] * len(keys)); G4 = _obj([0] * len(keys))
    for m, (a, d) in RB.SH.items():
        diff = _obj([Ed.get((-x - a, -y - d), 0) - Ed.get((x - a, y - d), 0) for (x, y) in keys])
        G3 = G3 + RB.AINT[m] * diff
        G4 = G4 + RB.AINT[m] * (2 - m) * diff
    X3 = RB.DA * la * Pv + 2 * RB.DEN_NU * G3; Y3 = RB.DA * lb * Pv
    X4 = RB.DA * la * (Pv + Jv) + RB.DEN_NU * G4; Y4 = RB.DA * lb * (Pv + Jv)
    Den3 = RB.DEN_NU * RB.DA << (S + 1)
    return kk, ll, q5_float(X3, Y3, Den3), q5_float(X4, Y4, Den3)


def witness_data(cand):
    """The exp-witness ingredients of rot_build.bounds as float coefficient arrays: v (phase 1 values of the
    sine series, index units), the defects d_j E~ - 2 i (d_j v) E~ (j = psi, phi; index units) and
    eps0 = |E~(0) - 1|.  Delta(rho) = e^{2 B} (eps0 + (1/2 + rho)(r_psi + r_phi)), B = 2 ||v||_w,
    r_j = 2 pi ||defect_j||_w (rot_build.bounds)."""
    v, E = cand["v"], cand["E"]
    out = {}
    for name, dv, dE in (("psi", v.dpsi(), E.dpsi()), ("phi", v.dphi(), E.dphi())):
        prod = dv.mul(E, RB.Weights(RB.RHO)).times_i().mul_int(2)
        d = dE.rescale(prod.S).sub(prod)
        out[name] = (d.k.copy(), d.l.copy(), np.array([float(F(int(x), 1 << d.S)) for x in d.v]))
    out["v"] = (v.k.copy(), v.l.copy(), np.array([float(F(int(x), 1 << v.S)) for x in v.v]))
    E00 = sum(int(x) for x in E.v)
    out["eps0"] = float(F(abs(E00 - (1 << E.S)), 1 << E.S))
    return out


def norms_of(k, l, c, N1=None, N2=None):
    w = np.exp(TP * RHO * (np.abs(k) + np.abs(l)))
    out = {"terms": int(len(c)), "kmax": int(np.abs(k).max()), "lmax": int(np.abs(l).max())}
    out["l1w"] = float(np.sum(np.abs(c) * w))
    corners = {}
    l2 = {}
    for sg in [(1, 1), (1, -1), (-1, 1), (-1, -1)]:
        wc = np.exp(TP * RHO * (sg[0] * k + sg[1] * l))
        corners[str(sg)] = float(np.sum(np.abs(c) * wc))
        l2[str(sg)] = float(np.sqrt(np.sum(np.abs(c) ** 2 * wc ** 2)))
    out["corner"] = max(corners.values()); out["corner_all"] = corners
    out["l2"] = max(l2.values())
    # sampled sup on the distinguished tori Im(psi, phi) = -rho sigma (weight e^{2 pi rho sigma.k})
    N1 = N1 or 1 << int(math.ceil(math.log2(8 * (out["kmax"] + 1))))
    N2 = N2 or 1 << int(math.ceil(math.log2(8 * (out["lmax"] + 1))))
    sup = 0.0
    for sg in [(1, 1), (1, -1)]:                           # the other two are conjugates (real on reals)
        wc = np.exp(TP * RHO * (sg[0] * k + sg[1] * l))
        C = np.zeros((N1, N2), complex)
        np.add.at(C, (k % N1, l % N2), 1j * c * wc)
        vals = np.fft.ifft2(C) * N1 * N2
        sup = max(sup, float(np.abs(vals).max()))
    out["sup_sampled"] = sup; out["grid"] = [N1, N2]
    out["ratio_l1w_over_sup"] = out["l1w"] / sup
    out["ratio_corner_over_sup"] = out["corner"] / sup
    return out


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "lower"
    t0 = time.time()
    cand = RB.build(which, 88, 88, 88, 318, log=lambda *a: None)
    print("built %s in %.1fs; checker bounds: R3_l1w %.4e R4_l1w %.4e" % (
        which, time.time() - t0, cand["bounds"]["R3_l1w"], cand["bounds"]["R4_l1w"]))
    k, l, c3, c4 = residual_rows(cand)
    res = {}
    for name, c in (("R3 (P1 row)", c3), ("R4 (P2 row)", c4)):
        nz = c != 0
        r = norms_of(k[nz], l[nz], c[nz])
        res[name] = r
        print("%s: terms %d |k|<=%d |l|<=%d  l1w %.4e  corner %.4e  l2 %.4e  sup(sampled %dx%d) %.4e  "
              "l1w/sup %.2f  corner/sup %.2f  l2/sup %.3f" % (
                  name, r["terms"], r["kmax"], r["lmax"], r["l1w"], r["corner"], r["l2"], r["grid"][0], r["grid"][1],
                  r["sup_sampled"], r["ratio_l1w_over_sup"], r["ratio_corner_over_sup"], r["l2"] / r["sup_sampled"]))
    # the witness part 2 eps sum A_m w^{|s_m|} Delta is added to R3 by the checker-style bound
    b = cand["bounds"]
    res["witness_part_P1"] = 2 * sum(abs(float(RB.EPSA[m])) * math.exp(TP * RHO * (abs(a) + abs(d)))
                                     for m, (a, d) in RB.SH.items()) * b["Delta"]
    res["eta3_checker"] = b["eta3_unscaled"]
    res["eta3_corner"] = TP * (res["R3 (P1 row)"]["corner"] + res["witness_part_P1"])
    res["eta3_sampled"] = TP * (res["R3 (P1 row)"]["sup_sampled"] + res["witness_part_P1"])
    print("eta3 (P1 row, theta units): checker %.4e  corner %.4e  sampled-sup %.4e  (witness part %.3e)" % (
        res["eta3_checker"], res["eta3_corner"], res["eta3_sampled"], TP * res["witness_part_P1"]))
    if "--json" in sys.argv:
        json.dump(res, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)


if __name__ == "__main__":
    main()
