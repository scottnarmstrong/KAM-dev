#!/usr/bin/env python3
"""SJS-X1: independent checks of a DD torus state (x1_dd.py), none of which the solver uses.

Untrusted design tooling.
  energy      H(K(p)) in DD on the whole grid: an invariant torus lies on one energy level, so max - min measures invariance;
  <Ghat>      the average over the torus of FH25's Ghat = G1 = Lambda1 - P1, P1 = |z1|^2 / 2, in DD (FH25 print 2.176574188839;
              SJS-PLAN's double torus 2.176574188839);
  actions     <Lambda1>, <I5>, <I6> and their ranges; the eccentricity ranges e_i = sqrt(1 - (G_i / Lambda_i)^2).
Usage: x1_check.py DD.npz [--json OUT]
"""
import argparse, json, os, sys
import numpy as np
import mpmath

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import x1_torus as XT
import x1_dd as XD
import hsyn as HS
from dd import DD
sys.path.pop(0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("--json")
    a = ap.parse_args()
    d = np.load(a.src)
    shape = tuple(int(x) for x in d["grid"]); phi = float(d["phi"])
    gr = XT.Grid(shape, d["G"], d["Fs"], float(d["cut"]))
    C = [XD.to_cdd(d["C_hi"][c], d["C_lo"][c]) for c in range(6)]
    del d
    Kg = []
    for c in (0, 2, 4):
        x, y = XT.pair_ifft(gr, C[c], C[c + 1])
        Kg += [x, y]
    del C
    ID = XT.ident_dd(gr)
    for i in range(3):
        Kg[i] = Kg[i] + ID[i]
    del ID
    z = [DD(x.hi.reshape(-1), x.lo.reshape(-1)) for x in Kg]
    del Kg
    n = z[0].hi.size
    K = HS.consts("dd")
    cs = HS.cs_of(phi, "dd")
    c, s = cs
    Hhi = np.empty(n); Hlo = np.empty(n); Ghi = np.empty(n); Glo = np.empty(n)
    ch = 65536
    for a0 in range(0, n, ch):
        sl = slice(a0, min(n, a0 + ch))
        zz = [DD(x.hi[sl], x.lo[sl]) for x in z]
        H = HS.H_chain(zz, cs, K)
        Hhi[sl], Hlo[sl] = H.hi, H.lo
        b1, b2, b3, La1, I5, I6 = zz
        s3, c3 = (b3 - b2).sincos()
        P1 = I5 * (c * c) + I6 * (s * s) - (I5 * I6).sqrt() * c3 * (c * s * 2.0)
        G1 = La1 - P1
        Ghi[sl], Glo[sl] = G1.hi, G1.lo
    H = DD(Hhi, Hlo)
    H0 = DD(np.float64(Hhi[0]), np.float64(Hlo[0]))
    dH = (H - H0).to_float()
    G = DD(Ghi, Glo)
    Gm = mpmath.fsum([mpmath.mpf(float(h)) for h in Ghi]) + mpmath.fsum([mpmath.mpf(float(l)) for l in Glo])
    Gm = Gm / n
    Hm = (mpmath.fsum([mpmath.mpf(float(h)) for h in Hhi]) + mpmath.fsum([mpmath.mpf(float(l)) for l in Hlo])) / n
    La1, I5, I6 = (z[3].to_float(), z[4].to_float(), z[5].to_float())
    La2 = HS.GTOT + I5 + I6 - La1
    G1 = G.to_float()
    G2 = HS.GTOT - G1
    e1 = np.sqrt(np.maximum(0, 1 - (G1 / La1) ** 2)); e2 = np.sqrt(np.maximum(0, 1 - (G2 / La2) ** 2))
    out = dict(src=os.path.basename(a.src), grid=list(shape), energy=mpmath.nstr(Hm, 32), energy_spread=float(dH.max() - dH.min()),
               Ghat_mean=mpmath.nstr(Gm, 30), FH25_Ghat="2.176574188839",
               actions=dict(Lambda1=[float(La1.min()), float(La1.max())], I5=[float(I5.min()), float(I5.max())],
                            I6=[float(I6.min()), float(I6.max())]),
               ecc=dict(e1=[float(e1.min()), float(e1.max())], e2=[float(e2.min()), float(e2.max())]))
    print("energy <H> = %s, spread max - min over the grid %.2e" % (out["energy"], out["energy_spread"]))
    print("<Ghat> = %s (FH25: 2.176574188839)" % out["Ghat_mean"])
    print("ranges: Lambda1 %s, I5 %s, I6 %s; e1 %.4f..%.4f, e2 %.4f..%.4f" % (out["actions"]["Lambda1"], out["actions"]["I5"],
                                                                         out["actions"]["I6"], e1.min(), e1.max(), e2.min(), e2.max()))
    if a.json:
        json.dump(out, open(a.json, "w"), indent=1)


if __name__ == "__main__":
    main()
