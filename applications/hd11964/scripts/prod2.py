#!/usr/bin/env python3
"""HD11964 phase 2: the order-2 producer in the exact form of the Lean identity, float64 leg (untrusted, Apache-2.0).

The Lean statement (`KAM/Application/LambdaDrift/LieRemainderChart.lean`, `chartRate_approxIntegral₂`): for planet i,
with the action Lam_i, its angle lam_i, D_i = d/dlam_i, the canonical bracket {a, b} = sum_j a_th b_I - a_I b_th over
the pairs (lam_j, Lam_j), (xi_j, eta_j), h = hProd 1 nu (the Kepler part) and P = H o Psi - h = mu f o Psi:

    F_i = Lam_i + D_i chi1 + D_i chi2 - 1/2 {D_i chi1, chi1}
    r1  = P - {chi1, h}                                   (= P - omega.d_lam chi1)
    r2  = {P - 1/2 {chi1, h}, chi1} - {chi2, h}
    {F_i, H} = -D_i r1 - D_i r2 + {D_i r1, chi1} + {D_i chi2, P} - 1/2 {{D_i chi1, chi1}, P}
             =: -T1 - T2 + T3 + T4 - T5/2.

The producer's generators solve the homological equations exactly on the mode set S = {0 < |k|, |k_c| <= Kc,
|k_b| <= Kb} (the design's S, every mode non-resonant):  omega(Lam).d_lam chi1 = Pi_S P,
omega(Lam).d_lam chi2 = Pi_S G2,  G2 = {P - 1/2 Pi_S P, chi1};  so r1 = (1 - Pi_S) P and r2 = (1 - Pi_S) G2 are
Fourier tails.  Every term is computed as its own function (tails by projection, brackets by products): no
cancellation.

The cell is kamx-hd-layer's worst cell (`tf_cell.py`): centre Lam = Lamhat - (rho + d) (corner -1-1), e_c = 0.6
(xi_c = sqrt(2 Gam_c), eta_c = 0), xi_b = eta_b = 0; normalised variables u = (x - centre)/h,
u = (dLam_c, dLam_b, dxi_c, deta_c, dxi_b, deta_b), the cell |u_j| <= 1.

Per planet and term the output gives (all labelled `estimated`: floating point, sampled):
  - `l1`: sum over the monomials of degree <= 3 (normalised by h^m) and the Fourier modes of |coefficient|, a bound of
    the degree-3 Taylor polynomial on the real cell; `l1w`: the same with the strip weight w^(|k_c|+|k_b|), w = 1.007;
  - `deg_l1`: the l1 norm per Taylor degree (the remainder estimate: twice the first omitted degree, or, where it is
    not computed, the geometric continuation);
  - `sup_sampled`: the max over the angle grid and sampled cell points (0, the 64 vertices, 200 random);
  - `a`: the sup bound estimate a_j = l1 + remainder estimate.
Also: the identity check at u = 0 (right side against the direct rate {F_i, H} with the EXACT gradient of H o Psi),
the range of F_i - Lam_i on the cell, and the phase-1 gate's construction at the same centre (cross-check).

Usage: python3 -I prod2.py OUT.json [--D=5] [--N1=448] [--N2=72] [--Kc=80] [--Kb=20] [--ec=0.6]
Run under the 8 GB cap.
"""
import json
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hd11964_model as HM  # noqa: E402
from jets import Jet  # noqa: E402
from normal_form import NormalForm  # noqa: E402

W_STRIP = 1.007
H_CELL = [11e-4, 4e-3, 3e-2, 15e-3, 8e-2, 8e-2]       # tf_cell.py's polydisc radii, u-order


def opt(name, default):
    return next((x.split("=", 1)[1] for x in sys.argv if x.startswith("--%s=" % name)), default)


def cell_centre(m, ec):
    """tf_cell.py's centre: Lam = Lamhat - (rho + d), Gam_c from e_c at Lam_c, xi_c = sqrt(2 Gam_c)."""
    import mpmath as mp
    rho, d = [HM.Fr(1, 10 ** 4), HM.Fr(3, 10 ** 3)], HM.Fr(1, 10 ** 3)
    Lc = [m.Lam(i) - HM.R(rho[i] + d) for i in range(2)]
    Gc = Lc[0] * (1 - mp.sqrt(1 - mp.mpf(ec) ** 2))
    xi_c = mp.sqrt(2 * Gc)
    return [float(x) for x in Lc], [float(xi_c), 0.0], [0.0, 0.0]


class Prod2(NormalForm):
    """The order-2 generators and the five terms of the Lean identity, on the grid jets of NormalForm."""

    def run2(self):
        mu = self.mu
        P = self.f.scale(mu)                       # P = mu f (exact, unfiltered)
        chi1, Rs1 = self.solve(P)                  # omega.d chi1 = Pi_S P
        G2 = self.bracket(P - Rs1.scale(0.5), chi1)
        chi2, Rs2 = self.solve(G2)                 # omega.d chi2 = Pi_S G2
        r1, r2 = P - Rs1, G2 - Rs2
        self.P, self.chi1, self.chi2, self.G2, self.r1, self.r2 = P, chi1, chi2, G2, r1, r2
        self.terms, Gs = [], []
        for i in range(2):
            D1, D2 = self.dlam(chi1)[i], self.dlam(chi2)[i]
            Dr1, Dr2 = self.dlam(r1)[i], self.dlam(r2)[i]
            B1 = self.bracket(D1, chi1)
            T = dict(T1=Dr1, T2=Dr2, T3=self.bracket(Dr1, chi1), T4=self.bracket(D2, P),
                     T5=self.bracket(B1, P))
            FmL = D1 + D2 - B1.scale(0.5)
            self.terms.append((T, FmL))
            Gs.append(FmL)
        self.G = {2: Gs}

    # ---- statistics of a jet on the cell -----------------------------------------------------------------------
    def hpow(self, deg, H):
        """h^m for the monomials up to degree deg (normalised variables)."""
        return np.array([np.prod([H[j] ** e for j, e in enumerate(mon)]) for mon in self.S6.mons[: self.S6.M(deg)]])

    def stats(self, J, samples, H=H_CELL):
        deg = J.deg
        hp = self.hpow(deg, H)
        C = np.fft.rfft2(J.c, axes=(1, 2)) / (self.N1 * self.N2)
        mult = np.ones(C.shape[1:])
        mult[:, 1:] = 2.0
        if self.N2 % 2 == 0:
            mult[:, -1] = 1.0
        wk = W_STRIP ** (np.abs(self.k1) + np.abs(self.k2))
        a = np.abs(C) * mult[None]
        per_mon = np.sum(a, axis=(1, 2)) * hp
        per_mon_w = np.sum(a * wk[None], axis=(1, 2)) * hp
        degs = np.array([sum(mn) for mn in self.S6.mons[: self.S6.M(deg)]])
        deg_l1 = [float(np.sum(per_mon[degs == k])) for k in range(deg + 1)]
        d3 = degs <= 3
        l1, l1w = float(np.sum(per_mon[d3])), float(np.sum(per_mon_w[d3]))
        if deg >= 4:
            rem = 2 * deg_l1[4]
            rem_kind = "2 x degree-4 l1"
        else:
            q = deg_l1[deg] / deg_l1[deg - 1] if deg_l1[deg - 1] > 0 else 0.0
            rem = 2 * deg_l1[deg] * q / max(1 - q, 1e-3) if q < 1 else float("inf")
            rem_kind = "geometric continuation beyond degree %d (x2)" % deg
        # sampled sup: the full available polynomial at the sample points, on the whole angle grid
        best = 0.0
        vals_min, vals_max = np.inf, -np.inf
        for u in samples:
            x = np.asarray(u) * np.asarray(H)
            wv = np.array([np.prod([x[j] ** e for j, e in enumerate(mon)]) for mon in self.S6.mons[: self.S6.M(deg)]])
            v = np.tensordot(wv, J.c, axes=(0, 0))
            best = max(best, float(np.max(np.abs(v))))
            vals_min, vals_max = min(vals_min, float(np.min(v))), max(vals_max, float(np.max(v)))
        # per-variable growth: the l1 norm of the pure powers u_j^k, k = 0..deg
        pure = []
        for j in range(6):
            row = []
            for k in range(deg + 1):
                e = [0] * 6
                e[j] = k
                row.append(float(per_mon[self.S6.idx[tuple(e)]]))
            pure.append(row)
        return dict(deg=deg, l1=l1, l1w=l1w, deg_l1=deg_l1, rem=rem, rem_kind=rem_kind, a=l1 + rem,
                    sup_sampled=best, min_sampled=vals_min, max_sampled=vals_max, pure_l1=pure)


def main():
    out_path = sys.argv[1]
    D = int(opt("D", "5"))
    N1, N2 = int(opt("N1", "448")), int(opt("N2", "72"))
    Kc, Kb = int(opt("Kc", "80")), int(opt("Kb", "20"))
    ec = float(opt("ec", "0.6"))
    m = HM.Model()
    nu = [float(HM.R(x)) for x in m.nu]
    mu = float(HM.R(m.mu))
    Lam, xi, eta = cell_centre(m, ec)
    t0 = time.time()
    pr = Prod2(nu, mu, N1=N1, N2=N2, N=D - 1, K1solve=Kc, K2solve=Kb)
    pr.setup(Lam, xi, eta)
    t1 = time.time()
    pr.run2()
    t2 = time.time()
    rng = np.random.default_rng(20261101)
    samples = [np.zeros(6)] + [np.array([(b >> j) & 1 for j in range(6)]) * 2.0 - 1.0 for b in range(64)]
    samples += list(rng.uniform(-1, 1, size=(200, 6)))
    res = dict(cell=dict(Lam=Lam, xi=xi, eta=eta, ec=ec, h=H_CELL, vars=["dLam_c", "dLam_b", "dxi_c", "deta_c",
                                                                           "dxi_b", "deta_b"]),
               grid=[N1, N2], D=D, S=dict(Kc=Kc, Kb=Kb), mu=mu, nu=nu, planets={})
    direct = pr.residual(2)
    cells = {"B": H_CELL, "B_xe4": [H_CELL[0], H_CELL[1], H_CELL[2] / 4, H_CELL[3] / 4, H_CELL[4], H_CELL[5]],
             "B_all4": [x / 4 for x in H_CELL]}
    res["cells"] = cells
    for i, name in enumerate(("c", "b")):
        T, FmL = pr.terms[i]
        st = {k: pr.stats(v, samples) for k, v in T.items()}
        st_alt = {c: {k: pr.stats(v, samples, H) for k, v in T.items()} for c, H in cells.items() if c != "B"}
        rhs0 = -T["T1"].at0() - T["T2"].at0() + T["T3"].at0() + T["T4"].at0() - 0.5 * T["T5"].at0()
        rate, _ = direct[i]
        a = [st["T%d" % j]["a"] for j in range(1, 6)]
        res["planets"][name] = dict(
            terms=st, terms_smaller_cells=st_alt,
            a_smaller_cells={c: [v["T%d" % j]["a"] for j in range(1, 6)] for c, v in st_alt.items()},
            a=a, eta_bound=a[0] + a[1] + a[2] + a[3] + a[4] / 2,
            identity_check=dict(direct_rate_sup=float(np.max(np.abs(rate))),
                                rhs_sup=float(np.max(np.abs(rhs0))),
                                max_abs_diff=float(np.max(np.abs(rate - rhs0)))),
            F_minus_Lam=pr.stats(FmL, samples))
    t3 = time.time()
    # the phase-1 construction at the same centre (its own mode set: the 2/3 box)
    nf = NormalForm(nu, mu, N1=N1, N2=N2, N=2)
    nf.setup(Lam, xi, eta)
    nf.run()
    gate = nf.residual(2)
    res["phase1_construction"] = dict(rate_sup=[float(np.max(np.abs(r))) for r, _ in gate],
                                      note="normal_form.NormalForm(N=2) at the same centre, u = 0")
    res["phase1_gate_worst_corner"] = dict(rate=[3.70e-10, 7.41e-11], e_c=0.612,
                                           note="validation/ladder.json, order 2, corner -1-1 s=1.0")
    res["seconds"] = dict(setup=t1 - t0, run=t2 - t1, stats=t3 - t2, phase1=time.time() - t3)
    with open(out_path, "w") as fh:
        json.dump(res, fh, indent=1)
    for name in ("c", "b"):
        p = res["planets"][name]
        print(name, "a =", ["%.3e" % x for x in p["a"]], "eta = %.3e" % p["eta_bound"],
              "identity: direct %.3e rhs %.3e diff %.2e" % (p["identity_check"]["direct_rate_sup"],
                                                            p["identity_check"]["rhs_sup"],
                                                            p["identity_check"]["max_abs_diff"]),
              "F-Lam [%.3e, %.3e]" % (p["F_minus_Lam"]["min_sampled"], p["F_minus_Lam"]["max_sampled"]), flush=True)
    print("phase-1 construction rate", res["phase1_construction"]["rate_sup"], "seconds", res["seconds"])


if __name__ == "__main__":
    main()
