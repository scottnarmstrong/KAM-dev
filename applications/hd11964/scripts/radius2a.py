#!/usr/bin/env python3
"""HD11964-ROT (3): the (2a) radius of the exact generator's enclosure on one cell (estimated; Apache-2.0).

The Lean bound `HD11964.Cover.norm_genChi_sub_le` (2a) and its decay variant `norm_genChi_sub_le_decay` (2b)
enclose chi1 = Pi_S P / (i k.omega) on a cell by the producer's centre c within

    (2a)  sum_{k in S} e^{2 pi rho |k|} (r_P B_k + |p_k|_1 eps_k + |p_k q_k - c_k|_1)        (on the strip rho)
    (2b)  sum_{k in S} e^{2 pi rho' |k|} (e^{-2 pi rho |k|} r_P B_k + |p_k|_1 eps_k + |p_k q_k - c_k|_1)

(theta = lambda/2pi, |k| = |k_c| + |k_b|; the model of P on strip(rho) x unit polydisc, evaluated on strip(rho')).
This script evaluates both on a cell of the fitted cover, from the producer's construction (`prod2_hp.py`):

  * P = mu f on the N1 x N2 grid as exact Taylor jets of degree DE = DJ + 1 in the six cell variables, and its
    exact DFT (the producer's code, fixed point 2^-FB);
  * p = the degree <= DJ part on the box |k_c| <= Kc, |k_b| <= Kb (the model's centre);
  * r_P(rho) = the weighted l1 norm sum_k e^{2 pi rho |k|} |.|_1 of everything else: the degree DJ + 1 part, the
    degrees > DJ + 1 extrapolated geometrically from the ratio of the last two degree norms, and the modes outside
    the box (an ESTIMATE of the model remainder: the layer's certified r_P also carries its arithmetic radii);
  * q_k = the degree <= DJ Taylor polynomial of 1/(k.omega(Lam_0 + h u)) in (u_Lam_c, u_Lam_b) (float64);
    B_k = 1/(|s_0| - sum_j |k_j| omega_j ((1 - h_j/Lam_j)^-3 - 1)) bounds |1/(k.omega)| on the complex polydisc;
    eps_k = the Cauchy bound of its Taylor remainder beyond degree DJ, from the polydisc of radius R;
  * c_k = the degree <= DJ part of p_k q_k (the producer's chi1); |p_k q_k - c_k|_1 = the l1 norm of the rest.

Output: a JSON summary (`--out`). Run under the 8 GB cap (the jets of degree DE are ~2.2x the producer's).
Usage: python3 -I radius2a.py --plan=PLAN.json --cell=K [--DJ=4] [--N1=256] [--N2=64] [--FB=120] [--PREC=160]
       [--rho=0.01,0.02,0.03] [--out=FILE.json]
"""
import json
import math
import os
import sys
import time

import mpmath as mp
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hd11964_model as HM  # noqa: E402
import prod2_hp as PH  # noqa: E402  (reads --FB, --SB from argv at import)

opt = PH.opt


def build_P(plan, K, DE, N1, N2):
    """P's exact DFT on the cell K of the plan: complex coefficients (monomial t, k_c index, k_b >= 0)."""
    m = HM.Model(dps=80)
    mp.mp.prec = int(opt("PREC", "160"))
    nu = [HM.R(x) for x in m.nu]
    mu = HM.R(m.mu)
    cq = PH.plan_cells(plan)[K]
    Lc = [HM.R(cq["c"][0]), HM.R(cq["c"][1])]
    xi_c, eta_c = HM.R(cq["c"][2]), HM.R(cq["c"][3])
    cb = (HM.R(cq["c"][4]), HM.R(cq["c"][5]))
    h = [HM.R(x) for x in cq["h"]]
    rot = (HM.R(cq["a"]), HM.R(cq["b"]))
    S3, S6 = PH.Space(3, DE), PH.Space(6, DE)
    jc = [PH.chart(S3, nu[0], 2 * mp.pi * g / N1, Lc[0], xi_c, eta_c, (h[0], h[2], h[3])) for g in range(N1)]
    jb = [PH.chart(S3, nu[1], 2 * mp.pi * g / N2, Lc[1], cb[0], cb[1], (h[1], h[4], h[5]), rot) for g in range(N2)]
    Q = [[PH.embed([J[k] for J in jc], S6, PH.CMAP, 0, N1, N2) for k in range(4)],
         [PH.embed([J[k] for J in jb], S6, PH.BMAP, 1, N1, N2) for k in range(4)]]
    del jc, jb
    qc, pc = Q[0][:2], Q[0][2:]
    qb, pb = Q[1][:2], Q[1][2:]
    Px, Py = pc[0] + pb[0], pc[1] + pb[1]
    dx, dy = qc[0] - qb[0], qc[1] - qb[1]
    del Q, qc, pc, qb, pb
    kin = Px.mul(Px) + Py.mul(Py)
    del Px, Py
    r2 = dx.mul(dx) + dy.mul(dy)
    del dx, dy
    ONE = PH.ONE
    a0 = r2.c[0]
    inv0 = (ONE * ONE) // a0
    isq = (ONE * ONE) // PH.vec_isqrt(a0 * ONE)
    coefs = [isq]
    for k in range(1, DE + 1):
        bk = mp.binomial(-0.5, k) / mp.binomial(-0.5, k - 1)
        coefs.append((((coefs[-1] * inv0) >> PH.FB) * PH.fx(bk)) >> PH.FB)
    g = r2.series(coefs)
    del r2
    f = PH.FJ(S6, [(a >> 1) for a in kin.c], kin.deg) - g.smul(PH.fx(nu[0] * nu[1]))
    del kin, g
    P = f.smul(PH.fx(mu))
    del f
    Pg = np.array([np.broadcast_to(np.asarray(a, dtype=object), (N1, N2)).copy() if isinstance(a, np.ndarray)
                   else np.full((N1, N2), a, dtype=object) for a in P.c])
    del P
    dft = PH.DFT(N1, N2)
    kfull = [k if k < N1 // 2 else k - N1 for k in range(N1)]
    Pre, Pim = dft.forward(Pg, kfull)
    del Pg
    sc = 2.0 ** -PH.FB
    Pc = (np.vectorize(float)(Pre) + 1j * np.vectorize(float)(Pim)) * sc
    return dict(S6=S6, Pc=Pc, kfull=kfull, K2=Pc.shape[2], nu=[float(x) for x in nu],
                L=[float(x) for x in Lc], h=[float(x) for x in h], cell=cq)


def inv_series(kc, kb, nu, L, hL, D):
    """Bivariate Taylor coefficients g[(a, b)] of 1/s(u), s = k_c omega_c(L_c + h_c u_0) + k_b omega_b(L_b + h_b u_1),
    a + b <= D, vectorised over the modes (kc, kb arrays)."""
    om = [[nu[j] ** 3 * float(mp.binomial(-3, m)) * L[j] ** (-3 - m) * hL[j] ** m for m in range(D + 1)]
          for j in range(2)]
    s = {(m, 0): kc * om[0][m] for m in range(1, D + 1)}
    s.update({(0, m): kb * om[1][m] for m in range(1, D + 1)})
    s0 = kc * om[0][0] + kb * om[1][0]
    g = {(0, 0): 1.0 / s0}
    for n in range(1, D + 1):
        for a in range(n + 1):
            b = n - a
            acc = 0.0
            for i in range(1, a + 1):
                acc = acc + s[(i, 0)] * g[(a - i, b)]
            for j in range(1, b + 1):
                acc = acc + s[(0, j)] * g[(a, b - j)]
            g[(a, b)] = -acc / s0
    return g, s0


def main():
    plan = opt("plan", "")
    K = int(opt("cell", "49"))
    DJ = int(opt("DJ", "4"))
    DE = DJ + 1
    Kc, Kb = int(opt("Kc", "80")), int(opt("Kb", "20"))
    N1, N2 = int(opt("N1", "256")), int(opt("N2", "64"))
    rhos = [float(x) for x in opt("rho", "0.01,0.02,0.03").split(",")]
    R = float(opt("R", "8"))
    t0 = time.time()
    cache = opt("cache", "")
    if cache and os.path.exists(cache):
        z = np.load(cache, allow_pickle=True)
        B = z["B"].item()
        B["S6"] = PH.Space(6, DE)
    else:
        B = build_P(plan, K, DE, N1, N2)
        if cache:
            np.savez(cache, B=np.array({k: v for k, v in B.items() if k != "S6"}, dtype=object))
    t1 = time.time()
    print("P and its DFT: %.1fs" % (t1 - t0), flush=True)
    S6, Pc, kfull, K2 = B["S6"], B["Pc"], B["kfull"], B["K2"]
    deg = np.array(S6.deg)
    kc = np.array(kfull, dtype=float).reshape(-1, 1)
    kb = np.arange(K2, dtype=float).reshape(1, -1)
    ksz = np.abs(kc) + kb                                       # |k|_1
    wfull = np.where(kb > 0, 2.0, 1.0) * np.ones_like(kc)      # the half plane k_b >= 0 stands for both signs
    inbox = (np.abs(kc) <= Kc) & (kb <= Kb)
    inS = inbox & ~((kc == 0) & (kb == 0))
    absP = np.abs(Pc)                                           # (M, N1, K2)

    def wnorm(mask_t, mask_k, rho):
        wt = wfull * np.exp(2 * math.pi * rho * ksz) * mask_k
        return float(np.einsum("tab,ab->", absP[mask_t], wt))

    # the half-plane modes of S (k_b > 0, or k_b = 0 and k_c > 0), each standing for k and -k
    half = inS & ((kb > 0) | (kc > 0))
    ia, ib = np.nonzero(half)
    kcs, kbs = kc[ia, 0], kb[0, ib]
    ks1 = np.abs(kcs) + kbs
    nu, L, h = B["nu"], B["L"], B["h"]
    # 1/(k.omega): Taylor to degree 2 DJ (the part beyond DJ is reported as a check of eps)
    g, s0 = inv_series(kcs, kbs, nu, L, h[:2], 2 * DJ)
    dev = [nu[j] ** 3 / L[j] ** 3 * ((1 - h[j] / L[j]) ** -3 - 1) for j in range(2)]
    Bk = 1.0 / (np.abs(s0) - np.abs(kcs) * dev[0] - kbs * dev[1])
    assert np.all(Bk > 0), "a divisor may vanish on the complex polydisc"
    # Cauchy: |g_ab| <= M_R R^-(a+b) on the polydisc of radius R; the best admissible R per mode
    epsk = np.full(kcs.shape, np.inf)
    for Rc in (1.25, 1.5, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64):
        if max(Rc * h[j] / L[j] for j in range(2)) >= 1:
            continue
        devR = [nu[j] ** 3 / L[j] ** 3 * ((1 - Rc * h[j] / L[j]) ** -3 - 1) for j in range(2)]
        den = np.abs(s0) - np.abs(kcs) * devR[0] - kbs * devR[1]
        bound = np.where(den > 0, 1.0 / np.where(den > 0, den, 1.0), np.inf) * sum(
            (n + 1) * Rc ** -n for n in range(DJ + 1, 400))
        epsk = np.minimum(epsk, bound)
    assert np.all(np.isfinite(epsk))
    print("h/L", [h[j] / L[j] for j in range(2)], "B_max %.3e eps_max %.3e" % (Bk.max(), epsk.max()), flush=True)
    eps_num = sum(np.abs(g[(a, n - a)]) for n in range(DJ + 1, 2 * DJ + 1) for a in range(n + 1))
    # p_k (degree <= DJ, 6 variables) and the product p_k q_k
    MJ_ = S6.M(DJ)
    pk = Pc[:MJ_, ia, ib]                                       # (M_DJ, #half modes)
    l1p = np.abs(pk).sum(axis=0)
    prod = {}
    for t in range(MJ_):
        mon = S6.mons[t]
        for (a, b), ga in g.items():
            if a + b > DJ:
                continue
            e = (mon[0] + a, mon[1] + b) + tuple(mon[2:])
            prod[e] = prod.get(e, 0) + pk[t] * ga
    l1c = sum(np.abs(v) for e, v in prod.items() if sum(e) <= DJ)       # |c_k|_1
    l1t = sum(np.abs(v) for e, v in prod.items() if sum(e) > DJ)        # |p_k q_k - c_k|_1
    # per-degree weighted norms of P (all modes) and the model remainder r_P(rho)
    out = dict(cell=K, slab=B["cell"]["slab"], grid=[N1, N2], DJ=DJ, Kc=Kc, Kb=Kb, FB=PH.FB, R=R,
               modes_S=int(inS.sum()), seconds_P=t1 - t0, rho={})
    for rho in rhos:
        Nd = [wnorm(deg == d, np.ones_like(inbox), rho) for d in range(DE + 1)]
        gam = Nd[DE] / Nd[DE - 1]
        beyond = Nd[DE] * gam / (1 - gam) if gam < 1 else float("inf")
        outbox = wnorm(deg <= DJ, ~inbox, rho)
        rP = Nd[DE] + beyond + outbox
        e = np.exp(2 * math.pi * rho * ks1)
        A = 2 * float((e * rP * Bk).sum())
        Bt = 2 * float((e * l1p * epsk).sum())
        Ct = 2 * float((e * l1t).sum())
        rec = dict(N_degree=Nd, ratio=gam, beyond=beyond, outbox=outbox, r_P=rP,
                   radius_2a=dict(rPB=A, peps=Bt, trunc=Ct, total=A + Bt + Ct),
                   chi1_norm_on_strip=2 * float((e * l1c).sum()))
        for rhop in (0.0, rho / 2):
            ep = np.exp(2 * math.pi * rhop * ks1)
            Ad = 2 * float((ep / e * rP * Bk).sum())
            Bd = 2 * float((ep * l1p * epsk).sum())
            Cd = 2 * float((ep * l1t).sum())
            rec["radius_2b_rho'=%g" % rhop] = dict(rPB=Ad, peps=Bd, trunc=Cd, total=Ad + Bd + Cd,
                                                   chi1_norm=2 * float((ep * l1c).sum()))
        out["rho"]["%g" % rho] = rec
        print("rho %g: N_d %s  r_P %.3e  (2a) %.3e  (2b, rho'=0) %.3e  |chi1| %.3e" % (
            rho, ["%.2e" % x for x in Nd], rP, A + Bt + Ct, rec["radius_2b_rho'=0"]["total"],
            rec["radius_2b_rho'=0"]["chi1_norm"]), flush=True)
    # ---- the tails (2d): |T_i| <= sum_{T \\ S} |k_i| |p_k|_1 + r_P tailWeight; the model's box T = S + {0}, so the
    # first sum vanishes. tailWeight by the closed form of `tailWeight_box_le` (isotropic strip rho), and, for
    # comparison, the same product form on an anisotropic strip (rho_c, rho_b) with r_P measured there.
    def geo(q, K):
        s0 = (1 + q) / (1 - q)
        s1 = 2 * q / (1 - q) ** 2
        t0 = 2 * q ** (K + 1) / (1 - q)
        t1 = 2 * q ** (K + 1) * ((K + 1) - K * q) / (1 - q) ** 2
        return s0, s1, t0, t1

    def wbound(qc, qb):
        s0c, s1c, t0c, t1c = geo(qc, Kc)
        s0b, s1b, t0b, t1b = geo(qb, Kb)
        return [t1c * s0b + s1c * t0b, t0c * s1b + s0c * t1b]

    def wnorm2(mask_t, mask_k, rc, rb):
        wt = wfull * np.exp(2 * math.pi * (rc * np.abs(kc) + rb * kb)) * mask_k
        return float(np.einsum("tab,ab->", absP[mask_t], wt))

    def rP2(rc, rb):
        Nd = [wnorm2(deg == d, np.ones_like(inbox), rc, rb) for d in range(DE + 1)]
        gam = Nd[DE] / Nd[DE - 1]
        beyond = Nd[DE] * gam / (1 - gam) if gam < 1 else float("inf")
        return Nd[DE] + beyond + wnorm2(deg <= DJ, ~inbox, rc, rb)

    # the Lean bounds weigh by sigma_j < rho_j (`tails_HD_of_cell_aniso`): sigma = 0.98 rho here
    tails = []
    grid = [(r, r) for r in rhos] + [(rc, rb) for rc in (0.02, 0.025, 0.03, 0.035)
                                     for rb in (0.1, 0.15, 0.2, 0.25)]
    for rc, rb in grid:
        rp = rP2(rc, rb)
        W = wbound(math.exp(-2 * math.pi * 0.98 * rc), math.exp(-2 * math.pi * 0.98 * rb))
        tails.append(dict(rho_c=rc, rho_b=rb, sigma=[0.98 * rc, 0.98 * rb], r_P=rp, weight=W,
                          T_bound=[rp * W[0], rp * W[1]]))
        print("tails rho_c %g rho_b %g: r_P %.3e weight %s bound T_c %.3e T_b %.3e" % (
            rc, rb, rp, ["%.3e" % x for x in W], rp * W[0], rp * W[1]), flush=True)
    out["tails"] = tails
    # the tail itself, from the data (all degrees <= DE, real theta, the unit polydisc): sum_{k not in S} |k_i||P_k|_1
    aP = absP.sum(axis=0)
    out["tail_data"] = [float((wfull * np.abs(kc) * aP * ~inS).sum()), float((wfull * kb * aP * ~inS).sum())]
    print("tail from the data (degree <= %d): T_c %.3e T_b %.3e" % (DE, *out["tail_data"]), flush=True)
    out["B_max"] = float(Bk.max())
    out["eps_max_cauchy"] = float(epsk.max())
    out["eps_max_numeric"] = float(eps_num.max())
    out["sum_B"] = 2 * float(Bk.sum())
    path = opt("out", "")
    if path:
        with open(path, "w") as fh:
            json.dump(out, fh, indent=1)
        print("wrote", path)


if __name__ == "__main__":
    main()
