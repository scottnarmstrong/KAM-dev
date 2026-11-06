"""Tube measurement of the brackets {F_j, H} on T = {u = tau(phi) + v, |v_j| <= kappa delta_j}.

Used by torus2.py (measured, floating). For each delta:
  eta_j = sum_{v-monomials m, deg <= Lv} sum_k |G_{j,m,k}| (kappa delta)^m        (truncated series)
        + sum_{s + t > Lv} |F-derivative|_s |H-derivative|_t                       (dropped products)
        + sum_i |d_q F_j| tail(dH/dI_i) + |d_u F_j| tail(dH~/dq_i)                 (H beyond degree Lv)
with Fourier majorants of the grid compositions; the 'full' variant sums every grid coefficient
(including the float64 noise floor), 'band80' only |k|_1 <= 80. The tube-inclusion margin is
kappa delta_j - ||F_j - c_j - v_j|| - delta_j (boundary separation onto the F-faces).
"""
from __future__ import annotations

import numpy as np

DELTAS = [1e-9, 1e-8, 1e-7, 3e-7, 1e-6, 3e-6, 1e-5, 2e-5]


def _coef(v):
    G2 = v.shape[0]
    return np.fft.fft2(v) / (G2 * G2)


def _kabs(G2):
    k = np.rint(np.fft.fftfreq(G2, 1.0 / G2)).astype(int)
    K1, K2 = np.meshgrid(k, k, indexing='ij')
    return np.abs(K1) + np.abs(K2) + np.abs(K1 + K2)


# ---------------------------------------------------------------------------------------------
# Tail-aware measurement (torus2.py): truncated bracket series + dropped products + H tails.

def profile(series, kc=80):
    out = {}
    for m, v in series.items():
        a = np.abs(_coef(v))
        if not out:
            sel = _kabs(v.shape[0]) <= kc
        out[m] = (float(a.sum()), float(a[sel].sum()))
    return out


def _w(m, r):
    return r[0] ** m[0] * r[1] ** m[1] * r[2] ** m[2]


def maj(prof, r, band=0):
    return sum(p[band] * _w(m, r) for m, p in prof.items())


def degprof(prof, r, n, band=0):
    d = np.zeros(n)
    for m, p in prof.items():
        d[sum(m)] += p[band] * _w(m, r)
    return d


def _seq(al, bmin, bmax, r, lmax=80):
    import math
    s = np.empty(lmax + 1)
    b = 1.0
    for l in range(lmax + 1):
        lg = max((al - l) * math.log(bmin), (al - l) * math.log(bmax)) + l * math.log(r)
        s[l] = abs(b) * math.exp(lg) if b != 0.0 else 0.0
        b = b * (al - l) / (l + 1)
    return s


def deriv_tails(terms, Bmin, Bmax, r, Lv, hess):
    """Majorants of the v-degree > Lv parts of dH/dI_i and dH~/dq_i at radius r about B in [Bmin, Bmax]."""
    cache = {}

    def tail(al):
        if al not in cache:
            s = [_seq(al[j], Bmin[j], Bmax[j], r[j]) for j in range(3)]
            conv = np.convolve(np.convolve(s[0], s[1]), s[2])
            cache[al] = float(conv[Lv + 1:].sum())
        return cache[al]
    tI = [0.0, 0.0, 0.0]
    tH = [0.0, 0.0, 0.0]
    for e, c in terms:
        n = [e[j] + e[j + 3] for j in range(3)]
        k = [e[j] - e[j + 3] for j in range(3)]
        al = tuple(x / 2.0 for x in n)
        th = tail(al)
        for i in range(3):
            tH[i] += abs(k[i]) * abs(c) * th
            if n[i]:
                a2 = list(al)
                a2[i] -= 1
                tI[i] += al[i] * abs(c) * tail(tuple(a2))
    tq = [tH[i] + sum(hess[i][l] * tI[l] for l in range(3)) for i in range(3)]
    return tI, tq


def inclusion_profile(Fu_j, j, cj):
    """m -> sum_k |coef of F_j - c_j - v_j| for the tube-inclusion margin (independent of delta)."""
    out = {}
    for m, v in Fu_j.items():
        b = _coef(v)
        if sum(m) == 1 and m[j] == 1:
            b[0, 0] -= 1.0
        elif sum(m) == 0:
            b[0, 0] -= cj
        out[m] = float(np.abs(b).sum())
    return out


def observable_profiles(G_j, dqF_j, dpF_j, Fu_j, j, cj):
    """The small per-observable summaries measure_profiles needs (the grid series can then be freed)."""
    return {'G': profile(G_j), 'dqF': [profile(s) for s in dqF_j], 'dpF': [profile(s) for s in dpF_j],
            'inc': inclusion_profile(Fu_j, j, cj)}


def measure2(Gs, Fu, dqFs, dpF, dIu, dqu, c, terms, Bmin, Bmax, hess, Lv, kappa, dw,
             deltas=DELTAS, log=print):
    obs = [observable_profiles(Gs[j], dqFs[j], dpF[j], Fu[j], j, c[j]) for j in range(3)]
    return measure_profiles(obs, [profile(s) for s in dIu], [profile(s) for s in dqu], terms, Bmin,
                            Bmax, hess, Lv, kappa, dw, deltas, log)


def measure_profiles(obs, PdI, Pdq, terms, Bmin, Bmax, hess, Lv, kappa, dw, deltas=DELTAS, log=print):
    PG = [o['G'] for o in obs]
    PdqF = [o['dqF'] for o in obs]
    PdpF = [o['dpF'] for o in obs]
    n = Lv + 1
    rows = []
    for delta in deltas:
        d = delta * np.array(dw)
        r = kappa * d
        if np.any(r >= np.array(Bmin)):
            log(f'delta={delta:.0e}: tube reaches I_j = 0; skipped')
            continue
        tI, tq = deriv_tails(terms, Bmin, Bmax, r, Lv, hess)
        row = {'delta': delta, 'd': d.tolist()}
        etaF, etaB, parts = [], [], []
        for j in range(3):
            full = maj(PG[j], r, 0)
            band = maj(PG[j], r, 1)
            dropped = 0.0
            ht = 0.0
            for i in range(3):
                for A, B in ((PdqF[j][i], PdI[i]), (PdpF[j][i], Pdq[i])):
                    a = degprof(A, r, n)
                    b = degprof(B, r, n)
                    dropped += sum(a[s] * b[t] for s in range(n) for t in range(n) if s + t > Lv)
                ht += maj(PdqF[j][i], r) * tI[i] + maj(PdpF[j][i], r) * tq[i]
            etaF.append(full + dropped + ht)
            etaB.append(band + dropped + ht)
            parts.append({'trunc_full': full, 'trunc_band80': band, 'dropped_products': dropped,
                          'H_tail': ht, 'by_degree_band80': degprof(PG[j], r, n, 1).tolist()})
        incl = []
        for j in range(3):
            rest = sum(a * _w(m, r) for m, a in obs[j]['inc'].items())
            incl.append(float(r[j] - rest - d[j]))
        row.update(eta_full=etaF, eta_band80=etaB, parts=parts, inclusion_margin=incl,
                   T_full=float(min((d[j] / 2) / etaF[j] for j in range(3))),
                   T_band80=float(min((d[j] / 2) / etaB[j] for j in range(3))))
        rows.append(row)
        bd = parts[2]['by_degree_band80']
        log(f"delta={delta:.0e}: T_full={row['T_full']:.2e} T_band80={row['T_band80']:.2e} yr; "
            f"eta_full={['%.1e' % x for x in etaF]}; U parts: trunc {parts[2]['trunc_band80']:.1e} "
            f"dropped {parts[2]['dropped_products']:.1e} Htail {parts[2]['H_tail']:.1e}; "
            f"U by degree {' '.join('%.0e' % x for x in bd)}; incl {['%.0e' % x for x in incl]}")
    return rows
