"""SJSU secular Hamiltonian at order two in the masses (SLG13 section 3, GLS17 section 2.2).

Pipeline, with f = f0 + f1 the first-order perturbation (f0: L-independent; f1: linear in L),
Z0 = n*.L + K2(L), K2 = sum_j (1/2) K2pp_j L_j^2, K2pp_j = -3 n*_j/Lambda*_j:

  chi_1 : n*.d_lambda X1 + [f0]_{0<|k|<=8, deg<=D1} = 0                 (SLG13 eq. 6)
  hat-h1 = f1 + {X1, K2}       (order-one, L-linear part of exp(L_X1) H)
  chi_2 : n*.d_lambda X2 + [hat-h1]_{0<|k|<=8, deg<=D1} = 0             (SLG13 eq. 7)
  Order-two part of H^(O2) = exp(L_X2) exp(L_X1) H^(T), truncated to L-degree <= 1:
      H2 = {X1, f} - 1/2 {X1, f0T} + 1/2 {X1, {X1, K2}}
           + {X2, f - f0T + {X1, K2}} - 1/2 {X2, hat-h1T}
  Secular part at L = 0:   <f0> + <H2>|_{L=0}                            (SLG13 eq. 9)
  Resonant step (SLG13 eqs. 10-12): h_res = [H2]_{+-(3,-5,-7)};
      X_res : n*.d_lambda X_res + [h_res]_{L=0, deg<=9} = 0
      mu^4 terms: < 1/2 {X_res, {X_res, K2}} + {X_res, h_res_1} + w {X_res, h_res_0} >,
      with w = 1/2 as printed in (12) ('printed') or w = 1 on the part of h_res_0 that X_res
      does not remove ('lie', the exact second-order Lie coefficient).

All brackets are evaluated exactly (no magnitude cutoffs) in the chosen numeric back end and
truncated only by the source's rules: degree <= D in (xi, eta), |k| <= 16, L-degree <= 1.
"""
from __future__ import annotations

import time
from fractions import Fraction

import mpmath
import numpy as np

from expansion import first_order_hamiltonian
from kepler_series import universal_series
from sjsu_common import Backend, physical_constants, RES
from sparse import SP, bracket


def nstar_split(f, c, bk, mode):
    """Frequencies used in the homological equations and the perturbation without the moved term.

    mode 'kepler'    : n*_j = Kepler frequency at Lambda*_j; f unchanged.
    mode 'corrected' : n*_j = Kepler frequency + coefficient of L_j in f at k = 0, (xi, eta) = 0
                       (the "term linear in the actions and independent of all the other canonical
                       variables", SLG13 eq. (5)); that term is removed from f.
    """
    nK = [bk.real(x) for x in c['n']]
    if mode == 'kepler':
        return nK, f, [mpmath.mpf(0)] * 3
    if mode != 'corrected':
        raise ValueError(mode)
    sel = f.is_secular() & (f.degree() == 0) & (f.L > 0)
    corr = [mpmath.mpf(0)] * 3
    for l, cc in zip(f.L[sel], f.C[sel]):
        corr[int(l) - 1] += bk.to_mpc(cc).real
    nvec = [bk.real(c['n'][j] + corr[j]) for j in range(3)]
    return nvec, f.select(~sel), corr


def compute_secular(astar, bk: Backend, D=18, D1=6, KF=16, KF_CHI=8, res=True, res_weight='printed',
                    log=print, U=None, return_intermediates=False, nstar='kepler'):
    t0 = time.time()
    c = physical_constants(astar)
    if U is None:
        U = universal_series(D, max(17, (KF + D) // 2 + 1))
    if res:
        hf = None
    else:
        def hf(Hi, Hj):
            return (np.abs(Hi) + np.abs(Hj)) <= KF_CHI
    log(f'[secular] first-order expansion D={D} KF={KF} backend={bk.name}')
    f = first_order_hamiltonian(bk, U, c, D=D, KF=KF, harm_filter=hf, log=log)
    log(f'[secular] f: {len(f)} terms ({time.time()-t0:.1f}s)')
    nvec, f, ncorr = nstar_split(f, c, bk, nstar)
    K2pp = [bk.real(x) for x in c['K2pp']]
    half = bk.real(Fraction(1, 2))

    f0 = f.select(f.L == 0)
    kn = f0.knorm()
    f0T = f0.select((kn > 0) & (kn <= KF_CHI) & (f0.degree() <= D1))
    X1 = f0T.homological(nvec)
    X1K2 = X1.bracket_K2(K2pp)
    f1 = f.select(f.L > 0)
    h1 = f1 + X1K2
    kn1 = h1.knorm()
    h1T = h1.select((kn1 > 0) & (kn1 <= KF_CHI) & (h1.degree() <= D1))
    X2 = h1T.homological(nvec)
    log(f'[secular] X1: {len(X1)} terms, X2: {len(X2)} terms ({time.time()-t0:.1f}s)')

    def H2_restricted(targets, maxdeg, Lmask):
        parts = []
        parts.append(bracket(X1, f, targets, maxdeg, 1, Lmask))
        parts.append(bracket(X1, f0T, targets, maxdeg, 1, Lmask).scaled(-half))
        parts.append(bracket(X1, X1K2, targets, maxdeg, 1, Lmask).scaled(half))
        rest = SP.concat(bk, [f, f0T.scaled(bk.real(-1)), X1K2]).consolidate()
        parts.append(bracket(X2, rest, targets, maxdeg, 1, Lmask))
        parts.append(bracket(X2, h1T, targets, maxdeg, 1, Lmask).scaled(-half))
        return SP.concat(bk, parts).consolidate()

    sec1 = f0.average()
    # split the order-two secular part into its chi_1 and chi_2 pieces for diagnostics
    zero = [(0, 0, 0)]
    s2a = SP.concat(bk, [bracket(X1, f, zero, D, 1, {0}),
                         bracket(X1, f0T, zero, D, 1, {0}).scaled(-half),
                         bracket(X1, X1K2, zero, D, 1, {0}).scaled(half)]).consolidate()
    rest0 = SP.concat(bk, [f0, f0T.scaled(bk.real(-1))]).consolidate()
    s2b = bracket(X2, rest0, zero, D, 1, {0})
    log(f'[secular] order-two secular: chi1 part {len(s2a)}, chi2 part {len(s2b)} terms ({time.time()-t0:.1f}s)')
    out = {'first': sec1, 'second_chi1': s2a, 'second_chi2': s2b, 'consts': c,
           'nstar': [bk.to_mpc(x).real for x in nvec], 'nstar_correction': ncorr}
    if res:
        kap = tuple(RES)
        mkap = tuple(-x for x in RES)
        hres = H2_restricted([kap, mkap], min(D, 11), {0, 1})
        hres0 = hres.select(hres.L == 0)
        hres1 = hres.select((hres.L > 0) & (hres.degree() <= 9))
        hres0T = hres0.select(hres0.degree() <= 9)
        Xr = hres0T.homological(nvec)
        XrK2 = Xr.bracket_K2(K2pp)
        p1 = bracket(Xr, XrK2, zero, D, 1, {0}).scaled(half)
        p2 = bracket(Xr, hres1, zero, D, 1, {0})
        if res_weight == 'printed':
            p3 = bracket(Xr, hres0, zero, D, 1, {0}).scaled(half)
        elif res_weight == 'lie':
            p3 = SP.concat(bk, [bracket(Xr, hres0T, zero, D, 1, {0}).scaled(half),
                                bracket(Xr, hres0.select(hres0.degree() > 9), zero, D, 1, {0})]).consolidate()
        else:
            raise ValueError(res_weight)
        s4 = SP.concat(bk, [p1, p2, p3]).consolidate()
        out['res'] = s4
        out['res_info'] = {'hres0_terms': len(hres0), 'hres1_terms': len(hres1), 'Xres_terms': len(Xr),
                           'kappa_dot_n': bk.to_mpc(kap[0] * nvec[0] + kap[1] * nvec[1] + kap[2] * nvec[2]).real}
        log(f'[secular] resonant step: h_res {len(hres)} terms, X_res {len(Xr)}, mu^4 part {len(s4)} '
            f'({time.time()-t0:.1f}s)')
    total = SP.concat(bk, [out['first'], out['second_chi1'], out['second_chi2']] + ([out['res']] if res else []))
    out['total'] = total.consolidate()
    if return_intermediates:
        out['f'] = f
        out['X1'] = X1
        out['X2'] = X2
    log(f'[secular] done: {len(out["total"])} complex secular terms ({time.time()-t0:.1f}s)')
    return out


# ----------------------------------------------------------------- real form
def _planet_real(p, q):
    """(xi - i eta)^p (xi + i eta)^q as {(a, b): Gaussian integer (re, im)} with xi^a eta^b."""
    from math import comb
    poly = {}
    # (xi - i eta)^p = sum_r C(p,r) xi^{p-r} (-i eta)^r ; (xi + i eta)^q = sum_s C(q,s) xi^{q-s} (i eta)^s
    ipow = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    for r in range(p + 1):
        for s in range(q + 1):
            # (-i)^r i^s = i^{s - r} * (-1)^r ... use i^{(s + 3r) mod 4}
            re, im = ipow[(s + 3 * r) % 4]
            cf = comb(p, r) * comb(q, s)
            key = (p - r + q - s, r + s)
            a, b = poly.get(key, (0, 0))
            poly[key] = (a + cf * re, b + cf * im)
    return poly


def to_real(sec: SP):
    """Secular complex series (K = 0, L = 0) -> {(a1,a2,a3,b1,b2,b3): (re mpf, im mpf)}
    for monomials xi_1^a1 xi_2^a2 xi_3^a3 eta_1^b1 eta_2^b2 eta_3^b3, using
    z_j^p zbar_j^q = 2^{-(p+q)/2} (xi_j - i eta_j)^p (xi_j + i eta_j)^q."""
    bk = sec.bk
    cache = {}
    out = {}
    for e, cc in zip(sec.E, sec.C):
        cm = bk.to_mpc(cc)
        d = int(sum(e))
        assert d % 2 == 0
        polys = []
        for j in range(3):
            pq = (int(e[2 * j]), int(e[2 * j + 1]))
            if pq not in cache:
                cache[pq] = _planet_real(*pq)
            polys.append(cache[pq])
        fac = cm / mpmath.mpf(2) ** (d // 2)
        for (a1, b1), g1 in polys[0].items():
            for (a2, b2), g2 in polys[1].items():
                re12 = g1[0] * g2[0] - g1[1] * g2[1]
                im12 = g1[0] * g2[1] + g1[1] * g2[0]
                for (a3, b3), g3 in polys[2].items():
                    re = re12 * g3[0] - im12 * g3[1]
                    im = re12 * g3[1] + im12 * g3[0]
                    if re == 0 and im == 0:
                        continue
                    key = (a1, a2, a3, b1, b2, b3)
                    out[key] = out.get(key, 0) + fac * mpmath.mpc(re, im)
    return out
