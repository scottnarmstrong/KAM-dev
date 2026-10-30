"""Attempt to reproduce the FH25 thresholds ||eta^DK|| = 1e-38, ||eta^N|| = 1e-44 (FH25 Sec. 5) from FH24 Appendix B.
Usage: python3 -I fh25run.py
"""
import math, os, sys, numpy as np
from mpmath import gammainc
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fh24consts as F

tau, gam = F.tau, F.gam
shells = np.load(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'shells1500.npy'))
M = len(shells) - 1
Z = F.zeta2(2**tau)


def cR_sharp(dl):
    S = float(np.sum(shells * np.exp(-2 * np.arange(M + 1) * dl)))
    tail = 2 ** (2 * tau + 1) * Z / gam**2 * (2 * dl) ** (-2 * tau) * float(gammainc(2 * tau + 1, 2 * dl * (M + 1)))
    return min(gam * dl**tau * math.sqrt(8 * (S + tail)), F.cRhat_2pi)


def rus(dl, rho, mode):
    if mode == 'uniform':
        return F.cRhat_2pi, F.c1fac * F.cRhat_2pi, F.cRhat_2pi
    return cR_sharp(dl), F.c1fac * cR_sharp(tau / (tau + 1) * dl), cR_sharp(rho)


def fmt(t):
    return ', '.join(f'{k}={v:.2e}' for k, v in sorted(t.items(), key=lambda kv: -kv[1]))


def direct(mode, nu, kap, vk, dist, cTh, cDTh, rho=0.1, rinf=0.0):
    dl = (rho - rinf) / 6
    sig = {k: v * F.SIGF for k, v in F.norms0.items()}
    cR, c1R, cRr = rus(dl, rho, mode)
    c = F.consts(rho, dl, cR, c1R, cRr, sig, nu, kap, vk, cTh, cDTh)
    a = (rho - rinf) / (rho - 3 * dl - rinf)
    gd = gam * dl**tau
    t = F.C_terms(c, F.norms0, sig, dist, nu, kap, vk, gd, a)
    C = max(t.values())
    eps_max = gam * dl ** (tau + 1) / C
    return c, t, C, eps_max, gd


def il_run(etaL, etaN, mode, nu, kap, vk, dist, cTh, cDTh, steps=10, rho=0.1, split=False, verbose=False):
    """Run `steps` Iterative-Lemma steps with bites delta_j = rho_j/6 (rho_{j+1} = rho_j/2), then the KAM theorem."""
    sig = {k: v * F.SIGF for k, v in F.norms0.items()}
    norms = dict(F.norms0)
    dst = dist
    r = rho
    for j in range(steps):
        dl = r / 6
        gd = gam * dl**tau
        cR, c1R, cRr = rus(dl, r, mode)
        c = F.consts(r, dl, cR, c1R, cRr, sig, nu, kap, vk, cTh, cDTh)
        eps = max(etaL, etaN / gd)
        x = eps / (gam * dl ** (tau + 1))
        if any(norms[k] >= sig[k] for k in norms) or dst <= 0:
            return False, j, 'margin exhausted'
        t = F.chat_terms(c, norms, sig, dst, nu, vk, gd)
        if split:
            # sharper: drifts with separate L/N constants  C^L etaL/(g d^{t+1}) + C^N etaN/(g^2 d^{2t+1})
            xL, xN = etaL / (gam * dl ** (tau + 1)), etaN / (gam**2 * dl ** (2 * tau + 1))
            drift = dict(DK=c['CdDKbbL'] * xL + c['CdDKbbN'] * xN, DKt=c['CdDKtbbL'] * xL + c['CdDKtbbN'] * xN,
                         B=c['CdBL'] * xL + c['CdBN'] * xN, N=c['CdNL'] * xL + c['CdNN'] * xN,
                         Nt=c['CdNtL'] * xL + c['CdNtN'] * xN, Tinv=c['CdTiL'] * xL + c['CdTiN'] * xN)
            ok = all(norms[k] + drift[k] < sig[k] for k in drift) and max(t['sym'], t['xiL'], t['dist'], t['vk']) * x < 1
            worst = max(((norms[k] + drift[k]) / sig[k], k) for k in drift)
        else:
            drift = {k: getattr_c(c, k) * x for k in ('DK', 'DKt', 'B', 'N', 'Nt', 'Tinv')}
            ok = max(t.values()) * x < 1
            worst = (max(t.values()) * x, max(t, key=t.get))
        if verbose:
            print(f' step {j}: rho={r:.3e} delta={dl:.3e} etaL={etaL:.2e} etaN={etaN:.2e} eps={eps:.2e} '
                  f'Chat*x={max(t.values())*x:.2e} worst={worst} QL={c["QbbL"]:.2e} QN={c["QbbN"]:.2e} ok={ok}')
        if not ok:
            return False, j, worst
        for k in drift:
            norms[k] += drift[k]
        dst -= c['CdKbb'] * eps / gd
        etaN, etaL = c['QbbN'] / dl * eps**2, c['QbbL'] / (gam * dl ** (tau + 1)) * eps**2
        r = r - 3 * dl
    if any(norms[k] >= sig[k] for k in norms) or dst <= 0:
        return False, steps, "margin exhausted"
    # KAM theorem at the end, delta = r/6, rho_inf = 0
    dl = r / 6
    gd = gam * dl**tau
    cR, c1R, cRr = rus(dl, r, mode)
    c = F.consts(r, dl, cR, c1R, cRr, sig, nu, kap, vk, cTh, cDTh)
    t = F.C_terms(c, norms, sig, dst, nu, kap, vk, gd, 2.0)
    eps = max(etaL, etaN / gd)
    val = max(t.values()) * eps / (gam * dl ** (tau + 1))
    if verbose:
        print(f' KAM: rho={r:.3e} eps={eps:.2e} C={max(t.values()):.2e} C*eps/(g d^(t+1))={val:.2e}')
    return val < 1, steps, val


def getattr_c(c, k):
    return dict(DK=c['CdDKbb'], DKt=c['CdDKtbb'], B=c['CdB'], N=c['CdN'], Nt=c['CdNt'], Tinv=c['CdTi'])[k]


if __name__ == '__main__':
    base = dict(nu=0.1, kap=0.5, vk=1e-25, dist=0.01, cTh=2 * F.cDXh, cDTh=2 * F.cD2Xh)
    print(f'gamma delta^tau = {gam*(0.1/6)**tau:.3e}, gamma delta^(tau+1) = {gam*(0.1/6)**(tau+1):.3e}')
    print(f'cRhat (1-periodic, FH24 L.2.14) = {F.cRhat_1per:.4f}; transported to 2pi angles = {F.cRhat_2pi:.3f}; c1 factor = {F.c1fac:.3f}')
    for mode in ('uniform', 'sharp'):
        cR, c1R, cRr = rus(0.1 / 6, 0.1, mode)
        print(f'\n=== mode {mode}: cR(delta)={cR:.3e} c1R(delta)={c1R:.3e} cR(rho)={cRr:.3e}')
        c, t, C, epsmax, gd = direct(mode, **base)
        print(' direct theorem C terms:', fmt(t))
        print(f' C = {C:.3e}; eps threshold = {epsmax:.3e}; i.e. etaL < {epsmax:.2e} and etaN < {epsmax*gd:.2e}')
        print(f' Q_L={c["QbbL"]:.3e} parts {fmt(c["QbbL_parts"])}')
        print(f' Q_N(bar)={c["QbN"]:.3e} parts {fmt(c["QbN_parts"])}; Q_N(barbar)={c["QbbN"]:.3e}')
        print(f' CdT^L parts {fmt(c["CdTL_parts"])}; CdT^N parts {fmt(c["CdTN_parts"])}')
        print(f' CxN^L={c["CxNL"]:.3e} CxN^N={c["CxNN"]:.3e} CxL={c["CxL"]:.3e} CdKb={c["CdKb"]:.3e} CdKbb={c["CdKbb"]:.3e} CT={c["CT"]:.3e}')
        for split in (False, True):
            print(f' -- 10 IL steps + theorem, split={split}: feasible (log10 etaL, log10 etaN):')
            for lL in range(-30, -60, -2):
                row = []
                for lN in range(-34, -64, -2):
                    ok, j, w = il_run(10.0**lL, 10.0**lN, mode, steps=10, split=split, **base)
                    row.append('#' if ok else str(j))
                print(f'   etaL=1e{lL}: ' + ''.join(row) + '   (etaN = 1e-34 ... 1e-62 step 2)')
