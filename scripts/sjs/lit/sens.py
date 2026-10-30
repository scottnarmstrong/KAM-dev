import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fh24consts as F, fh25run as R


def thr(fun, lo=-80.0, hi=-20.0):
    """largest log10 x with fun(10^x) True (monotone), by bisection"""
    if not fun(10**lo):
        return float('nan')
    if fun(10**hi):
        return hi
    for _ in range(50):
        m = 0.5 * (lo + hi)
        if fun(10**m):
            lo = m
        else:
            hi = m
    return lo


def report(label, mode='sharp', **kw):
    base = dict(nu=0.1, kap=0.5, vk=1e-3, dist=0.01, cTh=2 * F.cDXh, cDTh=2 * F.cD2Xh)
    base.update(kw)
    c, t, C, epsmax, gd = R.direct(mode, **base)
    bind = max(t, key=t.get)
    tL_split = thr(lambda x: R.il_run(x, 0.0, mode, split=True, **base)[0])
    tN_split = thr(lambda x: R.il_run(1e-38, x, mode, split=True, **base)[0])
    tN0_split = thr(lambda x: R.il_run(0.0, x, mode, split=True, **base)[0])
    tL_max = thr(lambda x: R.il_run(x, 0.0, mode, split=False, **base)[0])
    print(f'{label:38s} direct: C={C:.1e} ({bind}) etaL<{epsmax:.1e} etaN<{epsmax*gd:.1e} | IL+KAM max-form: etaL<1e{tL_max:.1f}, '
          f'etaN<1e{tL_max+math.log10(gd):.1f} | split: etaL<1e{tL_split:.1f} (etaN=0), etaN<1e{tN0_split:.1f} (etaL=0), '
          f'etaN<1e{tN_split:.1f} (etaL=1e-38)')


report('baseline sharp (guesses)')
report('baseline uniform cR', mode='uniform')
report('cTh=cDXh', cTh=F.cDXh)
report('cTh=cDXh, cDTh=cD2Xh', cTh=F.cDXh, cDTh=F.cD2Xh)
report('cTh=30 (CT~ actual torsion?)', cTh=30.0)
report('nu=0.01', nu=0.01)
report('kappa=0.1', kap=0.1)
report('kappa=0.9', kap=0.9)
for sf in (1e-12, 1e-10, 1e-8, 1e-6, 1e-4, 1e-2, 1e-1):
    F.SIGF = 1 + sf
    report(f'sigma = (1+{sf:g})*norm')
F.SIGF = 1 + 1e-10
for cd2 in (5e8, 5e10, 5e12):
    F.cD2Xh = cd2
    report(f'cD2Xh={cd2:g} (cDTh=2cD2Xh)', cDTh=2 * cd2)
F.cD2Xh = 5e10
