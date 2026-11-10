#!/usr/bin/env python3
"""G3 driver: great-inequality (Stage-II) averaging in Stage-I variables at one slow point (research scratch).

Stage I: the keep52nr normal form of order NI with jets of degree M (so Z_s has degree M + 1 - s).  Stage-II input:
the 5:2-family-and-secular part of Z = Z_1 + ... + Z_NI (harmonics m(2,-5,0), m in Z), grade s for Z_s.  Stage II
normalizes every m != 0 (kept: k = 0 only) to order M with the same exact divisors m (2 n_J - 5 n_S)(Lambda).
Reported: Lambda_S and Lambda_J rate ladders of Stage II (remainder of the next grade), and eps52 at the point.
Mode --proxy reproduces E7 (Stage-II input = the 5:2 family and secular part of f only, divisor 'linear', nominal).
usage: stage2.py POINTS.json INDEX OUT.json [--grid 64,64,32] [--NI 3] [--M 6] [--proxy]
"""
import argparse, json, os, resource, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import jets, model as M, nf


def family(F):
    out = {}
    for sh, v in F.items():
        ks = nf.Engine.kvecs(_E, sh)
        kJ, kS, kU = ks
        m = ((5 * kJ + 2 * kS == 0) & (kU == 0))
        m = np.broadcast_to(m, sh)
        if sh[2] > 1:      # project 3-D components onto the J-S plane (k_U = 0 slice)
            v = v[:, :, :, :1]
            m = m[:, :, :1]
            sh2 = (sh[0], sh[1], 1)
        else:
            sh2 = sh
        if sh2[0] == 1 or sh2[1] == 1:
            # J-only or S-only components: only k = 0 belongs to the family
            pass
        w = np.where(m.reshape(sh2), v, 0)
        if sh2 != (_E.NG[0], _E.NG[1], 1):
            full = np.zeros((v.shape[0], _E.NG[0], _E.NG[1], 1), dtype=v.dtype)
            full[:, : sh2[0], : sh2[1], :] = w
            w = full
        key = (_E.NG[0], _E.NG[1], 1)
        out[key] = out[key] + w if key in out else w
    return out


def eps52(slow, ng):
    k = np.array([2, -5, 0])
    n = M.n_kep(slow[0])
    v = M.pair_f_float(0, 1, slow, ng)
    c = np.fft.fft2(v) / v.size
    amp = 2 * abs(c[2, -5 % v.shape[1]])
    nu = float(k @ M.N_NB)
    kAk = float(np.sum(k * k * 3 * n / slow[0]))
    return amp, amp * kAk / nu ** 2


def main():
    global _E
    ap = argparse.ArgumentParser()
    ap.add_argument('points'); ap.add_argument('index', type=int); ap.add_argument('out')
    ap.add_argument('--grid', default='64,64,32'); ap.add_argument('--NI', type=int, default=3)
    ap.add_argument('--M', type=int, default=6); ap.add_argument('--proxy', action='store_true')
    ap.add_argument('--quiet', action='store_true')
    a = ap.parse_args()
    t0, w0 = time.process_time(), time.time()
    ng = tuple(int(x) for x in a.grid.split(','))
    P = json.load(open(a.points))
    pt = P['nominal'] if a.index < 0 else P['points'][a.index]
    nom = P['nominal']
    slow = tuple(np.array(pt[k], float) for k in ('Lambda', 'xi', 'eta'))
    slow_nom = tuple(np.array(nom[k], float) for k in ('Lambda', 'xi', 'eta'))
    B1 = jets.Basis(9, 1)
    _, g_nom = nf.f_fourier(B1, slow_nom, ng, np.zeros(3), slow_nom[0])
    _, g_pt = nf.f_fourier(B1, slow, ng, np.zeros(3), slow[0])
    dn = M.DN_STAR + (g_pt - g_nom)
    B = jets.Basis(9, a.M)
    f, _ = nf.f_fourier(B, slow, ng, dn, slow[0])
    div = 'linear' if a.proxy else 'kepler'
    _E = nf.Engine(B, ng, slow, dn, divisor=div, keep='keep52nr', verbose=not a.quiet)
    if a.proxy:
        graded = {1: family(f)}
        stage1 = None
    else:
        lad1, H1 = _E.run(f, a.NI, D=a.M)
        graded = {s: family(_E.split(H1[s])[0]) for s in range(1, a.NI + 1)}
        stage1 = lad1
    E2 = nf.Engine(B, ng, slow, dn, divisor=div, keep='secular', verbose=not a.quiet)
    lad2, _ = E2.run(None, a.M, D=a.M, rate_obs=('LJ', 'LS'), graded=graded)
    for o in ('LJ', 'LS'):
        for r in range(1, len(lad2)):
            lad2[r][o]['gain_remainder'] = lad2[r - 1][o]['remainder'] / max(lad2[r][o]['remainder'], 1e-300)
    amp, eps = eps52(slow, ng)
    out = {'point': pt, 'index': a.index, 'grid': ng, 'NI': a.NI, 'M': a.M, 'proxy': a.proxy, 'divisor': div,
           'dn': dn.tolist(), 'stage1_ladder': stage1, 'stage2_ladder': lad2, 'amp52': amp, 'eps52': eps,
           'cpu_s': time.process_time() - t0, 'wall_s': time.time() - w0,
           'peak_rss_mb': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024,
           'status': 'measured (float64 jets, sampled); not an enclosure'}
    json.dump(out, open(a.out, 'w'), indent=1)
    print('done', a.index, 'eps52 %.4f' % eps, 'cpu %.0f s' % out['cpu_s'], 'rss %.0f MB' % out['peak_rss_mb'])
    for r in lad2:
        print(r['order'], {o: '%.3e' % r[o]['remainder'] for o in ('LJ', 'LS')})


if __name__ == '__main__':
    main()
