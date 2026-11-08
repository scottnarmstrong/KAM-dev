#!/usr/bin/env python3
"""G1 driver: the keep52(+nr) Stage-I ladder to order N at one slow point of points.json (research scratch).

usage: ladder.py POINTS.json INDEX OUT.json [--grid 64,64,32] [--N 5] [--keep keep52nr] [--divisor kepler]
The Kolmogorov shift at a point is DN = (N_NB - n_Kep(Lambda*)) + (grad<f>(point) - grad<f>(nominal)).
"""
import argparse, json, os, resource, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import jets, model as M, nf


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('points'); ap.add_argument('index', type=int); ap.add_argument('out')
    ap.add_argument('--grid', default='64,64,32'); ap.add_argument('--N', type=int, default=5)
    ap.add_argument('--keep', default='keep52nr'); ap.add_argument('--divisor', default='kepler')
    ap.add_argument('--quiet', action='store_true')
    ap.add_argument('--census', action='store_true', help='G4: coefficient census of f, chi_r and H_s')
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
    B = jets.Basis(9, a.N)
    _, g_pt = nf.f_fourier(B1, slow, ng, np.zeros(3), slow[0])
    dn = M.DN_STAR + (g_pt - g_nom)
    f, _ = nf.f_fourier(B, slow, ng, dn, slow[0])
    E = nf.Engine(B, ng, slow, dn, divisor=a.divisor, keep=a.keep, verbose=not a.quiet)
    E.keep_chis = a.census
    lad, H = E.run(f, a.N)
    cen = None
    if a.census:
        taus = [1e-10, 1e-12, 1e-14, 1e-16]
        cen = {}
        for rz in (3e-3, 1e-2):
            rho = [5e-5] * 3 + [rz] * 6
            c = {'f': nf.census(B, f, rho, taus)}
            for r, chi in E.chis.items():
                c['chi%d' % r] = nf.census(B, chi, rho, taus)
            for s_, Hs in H.items():
                c['H%d' % s_] = nf.census(B, Hs, rho, taus)
            cen['rho_Lambda_5e-5_rho_z_%.0e' % rz] = c
    for o in ('F1', 'LU', 'LJ', 'LS'):
        for r in range(1, len(lad)):
            lad[r][o]['gain_remainder'] = lad[r - 1][o]['remainder'] / max(lad[r][o]['remainder'], 1e-300)
    out = {'point': pt, 'index': a.index, 'grid': ng, 'N': a.N, 'keep': a.keep, 'divisor': a.divisor,
           'dn': dn.tolist(), 'ladder': lad, 'census': cen,
           'cpu_s': time.process_time() - t0, 'wall_s': time.time() - w0,
           'peak_rss_mb': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024,
           'status': 'measured (float64 jets, sampled sup over the fast grid); not an enclosure'}
    json.dump(out, open(a.out, 'w'), indent=1)
    print('done', a.index, 'cpu %.0f s' % out['cpu_s'], 'rss %.0f MB' % out['peak_rss_mb'])


if __name__ == '__main__':
    main()
