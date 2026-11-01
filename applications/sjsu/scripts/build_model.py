#!/usr/bin/env python3
"""Build the SJSU18 secular model file (applications/sjsu/data/).

Example (from the repository root; heavy steps under a memory cap):
  systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0 nice -n 10 \
    python3 -I applications/sjsu/scripts/build_model.py --variant O2 \
      --out applications/sjsu/data/sjsu18-o2.json --work ~/kam-data/sjsu/build-o2

Variants
  O2 : strict order two in the masses (secular.py), all degrees <= 18, with the resonant
       mu^4 step of SLG13 eq. (12) (printed weight 1/2).
The output JSON contains the model in complex form (z_j = (xi_j - i eta_j)/sqrt 2) and in real
form (xi, eta), its components (first order, chi_1 and chi_2 parts of order two, resonant step),
all parameters, conventions, truncations and provenance.  Coefficients are decimal strings with
20 significant digits computed in 80-bit long double; see 'precision'.
"""
import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
REPO = os.path.abspath(os.path.join(HERE, '..', '..', '..'))

import mpmath
import numpy as np

from sjsu_common import Backend, physical_constants, TABLE1, MASS_RECIPROCALS, DEG_MAX, KF_MAX, KF_CHI, RES
from secular import compute_secular, to_real
from sparse import SP

ASTAR_DEFAULT = None  # filled from the committed N-body result (validation/astar.json)

CONVENTIONS = {
    'units': 'AU, year, G = 1, m0 = 4 pi^2 (SLG13 Table 1)',
    'masses': 'm_j = m0 / M_j with M_j = 1047.355, 3498.5, 22902.98 read as exact decimals',
    'planets': 'index 1, 2, 3 = Jupiter, Saturn, Uranus (in arrays: 0, 1, 2)',
    'canonical_variables': 'Poincare (canonical heliocentric), SLG13 eq. (2): Lambda_j = beta_j sqrt(mu_j a_j), '
                           'beta_j = m0 m_j/(m0+m_j), mu_j = G (m0+m_j); xi_j = sqrt(2 Gamma_j) cos varpi_j, '
                           'eta_j = -sqrt(2 Gamma_j) sin varpi_j, Gamma_j = Lambda_j (1 - sqrt(1 - e_j^2))',
    'symplectic_structure': 'coordinates (lambda_j, eta_j), momenta (Lambda_j, xi_j): {eta_j, xi_j} = 1, '
                            'so d eta/dt = dH/dxi, d xi/dt = -dH/deta',
    'complex_variables': 'z_j = (xi_j - i eta_j)/sqrt(2) = sqrt(Gamma_j) e^{i varpi_j}; {z_j, conj z_j} = -i; '
                         'dz/dt = -i dH/d(conj z)',
    'real_monomial_order': ['xi_J', 'xi_S', 'xi_U', 'eta_J', 'eta_S', 'eta_U'],
    'complex_monomial_order': ['z_J', 'zbar_J', 'z_S', 'zbar_S', 'z_U', 'zbar_U'],
    'secular_variables': 'the (xi, eta) after the near-identity transformations chi_1, chi_2 (and chi_res) '
                         'at L = 0, as in SLG13 eq. (9)/(12); not the osculating Poincare variables',
}


def git_commit():
    try:
        return subprocess.check_output(['git', '-C', REPO, 'rev-parse', 'HEAD'], text=True).strip()
    except Exception:
        return 'unknown'


def git_dirty():
    try:
        out = subprocess.check_output(['git', '-C', REPO, 'status', '--porcelain', 'applications/sjsu/scripts'], text=True)
        return bool(out.strip())
    except Exception:
        return True


def fmt(x, digits=20):
    return mpmath.nstr(x, digits, min_fixed=0, max_fixed=0, strip_zeros=False)


def symmetrize(sp: SP, bk):
    """Drop the additive constant; enforce reversibility and reality exactly.

    Returns (SP with real coefficients (c_PQ + c_QP)/2, diagnostics, dropped constant).  The
    diagnostics record the largest relative asymmetry |c_PQ - c_QP| and imaginary part before
    symmetrization (round-off size in exact arithmetic both vanish)."""
    d = {}
    const = mpmath.mpf(0)
    for e, cc in zip(sp.E, sp.C):
        key = tuple(int(x) for x in e)
        v = bk.to_mpc(cc)
        if sum(key) == 0:
            const += v.real
            continue
        d[key] = d.get(key, 0) + v
    asym = 0.0
    imag = 0.0
    keys = []
    vals = []
    for k, v in d.items():
        kk = (k[1], k[0], k[3], k[2], k[5], k[4])
        w = d.get(kk, mpmath.mpc(0))
        mag = max(abs(v), abs(w), mpmath.mpf('1e-300'))
        asym = max(asym, float(abs(v - w) / mag))
        imag = max(imag, float(abs(v.imag) / mag))
        keys.append(k)
        vals.append(bk.real((v.real + w.real) / 2))
    n = len(keys)
    out = SP(bk, np.zeros((n, 3)), np.array(keys).reshape(-1, 6), np.zeros(n), bk.array_from(vals))
    return out, {'max_rel_asymmetry': asym, 'max_rel_imag': imag}, const


def complex_terms(sp: SP, bk, digits=20):
    """[[p1,q1,p2,q2,p3,q3, 'coef']] (real coefficients; imaginary parts are checked separately)."""
    out = []
    maximag = 0.0
    for e, c in zip(sp.E, sp.C):
        v = bk.to_mpc(c)
        maximag = max(maximag, float(abs(v.imag)) / max(float(abs(v)), 1e-300))
        out.append([int(x) for x in e] + [fmt(v.real, digits)])
    out.sort(key=lambda t: (sum(t[:6]), t[:6]))
    return out, maximag


def real_terms(real, digits=20):
    out = []
    maximag = 0.0
    for k, v in real.items():
        if v == 0:
            continue
        maximag = max(maximag, float(abs(v.imag)) / max(float(abs(v)), 1e-300))
        out.append(list(k) + [fmt(v.real, digits)])
    out.sort(key=lambda t: (sum(t[:6]), t[:6]))
    return out, maximag


def census(sp: SP, real):
    deg = sp.degree()
    by = {}
    for d in sorted(set(int(x) for x in deg)):
        by[str(d)] = int((deg == d).sum())
    rdeg = {}
    for k in real:
        d = sum(k)
        rdeg[str(d)] = rdeg.get(str(d), 0) + 1
    charge = (sp.E[:, 0::2].sum(1) - sp.E[:, 1::2].sum(1))
    return {'complex_terms': len(sp), 'complex_terms_by_degree': by,
            'complex_terms_with_nonzero_charge': int((charge != 0).sum()),
            'real_terms': len(real), 'real_terms_by_degree': rdeg,
            'real_terms_odd_in_eta': int(sum(1 for k in real if sum(k[3:]) % 2)),
            'bounds': {'dense_even_degrees_2_18': 76713, 'reversible_even_eta': 38466,
                       'charge_balanced_complex': 7941}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--variant', default='O2', choices=['O2'])
    ap.add_argument('--astar', nargs=3)
    ap.add_argument('--astar-json', default=os.path.join(REPO, 'applications', 'sjsu', 'validation', 'astar.json'))
    ap.add_argument('--nstar', default='corrected', choices=['kepler', 'corrected'])
    ap.add_argument('--D', type=int, default=DEG_MAX)
    ap.add_argument('--D1', type=int, default=6)
    ap.add_argument('--res-weight', default='printed', choices=['printed', 'lie'])
    ap.add_argument('--backend', default='ld')
    ap.add_argument('--out', required=True)
    ap.add_argument('--work', help='directory for regenerable intermediates (never committed)')
    ap.add_argument('--version', default='0.1.0')
    ap.add_argument('--digits', type=int, default=None, help='significant digits written (default 25 for mp, 20 otherwise)')
    args = ap.parse_args()
    mpmath.mp.dps = 40
    t0 = time.time()
    if args.astar:
        astar_s = list(args.astar)
        astar_src = 'command line'
    else:
        with open(args.astar_json) as fh:
            aj = json.load(fh)
        astar_s = aj['astar']
        astar_src = f"{os.path.relpath(args.astar_json, REPO)}: {aj.get('definition', '')}"
    astar = [mpmath.mpf(s) for s in astar_s]
    bk = Backend(args.backend)
    digits = args.digits or (25 if args.backend == 'mp' else 20)
    out = compute_secular(astar, bk, D=args.D, D1=args.D1, res=True, res_weight=args.res_weight,
                          nstar=args.nstar, return_intermediates=bool(args.work))
    c = out['consts']
    comps_raw = {'first_order': out['first'], 'second_order_chi1': out['second_chi1'],
                 'second_order_chi2': out['second_chi2'], 'resonant_mu4': out['res']}
    comps = {}
    sym_diag = {}
    for name, sp in comps_raw.items():
        comps[name], sym_diag[name], const = symmetrize(sp, bk)
    total, sym_diag['total'], constant = symmetrize(out['total'], bk)
    real = to_real(total)
    real = {k: v for k, v in real.items() if sum(k[3:]) % 2 == 0}
    rscale = max(abs(v) for v in real.values())
    real = {k: v for k, v in real.items() if abs(v) > rscale * mpmath.mpf('1e-32')}
    cterms, cim = complex_terms(total, bk, digits)
    rterms, rim = real_terms(real, digits)
    comp_json = {}
    for name, sp in comps.items():
        ct, _ = complex_terms(sp, bk, digits)
        comp_json[name] = ct
    model = {
        'name': f'SJSU18-{args.variant}',
        'version': args.version,
        'description': ('Planar secular Sun-Jupiter-Saturn-Uranus Hamiltonian, polynomial of degree 18 in the '
                        'secular Poincare variables, reconstructed from the recipe of Sansottera-Locatelli-Giorgilli '
                        '(2013) section 3 strictly at order two in the masses (plus the resonant mu^4 terms of their '
                        'eq. (12)). It is a reconstruction, not the authors\' data file; see README and '
                        'docs/explorations/sjsu-model-recovery.md for every known difference.'),
        'license': 'CC BY 4.0 (applications/sjsu/data/LICENSE)',
        'conventions': CONVENTIONS,
        'truncations': {
            'degree_xi_eta': args.D, 'fourier_order_|k|': KF_MAX, 'fast_action_degree_perturbation': 1,
            'kepler_part': 'quadratic in L', 'chi1_chi2_harmonics': f'0 < |k| <= {KF_CHI}',
            'chi1_chi2_degree': args.D1, 'mass_order': 'strict two (all terms of the Lie series of order <= 2)',
            'resonant_step': {'harmonic': list(RES), 'chi_res_degree': 9,
                              'weight_on_h_res_0': args.res_weight},
            'nstar': args.nstar,
        },
        'parameters': {
            'astar_AU': astar_s, 'astar_source': astar_src,
            'm0': fmt(c['m0']), 'm': [fmt(x) for x in c['m']], 'mass_reciprocals': list(MASS_RECIPROCALS),
            'Lambda_star': [fmt(x) for x in c['Lambda']], 'n_kepler': [fmt(x) for x in c['n']],
            'nstar_used': [fmt(x) for x in out['nstar']],
            'nstar_correction': [fmt(x) for x in out['nstar_correction']],
            'K2pp': [fmt(x) for x in c['K2pp']],
            'kappa_dot_nstar_res': fmt(out['res_info']['kappa_dot_n']),
        },
        'precision': {
            'arithmetic': {'mp': 'mpmath, 40 significant digits (binary precision 136 bits) throughout',
                           'ld': '80-bit x87 long double (64-bit mantissa)', 'f64': 'IEEE double'}[args.backend]
                          + '; inputs: exact rational Kepler series, Laplace coefficients summed in mpmath at 40 digits, '
                            'masses and a* as exact decimals',
            'digits_written': digits,
            'max_relative_imaginary_part_complex_form': cim,
            'max_relative_imaginary_part_real_form': rim,
            'symmetrization': sym_diag,
            'note': 'reversibility (c_PQ = c_QP) and reality are enforced exactly after checking that the '
                    'computed asymmetry and imaginary parts are at round-off level (symmetrization); see '
                    'validation/precision.json for the float64 / long double / mpmath comparison',
        },
        'dropped_additive_constant': fmt(constant),
        'census': census(total, real),
        'provenance': {
            'generator': 'applications/sjsu/scripts/build_model.py', 'commit': git_commit(),
            'scripts_dirty': git_dirty(), 'command': ' '.join(sys.argv), 'python': platform.python_version(),
            'numpy': np.__version__, 'mpmath': mpmath.__version__, 'cpu_seconds': time.process_time(),
            'sources': ['SLG13: M. Sansottera, U. Locatelli, A. Giorgilli, Math. Comput. Simul. 88 (2013) 1-14, '
                        'doi:10.1016/j.matcom.2010.11.018, arXiv:1010.2609v1, sections 2-3, Table 1, Appendix A',
                        'GLS17: A. Giorgilli, U. Locatelli, M. Sansottera, Regul. Chaotic Dyn. 22 (2017) 54-77, '
                        'arXiv:1702.04894v1, section 2'],
        },
        'complex_form': {'variables': CONVENTIONS['complex_variables'],
                         'monomial_order': CONVENTIONS['complex_monomial_order'], 'terms': cterms},
        'real_form': {'monomial_order': CONVENTIONS['real_monomial_order'], 'terms': rterms},
        'components_complex_form': comp_json,
    }
    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)
    with open(args.out, 'w') as fh:
        json.dump(model, fh, indent=None, separators=(',', ':'))
        fh.write('\n')
    h = hashlib.sha256(open(args.out, 'rb').read()).hexdigest()
    print(f'wrote {args.out}: {len(cterms)} complex / {len(rterms)} real terms, sha256 {h}, '
          f'{time.time()-t0:.0f}s wall, {time.process_time():.0f}s cpu')
    inter = None
    if args.work:
        os.makedirs(os.path.expanduser(args.work), exist_ok=True)
        f = out['f']
        path = os.path.join(os.path.expanduser(args.work), 'first_order_expansion.npz')
        if bk.name == 'mp':
            re = np.array([mpmath.nstr(x.real, 25, min_fixed=0, max_fixed=0) for x in f.C])
            im = np.array([mpmath.nstr(x.imag, 25, min_fixed=0, max_fixed=0) for x in f.C])
        else:
            re = np.array([np.format_float_scientific(np.real(x), precision=20, unique=False) for x in f.C])
            im = np.array([np.format_float_scientific(np.imag(x), precision=20, unique=False) for x in f.C])
        np.savez_compressed(path, K=f.K, E=f.E, L=f.L, re=re, im=im)
        inter = (path, hashlib.sha256(open(path, 'rb').read()).hexdigest(), len(f))
        print('intermediate', path, inter[1])
    src = os.path.splitext(args.out)[0] + '.SOURCE.txt'
    aj_hash = hashlib.sha256(open(args.astar_json, 'rb').read()).hexdigest() if not args.astar else 'n/a'
    with open(src, 'w') as fh:
        fh.write(f"file: {os.path.basename(args.out)}\n")
        fh.write(f"sha256: {h}\n")
        fh.write(f"generator: applications/sjsu/scripts/build_model.py (KAM-dev)\n")
        fh.write(f"commit: {git_commit()}{' (scripts modified after this commit)' if git_dirty() else ''}\n")
        fh.write(f"command: python3 -I applications/sjsu/scripts/build_model.py {' '.join(sys.argv[1:])}\n")
        fh.write(f"a* input: {astar_src} (sha256 {aj_hash})\n")
        fh.write(f"environment: Python {platform.python_version()}, numpy {np.__version__}, mpmath {mpmath.__version__}\n")
        fh.write(f"cpu_seconds: {time.process_time():.0f}\n")
        if inter:
            fh.write(f"regenerable intermediate (not committed): first-order Fourier-Taylor expansion, {inter[2]} complex "
                     f"terms, {os.path.basename(inter[0])} sha256 {inter[1]} (numpy-version dependent container)\n")
        fh.write("license: CC BY 4.0 (see LICENSE in this directory)\n")
    print('wrote', src)


if __name__ == '__main__':
    main()
