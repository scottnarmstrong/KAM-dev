#!/usr/bin/env python3
"""Floating Birkhoff/observable scout on the literal SLG13 quartic table.

No trajectory integration, interval proof, full GLS17 reconstruction, or Lean
execution. All degree terms in {F,H4} are retained when measuring the residual.
Run: nice -n 10 python3 -I scripts/sjsu/scout.py --order 8
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import resource
import time

for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[name] = '1'
resource.setrlimit(resource.RLIMIT_CPU, (3300, 3350))
resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
import numpy as np

ZERO = (0,) * 6
PAIR_PRODUCTS = 0


def add(a, b, scale=1):
    out = a.copy()
    for k, c in b.items():
        out[k] = out.get(k, 0) + scale * c
    return {k: c for k, c in out.items() if c != 0}


def mul(a, b):
    out = {}
    for k, c in a.items():
        for l, d in b.items():
            m = tuple(x+y for x, y in zip(k, l))
            out[m] = out.get(m, 0) + c*d
    return {k: c for k, c in out.items() if c != 0}


def bracket(a, b, cap=100, complex_coordinates=True):
    """{z_j,zbar_j}=i; real ordering (xi,eta) has {xi,eta}=-1."""
    global PAIR_PRODUCTS
    out = {}
    bitems = [(k, c, sum(k)) for k, c in b.items()]
    for k, c in a.items():
        kd = sum(k)
        for l, d, ld in bitems:
            if kd+ld-2 > cap:
                continue
            PAIR_PRODUCTS += 1
            for j in range(3):
                factor = k[j]*l[j+3] - k[j+3]*l[j]
                if factor:
                    m = [x+y for x, y in zip(k, l)]
                    m[j] -= 1
                    m[j+3] -= 1
                    key = tuple(m)
                    value = c*d*factor*(1j if complex_coordinates else -1)
                    out[key] = out.get(key, 0) + value
    return {k: c for k, c in out.items() if c != 0}


def lie(f, generator, cap, sign=1):
    total, term = f.copy(), f.copy()
    for k in range(1, cap+1):
        term = {e: c*sign/k for e, c in bracket(term, generator, cap).items()}
        if not term:
            return total
        total = add(total, term)
    raise AssertionError('degree-truncated Lie series did not terminate')


def transform(poly, U):
    linear = []
    for i in range(6):
        p = {}
        for j in range(3):
            for conjugate in (False, True):
                e = [0]*6
                e[j + 3*conjugate] = 1
                c = U[i % 3, j] / math.sqrt(2)
                if i >= 3:
                    c *= 1j if conjugate else -1j
                p[tuple(e)] = c
        linear.append(p)
    out = {}
    for e, c in poly.items():
        p = {ZERO: float(c)}
        for i, count in enumerate(e):
            for _ in range(count):
                p = mul(p, linear[i])
        out = add(out, p)
    return out


def bound(poly, radii):
    return math.fsum(abs(c) * math.prod(radii[j]**(e[j]+e[j+3]) for j in range(3))
                     for e, c in poly.items())


def evaluate(poly, z):
    coordinates = list(z) + list(np.conj(z))
    return sum(c*math.prod(coordinates[j]**e[j] for j in range(6)) for e, c in poly.items())


def real_evaluate(poly, v):
    return sum(float(c)*math.prod(v[j]**e[j] for j in range(6)) for e, c in poly.items())


def evaluated_bracket(a, b, z):
    """Independent evaluation from the six partial derivatives (no coefficient product)."""
    w = list(z) + list(np.conj(z))
    def derivative(poly, j):
        return sum(c*e[j]*math.prod(w[i]**(e[i]-(i == j)) for i in range(6))
                   for e, c in poly.items() if e[j])
    da = [derivative(a, j) for j in range(6)]
    db = [derivative(b, j) for j in range(6)]
    return 1j*sum(da[j]*db[j+3]-da[j+3]*db[j] for j in range(3))


def amd_baseline(a, ecc, lam):
    amd = sum(l*(e*e)/(1+math.sqrt(1-e*e)) for l, e in zip(lam, ecc))
    emax = [math.sqrt(2*amd/l-(amd/l)**2) for l in lam]
    gaps = [a[i+1]*(1-emax[i+1])-a[i]*(1+emax[i]) for i in range(2)]
    return {'AMD': amd, 'Lambda': lam, 'eccentricity_caps_if_AMD_conserved': emax,
            'adjacent_radial_gaps_AU_if_AMD_conserved': gaps,
            'note': 'nominal Kepler data; conditional on exact AMD conservation, not true of the printed literal table'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, choices=[4, 6, 8, 10], default=8)
    parser.add_argument('--initial', choices=['table1', 'table2'], default='table1')
    args = parser.parse_args()
    start = time.process_time()
    root = Path(__file__).resolve().parent
    datafile = root/'slg13_quartic.json'
    data = json.loads(datafile.read_text())
    exact = {tuple(t['powers']): Fraction(t['coefficient']) for t in data['terms']}
    quadratic = {e: c for e, c in exact.items() if sum(e) == 2}
    quartic = {e: c for e, c in exact.items() if sum(e) == 4}
    A = np.zeros((3, 3))
    B = np.zeros((3, 3))
    for e, c in quadratic.items():
        indices = [i for i in range(6) for _ in range(e[i])]
        i, j = indices
        matrix = A if i < 3 else B
        i, j = i % 3, j % 3
        if i == j:
            matrix[i, i] += 2*float(c)
        else:
            matrix[i, j] += float(c)
            matrix[j, i] += float(c)
    omega, U = np.linalg.eigh((A+B)/2)
    # Choose eigenvector signs deterministically for reproducible phase data.
    for j in range(3):
        if U[np.argmax(abs(U[:, j])), j] < 0:
            U[:, j] *= -1
    original = transform(exact, U)
    H = {e: c for e, c in original.items() if sum(e) == 4}
    actions = []
    for j in range(3):
        e = [0]*6
        e[j] = e[j+3] = 1
        actions.append({tuple(e): 1.0})
        H = add(H, actions[-1], omega[j])
    # H is a generator model only. The actual residual below uses original,
    # including the quadratic mismatch from the floating eigendecomposition.
    m0 = (2*math.pi)**2
    mass = [m0/v for v in [1047.355, 3498.5, 22902.98]]
    a = [5.20463727204700266, 9.54108529142232165, 19.2231635458410572]
    ecc = [0.04785365972484999, 0.05460848595674678, 0.04858667407651962]
    varpi = [0.24927354029554571, 1.61225062288036902, 2.99374344439246487]
    lam = [m0*m/(m0+m)*math.sqrt((m0+m)*ai) for m, ai in zip(mass, a)]
    amp = [math.sqrt(2*l*e*e/(1+math.sqrt(1-e*e))) for l, e in zip(lam, ecc)]
    xi = np.array([r*math.cos(w) for r, w in zip(amp, varpi)])
    eta = np.array([-r*math.sin(w) for r, w in zip(amp, varpi)])
    z0 = (U.T @ xi + 1j*(U.T @ eta))/math.sqrt(2)
    if args.initial == 'table2':
        x0 = np.array([1.5407573458e-2, -3.0574059274e-2, 1.1186486403e-2])
        y0 = np.array([-2.5320810665e-2, -5.2728862107e-3, 6.0669645406e-3])
        z0 = (x0+1j*y0)/math.sqrt(2)
        xi, eta = U @ x0, U @ y0
    radii0 = np.abs(z0)
    total_action = {}
    for j in range(6):
        e = [0]*6
        e[j] = 2
        total_action[tuple(e)] = Fraction(1, 2)
    exact_amd_bracket = bracket(total_action, exact, complex_coordinates=False)
    max_defect = max(exact_amd_bracket.items(), key=lambda kv: abs(kv[1]))
    print('Table: 78 terms; frequencies:', omega, flush=True)
    print('Exact nonzero AMD bracket terms:', len(exact_amd_bracket), flush=True)
    report = {
        'status': 'MEASURED FLOATING SCOUT; no validated lifetime or GLS17 reproduction',
        'data_sha256': hashlib.sha256(datafile.read_bytes()).hexdigest(),
        'numpy_version': np.__version__,
        'coordinate_convention': 'z=(x+i*y)/sqrt(2), q=y, p=x, {z,zbar}=i; omega rad/year',
        'omega': omega.tolist(), 'linear_map_U': U.tolist(),
        'quadratic_blocks_difference_max': float(abs(A-B).max()),
        'initial_policy': ('SLG13 Table 1 nominal elements interpreted literally; no averaging correction or uncertainty'
                           if args.initial == 'table1' else
                           'SLG13 Table 2 modal coordinates interpreted literally; no validated map from Table 1'),
        'orthogonality_defect': float(abs(U.T @ U-np.eye(3)).max()),
        'xi0': xi.tolist(), 'eta0': eta.tolist(), 'modal_radii_z': radii0.tolist(),
        'modal_actions': (radii0**2).tolist(),
        'amd': amd_baseline(a, ecc, lam),
        'literal_table_amd_defect': {
            'nonzero_terms': len(exact_amd_bracket),
            'max_coefficient_powers': max_defect[0],
            'max_coefficient_exact': str(max_defect[1]),
            'max_coefficient_float': float(max_defect[1]),
        },
        'normalization': [], 'curve': [],
    }
    # Verify polynomial substitution independently at the nominal point.
    hreal = real_evaluate(exact, list(xi)+list(eta))
    hcomplex = evaluate(original, z0)
    assert abs(hreal-hcomplex) < 1e-12*abs(hreal)
    report['substitution_check_relative'] = float(abs(hreal-hcomplex)/abs(hreal))
    generators = []
    # Include K=2 (uncorrected quadratic actions) as the control.
    for order in range(2, args.order+1, 2):
        if order > 2:
            g = {e: c for e, c in H.items() if sum(e) == order}
            chi, divisors = {}, []
            for e, c in g.items():
                k = np.array(e[:3])-np.array(e[3:])
                if np.any(k):
                    divisor = float(k @ omega)
                    assert abs(divisor) > 1e-14, (e, divisor)
                    chi[e] = c/(1j*divisor)
                    divisors.append(abs(divisor))
            generators.append(chi)
            H = lie(H, chi, args.order)
            # The solved nonresonant coefficients are roundoff, and are kept.
            residual = {e: c for e, c in H.items() if sum(e) == order and e[:3] != e[3:]}
            report['normalization'].append({
                'degree': order, 'generator_terms': len(chi),
                'minimum_inverted_divisor_rad_per_year': min(divisors),
                'homological_relative_residual': bound(residual, radii0)/max(bound(g, radii0), 1e-300),
            })
        Fs = []
        for I in actions:
            F = I.copy()
            for chi in reversed(generators):
                F = lie(F, chi, order, sign=-1)
            Fs.append(F)
        brackets = [bracket(F, original) for F in Fs]
        corrections = [add(F, I, -1) for F, I in zip(Fs, actions)]
        probe = 0.37*z0*np.exp(1j*np.array([0.23, 0.71, 1.21]))
        checks = []
        for F, B in zip(Fs, brackets):
            check_scale = max(bound(B, radii0), 1e-30)
            error = abs(evaluate(B, probe)-evaluated_bracket(F, original, probe)) / check_scale
            assert error < 1e-10, (order, error)
            assert abs(evaluate(F, probe).imag) < 1e-12*bound(F, radii0)
            checks.append(float(error))
        report.setdefault('bracket_checks', []).append({'K': order, 'relative_evaluation_errors': checks})
        print('K=', order, 'F terms=', [len(F) for F in Fs],
              'bracket terms=', [len(B) for B in brackets], flush=True)
        # r=1 includes the nominal point, on the boundary of its action polydisk.
        # r<1 scales all nominal eccentricity coordinates and excludes that point.
        for r in [0.1, 0.2, 0.3, 0.5, 0.7, 1.0, 1.1]:
            best = None
            for factor in [1.025, 1.05, 1.1, 1.2, 1.3, 1.5, 2.0]:
                R = factor*r
                outer = R*radii0
                eta_bound = [bound(B, outer) for B in brackets]
                eps = [bound(C, outer) for C in corrections]
                # Boundary: I_j=R²a_j²; initial: I_j<=r²a_j².
                # |F-I|<=eps on outer domain gives gap >= difference-2eps.
                margins = [float((R*R-r*r)*radii0[j]**2-2*eps[j]) for j in range(3)]
                horizon = min(m/e for m, e in zip(margins, eta_bound))
                candidate = {'K': order, 'r': r, 'R': R, 'T_year_estimate': max(0, horizon),
                             'eta_per_year': eta_bound, 'correction_bounds': eps,
                             'boundary_margins': margins,
                             'modal_action_drift_at_half_T':
                                 [2*eps[j]+eta_bound[j]*max(0,horizon)/2 for j in range(3)],
                             'F_terms': [len(F) for F in Fs],
                             'bracket_terms': [len(B) for B in brackets],
                             'bracket_degree_census': [dict(Counter(sum(e) for e in B)) for B in brackets]}
                if best is None or horizon > best['T_year_estimate']:
                    best = candidate
            report['curve'].append(best)
    # Table 2 vs printed (24) uses coordinate amplitudes sqrt(x²+y²).
    tx = [1.5407573458e-2, -3.0574059274e-2, 1.1186486403e-2]
    ty = [-2.5320810665e-2, -5.2728862107e-3, 6.0669645406e-3]
    report['source_radius_check'] = {
        'table2_hypot': [math.hypot(x, y) for x, y in zip(tx, ty)],
        'equation24_radii': [2.5558203988e-2, 3.0601862602e-2, 1.1223294461e-2],
    }
    report['operation_pair_count'] = PAIR_PRODUCTS
    report['cpu_seconds'] = time.process_time()-start
    report['max_rss_MiB'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024
    out = root/'results'
    out.mkdir(exist_ok=True)
    suffix = '' if args.initial == 'table1' else '-table2'
    (out/f'scout-k{args.order}{suffix}.json').write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    lines = ['K,r,R,T_year_estimate,status']
    for row in report['curve']:
        lines.append(f"{row['K']},{row['r']},{row['R']},{row['T_year_estimate']:.12g},floating_literal_quartic_only")
    (out/f'curve-k{args.order}{suffix}.csv').write_text('\n'.join(lines)+'\n')
    print('CPU seconds', report['cpu_seconds'], 'RSS MiB', report['max_rss_MiB'], flush=True)
    print('\n'.join(lines), flush=True)


if __name__ == '__main__':
    main()
