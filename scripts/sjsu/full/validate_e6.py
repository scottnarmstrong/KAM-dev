#!/usr/bin/env python3
"""Validate the jet normal form against E6 (order3.json, keep52) at the nominal point: same divisor convention
(n = N_NB + HESS dLambda), same grid (128, 128, 64), orders 0-2."""
import json, os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import jets, model as M, nf

ng = tuple(int(x) for x in (sys.argv[1] if len(sys.argv) > 1 else '128,128,64').split(','))
div = sys.argv[2] if len(sys.argv) > 2 else 'linear'
t0 = time.process_time()
B = jets.Basis(9, 2)
slow = (M.LAM_STAR.copy(), M.XI0.copy(), M.ETA0.copy())
f, grad = nf.f_fourier(B, slow, ng, M.DN_STAR, M.LAM_STAR)
E = nf.Engine(B, ng, slow, M.DN_STAR, divisor=div, keep='keep52', verbose=True)
lad, _ = E.run(f, 2)
out = {'grid': ng, 'divisor': div, 'ladder': lad, 'secular_grad_Lambda_f': grad.tolist(), 'DN_star': M.DN_STAR.tolist(),
       'cpu_s': time.process_time() - t0}
ref = os.environ.get('E6_REF')
if ref:
    R = json.load(open(ref))['keep52']
    cmp = {}
    for r, key in enumerate(('order0', 'order1', 'order2')):
        cmp[key] = {o: [lad[r][o]['total'], R[key][i], lad[r][o]['total'] / R[key][i] - 1]
                    for i, o in enumerate(('LJ', 'LS', 'LU', 'F1'))}
    out['vs_E6'] = cmp
    for k, v in cmp.items():
        print(k, {o: '%.4e vs %.4e (%+.2e)' % tuple(x) for o, x in v.items()})
print(json.dumps(out['ladder'], indent=0)[:2000])
json.dump(out, open(sys.argv[3] if len(sys.argv) > 3 else 'validate_e6.json', 'w'), indent=1)
