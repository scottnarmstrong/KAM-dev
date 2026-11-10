#!/usr/bin/env python3
"""Independent map comparison and explicit failed-target tests; untrusted."""
import argparse
import json
import math
import resource
import time
from pathlib import Path
import numpy as np
from circle_scan import ALPHA, Grid, pad
from greene import W1, W0, force, hp, half_flow


def flow(q, p, eps, controlled, steps):
    q, p = q.copy(), p.copy()
    t = 0.
    for _ in range(steps):
        for w in (W1, W0, W1):
            d = w/steps/2
            q += d*hp(p)
            t += d
            f, _ = force(q, t, eps, controlled)
            p += w/steps*f
            q += d*hp(p)
            t += d
    return q, p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--root', required=True)
    ap.add_argument('--refine-residues')
    ap.add_argument('--eps', nargs='+', type=float, default=[.0042, .00426, .0043])
    a = ap.parse_args()
    root = Path(a.root)
    rows = []
    t0, c0 = time.time(), time.process_time()
    if a.refine_residues:
        source = json.loads(Path(a.refine_residues).read_text())
        for eps in a.eps:
            sample = [r for r in source['rows'] if r['eps'] == eps and r['q0'] == 0 and r['ok']]
            if not sample:
                raise ValueError(f'No accepted periodic-orbit seeds at epsilon {eps}')
            m = np.array([r['m'] for r in sample], float)
            n = np.array([r['n'] for r in sample], float)
            q0 = np.zeros(len(sample))
            p0 = np.array([r['p0'] for r in sample])
            for spp in (32, 64, 128):
                for _ in range(6):
                    err, b, res, det, _ = half_flow(p0, m, n, q0, eps, source['model']=='controlled', spp)
                    if np.max(abs(err)) < 8e-11:
                        break
                    p0 -= err/b
                for j in range(len(sample)):
                    row = dict(eps=eps, n=int(n[j]), m=int(m[j]), spp=spp, residue=float(res[j]),
                               p0=float(p0[j]), err=float(err[j]), det=float(det[j]))
                    rows.append(row)
                    print(json.dumps(row), flush=True)
        result = dict(rows=rows, wall_seconds=time.time()-t0, cpu_seconds=time.process_time()-c0,
                      maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        Path(a.out).write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps({k:v for k,v in result.items() if k!='rows'}), flush=True)
        return
    for n in (128, 256, 512):
        g = Grid(n, False)
        d = np.load(root/'results'/f'uncontrolled-{n}-last.npz')
        for eps in (.0012, .003):
            with np.errstate(all='ignore'):
                u, ok, it = g.solve(d['uhat'], eps)
                m = g.metrics(u, eps)
            row = dict(kind='uncontrolled_target_attempt', n=n, eps=eps,
                       ok=ok, iterations=it, **m)
            rows.append(row)
            print(json.dumps(row), flush=True)
    for n in (256, 512, 1024):
        for eps in (.0012, .003):
            path = root/('refined' if n == 1024 else 'results')/f'controlled-{n}-{eps:.7f}.npz'
            if not path.exists():
                continue
            d = np.load(path)
            u = d['uhat']
            g = Grid(n, True)
            _, _, p = g.residual(u, eps)
            uh1, ph1 = np.sum(u, axis=1), np.sum(g.fwd(p), axis=1)
            k = np.fft.fftfreq(n, 1/n)
            th = np.arange(24)/24
            def ev(h, x):
                return (np.exp(2j*np.pi*x[:, None]*k[None, :])@h).real
            q0, p0 = th+ev(uh1, th), ev(ph1, th)
            q1, p1 = th+ALPHA+ev(uh1, th+ALPHA), ev(ph1, th+ALPHA)
            for steps in (32, 64, 128, 256):
                qf, pf = flow(q0, p0, eps, True, steps)
                row = dict(kind='one_period_invariance', n=n, eps=eps, steps=steps,
                           qerr=float(np.max(abs(qf-q1))), perr=float(np.max(abs(pf-p1))))
                rows.append(row)
                print(json.dumps(row), flush=True)
            gp = Grid(n*2, True)
            row = dict(kind='padded_target', n=n, eps=eps, **gp.metrics(pad(u, 2*n), eps))
            rows.append(row)
            print(json.dumps(row), flush=True)
    # Independent full-period tangent matrix versus the half-period reversibility formula.
    old = json.loads((root/'results/greene-uncontrolled-32.json').read_text())['rows']
    seed = next(r for r in old if r['eps'] == .0012 and r['n'] == 31 and r['q0'] == 0)
    pp = np.array([seed['p0']])
    mm, nn, qq = np.array([18.]), np.array([31.]), np.array([0.])
    for spp in (32, 64, 128):
        for _ in range(5):
            err, bb, rr, det, _ = half_flow(pp, mm, nn, qq, .0012, False, spp)
            pp -= err/bb
        err, bb, rr, det, _ = half_flow(pp, mm, nn, qq, .0012, False, spp)
        ef, _, _, df, pf, aa, bb, cc, dd = half_flow(pp, 2*mm, 2*nn, qq, .0012, False, spp, True)
        row = dict(kind='full_period_validation', model='uncontrolled', eps=.0012,
                   numerator=18, denominator=31, spp=spp, p0=float(pp[0]),
                   half_residue=float(rr[0]), full_residue=float((2-aa[0]-dd[0])/4),
                   qperiod_error=float(ef[0]), pperiod_error=float(pf[0]-pp[0]),
                   full_determinant_error=float(df[0]-1))
        rows.append(row)
        print(json.dumps(row), flush=True)
    # Differentiate the literal potential numerically to check the force transcription.
    from circle_scan import C1, C2, KA, TAU
    q, ph, eps = np.array([.173, .397, .631]), .223, .003
    for controlled in (False, True):
        def potential(x):
            ca, cb = np.cos(TAU*(2*x-ph)), np.cos(TAU*(3*x-2*ph))
            return eps*(ca+cb)+(KA*eps**2*(C1*ca-C2*cb)**2 if controlled else 0)
        f, fq = force(q, ph, eps, controlled)
        d = 1e-6
        row = dict(kind='force_finite_difference', controlled=controlled,
                   force_error=float(np.max(abs(f+(potential(q+d)-potential(q-d))/(2*d)))),
                   force_derivative_error=float(np.max(abs(fq-(force(q+d, ph, eps, controlled)[0]-
                                                               force(q-d, ph, eps, controlled)[0])/(2*d)))))
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = dict(rows=rows, wall_seconds=time.time()-t0, cpu_seconds=time.process_time()-c0,
                  maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    Path(a.out).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}), flush=True)


if __name__ == '__main__':
    main()
