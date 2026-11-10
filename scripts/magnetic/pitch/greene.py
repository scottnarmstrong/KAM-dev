#!/usr/bin/env python3
"""Reversible periodic-orbit continuation and Greene residues; no rigor.

Fourth-order Yoshida composition of exact extended-Hamiltonian drift/kick
flows. Track both q(0)=0 and q(0)=1/2 symmetric branches from eps=0.
Solve q(n/2)=q(0)+m/2. At a symmetric orbit the full-period Greene
residue is -b*c, where [[a,b],[c,d]] is the half-period tangent map.
Every production run is CPU-capped and must run in the brief's 4G scope.
"""
import argparse
import json
import math
import resource
import time
from pathlib import Path
import numpy as np

resource.setrlimit(resource.RLIMIT_CPU, (3500, 3500))
TAU = 2*math.pi
C1, C2, KA = 32000/2777, 96000/7669, 1427/3200
W1 = 1/(2-2**(1/3))
W0 = -2**(1/3)*W1


def hp(p):
    return 1-1.5*p+p*p-.25*p**3


def hpp(p):
    return -1.5+2*p-.75*p*p


def force(q, t, eps, controlled):
    a, b = TAU*(2*q-t), TAU*(3*q-2*t)
    ca, sa, cb, sb = np.cos(a), np.sin(a), np.cos(b), np.sin(b)
    f = TAU*eps*(2*sa+3*sb)
    fq = TAU**2*eps*(4*ca+9*cb)
    if controlled:
        A = C1*ca-C2*cb
        Aq = TAU*(-2*C1*sa+3*C2*sb)
        Aqq = TAU**2*(-4*C1*ca+9*C2*cb)
        f -= 2*KA*eps**2*A*Aq
        fq -= 2*KA*eps**2*(Aq*Aq+A*Aqq)
    return f, fq


def half_flow(p0, m, n, q0, eps, controlled, spp, return_matrix=False):
    # Batch all orbits, using at least spp steps per forcing period each.
    count = int(math.ceil(max(n)*spp/2))
    dt = n/(2*count)
    q, p, t = q0.copy(), p0.copy(), np.zeros_like(p0)
    aa, bb, cc, dd = np.ones_like(p), np.zeros_like(p), np.zeros_like(p), np.ones_like(p)
    for _ in range(count):
        for w in (W1, W0, W1):
            d = w*dt/2
            shear = d*hpp(p)
            q += d*hp(p)
            t += d
            aa += shear*cc
            bb += shear*dd
            f, fq = force(q, t, eps, controlled)
            p += w*dt*f
            cc += w*dt*fq*aa
            dd += w*dt*fq*bb
            shear = d*hpp(p)
            q += d*hp(p)
            t += d
            aa += shear*cc
            bb += shear*dd
    result = (q-q0-m/2, bb, -bb*cc, aa*dd-bb*cc, p)
    return result+(aa, bb, cc, dd) if return_matrix else result


def initial_p(freq):
    p = np.full(freq.shape, .35)
    for _ in range(12):
        p -= (hp(p)-freq)/hpp(p)
    return p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--model', choices=['controlled', 'uncontrolled'], required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--spp', type=int, default=48)
    ap.add_argument('--max-den', type=int, default=179)
    ap.add_argument('--stop', type=float, default=.006)
    ap.add_argument('--step', type=float, default=.000025)
    ap.add_argument('--resume', help='Resume from last complete successful epsilon in this JSON')
    ap.add_argument('--tolerance', type=float, default=4e-12)
    ap.add_argument('--symmetry', choices=['both', 'zero', 'half'], default='both')
    a = ap.parse_args()
    # Exact continued fraction prefix from the frozen quadratic irrational.
    cf = [0, 1, 1, 2, 1, 1, 2, 3]+[1]*12
    pm2, pm1, qm2, qm1 = 0, 1, 1, 0
    rats = []
    for k in cf:
        p, q = k*pm1+pm2, k*qm1+qm2
        pm2, pm1, qm2, qm1 = pm1, p, qm1, q
        if 12 <= q <= a.max_den:
            rats.append((p, q))
    m = np.repeat(np.array([x[0] for x in rats], float), 2)
    n = np.repeat(np.array([x[1] for x in rats], float), 2)
    q0 = np.tile([0., .5], len(rats))
    if a.symmetry != 'both':
        keep = q0 == (0. if a.symmetry == 'zero' else .5)
        m, n, q0 = m[keep], n[keep], q0[keep]
    p0 = initial_p(m/n)
    start = 0.
    if a.resume:
        old = json.loads(Path(a.resume).read_text())['rows']
        for e in sorted({r['eps'] for r in old}, reverse=True):
            sample = []
            for mj, nj, qj in zip(m, n, q0):
                found = [r for r in old if r['eps'] == e and r['m'] == mj and
                         r['n'] == nj and r['q0'] == qj and r['ok']]
                if found:
                    sample.append(found[-1]['p0'])
            if len(sample) == len(p0):
                p0 = np.array(sample)
                start = e
                break
    controlled = a.model == 'controlled'
    rows = []
    t0, c0 = time.time(), time.process_time()
    for eps in np.arange(start, a.stop+a.step/4, a.step):
        good = np.ones(len(p0), bool)
        with np.errstate(all='ignore'):
            for it in range(16):
                err, b, residues, det, _ = half_flow(p0, m, n, q0, eps, controlled, a.spp)
                active = abs(err) > a.tolerance
                if not active.any():
                    break
                delta = np.divide(err, b, out=np.zeros_like(err), where=abs(b)>1e-12)
                good &= np.isfinite(delta) & (abs(delta) < .005)
                p0 -= np.where(active & good, np.clip(delta, -.001, .001), 0)
                if not (active & good).any():
                    break
        for j in range(len(p0)):
            row = dict(eps=round(float(eps), 10), m=int(m[j]), n=int(n[j]),
                       q0=float(q0[j]), p0=float(p0[j]), err=float(err[j]),
                       residue=float(residues[j]), det=float(det[j]),
                       ok=bool(abs(err[j])<max(2e-10, 2*a.tolerance) and good[j]), iterations=it)
            rows.append(row)
        # Do not trust a branch after its Newton continuation loses it.
        if not np.all(good) or np.max(abs(err)) > max(2e-10, 2*a.tolerance):
            print(json.dumps(dict(event='branch_loss', eps=float(eps), rows=rows[-len(p0):])), flush=True)
            break
        print(json.dumps(dict(eps=round(float(eps), 10), residues=residues.tolist(),
                              maxerr=float(np.max(abs(err))), maxdeterr=float(np.max(abs(det-1))))), flush=True)
    result = dict(model=a.model, spp=a.spp, arguments=vars(a), numpy_version=np.__version__, rows=rows,
                  wall_seconds=time.time()-t0, cpu_seconds=time.process_time()-c0,
                  maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    Path(a.out).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}), flush=True)


if __name__ == '__main__':
    main()
