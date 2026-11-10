#!/usr/bin/env python3
"""Untrusted Fourier parameterization experiment; numpy only; no certificate.

Run under the systemd scope specified in BRIEF-MAG-PITCH.md.  CPU hard stop
is 3500 s.  Odd u, q=theta+u, p=(h')^{-1}(alpha+D u), phi=t.
Levi-Civita quasi-Newton: D(a D W)=-N L, delta u=N W,
N=1+u_theta, a=N^2/h''(p), L=D p+V_q. Mean constraints solve the
two cohomological equations. This is derived independently but matches the
existing producer's double-precision equations. Failures are not disproofs.
"""
import argparse
import json
import math
import os
import resource
import time
from pathlib import Path

os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
import numpy as np

resource.setrlimit(resource.RLIMIT_CPU, (3500, 3500))
ALPHA = (7913 - math.sqrt(5)) / 13618
TAU = 2 * math.pi
C1, C2, KA = 32000 / 2777, 96000 / 7669, 1427 / 3200


def hp(p):
    return 1 - 1.5*p + p*p - .25*p**3


def hpp(p):
    return -1.5 + 2*p - .75*p*p


def pad(a, n):
    k = np.fft.fftfreq(a.shape[0], 1/a.shape[0]).astype(int)
    b = np.zeros((n, n), complex)
    b[np.ix_(k % n, k % n)] = a
    return b


class Grid:
    def __init__(self, n, controlled):
        self.n, self.controlled = n, controlled
        k = np.fft.fftfreq(n, 1/n)
        self.k, self.l = np.meshgrid(k, k, indexing='ij')
        self.d = TAU*1j*(ALPHA*self.k+self.l)
        self.di = np.zeros_like(self.d)
        np.divide(1, self.d, out=self.di, where=self.d != 0)
        self.cut = (abs(self.k) <= n//3) & (abs(self.l) <= n//3)
        self.th = (np.arange(n)/n)[:, None]
        self.ph = (np.arange(n)/n)[None, :]
        self.neg = (-np.arange(n)) % n

    def fwd(self, a):
        return np.fft.fft2(a)/self.n**2

    def inv(self, a):
        return np.fft.ifft2(a).real*self.n**2

    def odd(self, a):
        b = a.imag
        return .5j*(b-b[self.neg][:, self.neg])*self.cut

    def residual(self, uhat, eps):
        u = self.inv(uhat)
        ut = self.inv(TAU*1j*self.k*uhat)
        y = ALPHA+self.inv(self.d*uhat)
        p = np.full(y.shape, .35)
        for _ in range(10):
            p -= (hp(p)-y)/hpp(p)
        a, b = TAU*(2*(self.th+u)-self.ph), TAU*(3*(self.th+u)-2*self.ph)
        ca, sa, cb, sb = np.cos(a), np.sin(a), np.cos(b), np.sin(b)
        vq = -TAU*eps*(2*sa+3*sb)
        if self.controlled:
            vq += 2*KA*eps**2*(C1*ca-C2*cb)*TAU*(-2*C1*sa+3*C2*sb)
        L = self.inv(self.d*self.fwd(p))+vq
        return L, ut, p

    def solve(self, initial, eps, maxiter=35):
        uhat = initial.copy()
        best = float('inf')
        for it in range(maxiter):
            L, ut, p = self.residual(uhat, eps)
            err = float(np.max(abs(L)))
            if not np.isfinite(err) or np.max(abs(p)) > 3 or np.max(abs(ut)) > 8:
                return uhat, False, it
            if err < 3e-11:
                return uhat, True, it
            N = 1+ut
            if np.min(N) < .015:
                return uhat, False, it
            a = N*N/hpp(p)
            Y = self.inv(-self.fwd(N*L)*self.di)
            c = -np.mean(Y/a)/np.mean(1/a)
            W = self.inv(self.fwd((Y+c)/a)*self.di)
            du = self.odd(self.fwd(N*W))
            accepted = False
            for fac in (1., .5, .25, .125, .0625):
                trial = uhat+fac*du
                Lt, _, _ = self.residual(trial, eps)
                if np.max(abs(Lt)) < err:
                    uhat = trial
                    accepted = True
                    break
            if not accepted or (it > 10 and err > best*.999):
                return uhat, False, it
            best = min(best, err)
        return uhat, False, maxiter

    def metrics(self, uhat, eps):
        L, ut, p = self.residual(uhat, eps)
        fh = self.fwd(L)
        edge = (abs(self.k) > self.n*.27) | (abs(self.l) > self.n*.27)
        return dict(sup=float(np.max(abs(L))), l1=float(np.sum(abs(fh))),
                    pmin=float(np.min(p)), pmax=float(np.max(p)),
                    slope=float(np.min(1+ut)), tail=float(np.sum(abs(uhat[edge]))),
                    p00=float(p[0, 0]), umax=float(np.max(abs(self.inv(uhat)))))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--model', choices=['controlled', 'uncontrolled'], required=True)
    ap.add_argument('--max-n', type=int, default=512)
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    t0, c0 = time.time(), time.process_time()
    rows = []
    for n in (64, 128, 256, 512, 1024):
        if n > a.max_n:
            break
        g = Grid(n, a.model == 'controlled')
        u = np.zeros((n, n), complex)
        eps, step = 0., .0001
        lastgood = 0.
        while eps < .009:
            target = round(eps+step, 10)
            with np.errstate(all='ignore'):
                trial, ok, it = g.solve(u, target)
            if ok:
                eps, u, lastgood = target, trial, target
                m = g.metrics(u, eps)
                row = dict(n=n, eps=eps, ok=True, iterations=it, **m)
                if abs(eps-.0012) < 1e-9 or abs(eps-.003) < 1e-9:
                    gp = Grid(2*n, a.model == 'controlled')
                    row['padded'] = gp.metrics(pad(u, 2*n), eps)
                    np.savez_compressed(out/f'{a.model}-{n}-{eps:.7f}.npz', uhat=u, eps=eps)
                rows.append(row)
                print(json.dumps(row), flush=True)
                if step < .0001 and m['tail'] < 1e-9:
                    step = min(.0001, step*2)
            else:
                row = dict(n=n, eps=target, ok=False, iterations=it, lastgood=lastgood)
                rows.append(row)
                print(json.dumps(row), flush=True)
                if step <= .000003125:
                    break
                step /= 2
        np.savez_compressed(out/f'{a.model}-{n}-last.npz', uhat=u, eps=eps)
        gp = Grid(2*n, a.model == 'controlled')
        row = dict(n=n, endpoint=eps, next_failure=round(eps+step, 10),
                   endpoint_metrics=g.metrics(u, eps),
                   padded=gp.metrics(pad(u, 2*n), eps))
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = dict(model=a.model, alpha=ALPHA, arguments=vars(a), numpy_version=np.__version__, rows=rows,
                  wall_seconds=time.time()-t0, cpu_seconds=time.process_time()-c0,
                  maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    (out/f'{a.model}-scan.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}), flush=True)


if __name__ == '__main__':
    main()
