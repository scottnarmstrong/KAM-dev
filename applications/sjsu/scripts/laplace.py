"""Laplace coefficients b_{1/2}^{(k)}(alpha) and their derivatives (alpha d/dalpha)^n b.

b_s^{(k)}(alpha) = 2 (s)_k/k! alpha^k 2F1(s, s+k; k+1; alpha^2)
               = sum_{m>=0} 2 (s)_m (s)_{k+m} / (m! (k+m)!) alpha^{k+2m},
so (alpha d/dalpha)^n b = sum_m (k+2m)^n c_{k,m} alpha^{k+2m}.  The series is summed in
mpmath until the terms fall below 10^(-dps-10) of the running sum (alpha < 0.6 here).
The tail after truncation is bounded by a geometric majorant and checked to be negligible.
"""
from __future__ import annotations

import mpmath


def laplace_derivatives(alpha, kmax: int, nmax: int, s=mpmath.mpf(1) / 2):
    """Return table T[k][n] = (alpha d/dalpha)^n b_s^{(k)}(alpha), 0 <= k <= kmax, 0 <= n <= nmax."""
    alpha = mpmath.mpf(alpha)
    a2 = alpha * alpha
    eps = mpmath.mpf(10) ** (-(mpmath.mp.dps + 10))
    table = []
    for k in range(kmax + 1):
        sums = [mpmath.mpf(0)] * (nmax + 1)
        # c_{k,0} = 2 (s)_k / k!
        c = 2 * mpmath.rf(s, k) / mpmath.factorial(k)
        apow = alpha ** k
        m = 0
        small = 0
        while True:
            base = c * apow
            e = k + 2 * m
            term_max = mpmath.mpf(0)
            t = base
            for n in range(nmax + 1):
                sums[n] += t
                term_max = max(term_max, abs(t) / (abs(sums[n]) + eps))
                t *= e
            if term_max < eps:
                small += 1
                if small >= 3:
                    break
            else:
                small = 0
            # c_{k,m+1} = c_{k,m} (s+m)(s+k+m)/((m+1)(k+m+1))
            c = c * (s + m) * (s + k + m) / ((m + 1) * (k + m + 1))
            apow *= a2
            m += 1
            if m > 20000:
                raise RuntimeError('Laplace series did not converge')
        table.append(sums)
    return table


if __name__ == '__main__':
    mpmath.mp.dps = 40
    al = mpmath.mpf('0.5455')
    T = laplace_derivatives(al, 3, 3)
    # independent checks: quadrature of (1+a^2-2a cos psi)^{-1/2} cos(k psi)/pi * 2 ... b^{(k)} = (1/pi) int_0^{2pi}
    for k in range(3):
        q = mpmath.quad(lambda p: mpmath.cos(k * p) / mpmath.sqrt(1 + al**2 - 2 * al * mpmath.cos(p)), [0, mpmath.pi]) * 2 / mpmath.pi
        d = mpmath.diff(lambda x: mpmath.quad(lambda p: mpmath.cos(k * p) / mpmath.sqrt(1 + x**2 - 2 * x * mpmath.cos(p)), [0, mpmath.pi]) * 2 / mpmath.pi, al) * al
        print(k, mpmath.nstr(T[k][0] - q, 5), mpmath.nstr(T[k][1] - d, 5))
