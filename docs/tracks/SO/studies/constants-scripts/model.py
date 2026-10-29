"""Exact model data of the SO track (proposal 2.3, owner decision D30).  Untrusted tooling.

pi-free normalisation: v = 2*pi*u, rotating coordinates psi = theta1 - theta2, phi = theta2, Fourier characters
e_{k,l}(psi,phi) = exp(2*pi*i*(k*psi + l*phi)), Dt = (nu - 1) d_psi + d_phi in index units, i.e. Dt e_{k,l} =
i*((nu-1)*k + l) e_{k,l}.  With q = theta1 + u the invariance equation  D^2 u + d_q V(theta1+u, theta2) = 0  times
2*pi equals  2*pi*r = 4*pi^2 * R(v)  with

    R(v) = Dt^2 v + 2*eps * sum_{m=1..7} A_m(e) * sin(2*pi*(2*psi + (2-m)*phi) + 2*v),

i.e. r = 2*pi*R(v)  (so R contains no pi except inside the characters of the forcing).  With E = exp(2*i*v):
    sin(theta_m + 2v) = Im(e_{(2,2-m)} * E),   p = nu + Dt v.
"""
from fractions import Fraction as F

E_ORB = F(549, 10000)
EPS = F(69, 200000)
M_MODES = range(1, 8)
SHIFT = {m: (2, 2 - m) for m in M_MODES}   # Fourier shift (k,l) of e^{i theta_m}

def A_coeffs(e):
    e = F(e)
    return {
        1: -e / 4 + e**3 / 32,
        2: F(1, 2) - 5 * e**2 / 4 + 13 * e**4 / 32,
        3: 7 * e / 4 - 123 * e**3 / 32,
        4: 17 * e**2 / 4 - 115 * e**4 / 12,
        5: 845 * e**3 / 96 - 32525 * e**5 / 1536,
        6: 533 * e**4 / 32,
        7: 228347 * e**5 / 7680,
    }

A_EXACT = A_coeffs(E_ORB)

# alpha = 1/(40+g), g=(sqrt5-1)/2  =  (79 - sqrt5)/3118 = (79/3118) + (-1/3118) sqrt5   (element of Q(sqrt5))
ALPHA = (F(79, 3118), F(-1, 3118))
def nu_minus_one(which):
    """nu - 1 as a Q(sqrt5) pair (x, y) = x + y*sqrt5; which in {'lower','upper'}."""
    s = -1 if which == "lower" else 1
    return (s * ALPHA[0], s * ALPHA[1])
