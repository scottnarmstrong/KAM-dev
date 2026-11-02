"""Shared constants, source data and numeric back ends for the SJSU18 pipeline.

Conventions (see applications/sjsu/README.md, "Conventions"):
  * Units: AU, year, G = 1, Sun mass m0 = 4 pi^2 (SLG13 Table 1).
  * Planets j = 1, 2, 3 = Jupiter, Saturn, Uranus; m_j = m0 / M_j with M_j the
    printed reciprocal mass ratios, read as exact decimals.
  * Canonical heliocentric (Poincare) variables, SLG13 eq. (2):
      Lambda_j = beta_j sqrt(mu_j a_j),  beta_j = m0 m_j/(m0+m_j),  mu_j = G (m0+m_j),
      lambda_j = M_j + varpi_j,
      xi_j  =  sqrt(2 Gamma_j) cos varpi_j,  eta_j = -sqrt(2 Gamma_j) sin varpi_j,
      Gamma_j = Lambda_j (1 - sqrt(1 - e_j^2)).
    Coordinates are (lambda_j, eta_j), momenta (Lambda_j, xi_j):
      {lambda_j, Lambda_j} = 1, {eta_j, xi_j} = 1  (so {xi_j, eta_j} = -1).
  * Complex secular variables z_j = (xi_j - i eta_j)/sqrt(2) = sqrt(Gamma_j) e^{i varpi_j},
    with {z_j, conj z_j} = -i, Gamma_j = z_j conj(z_j).
  * Poisson bracket {f, g} = sum_j (f_lambda g_L - f_L g_lambda) - i (f_z g_zbar - f_zbar g_z).
"""
from __future__ import annotations

import os
from fractions import Fraction

for _name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ.setdefault(_name, '1')

import resource

import mpmath
import numpy as np


def limit_memory(gib: float = 7.5):
    """Cap the address space (brief: RSS under 8 GB per process)."""
    lim = int(gib * 1024 ** 3)
    resource.setrlimit(resource.RLIMIT_AS, (lim, lim))

# ---------------------------------------------------------------- source data
# SLG13 Table 1 (= GLS17 Table 1), exact decimal strings as printed.
MASS_RECIPROCALS = ('1047.355', '3498.5', '22902.98')
TABLE1 = {
    'a': ('5.20463727204700266', '9.54108529142232165', '19.2231635458410572'),
    'M': ('3.04525729444853654', '5.32199311882584869', '0.19431922829271914'),
    'e': ('0.04785365972484999', '0.05460848595674678', '0.04858667407651962'),
    'omega': ('0.24927354029554571', '1.61225062288036902', '2.99374344439246487'),
}
# SLG13 Table 2 (= GLS17 Table 2): linear secular frequencies (rad/yr) and initial data.
TABLE2 = {
    'nu': ('-1.1212724892e-4', '-1.9688444678e-5', '-1.1134564418e-5'),
    'x0': ('1.5407573458e-2', '-3.0574059274e-2', '1.1186486403e-2'),
    'y0': ('-2.5320810665e-2', '-5.2728862107e-3', '6.0669645406e-3'),
}
# SLG13 eq. (24): printed polydisk radii.
SLG13_RADII = ('2.5558203988e-2', '3.0601862602e-2', '1.1223294461e-2')
# GLS17 eq. (37): frequency-analysis frequencies of the secular flow from Table 2.
GLS17_OMEGA = ('-1.51665408389554804e-4', '-2.05981220762083458e-5', '-1.16008414414439544e-5')

PAIRS = ((0, 1), (0, 2), (1, 2))  # (inner, outer), planet indices 0, 1, 2 = J, S, U
DEG_MAX = 18      # SLG13 (b2): degree in (xi, eta)
KF_MAX = 16       # SLG13 (b3): trigonometric degree |k| = |k1|+|k2|+|k3|
KF_CHI = 8        # SLG13 eqs. (6)-(7): K_F = 8
RES = (3, -5, -7)  # SLG13 eq. (10)


# -------------------------------------------------------------- numeric types
class Backend:
    """Arithmetic back end: 'f64' (complex128), 'ld' (80-bit complex long double)
    or 'mp' (mpmath mpc objects at `dps` digits, stored in numpy object arrays)."""

    def __init__(self, name: str = 'ld', dps: int = 40):
        self.name = name
        self.dps = dps
        mpmath.mp.dps = max(dps, 40)
        if name == 'f64':
            self.dtype = np.complex128
            self.rdtype = np.float64
        elif name == 'ld':
            self.dtype = np.clongdouble
            self.rdtype = np.longdouble
        elif name == 'mp':
            self.dtype = object
            self.rdtype = object
        else:
            raise ValueError(name)

    # scalar conversions ---------------------------------------------------
    def real(self, x):
        """Real scalar from Fraction, int, str, mpf or float."""
        if self.name == 'mp':
            return mpmath.mpc(_to_mpf(x), 0)
        s = mpmath.nstr(_to_mpf(x), 40, min_fixed=-1, max_fixed=-1) if not isinstance(x, str) else x
        return self.dtype(self.rdtype(s))

    def cplx(self, re, im):
        if self.name == 'mp':
            return mpmath.mpc(_to_mpf(re), _to_mpf(im))
        return self.real(re) + self.real(im) * self.dtype(1j)

    def zeros(self, shape):
        z = np.zeros(shape, dtype=self.dtype)
        if self.name == 'mp':
            z.fill(mpmath.mpc(0))
        return z

    def array_from(self, values):
        """1-d array of backend scalars from a list of backend scalars."""
        out = np.empty(len(values), dtype=self.dtype)
        for i, v in enumerate(values):
            out[i] = v
        return out

    def to_mpc(self, x):
        if self.name == 'mp':
            return mpmath.mpc(x)
        xr = np.real(x)
        xi = np.imag(x)
        if self.name == 'ld':
            return mpmath.mpc(mpmath.mpf(np.format_float_scientific(xr, precision=21, unique=False)),
                              mpmath.mpf(np.format_float_scientific(xi, precision=21, unique=False)))
        return mpmath.mpc(float(xr), float(xi))

    def abs(self, arr):
        if self.name == 'mp':
            return np.array([float(abs(v)) for v in arr])
        return np.abs(arr).astype(np.float64)


def _to_mpf(x):
    if isinstance(x, Fraction):
        return mpmath.mpf(x.numerator) / x.denominator
    if isinstance(x, mpmath.mpf):
        return x
    if isinstance(x, (int, str)):
        return mpmath.mpf(x)
    if isinstance(x, float):
        return mpmath.mpf(x)
    if isinstance(x, (np.floating,)):
        return mpmath.mpf(np.format_float_scientific(x, precision=21, unique=False))
    raise TypeError(type(x))


def frac_dec(s: str) -> Fraction:
    """Exact rational value of a printed decimal string."""
    return Fraction(s)


# --------------------------------------------------------------- physical data
def physical_constants(astar):
    """Masses and Kepler data at reference semi-major axes `astar` (3 mpf or strings).

    Returns a dict of mpf values: m0, m (3), beta, mu, Lambda, n, a, K2pp (= d^2 H_Kep/dLambda^2).
    """
    mp = mpmath.mp
    m0 = 4 * mp.pi ** 2
    m = [m0 / mpmath.mpf(Fraction(r).numerator) * Fraction(r).denominator for r in MASS_RECIPROCALS]
    beta = [m0 * mj / (m0 + mj) for mj in m]
    mu = [m0 + mj for mj in m]  # G = 1
    a = [mpmath.mpf(x) if not isinstance(x, mpmath.mpf) else x for x in astar]
    Lam = [beta[j] * mpmath.sqrt(mu[j] * a[j]) for j in range(3)]
    n = [mpmath.sqrt(mu[j] / a[j] ** 3) for j in range(3)]
    K2pp = [-3 * n[j] / Lam[j] for j in range(3)]
    return {'m0': m0, 'm': m, 'beta': beta, 'mu': mu, 'a': a, 'Lambda': Lam, 'n': n, 'K2pp': K2pp}
