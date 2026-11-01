#!/usr/bin/env python3
"""LP-QUANT: test systems, in LP's normalization.  Untrusted design tooling, no Lean.

Units as in LP:MAIN (1): G = 1, stellar mass 1, length AU.  One time unit is sqrt(AU^3/(G M_star)), i.e.
yr/(2 pi sqrt(M_star/M_sun)).  Planet masses m_i = mu nu_i with max nu = 1, so mu is the largest planet/star ratio.

Every datum carries a provenance string.  All inputs here are published nominal values, NOT enclosures.  The
canonical axis of LP (2) differs from a published osculating or mean axis at O(mu); `a` below is used as the canonical
axis and chain.py reports the sensitivity of the divisors to that O(mu) shift.
"""
from dataclasses import dataclass, field
import math
import numpy as np

MSUN_MEARTH = 332946.0487  # IAU 2015 nominal GM_sun/GM_earth
MJ_RATIO, MS_RATIO, MU_RATIO, MN_RATIO = 1047.3486, 3497.898, 22902.98, 19412.24  # GM_sun/GM_planet (DE405 era)
# Standish, "Keplerian elements for approximate positions of the major planets" (JPL), Table 1, J2000 elements (1800-2050).
A_STD = dict(J=5.20288700, S=9.53667594, U=19.18916464, N=30.06992276)
E_STD = dict(J=0.04838624, S=0.05386179, U=0.04725744, N=0.00859048)
# Inclinations to the invariable plane, degrees (Souami-Souchay 2012, A&A 543 A133, Table 2).
I_INV = dict(J=0.3219, S=0.9255, U=0.9947, N=0.7354)


@dataclass
class System:
    name: str
    klass: str  # 'solar', 'earth', 'exo', 'scaled'
    m: np.ndarray  # planet/star mass ratios
    a: np.ndarray  # canonical axes, AU
    e: np.ndarray  # eccentricities at epoch
    inc: np.ndarray = None  # inclinations to the invariable plane, degrees (None: planar)
    mstar: float = 1.0  # solar masses, only for the year conversion
    source: str = ""
    note: str = ""

    def __post_init__(self):
        self.m = np.asarray(self.m, float)
        self.a = np.asarray(self.a, float)
        self.e = np.asarray(self.e, float)
        self.n = len(self.m)
        self.inc = np.zeros(self.n) if self.inc is None else np.asarray(self.inc, float)

    @property
    def mu(self):
        return float(np.max(self.m))

    @property
    def nu(self):
        return self.m / self.mu

    @property
    def I0(self):
        """Lambda_i = nu_i sqrt(a_i), normalized actions (physical action / mu)."""
        return self.nu * np.sqrt(self.a)

    @property
    def omega(self):
        """Radian frequencies nu_i^3/I_i^3 = a_i^(-3/2), per time unit."""
        return self.a ** (-1.5)

    @property
    def years_per_unit(self):
        return 1.0 / (2 * math.pi * math.sqrt(self.mstar))

    def with_mu(self, mu):
        """Same shape (nu, axes, eccentricities) at a different largest mass ratio.  NB eccentricities are kept, so the
        normalized AMD C is unchanged, as in LP's theorem, where delta is the NORMALIZED margin."""
        return System(self.name + f"@mu={mu:.0e}", "scaled", self.nu * mu, self.a, self.e, self.inc, self.mstar,
                      self.source, "mass-scaled copy")


def solar(names, planar=False, name=None):
    r = dict(J=MJ_RATIO, S=MS_RATIO, U=MU_RATIO, N=MN_RATIO)
    m = [1 / r[c] for c in names]
    a = [A_STD[c] for c in names]
    e = [E_STD[c] for c in names]
    inc = None if planar else [I_INV[c] for c in names]
    return System(name or "-".join(names), "solar", m, a, e, inc, 1.0,
                  "IAU/DE405 mass ratios; Standish J2000 a, e; Souami-Souchay 2012 inclinations",
                  "planar: inclinations dropped" if planar else "")


def period_axes(P_days, mstar):
    """Axes from periods (the frequency is what the divisors see): a^3 = M P^2 in AU, yr, Msun."""
    P = np.asarray(P_days, float) / 365.25
    return (mstar * P ** 2) ** (1 / 3)


def exo(name, mstar, P, m_earth, e, source, note=""):
    return System(name, "exo", np.asarray(m_earth, float) / (MSUN_MEARTH * mstar), period_axes(P, mstar), e, None, mstar,
                  source, note)


PHI = (1 + 5 ** 0.5) / 2


def earth_like(name, freqs, e, note):
    """Earth-mass planets around a Sun-like star; `freqs` = omega_i/omega_1, inner to outer.  They are chosen in a real
    number field of degree n so that (1, freqs) has no rational relation (an earlier draft with two ratios in Q(sqrt 5)
    had an exact relation at |k| ~ 200, caught by divisors.py)."""
    n = len(freqs)
    a = np.asarray(freqs, float) ** (-2 / 3)
    return System(name, "earth", np.full(n, 1 / MSUN_MEARTH), a, np.full(n, e), None, 1.0, "synthetic", note)


def catalogue():
    S = {}
    S["SJ"] = solar("JS", planar=True, name="Sun-Jupiter-Saturn (planar)")
    S["SJs"] = solar("JS", name="Sun-Jupiter-Saturn (spatial)")
    S["JSUN"] = solar("JSUN", planar=True, name="J-S-U-N (planar)")
    S["JSUNs"] = solar("JSUN", name="J-S-U-N (spatial)")
    # Sensitivity variant: canonical axes chosen so that omega(I0) + mu d<f>/dI equals the true mean motions (P_J = 4332.589 d,
    # P_S = 10759.22 d).  The shift of the fast average (-8.6e-5, +7.2e-5) is the one computed by fast_newton for "SJ".
    om_true = 2 * math.pi / np.array([4332.589, 10759.22]) * 365.25 / (2 * math.pi)
    om_can = om_true - np.array([-8.6e-5, 7.2e-5])
    S["SJcal"] = System("Sun-Jupiter-Saturn (planar, frequency-calibrated)", "solar", S["SJ"].m, om_can ** (-2 / 3), S["SJ"].e,
                        None, 1.0, S["SJ"].source, "canonical axes from true mean motions")
    # Synthetic frequencies.  n = 2: quadratic irrationals; n = 3: basis of Q(t), t = 2^(1/3).  Compact variants sit at about
    # 12-15 mutual Hill radii.
    t = 2 ** (1 / 3)
    S["E2w"] = earth_like("2 Earths, wide", [1, 1 / (2 * PHI)], 0.02, "period ratio 2 phi = 3.236")
    S["E3w"] = earth_like("3 Earths, wide", [1, t - 0.95, t * t - 1.5], 0.02, "period ratios 3.227, 3.545")
    S["E2c"] = earth_like("2 Earths, compact", [1, 1 / (1 + 1 / (2 + PHI))], 0.01, "period ratio 1.276")
    S["E3c"] = earth_like("3 Earths, compact", [1, t - 0.476, t * t - 0.95], 0.01, "period ratios 1.276, 1.230")
    # Pinned in docs/explorations/amd-crossing/A7-practical.md section 5 (table and source list there).
    S["HD109271"] = exo("HD 109271", 1.047, [7.8543, 30.93], [17, 24], [0.25, 0.15],
                        "Lo Curto+ 2013 Table 2 via A7", "near 4:1; m sin i, edge-on assumed")
    S["HD1461"] = exo("HD 1461", 1.02, [5.77152, 13.5052], [6.44, 5.59], [0.131, 0.228],
                      "Diaz+ 2016 Table 5 via A7", "e = 95% upper limits; near 7:3; m sin i")
    S["HD11964"] = exo("HD 11964", 1.12, [37.9196, 1935.0], [24.3, 201], [0.106, 0.101],
                       "Rosenthal+ 2021 via A7", "wide; m sin i")
    S["HD69830"] = exo("HD 69830", 0.86, [8.667, 31.56, 197], [10.2, 11.8, 18.1], [0.10, 0.13, 0.07],
                       "Lovis+ 2006 via A7", "historical fit; three-frequency near-commensurability; m sin i")
    S["HD96700"] = exo("HD 96700", 0.89, [8.1245, 19.88, 103.5], [8.9, 3.5, 12.7], [0.0, 0.0, 0.27],
                       "Unger+ 2021 via A7", "expected to fail the strong AMD test")
    return S


if __name__ == "__main__":
    for k, s in catalogue().items():
        print(f"{k:10s} n={s.n} mu={s.mu:.3e} nu={np.round(s.nu, 4)} a={np.round(s.a, 4)} P/P1="
              f"{np.round((s.a / s.a[0]) ** 1.5, 4)}")
