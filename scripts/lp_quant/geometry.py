#!/usr/bin/env python3
"""LP-QUANT: the sharp geometry of LP:MAIN Lemmas 3-6 as numbers.  Untrusted design tooling, double precision.

 pair_threshold     B_ij (3): contact minimization (15); the objective is convex on the fixed interval, so the tangent
                    at the numerical minimizer is a LOWER bound of B_ij (label `bounded`, modulo outward rounding).
 grad_B             envelope-theorem gradient of B at I (active branch).
 Omega_B, budgets   the modulus of Lemma 6 and the action budgets of (39), with the signed sharpening
                    Phi(I) = sum I - B(I) and the energy-shell sharpening.
 dstar, dpair       LP0's constants: (16)/(41) closed form and the sharp values (1-D convex problems) that replace the
                    compactness argument of Lemma 5.
"""
import itertools
import math
import numpy as np


def D(u):
    return 1 - np.sqrt(np.maximum(1 - u * u, 0.0))


def Dp(u):
    return u / np.sqrt(np.maximum(1 - u * u, 1e-30))


def Dinv(y):
    """Inverse of D on [0,1]."""
    return np.sqrt(np.clip(1 - (1 - y) ** 2, 0, 1))


def amd(I, e, inc_deg=None):
    """C = sum I_i (1 - sqrt(1-e_i^2) cos i_i); with i_i the inclination to the invariable plane this is exact (MAIN (13))."""
    c = 1.0 if inc_deg is None else np.cos(np.radians(inc_deg))
    return float(np.sum(I * (1 - np.sqrt(1 - e * e) * c)))


def pair_contact(Ii, Ij, ai, aj):
    """Minimize g(u) = Ii D(u) + Ij D(1-alpha-alpha u) on [0, min(1,(1-alpha)/alpha)] by bisection on g' (g is convex).
    Returns (u, v, value, lower_bound)."""
    alpha = ai / aj
    umax = min(1.0, (1 - alpha) / alpha)

    def gp(u):
        v = 1 - alpha - alpha * u
        return Ii * Dp(u) - alpha * Ij * Dp(v)

    lo, hi = 0.0, umax * (1 - 1e-15)
    if gp(lo) >= 0:
        lo = hi = 0.0
    elif gp(hi) <= 0:
        lo = hi
    else:
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if gp(mid) > 0:
                hi = mid
            else:
                lo = mid
            if hi - lo < 1e-16:
                break
    u = 0.5 * (lo + hi)
    v = 1 - alpha - alpha * u
    val = float(Ii * D(u) + Ij * D(v))
    lb = val - abs(float(gp(u))) * umax  # convexity: g(x) >= g(u) + g'(u)(x-u)
    return u, v, val, lb


def thresholds(I, nu):
    """(B, B_cross, B_star, list of (i, u, v, B_ij, lower bound)), MAIN (3); the minimum runs over adjacent pairs."""
    a = (I / nu) ** 2
    pairs = []
    for i in range(len(I) - 1):
        u, v, val, lb = pair_contact(I[i], I[i + 1], a[i], a[i + 1])
        pairs.append((i, u, v, val, lb))
    Bc = min(p[3] for p in pairs)
    Bs = float(np.min(I))
    return min(Bc, Bs), Bc, Bs, pairs


def B(I, nu):
    return thresholds(I, nu)[0]


def B_lower(I, nu):
    a = thresholds(I, nu)
    return min(min(p[4] for p in a[3]), a[2])


def grad_B(I, nu):
    """Gradient of the active branch.  B_ij: alpha = a_i/a_j, v = 1-alpha-alpha u:
    d_i B_ij = D(u) - 2 alpha I_j D'(v)(1+u)/I_i,  d_j B_ij = D(v) + 2 alpha D'(v)(1+u)."""
    b, bc, bs, pairs = thresholds(I, nu)
    g = np.zeros(len(I))
    if bs <= bc:
        g[int(np.argmin(I))] = 1.0
        return g
    i, u, v, val, _ = min(pairs, key=lambda p: p[3])
    a = (I / nu) ** 2
    al = a[i] / a[i + 1]
    g[i] = D(u) - 2 * al * I[i + 1] * Dp(v) * (1 + u) / I[i]
    g[i + 1] = D(v) + 2 * al * Dp(v) * (1 + u)
    return g


def _corners(I0, r):
    n = len(I0)
    for sg in itertools.product((-1.0, 1.0), repeat=n):
        yield I0 + r * np.array(sg)


def lip_B(I0, nu, rU):
    """sup of |grad B|_1 on the sup-ball of radius rU about I0, sampled at the corners, faces' centres and the centre
    (label `estimated`; B is piecewise C^1 and the gradient varies by O(rU) so the sample is accurate for small rU)."""
    n = len(I0)
    pts = [I0] + list(_corners(I0, rU)) + [I0 + rU * s * np.eye(n)[i] for i in range(n) for s in (-1, 1)]
    return max(float(np.sum(np.abs(grad_B(p, nu)))) for p in pts)


def Omega_B(I0, nu, r, rU=None):
    """Lemma 6's modulus on U = sup-ball(I0, rU): the bound Lip(B) r."""
    rU = r if rU is None else rU
    return lip_B(I0, nu, rU) * r


def phi_loss(I0, nu, r):
    """Signed loss: max over the r-box of [Phi(I) - Phi(I0)], Phi = sum I - B(I).  By (13) and (17), this is what actually
    erodes the margin, since C(t) - B(I(t)) = C(0) - B(I0) + Phi(I(t)) - Phi(I0)."""
    p0 = float(np.sum(I0)) - B(I0, nu)
    return max(float(np.sum(p)) - B(p, nu) - p0 for p in _corners(I0, r))


def phi_loss_energy(I0, nu, r, omega, eshell=0.0):
    """As phi_loss, on the energy shell |omega.(I-I0)| <= eshell: the box vertices with one free coordinate."""
    n = len(I0)
    grad = 1 - grad_B(I0, nu)
    best = -math.inf
    p0 = float(np.sum(I0)) - B(I0, nu)
    for j in range(n):
        others = [i for i in range(n) if i != j]
        for sg in itertools.product((-1.0, 1.0), repeat=n - 1):
            d = np.zeros(n)
            for s, i in zip(sg, others):
                d[i] = r * s
            for es in (-eshell, eshell):
                dj = (es - float(omega[others] @ d[others])) / omega[j]
                if abs(dj) <= r:
                    d[j] = dj
                    p = I0 + d
                    best = max(best, float(np.sum(p)) - B(p, nu) - p0)
    return best


def solve_budget(fun, target, hi):
    """Largest r in (0, hi] with fun(r) <= target (fun increasing)."""
    if fun(hi) <= target:
        return hi
    lo = 0.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if fun(mid) <= target:
            lo = mid
        else:
            hi = mid
    return lo


def budgets(I0, nu, delta, omega):
    """Allowed action drift r under three bookkeepings.
      r_lit_half : n r + Omega_B(r) <= delta/2     (orchestrator's Lambda-only budget: margin delta/2 left, LP0 with m = delta/2)
      r_lit_q    : n r + Omega_B(r) <= delta/4     (the budget (39) of the proof, `exists_budget_radius`)
      r_signed   : max box Phi loss <= delta/2     (sharpening, same exact identity)
      r_energy   : same on the energy shell       (sharpening, exact energy integral; shell thickness set by the caller)"""
    n = len(I0)
    top = 0.45 * float(np.min(I0))
    f1 = lambda r: n * r + Omega_B(I0, nu, r)
    out = dict(r_lit_half=solve_budget(f1, delta / 2, top), r_lit_q=solve_budget(f1, delta / 4, top),
               r_signed=solve_budget(lambda r: phi_loss(I0, nu, r), delta / 2, top))
    out["r_energy"] = solve_budget(lambda r: phi_loss_energy(I0, nu, r, omega), delta / 2, top)
    return out


def weighted_loss(I0, nu, rvec):
    """Margin lost for a per-planet box |Lambda_i - I0_i| <= rvec_i: max over the vertices of Phi(I) - Phi(I0).  The sup-norm budget of
    the proof is the case rvec = r(1,...,1); it is too crude when the heaviest planet oscillates most but the margin is set
    by a light pair (J-S-U-N)."""
    n = len(I0)
    p0 = float(np.sum(I0)) - B(I0, nu)
    best = -math.inf
    for sg in itertools.product((-1.0, 1.0), repeat=n):
        p = I0 + np.array(sg) * rvec
        best = max(best, float(np.sum(p)) - B(p, nu) - p0)
    return best


def dstar_formula(I, nu, m):
    """(16)/(41) with amendment N11: d_* = a_min m^2 / (2 I_max^2)."""
    a = (I / nu) ** 2
    return float(np.min(a) * m * m / (2 * np.max(I) ** 2))


def dstar_sharp(I, nu, m):
    """min_i a_i (1 - e_i^max), e_i^max from I_i D(e_i) <= B - m: exact solution of the compactness problem at fixed I."""
    b = B(I, nu)
    a = (I / nu) ** 2
    return float(np.min(a * (1 - Dinv(np.clip((b - m) / I, 0, 1)))))


def dpair_sharp(I, nu, m):
    """Minimum over (e_i, e_{i+1}) with I_i D(e_i) + I_{i+1} D(e_{i+1}) <= B - m of the adjacent gap: the constant Lemma 5
    gets by compactness.  Convex: minimize the linear gap on a convex sublevel set; scan the boundary."""
    b = B(I, nu)
    a = (I / nu) ** 2
    best = math.inf
    for i in range(len(I) - 1):
        umax = float(Dinv(min(1.0, (b - m) / I[i])))
        us = np.linspace(0, umax, 20001)
        vs = Dinv(np.clip((b - m - I[i] * D(us)) / I[i + 1], 0, 1))
        best = min(best, float(np.min(a[i + 1] * (1 - vs) - a[i] * (1 + us))))
    return best


def ecc_caps(I, C):
    """e_i^max on the AMD ball sum I_i D(e_i) <= C."""
    return Dinv(np.clip(C / I, 0, 1))


if __name__ == "__main__":
    import sys, os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from systems import catalogue
    for k, s in catalogue().items():
        I = s.I0
        b, bc, bs, pairs = thresholds(I, s.nu)
        C = amd(I, s.e, s.inc)
        print(f"{k:9s} B={b:.6g} (pair {min(pairs, key=lambda p: p[3])[0]}) C={C:.6g} beta=C/B={C / b:.3f} delta={b - C:.5g}"
              f" lb-gap={b - B_lower(I, s.nu):.1e}")
