#!/usr/bin/env python3
"""Hamiltonians of the candidate applications, as Python functions of Jets (kamlib.Jet), period-1 angles.

Each model function returns H(z), z = [q1, q2, p1, p2].  Every H below uses only constants, +, *, /, integer powers,
sin, cos and (where marked) sqrt, i.e. it is a HamExpr of KAM/Certificate/Expr/Basic.lean, with sqrt as the one new primitive.
"""
import math
import numpy as np
from kamlib import Jet

TWO_PI = 2 * math.pi


def jsin(x):
    return x.sin() if isinstance(x, Jet) else np.sin(x)


def jcos(x):
    return x.cos() if isinstance(x, Jet) else np.cos(x)


def jsqrt(x):
    return x.sqrt() if isinstance(x, Jet) else np.sqrt(x)


# ---------------------------------------------------------------------------------------------
# spin-orbit
# ---------------------------------------------------------------------------------------------

def moon_A(e):
    """the 7 coefficients A_m(e), m = 1..7, of the SO proposal section 2.3 (Celletti (7.55))."""
    return {1: -e / 4 + e ** 3 / 32, 2: 0.5 - 5 * e ** 2 / 4 + 13 * e ** 4 / 32, 3: 7 * e / 4 - 123 * e ** 3 / 32,
            4: 17 * e ** 2 / 4 - 115 * e ** 4 / 12, 5: 845 * e ** 3 / 96 - 32525 * e ** 5 / 1536,
            6: 533 * e ** 4 / 32, 7: 228347 * e ** 5 / 7680}


def hansen_A(e, mmax=24, N=4096):
    """exact coefficients of (a/r)^3 exp(-2 i f) = sum_m 2 A_m exp(-i m l): A_m = X_m/2, the convention of moon_A
    (the potential is -eps sum_m A_m cos(2 q - m l), with q, l in radians)."""
    l = 2 * np.pi * np.arange(N) / N
    u = l.copy()
    for _ in range(50):
        u = u - (u - e * np.sin(u) - l) / (1 - e * np.cos(u))
    r = 1 - e * np.cos(u)
    cf = (np.cos(u) - e) / r
    sf = np.sqrt(1 - e * e) * np.sin(u) / r
    z = (cf + 1j * sf) ** 2           # exp(2 i f)
    g = (1 / r ** 3) * np.conj(z)     # (a/r)^3 exp(-2 i f)
    # g = sum_m c_m exp(-i m l)
    c = np.fft.fft(g) / N             # coefficient of exp(-i m l) at index m
    A = {}
    for m in range(-mmax, mmax + 1):
        A[m] = float(c[(-m) % N].real) / 2
    return A


def spin_rot(eps, A, delta=1.0, scale=1.0):
    """rotated frame about the p:... resonance: Q1 = q - (delta) phi, Q2 = phi, P1 = p, P2 = J + delta p.
    H = P1^2/2 - delta P1 + P2 + V(Q1 + delta Q2, Q2), V = -eps sum A_m cos 2 pi (2 q - m phi).
    delta = 1: synchronous (the SO client, O5); delta = 3/2: Mercury."""
    def H(z):
        q, ph, p, j = z
        V = 0.0
        for m, a in A.items():
            if a != 0:
                V = V + (-eps * a) * jcos(TWO_PI * (2 * q + (2 * delta - m) * ph))
        return (p * p) * 0.5 - p * delta + j + V
    return H


def spin_kepler(eps, e, delta=1.0):
    """EXACT Keplerian forcing with no Kepler equation.  Start from H = J + p^2/2 + V(q, l), V = -(eps/2)(a/r)^3 cos 2(q - f), period-1 variables.
    With phi the mean anomaly/2 pi, the map phi = w - (e/2 pi) sin(2 pi w), J = U/(1 - e cos 2 pi w) is symplectic (dphi ^ dJ = dw ^ dU), and it goes the easy way round: phi is
    a function of w.  On the level H = 0 the orbits of H are those of H' = rho H = U + rho (p^2/2 + V), rho = 1 - e cos 2 pi w = r/a (a time change ds = dt/rho).
    In w every forcing term is a rational function of cos, sin of 2 pi w:  r/a = rho, cos f = (cos u - e)/rho, sin f = b sin u/rho, b = sqrt(1 - e^2) a constant.
    Rotated frame Q1 = q - delta w, Q2 = w, P1 = p, P2 = U + delta p, as spin_rot.  Uses only const, add, mul, div, cosMode, sinMode: a HamExpr of version 1."""
    b = math.sqrt(1 - e * e)
    def H(z):
        Q, w, p, P2 = z
        u = TWO_PI * w
        cu, su = jcos(u), jsin(u)
        rho = 1.0 - e * cu
        ir = 1 / rho
        cf = (cu - e) * ir
        sf = (su * b) * ir
        c2f = cf * cf - sf * sf
        s2f = (cf * sf) * 2.0
        ph = TWO_PI * (2 * Q + 2 * delta * w)
        c2q, s2q = jcos(ph), jsin(ph)
        V = (ir * ir * ir) * (c2q * c2f + s2q * s2f) * (-eps / 2)
        return P2 - p * delta + rho * ((p * p) * 0.5 + V)
    return H


def spin_librational(eps, A, delta=1.0, a=None, c0=0.0, q0=0.0):
    """librational polar chart about (Q1, P1) = (q0, delta + c0):
       Q1 = q0 + a sqrt(2 I) sin(2 pi th), P1 = delta + c0 + sqrt(2 I)/a cos(2 pi th),
    with a chosen so the linearization is circular.  dQ1 ^ dP1 = 2 pi dth ^ dI, so X = 2 pi I is the action conjugate to the period-1 angle th.
    The clock pair (phi, P2) is unchanged."""
    def H(z):
        th, ph, X, j = z
        I = X * (1 / TWO_PI)
        r = jsqrt(I * 2.0)
        Q = q0 + a * (r * jsin(TWO_PI * th))
        P = delta + c0 + (r * jcos(TWO_PI * th)) * (1 / a)
        V = 0.0
        for m, co in A.items():
            if co != 0:
                V = V + (-eps * co) * jcos(TWO_PI * (2 * Q + (2 * delta - m) * ph))
        return (P * P) * 0.5 - P * delta + j + V
    return H


# ---------------------------------------------------------------------------------------------
# restricted three-body problem
# ---------------------------------------------------------------------------------------------

def cc07(eps):
    """Celletti-Chierchia 2007 truncated Sun-Jupiter-Victoria Hamiltonian (Delaunay), exactly as displayed in Celletti's
    survey mp_arc 07-303 sec. 6.4, with a = L^2, e = sqrt(1 - G^2/L^2), ell, g in radians.  Period-1 form: q = (ell, g)/2 pi, p = 2 pi (L, G) and
    H_p1(q, p) = 2 pi H(2 pi q, p/2 pi), which is canonical with time unit 2 pi, so frequencies are the rates of (ell, g) in rad per unit, here (1/L^3, -1)."""
    def H(z):
        q1, q2, P1, P2 = z
        L = P1 * (1 / TWO_PI)
        G = P2 * (1 / TWO_PI)
        l = TWO_PI * q1
        g = TWO_PI * q2
        a = L * L
        e = jsqrt(1.0 - (G * G) / (L * L))
        h0 = (-0.5) * (1 / (L * L)) - G
        a2 = a * a; a3 = a2 * a; a4 = a2 * a2; a5 = a3 * a2
        f = (1.0 + a2 * 0.25 + (9 / 64) * a4 + (3 / 8) * (a2 * (e * e))
             + (-(0.5 + (9 / 16) * a2) * (a2 * e)) * jcos(l)
             + ((3 / 8) * a3 * 1.0 + (15 / 64) * a5) * jcos(l + g)
             + (-(9 / 4 + (5 / 4) * a2) * (a2 * e)) * jcos(l + 2 * g)
             + ((3 / 4) * a2 + (5 / 16) * a4) * jcos(2 * l + 2 * g)
             + ((3 / 4) * (a2 * e)) * jcos(3 * l + 2 * g)
             + ((5 / 8) * a3 + (35 / 128) * a5) * jcos(3 * l + 3 * g)
             + ((35 / 64) * a4) * jcos(4 * l + 4 * g)
             + ((63 / 128) * a5) * jcos(5 * l + 5 * g))
        return (h0 - f * eps) * TWO_PI
    return H


def pcr3bp_polar(mu, r0, kap):
    """Exact PCR3BP, rotating barycentric frame, Jupiter at (1 - mu, 0), n_J = 1 (rad):
       H = p_r^2/2 + G^2/(2 r^2) - G - (1 - mu)/r1 - mu/r2,
    with the radial polar chart r = r0 + kap sqrt(2 I) sin(alpha), p_r = sqrt(2 I)/kap cos(alpha).
    Period-1 form as in cc07: q = (theta, alpha)/2 pi, p = 2 pi (G, I), H_p1 = 2 pi H."""
    def H(z):
        q1, q2, P1, P2 = z
        G = P1 * (1 / TWO_PI)
        I = P2 * (1 / TWO_PI)
        th = TWO_PI * q1
        al = TWO_PI * q2
        rt = jsqrt(I * 2.0)
        r = r0 + kap * (rt * jsin(al))
        pr = (rt * jcos(al)) * (1 / kap)
        c = jcos(th)
        r1 = jsqrt(r * r + (2 * mu) * (r * c) + mu * mu)
        r2 = jsqrt(r * r - (2 * (1 - mu)) * (r * c) + (1 - mu) ** 2)
        return ((pr * pr) * 0.5 + (G * G) * (1 / (r * r)) * 0.5 - G - (1 - mu) * (1 / r1) - mu * (1 / r2)) * TWO_PI
    return H


def hill_polar(m, r0, kap):
    """Planar Hill problem in Moon units (Earth GM = 1, Moon mean motion ~ 1), Sun mean motion m:
       H = p_r^2/2 + G^2/(2 r^2) - m G - 1/r - m^2 r^2 (3 cos^2 theta - 1)/2,
    theta measured from the Sun direction in the frame rotating at m.  Same radial polar chart as pcr3bp_polar."""
    def H(z):
        q1, q2, P1, P2 = z
        G = P1 * (1 / TWO_PI)
        I = P2 * (1 / TWO_PI)
        th = TWO_PI * q1
        al = TWO_PI * q2
        rt = jsqrt(I * 2.0)
        r = r0 + kap * (rt * jsin(al))
        pr = (rt * jcos(al)) * (1 / kap)
        c = jcos(th)
        return ((pr * pr) * 0.5 + (G * G) * (1 / (r * r)) * 0.5 - m * G - (1 / r)
                - (m * m) * ((r * r) * ((c * c) * 3.0 - 1.0) * 0.5)) * TWO_PI
    return H


def henon_heiles_polar(r0, kap):
    """Hénon-Heiles in the plane polar chart: x = r cos th, y = r sin th, V = r^2/2 + r^3 sin(3 th)/3.
       H = p_r^2/2 + G^2/(2 r^2) + r^2/2 + r^3 sin(3 th)/3, loop tori (G != 0)."""
    def H(z):
        q1, q2, P1, P2 = z
        G = P1 * (1 / TWO_PI)
        I = P2 * (1 / TWO_PI)
        th = TWO_PI * q1
        al = TWO_PI * q2
        rt = jsqrt(I * 2.0)
        r = r0 + kap * (rt * jsin(al))
        pr = (rt * jcos(al)) * (1 / kap)
        return ((pr * pr) * 0.5 + (G * G) * (1 / (r * r)) * 0.5 + (r * r) * 0.5 + (r * r * r) * ((1 / 3) * jsin(3 * th))) * TWO_PI
    return H


def trojan_shear(mu, kap_r, kap_t, G0=1.0, th0=math.pi / 3, rho0=0.0):
    """PCR3BP near L4 in guiding-centre form.  The exact canonical shear  r = rho + G^2, theta = th + 2 G p  (generating function
    F = (r - G^2) p + theta G) centres the epicycle on the circular radius of the current G; then the polar charts
       rho = kap_r sqrt(2 I) sin(alpha), p = sqrt(2 I)/kap_r cos(alpha),
       th = th0 + kap_t sqrt(2 Y) sin(beta), G = G0 + sqrt(2 Y)/kap_t cos(beta).
    Polynomial charts plus sqrt, so H stays a HamExpr with sqrt.  Angles (alpha, beta)/2 pi, actions 2 pi (I, Y)."""
    def H(z):
        q1, q2, P1, P2 = z
        I = P1 * (1 / TWO_PI)
        Y = P2 * (1 / TWO_PI)
        al = TWO_PI * q1
        be = TWO_PI * q2
        rI = jsqrt(I * 2.0)
        rY = jsqrt(Y * 2.0)
        rho = rho0 + kap_r * (rI * jsin(al))
        p = (rI * jcos(al)) * (1 / kap_r)
        G = G0 + (rY * jcos(be)) * (1 / kap_t)
        th = th0 + kap_t * (rY * jsin(be)) + (G * p) * 2.0
        r = rho + G * G
        c = jcos(th)
        r1 = jsqrt(r * r + (2 * mu) * (r * c) + mu * mu)
        r2 = jsqrt(r * r - (2 * (1 - mu)) * (r * c) + (1 - mu) ** 2)
        return ((p * p) * 0.5 + (G * G) * (1 / (r * r)) * 0.5 - G - (1 - mu) * (1 / r1) - mu * (1 / r2)) * TWO_PI
    return H


def henon_heiles_t(t, r0, kap):
    """Hénon-Heiles with the cubic term scaled by t (t = 0: isotropic oscillator), plane polar chart."""
    def H(z):
        q1, q2, P1, P2 = z
        G = P1 * (1 / TWO_PI)
        I = P2 * (1 / TWO_PI)
        th = TWO_PI * q1
        al = TWO_PI * q2
        rt = jsqrt(I * 2.0)
        r = r0 + kap * (rt * jsin(al))
        pr = (rt * jcos(al)) * (1 / kap)
        return ((pr * pr) * 0.5 + (G * G) * (1 / (r * r)) * 0.5 + (r * r) * 0.5 + (r * r * r) * ((t / 3) * jsin(3 * th))) * TWO_PI
    return H
