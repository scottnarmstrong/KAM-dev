#!/usr/bin/env python3
"""Track W, milestone W0: exact and numerical checks of the normalization of the cubic Dirichlet wave equation

    u_tt = u_xx - m u - u^3  on (0, pi),  u(t,0) = u(t,pi) = 0,  m > 0,

in the conventions of blueprint-W/parts/w0-conventions.tex:
phi_j = sqrt(2/pi) sin(jx), lambda_j = sqrt(j^2+m), u = sum q_j phi_j / sqrt(lambda_j), u_t = sum sqrt(lambda_j) p_j phi_j,
H = 1/2 sum lambda_j (q_j^2+p_j^2) + 1/4 int u^4, actions I_j = (q_j^2+p_j^2)/2 = |z_j|^2, z_j = (q_j + i p_j)/sqrt 2.

Usage:  python3 scripts/wave/w0_checks.py      (sympy + numpy; about a minute)
Every check prints PASS/FAIL; the script exits nonzero on any FAIL. Output of the recorded run is at the end.
"""
import itertools
import math
import sys

import numpy as np
import sympy as sp

sys.stdout.reconfigure(line_buffering=True)

FAILS = []


def check(name, ok, detail=""):
    print(f"[{'PASS' if ok else 'FAIL'}] {name}" + (f": {detail}" if detail else ""))
    if not ok:
        FAILS.append(name)


x = sp.symbols("x", real=True)
m = sp.symbols("m", positive=True)


def lam(j, mm=m):
    return sp.sqrt(j**2 + mm)


# ---------------------------------------------------------------- 1. sine-product integrals g_{ijkl}
def g_closed(i, j, k, l):
    """Closed form (Lemma bpW:w0:quartic-coeff): g_{ijkl} = int_0^pi phi_i phi_j phi_k phi_l dx."""
    d = lambda c: 1 if c else 0
    plus = d(i + l == j + k) + d(i + k == j + l) + d(i + j == k + l)
    minus = d(i == j + k + l) + d(j == i + k + l) + d(k == i + j + l) + d(l == i + j + k)
    return sp.Rational(plus - minus) / (2 * sp.pi)


def g_int(i, j, k, l):
    """Integer numerator 2*pi*g_ijkl of the closed form."""
    plus = (i + l == j + k) + (i + k == j + l) + (i + j == k + l)
    minus = (i == j + k + l) + (j == i + k + l) + (k == i + j + l) + (l == i + j + k)
    return int(plus) - int(minus)


def g_exact(i, j, k, l):
    phi = lambda n: sp.sqrt(2 / sp.pi) * sp.sin(n * x)
    return sp.simplify(sp.integrate(sp.expand(sp.simplify(sp.fu(phi(i) * phi(j) * phi(k) * phi(l)))), (x, 0, sp.pi)))


print("== 1. quartic sine integrals ==")
bad = [t for t in itertools.combinations_with_replacement(range(1, 4), 4) if sp.simplify(g_exact(*t) - g_closed(*t)) != 0]
check("closed form of g_ijkl vs exact symbolic integral, sorted (i,j,k,l) in {1..3}^4", not bad, f"mismatches {bad}")
# midpoint rule with M nodes integrates cos(nx) on [0,pi] exactly for 0 < |n| < 2M; the integrand has degree <= 4*12
M = 256
xs = (np.arange(M) + 0.5) * math.pi / M
PH = np.sqrt(2 / math.pi) * np.sin(np.outer(np.arange(1, 13), xs))
err = 0.0
for i, j, k, l in itertools.product(range(12), repeat=4):
    val = (math.pi / M) * np.sum(PH[i] * PH[j] * PH[k] * PH[l])
    err = max(err, abs(val - g_int(i + 1, j + 1, k + 1, l + 1) / (2 * math.pi)))
check("closed form vs exact quadrature for all ordered (i,j,k,l) in {1..12}^4", err < 1e-12, f"max error {err:.1e}")
check("g_iiii = 3/(2 pi)", all(g_closed(i, i, i, i) == sp.Rational(3, 2) / sp.pi for i in range(1, 30)))
check("g_iijj = 1/pi (i != j)", all(g_closed(i, i, j, j) == 1 / sp.pi for i in range(1, 20) for j in range(1, 20) if i != j))
check("g_1113 = -1/(2 pi) (a non-resonant quartic term)", g_closed(1, 1, 1, 3) == -1 / (2 * sp.pi))
# selection rule
sel_ok = all(
    g_closed(i, j, k, l) == 0
    for i, j, k, l in itertools.product(range(1, 9), repeat=4)
    if not any(s1 * i + s2 * j + s3 * k + l == 0 for s1, s2, s3 in itertools.product((1, -1), repeat=3))
)
check("selection rule: g_ijkl = 0 unless +-i+-j+-k+-l = 0 (indices <= 8)", sel_ok)
# P96-W (11): G_iijj = (2 + delta_ij)/(2 pi lambda_i lambda_j) with the lambda-weights of P96-W (10)
check("P96-W (11) agrees with g/(sqrt(lambda^4)) for i,j <= 6",
      all(sp.simplify(g_closed(i, i, j, j) / (lam(i) * lam(j)) - (2 + (i == j)) / (2 * sp.pi * lam(i) * lam(j))) == 0
          for i in range(1, 7) for j in range(1, 7)))

# ---------------------------------------------------------------- 2. symplectic / complex conventions
print("== 2. coordinates ==")
q, p, I, ph, lj = sp.symbols("q p I phi lambda_j", real=True)
Q = sp.sqrt(2 * I) * sp.cos(ph)
P = -sp.sqrt(2 * I) * sp.sin(ph)
jac = sp.simplify(sp.Matrix([[sp.diff(Q, ph), sp.diff(Q, I)], [sp.diff(P, ph), sp.diff(P, I)]]).det())
check("(phi, I) -> (q,p) = (sqrt(2I) cos phi, -sqrt(2I) sin phi) has Jacobian det 1, i.e. dq^dp = dphi^dI", jac == 1, f"det = {jac}")
check("I = (q^2+p^2)/2 on that chart", sp.simplify((Q**2 + P**2) / 2 - I) == 0)
z = (Q + sp.I * P) / sp.sqrt(2)
check("z = (q+ip)/sqrt2 = sqrt(I) e^{-i phi}, |z|^2 = I", sp.simplify(z - sp.sqrt(I) * sp.exp(-sp.I * ph)) == 0)
# linear flow qdot = lambda p, pdot = -lambda q gives zdot = -i lambda z
zdot = (lj * p + sp.I * (-lj * q)) / sp.sqrt(2)
check("q' = lam p, p' = -lam q  =>  z' = -i lam z", sp.simplify(zdot - (-sp.I * lj * (q + sp.I * p) / sp.sqrt(2))) == 0)
# dq^dp = i dz ^ dzbar: coefficient of dq^dp in dz^dzbar is det [[1/sqrt2, i/sqrt2],[1/sqrt2, -i/sqrt2]]
dzdz = sp.Matrix([[1, sp.I], [1, -sp.I]]) / sp.sqrt(2)
check("i dz^dzbar = dq^dp", sp.simplify(sp.I * dzdz.det()) == 1, f"i*det = {sp.simplify(sp.I*dzdz.det())}")

# ---------------------------------------------------------------- 3. averaged quartic term, A and B
print("== 3. averaged quartic term: twist A and coupling B ==")
N = 4
Is = sp.symbols(f"I1:{N+1}", positive=True)
cs = sp.symbols(f"c1:{N+1}")
Lam = [lam(j) for j in range(1, N + 1)]
qs = [sp.sqrt(2 * Is[j]) * cs[j] for j in range(N)]  # q_j = sqrt(2 I_j) cos phi_j, c_j = cos phi_j
G4 = sp.Rational(1, 4) * sum(
    g_closed(i + 1, j + 1, k + 1, l + 1) * qs[i] * qs[j] * qs[k] * qs[l] / sp.sqrt(Lam[i] * Lam[j] * Lam[k] * Lam[l])
    for i, j, k, l in itertools.product(range(N), repeat=4))
G4 = sp.expand(G4)
moments = {0: 1, 1: 0, 2: sp.Rational(1, 2), 3: 0, 4: sp.Rational(3, 8)}  # E[cos^n] over independent angles


def average(expr):
    poly = sp.Poly(expr, *cs)
    out = 0
    for mon, coeff in poly.terms():
        w = coeff
        for e in mon:
            w *= moments[e]
        out += w
    return sp.expand(out)


avgG = average(G4)
A_formula = lambda i, j: (sp.Rational(9, 8) if i == j else sp.Rational(3, 2)) / (sp.pi * lam(i) * lam(j))
target = sum(sp.Rational(1, 2) * A_formula(i, j) * Is[i - 1] * Is[j - 1] for i in range(1, N + 1) for j in range(1, N + 1))
check("<G>(I) = 1/2 sum_{i,j} A_ij I_i I_j with A_ii = 9/(8 pi lam_i^2), A_ij = 3/(2 pi lam_i lam_j) (modes 1..4)",
      sp.simplify(avgG - sp.expand(target)) == 0)
A = sp.Matrix(2, 2, lambda a, b: A_formula(a + 1, b + 1))
B = sp.Matrix(N - 2, 2, lambda a, b: A_formula(a + 3, b + 1))
print("   A =", sp.simplify(A))
print("   B (rows j = 3..4, cols i = 1,2) =", sp.simplify(B))
check("B_ji = 3/(2 pi lam_j lam_i) for normal j, tangential i = coefficient of I_i Z_j in <G>",
      all(sp.simplify(sp.diff(avgG, Is[i], Is[jn]) - A_formula(jn + 1, i + 1)) == 0 for i in range(2) for jn in range(2, N)))
detA = sp.factor(sp.simplify(A.det()))
print("   det A =", detA)
check("det A = -63/(64 pi^2 (1+m)(4+m))", sp.simplify(detA + sp.Rational(63, 64) / (sp.pi**2 * (1 + m) * (4 + m))) == 0)
Dm = sp.diag(*[1 / lam(j) for j in (1, 2)])
check("A = 3/(8 pi) D (4 * 11^T - Id) D", sp.simplify(A - sp.Rational(3, 8) / sp.pi * Dm * (4 * sp.ones(2, 2) - sp.eye(2)) * Dm) == sp.zeros(2, 2))
check("det A has no zero for m > 0 (numerator constant, denominator positive)",
      sp.solve(sp.numer(sp.together(detA)), m) == [])

# ---------------------------------------------------------------- 4. E-PDE-W-1: the printed P96-W chain
print("== 4. P96-W printed quartic chain (E-PDE-W-1) ==")
Gbar_printed = lambda i, j: (sp.Integer(6) / sp.pi) * (4 - (1 if i == j else 0)) / (lam(i) * lam(j))
ratios = {(i, j): sp.simplify(Gbar_printed(i, j) / A_formula(i, j)) for i in (1, 2, 3) for j in (1, 2, 3)}
check("printed Gbar_ij / A_ij = 16 for all i, j", set(ratios.values()) == {16}, f"ratios {set(ratios.values())}")
# where the 16 comes from: q_i = (z_i + zbar_i)/sqrt2, so q^4 = (1/4) prod (z+zbar); p.282 line 1 omits this 1/4, line 2 drops the 1/4 of (9)
zz = sp.symbols("z", complex=True)
zb = sp.conjugate(zz)
qz = (zz + zb) / sp.sqrt(2)
coef = sp.Poly(sp.expand(qz**4), zz, zb).coeff_monomial(zz**2 * zb**2)
check("q^4 with q = (z+zbar)/sqrt2 has |z|^4-coefficient 6/4 (so (1/4) G q^4 -> (1/16) G (z+zbar)^4)", coef == sp.Rational(3, 2))
# counting of P96-W p.284 from the printed sum' G w^4 (no prefactor): Gbar_ii = 12 G_iiii, Gbar_ij = 24 G_iijj
Gw = lambda i, j: g_closed(i, i, j, j) / (lam(i) * lam(j))
check("p.284 counting 24 G_iijj, 12 G_iiii reproduces the printed Gbar", all(
    sp.simplify((24 if i != j else 12) * Gw(i, j) - Gbar_printed(i, j)) == 0 for i in (1, 2, 3) for j in (1, 2, 3)))
check("with the correct prefactor 1/16: (1/16)*(24 G_iijj, 12 G_iiii) = A", all(
    sp.simplify(sp.Rational(1, 16) * (24 if i != j else 12) * Gw(i, j) - A_formula(i, j)) == 0 for i in (1, 2, 3) for j in (1, 2, 3)))
check("p.287 convention I = |z|^2/2 would turn Gbar = 1/2 sum Gbar |z|^2|z|^2 into 1/2 <(4 Gbar) I, I>",
      sp.expand(sp.Rational(1, 2) * (2 * I) * (2 * I)) == sp.expand(sp.Rational(1, 2) * 4 * I * I))

# ---------------------------------------------------------------- 5. nondegeneracy (A2), (A3) for J = {1,2}
print("== 5. nondegeneracy for J = {1,2} ==")


def lam_f(j, mv):
    return math.sqrt(j * j + mv)


def A3_min(mv, K=12, NMAX=40):
    """min over (k,l), 1<=|l|<=2, |k_i|<=K, normal modes 3..NMAX, of max(|const part|, |linear part|)."""
    l1, l2 = lam_f(1, mv), lam_f(2, mv)
    Am = np.array([[9 / (8 * math.pi * l1 * l1), 3 / (2 * math.pi * l1 * l2)], [3 / (2 * math.pi * l1 * l2), 9 / (8 * math.pi * l2 * l2)]])
    bvec = np.array([1 / l1, 1 / l2])
    ls = []
    for a in range(3, NMAX + 1):
        for s in (1, -1):
            ls.append({a: s})
            ls.append({a: 2 * s})
            for b in range(a + 1, NMAX + 1):
                for t in (1, -1):
                    ls.append({a: s, b: t})
    best = math.inf
    for k1 in range(-K, K + 1):
        for k2 in range(-K, K + 1):
            kv = np.array([k1, k2])
            for l in ls:
                const = k1 * l1 + k2 * l2 + sum(c * lam_f(j, mv) for j, c in l.items())
                lin = Am @ kv + sum(c * 3 / (2 * math.pi * lam_f(j, mv)) for j, c in l.items()) * bvec
                best = min(best, max(abs(const), np.max(np.abs(lin))))
    return best


for mv in (0.1, 1.0, 10.0, 43.0):
    v = A3_min(mv)
    check(f"(A3) affine non-identity, m = {mv}: min over |k_i|<=12, normal modes 3..40, of max(|const|,|linear|)", v > 1e-9, f"{v:.3e}")
check("(A2) <l,beta> != 0: min |lam_a +- lam_b|, |lam_a| over 3<=a<b<=200, m = 0.1", min(
    [abs(lam_f(a, 0.1) - lam_f(b, 0.1)) for a in range(3, 200) for b in range(a + 1, 201)] + [lam_f(3, 0.1)]) > 0)

# ---------------------------------------------------------------- 6. qualitative quartic nonresonance (all indices)
print("== 6. quartic nonresonance: sigma.lambda = 0 with g != 0 only for pairings ==")


def nonres_min(mv, NMAX=30):
    lv = [0.0] + [lam_f(j, mv) for j in range(1, NMAX + 1)]
    best = math.inf
    for i, j, k, l in itertools.combinations_with_replacement(range(1, NMAX + 1), 4):
        if g_int(i, j, k, l) == 0:
            continue  # g is symmetric
        idx = (i, j, k, l)
        for sig in itertools.product((1, -1), repeat=4):
            pos = sorted(idx[t] for t in range(4) if sig[t] > 0)
            neg = sorted(idx[t] for t in range(4) if sig[t] < 0)
            if pos == neg:
                continue  # trivial pairing z_a z_b zbar_a zbar_b
            best = min(best, abs(sum(sig[t] * lv[idx[t]] for t in range(4))))
    return best


for mv in (0.01, 0.1, 1.0, 10.0):
    v = nonres_min(mv)
    check(f"m = {mv}: min |sum sigma_t lam_(i_t)| over non-trivial sign patterns, indices <= 30, g != 0", v > 0, f"{v:.3e}")

# ---------------------------------------------------------------- 7. Duffing check
print("== 7. one-mode Duffing consistency ==")
amp, lamj, eps = sp.symbols("a lambda epsilon", positive=True)
lind = 3 * eps * amp**2 / (8 * lamj)  # Lindstedt shift for x'' + lam^2 x + eps x^3 = 0
Ij = lamj * amp**2 / 2  # x = q/sqrt(lam), q amplitude sqrt(2 I)  =>  a^2 = 2 I / lam
nf = sp.Rational(9, 8) / (sp.pi * lamj**2) * Ij  # A_jj I_j
check("Lindstedt shift with eps = g_jjjj = 3/(2pi) equals A_jj I_j", sp.simplify(lind.subs(eps, sp.Rational(3, 2) / sp.pi) - nf) == 0)


def period_numeric(lv, a0, epsv):
    # x'' = -lv^2 x - epsv x^3, x(0) = a0, x'(0) = 0; quarter period by RK4 until x' changes sign -> x = 0 crossing
    def f(s):
        return np.array([s[1], -lv * lv * s[0] - epsv * s[0] ** 3])
    h = 1e-4
    s = np.array([a0, 0.0])
    t = 0.0
    while True:
        k1 = f(s); k2 = f(s + h / 2 * k1); k3 = f(s + h / 2 * k2); k4 = f(s + h * k3)
        s_new = s + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        if s_new[0] < 0:  # first zero of x at t = T/4; linear interpolation
            tc = t + h * s[0] / (s[0] - s_new[0])
            return 4 * tc
        s, t = s_new, t + h


for mv in (0.1, 1.0, 10.0):
    lv = math.sqrt(1 + mv)
    ratios_d = []
    for a0 in (0.2, 0.1, 0.05):
        T = period_numeric(lv, a0, 1.5 / math.pi)
        Iv = lv * a0 * a0 / 2
        ratios_d.append((2 * math.pi / T - lv) / (9 * Iv / (8 * math.pi * lv * lv)))
    check(f"m = {mv}, mode 1: (omega_numeric - lam) / (A_11 I) -> 1 as amplitude halves (printed P96-W value would give 1/16)",
          abs(ratios_d[-1] - 1) < 0.01 and abs(ratios_d[-1] - 1) < abs(ratios_d[0] - 1), " ".join(f"{e:.5f}" for e in ratios_d))

# ---------------------------------------------------------------- 8. cubic gradient bound
print("== 8. cubic gradient bound ||G_q(q)||_{1,2} <= C ||q||_{1,1}^3,  C = 8(1+2 zeta(3))/pi ==")
zeta3 = 1.2020569031595942
Cbound = 8 * (1 + 2 * zeta3) / math.pi
print(f"   C = {Cbound:.6f}")
rng = np.random.default_rng(0)


def norm_ap(v, a, pp):
    j = np.arange(1, len(v) + 1)
    return math.sqrt(np.sum(np.abs(v) ** 2 * j ** (2 * pp) * np.exp(2 * a * j)))


def Gq(qv, mv, M=4096):
    # sine coefficients via quadrature on a uniform grid (exact for trigonometric polynomials of degree < 2M)
    n = len(qv)
    j = np.arange(1, n + 1)
    lv = np.sqrt(j * j + mv)
    xs = (np.arange(M) + 0.5) * math.pi / M
    S = np.sqrt(2 / math.pi) * np.sin(np.outer(xs, j))
    U = S @ (qv / np.sqrt(lv))
    nl = 3 * n + 1
    jl = np.arange(1, nl + 1)
    Sl = np.sqrt(2 / math.pi) * np.sin(np.outer(xs, jl))
    coeff = (math.pi / M) * (Sl.T @ (U**3))
    return coeff / np.sqrt(np.sqrt(jl * jl + mv))


worst = 0.0
for mv in (0.1, 1.0, 10.0):
    for trial in range(20):
        n = 12
        qv = rng.normal(size=n) * np.exp(-np.arange(1, n + 1) * rng.uniform(1.0, 2.5))
        gv = Gq(qv, mv)
        r = norm_ap(gv, 1, 2) / norm_ap(qv, 1, 1) ** 3
        worst = max(worst, r)
check("max over 60 random trials of ||G_q||_{1,2} / ||q||_{1,1}^3 <= C", worst <= Cbound, f"max ratio {worst:.4f}")
# trilinear-formula check: (G_q)_l = lam_l^{-1/2} sum g_ijkl q_i q_j q_k / sqrt(lam_i lam_j lam_k)
qv = np.array([0.3, -0.2, 0.1, 0.05])
mv = 1.0
lv = np.sqrt(np.arange(1, 5) ** 2 + mv)
direct = []
for l in range(1, 13):
    s = 0.0
    for i, j, k in itertools.product(range(4), repeat=3):
        s += g_int(i + 1, j + 1, k + 1, l) / (2 * math.pi) * qv[i] * qv[j] * qv[k] / math.sqrt(lv[i] * lv[j] * lv[k])
    direct.append(s / math.sqrt(math.sqrt(l * l + mv)))
check("gradient of 1/4 int U^4 = trilinear sum with g_ijkl (quadrature vs closed form)", np.max(np.abs(np.array(direct) - Gq(qv, mv)[:12])) < 1e-12)

# ---------------------------------------------------------------- 9. errata spot checks
print("== 9. errata spot checks ==")
# new: P96-W p.280 claims ||Sq||_{a,s+1/2} <= ||q||_{a,s} in the two-sided norm; it is <= sqrt2 ||q|| and fails for q = e_1, m = 1
mv = 1.0
two_sided_sq = 2 * (1 / math.sqrt(1 + mv)) * 1 ** (2 * 0 + 1)  # a = 0, s = 0, q = e_1
check("P96-W p.280: ||S e_1||^2_{0,1/2} = 2/sqrt(1+m) > 1 = ||e_1||^2_{0,0} at m = 1 (printed inequality fails)", two_sided_sq > 1, f"{two_sided_sq:.4f}")
# KP96 Lemma 6 (A2) with m = -9, J = {1,2}: lambda_3 = 3^2 + m = 0
check("E-PDE-KP-2: NLS lambda_3 = 9 + m = 0 at m = -9", 9 + (-9) == 0)
# KP96: Gbar = 1/2 sum Gbar_ij |q_i|^2 |q_j|^2 and I = |q|^2/2 give q_k' = i(lam_k + 4 sum Gbar_kj I_j) q_k
qk = sp.symbols("q1:3")
qb = sp.symbols("qb1:3")
Gb = sp.Matrix([[3, 4], [4, 3]]) / (4 * sp.pi)
lN = sp.symbols("l1:3")
Hn = sum(lN[a] * qk[a] * qb[a] for a in range(2)) / 2 + sum(Gb[a, b] * qk[a] * qb[a] * qk[b] * qb[b] for a in range(2) for b in range(2)) / 2
rate = [sp.expand(2 * sp.diff(Hn, qb[a]) / qk[a]) for a in range(2)]  # q' = 2i dH/dqbar = i * rate * q
Iv = [qk[a] * qb[a] / 2 for a in range(2)]
check("E-PDE-KP-1: KP96 (5)-(6) dynamics give omega = lam + 4 Gbar I with I = |q|^2/2",
      all(sp.expand(rate[a] - (lN[a] + 4 * sum(Gb[a, b] * Iv[b] for b in range(2)))) == 0 for a in range(2)))
# KP96 Lemma 4 coefficient itself: resonant part of 1/4 sum G_ijkl q_i q_j qbar_k qbar_l
check("KP96 Lemma 4 Gbar_ij = (4 - delta_ij)/(4 pi) is the resonant part of (7)",
      sp.Rational(1, 4) * sp.Rational(3, 2) / sp.pi == sp.Rational(1, 2) * Gb[0, 0] and sp.Rational(1, 4) * 4 / sp.pi == Gb[0, 1])

print()
if FAILS:
    print("FAILED:", FAILS)
    sys.exit(1)
print("ALL CHECKS PASS")

# ---------------------------------------------------------------- recorded run (2026-10-28, sympy 1.14.0, numpy 2.5.0)
# == 1. quartic sine integrals ==
# [PASS] closed form of g_ijkl vs exact symbolic integral, sorted (i,j,k,l) in {1..3}^4: mismatches []
# [PASS] closed form vs exact quadrature for all ordered (i,j,k,l) in {1..12}^4: max error 1.7e-16
# [PASS] g_iiii = 3/(2 pi)
# [PASS] g_iijj = 1/pi (i != j)
# [PASS] g_1113 = -1/(2 pi) (a non-resonant quartic term)
# [PASS] selection rule: g_ijkl = 0 unless +-i+-j+-k+-l = 0 (indices <= 8)
# [PASS] P96-W (11) agrees with g/(sqrt(lambda^4)) for i,j <= 6
# == 2. coordinates ==
# [PASS] (phi, I) -> (q,p) = (sqrt(2I) cos phi, -sqrt(2I) sin phi) has Jacobian det 1, i.e. dq^dp = dphi^dI: det = 1
# [PASS] I = (q^2+p^2)/2 on that chart
# [PASS] z = (q+ip)/sqrt2 = sqrt(I) e^{-i phi}, |z|^2 = I
# [PASS] q' = lam p, p' = -lam q  =>  z' = -i lam z
# [PASS] i dz^dzbar = dq^dp: i*det = 1
# == 3. averaged quartic term: twist A and coupling B ==
# [PASS] <G>(I) = 1/2 sum_{i,j} A_ij I_i I_j with A_ii = 9/(8 pi lam_i^2), A_ij = 3/(2 pi lam_i lam_j) (modes 1..4)
#    A = Matrix([[9/(8*pi*(m + 1)), 3/(2*pi*sqrt(m**2 + 5*m + 4))], [3/(2*pi*sqrt(m**2 + 5*m + 4)), 9/(8*pi*(m + 4))]])
#    B (rows j = 3..4, cols i = 1,2) = Matrix([[3/(2*pi*sqrt(m**2 + 10*m + 9)), 3/(2*pi*sqrt(m**2 + 13*m + 36))], [3/(2*pi*sqrt(m**2 + 17*m + 16)), 3/(2*pi*sqrt(m**2 + 20*m + 64))]])
# [PASS] B_ji = 3/(2 pi lam_j lam_i) for normal j, tangential i = coefficient of I_i Z_j in <G>
#    det A = -63/(64*pi**2*(m + 1)*(m + 4))
# [PASS] det A = -63/(64 pi^2 (1+m)(4+m))
# [PASS] A = 3/(8 pi) D (4 * 11^T - Id) D
# [PASS] det A has no zero for m > 0 (numerator constant, denominator positive)
# == 4. P96-W printed quartic chain (E-PDE-W-1) ==
# [PASS] printed Gbar_ij / A_ij = 16 for all i, j: ratios {16}
# [PASS] q^4 with q = (z+zbar)/sqrt2 has |z|^4-coefficient 6/4 (so (1/4) G q^4 -> (1/16) G (z+zbar)^4)
# [PASS] p.284 counting 24 G_iijj, 12 G_iiii reproduces the printed Gbar
# [PASS] with the correct prefactor 1/16: (1/16)*(24 G_iijj, 12 G_iiii) = A
# [PASS] p.287 convention I = |z|^2/2 would turn Gbar = 1/2 sum Gbar |z|^2|z|^2 into 1/2 <(4 Gbar) I, I>
# == 5. nondegeneracy for J = {1,2} ==
# [PASS] (A3) affine non-identity, m = 0.1: min over |k_i|<=12, normal modes 3..40, of max(|const|,|linear|): 1.181e-01
# [PASS] (A3) affine non-identity, m = 1.0: min over |k_i|<=12, normal modes 3..40, of max(|const|,|linear|): 1.044e-01
# [PASS] (A3) affine non-identity, m = 10.0: min over |k_i|<=12, normal modes 3..40, of max(|const|,|linear|): 2.304e-02
# [PASS] (A3) affine non-identity, m = 43.0: min over |k_i|<=12, normal modes 3..40, of max(|const|,|linear|): 1.095e-02
# [PASS] (A2) <l,beta> != 0: min |lam_a +- lam_b|, |lam_a| over 3<=a<b<=200, m = 0.1
# == 6. quartic nonresonance: sigma.lambda = 0 with g != 0 only for pairings ==
# [PASS] m = 0.01: min |sum sigma_t lam_(i_t)| over non-trivial sign patterns, indices <= 30, g != 0: 4.105e-07
# [PASS] m = 0.1: min |sum sigma_t lam_(i_t)| over non-trivial sign patterns, indices <= 30, g != 0: 4.104e-06
# [PASS] m = 1.0: min |sum sigma_t lam_(i_t)| over non-trivial sign patterns, indices <= 30, g != 0: 4.098e-05
# [PASS] m = 10.0: min |sum sigma_t lam_(i_t)| over non-trivial sign patterns, indices <= 30, g != 0: 4.033e-04
# == 7. one-mode Duffing consistency ==
# [PASS] Lindstedt shift with eps = g_jjjj = 3/(2pi) equals A_jj I_j
# [PASS] m = 0.1, mode 1: (omega_numeric - lam) / (A_11 I) -> 1 as amplitude halves (printed P96-W value would give 1/16): 0.99623 0.99905 0.99976
# [PASS] m = 1.0, mode 1: (omega_numeric - lam) / (A_11 I) -> 1 as amplitude halves (printed P96-W value would give 1/16): 0.99792 0.99948 0.99987
# [PASS] m = 10.0, mode 1: (omega_numeric - lam) / (A_11 I) -> 1 as amplitude halves (printed P96-W value would give 1/16): 0.99962 0.99991 0.99998
# == 8. cubic gradient bound ||G_q(q)||_{1,2} <= C ||q||_{1,1}^3,  C = 8(1+2 zeta(3))/pi ==
#    C = 8.668505
# [PASS] max over 60 random trials of ||G_q||_{1,2} / ||q||_{1,1}^3 <= C: max ratio 2.9836
# [PASS] gradient of 1/4 int U^4 = trilinear sum with g_ijkl (quadrature vs closed form)
# == 9. errata spot checks ==
# [PASS] P96-W p.280: ||S e_1||^2_{0,1/2} = 2/sqrt(1+m) > 1 = ||e_1||^2_{0,0} at m = 1 (printed inequality fails): 1.4142
# [PASS] E-PDE-KP-2: NLS lambda_3 = 9 + m = 0 at m = -9
# [PASS] E-PDE-KP-1: KP96 (5)-(6) dynamics give omega = lam + 4 Gbar I with I = |q|^2/2
# [PASS] KP96 Lemma 4 Gbar_ij = (4 - delta_ij)/(4 pi) is the resonant part of (7)
#
# ALL CHECKS PASS
