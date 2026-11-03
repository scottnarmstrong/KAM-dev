"""Hénon–Heiles model, homological equations, Lie chain, action-only normal form (exact over Q(sqrt2))."""
from fractions import Fraction as F
from itertools import product
from qs import QS, ZERO, ONE, R2
from poly import *

OMEGA = QS(0, F(1, 2))  # sqrt2/2


def model_H():
    H = padd(action(0), psmul(-OMEGA, action(1)))
    H = padd(H, {(2, 1, 0, 0): ONE, (0, 3, 0, 0): QS(F(-1, 3))})
    return H


def H2():
    return padd(action(0), psmul(-OMEGA, action(1)))


def monos(d):
    out = []
    for k in product(range(d + 1), repeat=2 * N):
        if sum(k) == d:
            out.append(k)
    return out


def homog(P, d):
    return {k: v for k, v in P.items() if deg(k) == d}


def solve_linear(cols, rhs_keys, rhs):
    """Solve sum_j x_j cols[j] = rhs (dict polys) over Q(sqrt2); free variables set to 0."""
    keys = sorted(set(rhs_keys))
    idx = {k: i for i, k in enumerate(keys)}
    m, n = len(keys), len(cols)
    A = [[ZERO] * (n + 1) for _ in range(m)]
    for j, c in enumerate(cols):
        for k, v in c.items():
            A[idx[k]][j] = v
    for k, v in rhs.items():
        A[idx[k]][n] = v
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, m) if not A[i][c].iszero()), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        iv = A[r][c].inv()
        A[r] = [x * iv for x in A[r]]
        for i in range(m):
            if i != r and not A[i][c].iszero():
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    for i in range(r, m):
        assert A[i][n].iszero(), "inconsistent system"
    x = [ZERO] * n
    for i, c in enumerate(piv):
        x[c] = A[i][n]
    return x


def solve_homological(G, d):
    """chi_d with {H2, chi_d} = -(G_d - avg G_d), purely non-averaged (avg chi = 0)."""
    Gd = homog(G, d)
    Gp = psub(Gd, avg_poly(Gd))
    basis = monos(d)
    h2 = H2()
    cols = [bracket(h2, {k: ONE}) for k in basis]
    keys = set(monos(d))
    chi_c = solve_linear(cols, keys, pneg(Gp))
    chi = clean({k: v for k, v in zip(basis, chi_c)})
    chi = psub(chi, avg_poly(chi))  # remove the kernel component (still a solution)
    assert clean(padd(bracket(h2, chi), Gp)) == {}
    return chi


def build_chain(Ls, verbose=False):
    """Ls = Lie orders for chi_3, chi_4, ... ; returns dict with H, steps (gen,out,L), Nact, P."""
    H = model_H()
    Q = H
    steps = []
    for idx, L in enumerate(Ls):
        d = idx + 3
        chi = solve_homological(Q, d)
        out = liesum(chi, Q, L)
        steps.append(dict(deg=d, gen=chi, inp=Q, out=out, L=L))
        Q = out
        if verbose:
            print(f"chi_{d}: {len(chi)} monos; Q_{idx+1}: {len(out)} monos", flush=True)
    Nact = avg_action(Q)
    P = psub(Q, act_subst(Nact))
    return dict(H=H, steps=steps, Nact=Nact, P=P, Qm=Q)
