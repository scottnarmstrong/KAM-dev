"""Certificate parameters and exact evaluation of every premise of checkOscChain / oscillatorChain_physical."""
from fractions import Fraction as F
from math import factorial, isqrt
from poly import *
from qs import QS

GRID_RHO = F(1, 10 ** 9)
GRID_DELTA = F(1, 10 ** 12)


def ceil_grid(x, g):
    q = x / g
    n = q.numerator // q.denominator
    if n * g < x:
        n += 1
    return n * g


def small_field_m(chi, rho):
    m = F(0)
    for i in range(N):
        m = max(m, supbound(dq(i, chi), rho), supbound(dp(i, chi), rho))
    return m


def choose_steps(chain, r, dc):
    """Backward choice of (rho_k, delta_k, eps_k=1/2); steps list is outermost first (chi3, chi4, ...)."""
    st = chain["steps"]
    tail_after = F(0)
    out = [None] * len(st)
    for k in range(len(st) - 1, -1, -1):
        chi = st[k]["gen"]
        rho = ceil_grid(r + dc + tail_after, GRID_RHO)
        for _ in range(100):
            m = small_field_m(chi, rho)
            delta = ceil_grid(2 * m, GRID_DELTA)
            need = max(r + dc + tail_after + delta / 2, r + tail_after + delta)
            new = ceil_grid(need, GRID_RHO)
            if new == need:
                new += GRID_RHO  # strict inequalities
            if new <= rho:
                break
            rho = new
        m = small_field_m(chi, rho)
        delta = ceil_grid(2 * m, GRID_DELTA)
        eps = F(1, 2)
        assert eps * delta >= m
        assert r + dc + tail_after + delta / 2 < rho and r + tail_after + delta < rho
        out[k] = dict(rho=rho, delta=delta, eps=eps, m=m, order=st[k]["L"])
        tail_after += eps * delta
    return out, tail_after


def residual_bound(P, j, r):
    """cartSupBound (cartBracket (cartAction j) P) r r on the RAW bracket (exact, = Lean value up to the
    conservative absUB of the integer multiples, which is exact since the multipliers are rational)."""
    s = F(0)
    for k, v in P.items():
        s += v.absub() * (k[j] + k[N + j]) * r ** deg(k)
    return s


def evaluate(chain, r, dc, b, a, T, epsb, a_phys, s, steps=None, tail=None):
    """Evaluate every conjunct. Returns dict with 'checks' (list of (name, lean_ref, ok, lhs, rhs, margin))."""
    if steps is None:
        steps, tail = choose_steps(chain, r, dc)
    st = chain["steps"]
    contrib = []
    Bk = []
    Q = chain["H"]
    for k, s_ in enumerate(st):
        bnd = wadpow_bound(s_["gen"], s_["L"], s_["inp"], steps[k]["rho"]) / factorial(s_["L"])
        Bk.append(bnd)
    Btot = sum(Bk, F(0))
    res = [residual_bound(chain["P"], j, r) for j in range(N)]
    lie_tail = [2 * r * Btot / dc for _ in range(N)]
    eta_min = [res[j] + lie_tail[j] for j in range(N)]
    return dict(steps=steps, tail=tail, Bk=Bk, Btot=Btot, res=res, lie_tail=lie_tail, eta_min=eta_min)
