#!/usr/bin/env python3
"""LOCK-GEN part 2: floating-point mirror of the disc pass `Slp.balls` (KAM/Certificate/Expr/Ball.lean, with the
sqrt arm `ballSqrt` of branch inp-locksqrt) and of the bound sums `hamBoundsOk` / `hamClaimOk`, to predict the
M of `checkHamBounds` and the refined claim (dh, dx, d2x, d2h) the kernel can certify.

Design tooling: balls are (complex centre, radius) in double precision; every radius is inflated by 1e-12
relative per operation (the landed pass rounds outward to `slpBallPrec` bits, which is far finer).  `exp` follows
`ballExp` (halvings `cexpHalvings`, then squaring), `inv` the landed max-norm rule, `sqrt` the anchor rule
(radius (|re c - s²| + |im c| + r)/s, s = √(re c)).  Untrusted tooling.
"""
import math
import cmath

PI_LO, PI_HI = 3.14159265358979, 3.14159265358980
INFL = 1 + 1e-12


def const_ball(re, im, deg):
    lo = (2 * PI_LO) ** deg if deg >= 0 else (2 * PI_HI) ** deg
    hi = (2 * PI_HI) ** deg if deg >= 0 else (2 * PI_LO) ** deg
    c, r = (lo + hi) / 2, (hi - lo) / 2
    z = complex(float(re), float(im))
    return (z * c, (abs(z.real) + abs(z.imag)) * r)


def times(b1, b2):
    (c1, r1), (c2, r2) = b1, b2
    return (c1 * c2, (r1 * (abs(c2.real) + abs(c2.imag) + r2) + (abs(c1.real) + abs(c1.imag)) * r2) * INFL)


def ball_exp(c, r):
    s = int(math.log2(math.ceil(2 * (abs(c.real) + abs(c.imag) + r)) or 1)) + 1
    z, rr = c / 2 ** s, r / 2 ** s
    e = cmath.exp(z)
    b = (e, abs(e) * math.expm1(rr) * (1 + 1e-9) + 1e-30)
    for _ in range(s):
        b = times(b, b)
    return b


def ball_inv(c, r):
    m = max(abs(c.real), abs(c.imag))
    if not r < m:
        return None
    return (1 / c, r / ((m - r) * m) * INFL)


def ball_sqrt(c, r):
    if not r < c.real:
        return None
    s = math.sqrt(c.real)
    R = abs(c.real - s * s) + abs(c.imag) + r
    if not (s > 0 and R < s * s):
        return None
    return (complex(s, 0), R / s * INFL)


def balls(prog, n, wH, centre, radius):
    """The slot balls of `prog` (lock_jet op tuples) on certDomain n rhoH centre radius; wH >= e^{2 pi rhoH}."""
    out = []
    for op in prog:
        t = op[0]
        if t == "const":
            b = const_ball(op[1], op[2], op[3])
        elif t == "action":
            j = op[1]
            b = (complex(float(centre[j]), 0), float(radius[j])) if j < n else (0j, 0.0)
        elif t == "char":
            b = (0j, float(wH) ** sum(abs(x) for x in op[1]))
        elif t == "add":
            (c1, r1), (c2, r2) = out[op[1]], out[op[2]]
            b = (c1 + c2, (r1 + r2) * INFL)
        elif t == "mul":
            b = times(out[op[1]], out[op[2]])
        elif t == "exp":
            b = ball_exp(*out[op[1]])
        elif t == "inv":
            b = ball_inv(*out[op[1]])
        elif t == "sqrt":
            b = ball_sqrt(*out[op[1]])
        else:
            raise ValueError(t)
        if b is None:
            return None, len(out)
        out.append(b)
    return out, None


def mag(bs, i):
    c, r = bs[i]
    return abs(c.real) + abs(c.imag) + r


def bound_sums(J, bs, m=4):
    """The five hamBoundsOk quantities and the four hamClaimOk claims from the slot balls."""
    d1 = [mag(bs, J["d1"][a]) for a in range(m)]
    rows2 = [sum(mag(bs, J["d2"][a][b]) for b in range(m)) for a in range(m)]
    rows3 = [sum(mag(bs, J["d3"][a][b][e]) for b in range(m) for e in range(m)) for a in range(m)]
    dh, dx, d2x, d2h = sum(d1), max(rows2), max(rows3), sum(rows2)
    return dict(dh=dh, dx=dx, d2x=d2x, d2h=d2h, M=max(dh, max(d1), dx, d2x, d2h), d1=d1, rows2=rows2, rows3=rows3)
