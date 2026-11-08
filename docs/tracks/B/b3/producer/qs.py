"""Exact arithmetic in Q(sqrt 2): x = a + b*sqrt(2), a, b Fractions.

Mirrors the B3-COEF layer: absUB(x) = |a| + |b| * 141422/100000 (a rational majorant of |x|).
"""
from fractions import Fraction as F

S2UB = F(141422, 100000)  # rational upper bound of sqrt 2


class QS:
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a = a if isinstance(a, F) else F(a)
        self.b = b if isinstance(b, F) else F(b)

    def __add__(s, o):
        o = _c(o)
        return QS(s.a + o.a, s.b + o.b)

    __radd__ = __add__

    def __sub__(s, o):
        o = _c(o)
        return QS(s.a - o.a, s.b - o.b)

    def __rsub__(s, o):
        return _c(o) - s

    def __neg__(s):
        return QS(-s.a, -s.b)

    def __mul__(s, o):
        o = _c(o)
        return QS(s.a * o.a + 2 * s.b * o.b, s.a * o.b + s.b * o.a)

    __rmul__ = __mul__

    def inv(s):
        n = s.a * s.a - 2 * s.b * s.b
        return QS(s.a / n, -s.b / n)

    def __truediv__(s, o):
        return s * _c(o).inv()

    def iszero(s):
        return s.a == 0 and s.b == 0

    def __eq__(s, o):
        o = _c(o)
        return s.a == o.a and s.b == o.b

    def __hash__(s):
        return hash((s.a, s.b))

    def absub(s):
        return abs(s.a) + abs(s.b) * S2UB

    def __float__(s):
        return float(s.a) + float(s.b) * 2 ** 0.5

    def __repr__(s):
        return f"({s.a} + {s.b}*r2)"


def _c(o):
    return o if isinstance(o, QS) else QS(o)


ZERO = QS(0)
ONE = QS(1)
R2 = QS(0, 1)
