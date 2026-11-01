#!/usr/bin/env python3
"""Regression check of the shape guards of the two-frequency design routines (CERTIFIER-V2-FIXES F4).

Untrusted design tooling.  Unsupported dimensions, vectors of length other than 2 and non-finite scalars raise a
ValueError that names the problem; the two-frequency benchmarks keep their values (recorded before the guards were
added, compared to 12 digits here; the exact before/after comparison is in the V2-FIXES handoff).

Usage: python3 -B -I scripts/apost_sharp/check_smalldiv_shapes.py
"""
import importlib.util, math, os, sys
from fractions import Fraction as F

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


sd = load("smalldiv", os.path.join(HERE, "smalldiv.py"))
sup = load("smalldiv_sup", os.path.join(HERE, "smalldiv_sup.py"))
cert = load("certifier_smalldiv", os.path.join(HERE, "..", "certifier", "smalldiv.py"))
NAN, INF = float("nan"), float("inf")
R2 = math.sqrt(2)
fails = []


def check(name, cond, info=""):
    print("%-58s %s" % (name, "ok" if cond else "FAIL %s" % (info,)))
    if not cond:
        fails.append(name)


def rejects(name, f, *words):
    """f() must raise a ValueError whose message contains every word."""
    try:
        v = f()
    except ValueError as e:
        check(name, all(w in str(e) for w in words), e)
    else:
        check(name, False, "returned %r" % (v,))


def main():
    # the unsupported examples of the review (same value for a resonant and a non-resonant vector)
    rejects("c_freq, resonant (1, r2, 1 + r2), n = 3",
            lambda: sd.c_freq((1, R2, 1 + R2), .01, 2, .05, n=3, N=20), "n must be 2")
    rejects("c_freq, (1, r2, 8), n = 3", lambda: sd.c_freq((1, R2, 8), .01, 2, .05, n=3, N=20), "n must be 2")
    rejects("c_freq, length 3 with default n", lambda: sd.c_freq((1, R2, 8), .01, 2, .05), "length 2")
    rejects("c_freq, length 2 with n = 3", lambda: sd.c_freq((1, R2), .01, 2, .05, n=3), "n must be 2")
    rejects("c_freq, n = 1", lambda: sd.c_freq((1, R2), .01, 2, .05, n=1), "n must be 2")
    # lengths and shapes
    for name, om in (("length 1", (1.0,)), ("length 3", (1.0, R2, 8.0)), ("scalar", 1.0), ("matrix", np.eye(2)),
                     ("ragged", [[1.0, 2.0], [3.0]]), ("None", None)):
        rejects("S_finite, %s" % name, lambda: sd.S_finite(om, .05, 20), "length 2")
        rejects("gamma_inf, %s" % name, lambda: sd.gamma_inf(om, .05, .01), "length 2")
    # non-finite scalars
    for bad, word in ((NAN, "omega_2"), (INF, "omega_2"), (-INF, "omega_2")):
        rejects("S_finite, omega_2 = %r" % bad, lambda: sd.S_finite((1.0, bad), .05, 20), word)
        rejects("gamma_inf, omega_2 = %r" % bad, lambda: sd.gamma_inf((1.0, bad), .05, .01), word)
    om = (1.0, R2)
    for bad in (NAN, INF):
        rejects("c_freq, delta = %r" % bad, lambda: sd.c_freq(om, .01, 1, bad), "delta")
        rejects("c_freq, gamma = %r" % bad, lambda: sd.c_freq(om, bad, 1, .05), "gamma")
        rejects("c_freq, tau = %r" % bad, lambda: sd.c_freq(om, .01, bad, .05), "tau")
        rejects("S_finite, N = %r" % bad, lambda: sd.S_finite(om, .05, bad), "N")
        rejects("S_tail, delta = %r" % bad, lambda: sd.S_tail(.01, 1, bad, 20), "delta")
        rejects("gamma_inf, delta = %r" % bad, lambda: sd.gamma_inf(om, bad, .01), "delta")
        rejects("c_classical, delta = %r" % bad, lambda: sd.c_classical(2, 1, bad), "delta")
        rejects("c_v1, tau = %r" % bad, lambda: sd.c_v1(2, bad), "tau")
        rejects("c_inf_classical, tau = %r" % bad, lambda: sd.c_inf_classical(bad), "tau")
    # the fibered routines: omega = (alpha, 1), alpha a real scalar
    for name, alpha in (("nan", NAN), ("inf", INF), ("a vector", (1.0, 2.0))):
        rejects("smalldiv_sup.gamma_inf, alpha = %s" % name, lambda: sup.gamma_inf(alpha, .01, 1, .05), "alpha")
        rejects("smalldiv_sup.best_gamma, alpha = %s" % name, lambda: sup.best_gamma(alpha, 1), "alpha")
        rejects("certifier S_bound, alpha = %s" % name, lambda: cert.S_bound(alpha, .05), "alpha")
    rejects("certifier gamma_spec, n = 3", lambda: cert.gamma_spec(.3, .05, n=3), "n must be 2")
    rejects("certifier S_generic, delta = nan", lambda: cert.S_generic(.01, 1, NAN), "delta")

    # the general-n formula stays general (SJS uses it at n = 3)
    check("c_classical keeps n = 3", sd.c_classical(3, 2.4, .05) > 0)

    # values recorded before the guards
    alpha = (79 - math.sqrt(5)) / 3118
    c = 7 / 4; s = 1 + 1e-6
    w = (c * (-alpha) / s, c / s); g = c / (42 * s)
    rho = 1 / 70; d0 = (rho - rho / 1000) / 6
    for d, v0, N0 in ((rho, 0.006717403402355695, 89), (d0, 0.002975593970813585, 535)):
        v, N = sd.c_freq(w, g, 1, d)
        check("benchmark c_freq at delta = %.6g" % d, math.isclose(v, v0, rel_tol=1e-12) and N == N0, (v, N))
    v = sd.c_freq((1, R2), .01, 2, .05, n=2, N=20)[0]
    check("benchmark c_freq (1, r2), n = 2", math.isclose(v, 0.0016305714814815013, rel_tol=1e-12), v)
    v = sd.S_finite((F(1, 3), F(5, 7)), .05, 12)
    check("rational vector accepted", v > 0, v)
    check("list and array accepted", sd.S_finite([1.0, R2], .05, 12) == sd.S_finite(np.array([1.0, R2]), .05, 12))

    print("small-divisor shape checks:", "all passed" if not fails else "FAILED: %s" % ", ".join(fails))
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
