#!/usr/bin/env python3
"""LP-QUANT: small divisors of the initial Kepler frequencies.  Untrusted design tooling, double precision.

 alpha_table(omega, Ks)        alpha(K) = min_{0<|k|_1<=K} |k.omega| (radian frequencies), by enumeration of all prefixes
                               (k_1..k_{n-1}) with the best admissible k_n.  Exact for the given double-precision omega.
 alpha_pairs(omega, Ks)        the same over k with at most two nonzero entries: the modes of f itself (f is a sum of
                               pair terms and one-planet terms, MAIN (1)).
 gamma_of_tau(omega, tau, Kmax) gamma(tau) = min_{0<|k|_1<=Kmax} |k.omega| |k|_1^tau.  For a measured omega this is only
                               an UPPER estimate of the inf over all k (label `estimated`): no finite frequency datum
                               decides the all-orders condition (5).  One can only select a Diophantine vector in the
                               measurement box; see notes in docs/campaign/studies/LP-QUANT.md.
 nearest_resonances(omega, K)  the smallest |k.omega| per order.
"""
import itertools
import math
import numpy as np


def _prefixes(n1, K):
    """All integer vectors of length n1 with |.|_1 <= K, first nonzero entry positive or all zero (k ~ -k)."""
    if n1 == 1:
        return np.arange(0, K + 1)[:, None]
    rng = np.arange(-K, K + 1)
    mesh = np.meshgrid(*([rng] * n1), indexing="ij")
    P = np.stack([m.ravel() for m in mesh], axis=-1)
    P = P[np.sum(np.abs(P), axis=1) <= K]
    nz = P != 0
    first = np.argmax(nz, axis=1)
    sign = P[np.arange(len(P)), first]
    return P[(sign > 0) | (~nz.any(axis=1))]


def alpha_table(omega, Ks):
    Ks = sorted(set(int(k) for k in Ks))
    n = len(omega)
    Kmax = Ks[-1]
    P = _prefixes(n - 1, Kmax)
    Pn = np.sum(np.abs(P), axis=1)
    v = P @ np.asarray(omega[:-1])
    wn = float(omega[-1])
    kstar = -v / wn
    res = {}
    for K in Ks:
        sel = Pn <= K
        m = (K - Pn[sel]).astype(float)
        ks = kstar[sel]
        vv = v[sel]
        z = Pn[sel] == 0
        best = np.inf
        for f in (np.floor, np.ceil):
            k = np.clip(f(ks), -m, m)
            val = np.abs(vv + k * wn)
            val = np.where(z & (k == 0), np.inf, val)  # exclude k = 0
            best = min(best, float(np.min(val)))
        # for the zero prefix the best nonzero k_n is +-1
        res[K] = min(best, abs(wn))
    return res


def alpha_pairs(omega, Ks):
    Ks = sorted(set(int(k) for k in Ks))
    n = len(omega)
    out = {K: np.inf for K in Ks}
    for i, j in itertools.combinations(range(n), 2):
        t = alpha_table(np.array([omega[i], omega[j]]), Ks)
        for K in Ks:
            out[K] = min(out[K], t[K])
    return out


def gamma_of_tau(omega, tau, Kmax):
    """min over best approximants, up to Kmax."""
    n = len(omega)
    P = _prefixes(n - 1, Kmax)
    Pn = np.sum(np.abs(P), axis=1)
    v = P @ np.asarray(omega[:-1])
    wn = float(omega[-1])
    ks = -v / wn
    best, arg = math.inf, None
    for f in (np.floor, np.ceil, lambda x: 0 * x):
        k = f(ks)
        norm = Pn + np.abs(k)
        ok = (norm > 0) & (norm <= Kmax)
        val = np.where(ok, np.abs(v + k * wn) * norm ** tau, np.inf)
        i = int(np.argmin(val))
        if val[i] < best:
            best, arg = float(val[i]), tuple(int(x) for x in P[i]) + (int(k[i]),)
    return best, arg


def nearest_resonances(omega, K, top=8):
    """List (|k|_1, k, |k.omega|) of record-setting divisors with |k|_1 <= K (each strictly smaller than all lower orders)."""
    n = len(omega)
    P = _prefixes(n - 1, K)
    Pn = np.sum(np.abs(P), axis=1)
    v = P @ np.asarray(omega[:-1])
    wn = float(omega[-1])
    ks = np.rint(-v / wn)
    norm = Pn + np.abs(ks)
    val = np.abs(v + ks * wn)
    ok = (norm > 0) & (norm <= K)
    order = np.lexsort((val[ok], norm[ok]))
    Pk, nk, vk, kk = P[ok][order], norm[ok][order], val[ok][order], ks[ok][order]
    out, cur = [], math.inf
    for p, nn, vv, kk1 in zip(Pk, nk, vk, kk):
        if vv < cur:
            cur = vv
            out.append((int(nn), tuple(int(x) for x in p) + (int(kk1),), float(vv)))
    return out[-top:] if len(out) > top else out


if __name__ == "__main__":
    import sys, os
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from systems import catalogue
    for k, s in catalogue().items():
        if s.name.endswith("(spatial)"):
            continue
        Ks = [4, 8, 16, 32, 64, 128, 256] if s.n <= 3 else [4, 8, 16, 32, 64]
        a = alpha_table(s.omega, Ks)
        print(k, {K: f"{v:.3e}" for K, v in a.items()})
        print("   records", nearest_resonances(s.omega, min(Ks[-1], 64)))
