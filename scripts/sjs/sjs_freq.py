#!/usr/bin/env python3
"""SJS-FEAS: Diophantine data and small-divisor sums of the planar Sun-Jupiter-Saturn frequency vector.

Untrusted design tooling.  Frequencies of Figueras-Haro 2025 (arXiv:2403.10152, (4.1)-(4.2)), angular units
(rad per time unit, angles 2 pi-periodic):  w = (w_l1, w_l2, w_g) = (0.0839549..., 0.0338240..., -1.85008e-5).
Our period-1 convention: omega = w / (2 pi) (cycles per time unit); gamma_p1 = gamma_FH / (2 pi); strips rho_p1 = rho_FH/(2 pi).

1. gamma(tau) = inf_{0 < |k|_1 <= K} |k|_1^tau |k.w|  (numerical, K up to 2000; for each (k1, k2) only the k3 nearest to
   the resonance matters), for tau in {2, 2.4, 3}; FH25 certify tau = 2.4, gamma = 1.69e-6 (FH units).
2. S(w, delta) = sum_{k != 0} |k.omega|^-2 e^{-4 pi delta |k|_1} (SHARP-PLUS convention, period-1 delta) by fibres in k3:
   exact for the (k1, k2) whose fibre comes close to resonance, the bound 1/(|a| - |k3| om3)^2 otherwise; and the
   frequency-specific cohomological constant Gamma_spec(delta) = (2 pi)^-1 2^{n/2} S^{1/2} (n = 3), against the
   classical/Russmann form c_R gamma^-1 delta^-tau.
Usage: python3 -I scripts/sjs/sjs_freq.py [--json OUT]
"""
import sys, json, math
import numpy as np

W = np.array([8.39549288702546301204e-2, 3.38240117059304358259e-2, -1.85007988077595000000e-5])
TP = 2 * math.pi
GAMMA_FH, TAU_FH = 1.69e-6, 2.4
RHO_FH = 0.1


def dioph(w, taus=(2.0, 2.4, 3.0), K=2000):
    """min over 0 < |k|_1 <= K of |k|_1^tau |k.w| (best k3 per (k1, k2)); returns {tau: (value, k)}."""
    best = {t: (math.inf, None) for t in taus}
    for k1 in range(0, K + 1):
        m = K - k1
        k2 = np.arange(-m, m + 1)
        a = k1 * w[0] + k2 * w[1]
        for d in (-1, 0, 1):
            k3 = np.rint(-a / w[2]) + d
            n1 = k1 + np.abs(k2) + np.abs(k3)
            ok = (n1 <= K) & (n1 > 0)
            if k1 == 0:
                ok &= ~((k2 == 0) & (k3 == 0)) & ((k2 > 0) | ((k2 == 0) & (k3 > 0)))
            v = np.abs(a + k3 * w[2])
            for t in taus:
                val = np.where(ok, n1 ** t * v, np.inf)
                i = int(np.argmin(val))
                if val[i] < best[t][0]:
                    best[t] = (float(val[i]), (k1, int(k2[i]), int(k3[i])))
    return best


def S3(om, delta, A0fac=10.0):
    """sum_{k != 0} |k.om|^-2 e^{-4 pi delta |k|_1} for om in R^3 with |om3| << |om1|, |om2| (period-1 units).
    Fibres over (k1, k2): exact k3-sum where |a| < A0 = A0fac K3 |om3| (K3: e^{-4 pi delta K3} = e^-40), otherwise
    the bound e^{-4 pi delta(|k1|+|k2|)} coth(2 pi delta) / (|a|(1 - 1/A0fac))^2."""
    b = 4 * math.pi * delta
    K = int(math.ceil(40 / b))
    K3 = K
    k3 = np.arange(-K3, K3 + 1)
    w3 = np.exp(-b * np.abs(k3))
    A0 = A0fac * K3 * abs(om[2])
    coth = 1 / math.tanh(b / 2)
    tot_near = 0.0; tot_far = 0.0; n_near = 0
    for k1 in range(-K, K + 1):
        m = K - abs(k1)
        k2 = np.arange(-m, m + 1)
        a = k1 * om[0] + k2 * om[1]
        base = np.exp(-b * (abs(k1) + np.abs(k2)))
        far = np.abs(a) >= A0
        tot_far += float(np.sum(base[far] * coth / (np.abs(a[far]) * (1 - 1 / A0fac)) ** 2))
        idx = np.nonzero(~far)[0]
        n_near += len(idx)
        for i in idx:
            d = np.abs(a[i] + k3 * om[2])
            msk = ~((k1 == 0) & (k2[i] == 0) & (k3 == 0))
            tot_near += float(base[i] * np.sum(np.where(msk, w3 / np.where(d > 0, d, 1.0) ** 2, 0.0)))
    return tot_near + tot_far, dict(near=tot_near, far=tot_far, n_near_fibres=n_near, K=K)


def main():
    out = {}
    omega = W / TP
    print("frequencies (FH units, rad/time):", W, " period-1:", omega)
    print("near resonance 2 w1 - 5 w2 =", 2 * W[0] - 5 * W[1], " (k3 that cancels it:", -(2 * W[0] - 5 * W[1]) / W[2], ")")
    d = dioph(W)
    out["dioph_FH_units"] = {str(t): dict(gamma=v, k=k) for t, (v, k) in d.items()}
    for t, (v, k) in d.items():
        print("tau %.1f: min |k|^tau |k.w| = %.4e at k = %s   (FH25: tau 2.4, gamma 1.69e-6)" % (t, v, k))
    rho = RHO_FH / TP
    out["S"] = {}
    from math import gamma as G
    for frac in (1 / 6, 1 / 12, 1 / 24):
        delta = rho * frac
        S, info = S3(omega, delta)
        Gs = (TP) ** -1 * 2 ** 1.5 * math.sqrt(S)
        gam = GAMMA_FH / TP
        # classical constant of the full-strip route (SHARP-PLUS smalldiv.c_classical), tau = 2.4, n = 3
        tau = TAU_FH
        import mpmath as mp
        A = 2 * 2 ** (2 * tau) * float(mp.zeta(2, 2 ** tau))
        eps = 4 * math.pi * delta * (2 * tau / math.e) ** (2 * tau) / G(2 * tau + 1)
        ccl = TP ** -1 * 2 ** 1.5 * math.sqrt(A * G(2 * tau + 1) * (1 + eps)) * (4 * math.pi) ** (-tau)
        Gcl = ccl / (gam * delta ** tau)
        print("delta = rho/%d = %.5f (period-1): S %.4e (near %.3e from %d fibres, far %.3e)  Gamma_spec %.3e | "
              "classical c %.4f -> Gamma %.3e | ratio %.3e (%.1f orders)" % (
                  round(1 / frac), delta, S, info["near"], info["n_near_fibres"], info["far"], Gs, ccl, Gcl,
                  Gcl / Gs, math.log10(Gcl / Gs)))
        out["S"]["rho/%d" % round(1 / frac)] = dict(delta=delta, S=S, Gamma_spec=Gs, c_classical=ccl,
                                                     Gamma_classical=Gcl, **info)
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=str)


if __name__ == "__main__":
    main()
