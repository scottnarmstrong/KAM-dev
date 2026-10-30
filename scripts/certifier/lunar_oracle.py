#!/usr/bin/env python3
"""SHARP-CERTSIDE: norm oracle of the lunar spin-orbit candidates for the free-parameter optimizer.

Untrusted design tooling (double precision; numbers for docs/campaign/design/CERTIFIER-SHARPNESS.md).

Data: the rotated-frame candidate of SO-GEN2 (scripts/spin_orbit/rot_build.py, read-only import), truncated as
the emitted certificates (Lv = LE = LJ = 88, S = 318):  K'(theta) = (psi + u, phi, p, p + J), u = v/(2 pi),
H' = P1^2/2 - P1 + P2 + V(Q),  V(Q) = - sum_m eps A_m cos(2 pi s_m.Q),  s_m = (2, 2 - m),  omega' = (nu - 1, 1).

Free parameters handled here (all exact symmetries of the problem, so the certificate checks the transformed
data with the unchanged theorem):
  frame A in GL(2, Z) (relative to the rotated frame):   Q~ = A Q,  P~ = lam A^{-T} P,  theta~ = A theta
      (conformally symplectic with factor lam, so H~ = c lam H(A^{-1} Q~, A^T P~ / lam) has the conjugate flow);
  time scale c:  omega~ = c A omega',  invariance error and M scale by c, the bordered torsion inverse by 1/c.
The theta frame of the pilot is A = [[1, 1], [0, 1]].

Every norm is returned in three REGIMES:
  'l1'      the current checker: weighted l1  sum |c_k| w^{|k~|_1} (+ the checker's row-sum structure);
  'corner'  the vertex bound max_sigma sum |c_k| e^{2 pi rho sigma.k~} (rigorous, same data; proposal P1);
  'sup'     sampled sup on the distinguished boundary of the theta~-polystrip (max principle) -- what a
            grid + interpolation enclosure (proposal P2) reaches up to its interpolation error.
The H-majorant is the checker's construction (product domain T_{rho_H} x discs, cosh bounds) in every regime;
in 'sup' the strip image is measured instead of bounded through iota.
"""
import os, sys, math, json, time, pickle
import numpy as np
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "spin_orbit"))

TP = 2 * math.pi
OM = np.block([[np.zeros((2, 2)), -np.eye(2)], [np.eye(2), np.zeros((2, 2))]])     # Omega0 (a,b) -> (-b,a)
JX = np.block([[np.zeros((2, 2)), np.eye(2)], [-np.eye(2), np.zeros((2, 2))]])     # X_H = JX grad H
REGIMES = ("l1", "corner", "sup")


def _arr(sp):
    """(k, l, complex coefficients) of a rotlib SPoly (phase 1 = i * values)."""
    c = np.array([float(F(int(x), 1 << sp.S)) for x in sp.v])
    if sp.ph == 1:
        c = 1j * c
    return np.asarray(sp.k, dtype=np.int64), np.asarray(sp.l, dtype=np.int64), c


class Series:
    """A Fourier series sum c_kappa e_kappa(theta) in base (psi, phi) indices."""

    def __init__(self, k, l, c):
        self.k, self.l, self.c = np.asarray(k, np.int64), np.asarray(l, np.int64), np.asarray(c, complex)

    @staticmethod
    def const(a):
        return Series([0], [0], [a])

    def d(self, j):
        """d/d theta_j (period-1 angles): multiply by 2 pi i kappa_j."""
        m = self.k if j == 0 else self.l
        return Series(self.k, self.l, self.c * (TP * 1j) * m)

    def lin(self, other, a=1.0, b=1.0):
        k = np.concatenate([self.k, other.k]); l = np.concatenate([self.l, other.l])
        c = np.concatenate([a * self.c, b * other.c])
        return Series(k, l, c).compress()

    def scale(self, a):
        return Series(self.k, self.l, a * self.c)

    def compress(self):
        if len(self.c) == 0:
            return self
        key = (self.k + 4096) * 8192 + (self.l + 4096)
        u, inv = np.unique(key, return_inverse=True)
        c = np.zeros(len(u), complex); np.add.at(c, inv, self.c)
        return Series(u // 8192 - 4096, u % 8192 - 4096, c)

    def grid(self, N1, N2, y=(0.0, 0.0)):
        C = np.zeros((N1, N2), complex)
        w = np.exp(-TP * (self.k * y[0] + self.l * y[1]))
        np.add.at(C, (self.k % N1, self.l % N2), self.c * w)
        return np.fft.ifft2(C) * N1 * N2

    def norms(self, A, rho):
        """(l1, corner) of the series in theta~ = A theta coordinates on T_rho (index kappa~ = A^{-T} kappa)."""
        Ait = np.linalg.inv(A).T
        kt = np.rint(Ait[0, 0] * self.k + Ait[0, 1] * self.l).astype(np.int64)
        lt = np.rint(Ait[1, 0] * self.k + Ait[1, 1] * self.l).astype(np.int64)
        a = np.abs(self.c)
        l1 = float(np.sum(a * np.exp(TP * rho * (np.abs(kt) + np.abs(lt)))))
        cor = {}
        for sg in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
            cor[sg] = float(np.sum(a * np.exp(TP * rho * (sg[0] * kt + sg[1] * lt))))
        return l1, cor


def series_from_grid(vals, N1, N2, rel=1e-13):
    """Fourier coefficients of real-grid values (base indices), band-limited to |k| < N1/4, |l| < N2/4 and cut at
    rel * max (the approximate-inverse witness of the checker; FFT noise must not meet the strip weights)."""
    C = np.fft.fft2(vals) / (N1 * N2)
    kk = np.fft.fftfreq(N1, 1 / N1).astype(np.int64)[:, None] * np.ones((1, N2), np.int64)
    ll = np.fft.fftfreq(N2, 1 / N2).astype(np.int64)[None, :] * np.ones((N1, 1), np.int64)
    m = (np.abs(C) > rel * np.abs(C).max()) & (np.abs(kk) < N1 // 4) & (np.abs(ll) < N2 // 4)
    return Series(kk[m], ll[m], C[m])


class LunarOracle:
    def __init__(self, which, cache_dir=None, log=print):
        self.which = which
        self.log = log
        import model
        self.eps = {m: float(model.EPS * model.A_EXACT[m]) for m in model.M_MODES}
        self.shift = {m: (2, 2 - m) for m in model.M_MODES}
        a = (79 - math.sqrt(5)) / 3118
        self.nu = 1 - a if which == "lower" else 1 + a
        self.om = np.array([self.nu - 1, 1.0])
        self._load(cache_dir)
        self.N1, self.N2 = 1024, 256
        self._frame_cache = {}

    # ------------------------------------------------------------------ data
    def _load(self, cache_dir):
        path = os.path.join(cache_dir, "lunar_%s.pkl" % self.which) if cache_dir else None
        if path and os.path.exists(path):
            d = pickle.load(open(path, "rb"))
        else:
            import rot_build as RB
            import measure_residual as MR
            t0 = time.time()
            cand = RB.build(self.which, 88, 88, 88, 318, log=lambda *a: None)
            k, l, c3, c4 = MR.residual_rows(cand)
            wd = MR.witness_data(cand)
            d = dict(v=_arr(cand["v"]), p=_arr(cand["p"]), J=_arr(cand["J"]), R3=(k, l, c3), R4=(k, l, c4),
                     witness=wd, checker=dict(eta3=cand["bounds"]["eta3_unscaled"],
                                              eta4=cand["bounds"]["eta4_unscaled"],
                                              energy=cand["bounds"]["energy_unscaled"]))
            self.log("  built and measured %s in %.1fs" % (self.which, time.time() - t0))
            if path:
                os.makedirs(cache_dir, exist_ok=True)
                pickle.dump(d, open(path, "wb"))
        self.d = d
        v = Series(*d["v"]); p = Series(*d["p"]); J = Series(*d["J"])
        self.u = v.scale(1 / TP)                        # Q1 = psi + u
        self.p = p
        self.P2 = p.lin(J)
        # residual action rows in theta units (sign irrelevant for norms): 2 pi R3, 2 pi R4 (phase-1 values)
        self.R = [Series(d["R3"][0], d["R3"][1], 1j * TP * d["R3"][2]),
                  Series(d["R4"][0], d["R4"][1], 1j * TP * d["R4"][2])]
        self.R = [r.compress() for r in self.R]
        self.wd = d["witness"]

    # ------------------------------------------------------------------ geometry in the base frame
    def L_series(self):
        """L = DK' (4 x 2) as series, base frame and base angles."""
        one = Series.const(1.0); zero = Series([], [], [])
        u, p, P2 = self.u, self.p, self.P2
        return [[one.lin(u.d(0)), u.d(1)], [zero, one], [p.d(0), p.d(1)], [P2.d(0), P2.d(1)]]

    def frame_L(self, A, lam):
        """L~ = diag(A, lam A^{-T}) L A^{-1} as 4 x 2 series."""
        L = self.L_series()
        Ai = np.linalg.inv(A); Ait = Ai.T
        R = np.zeros((4, 4)); R[:2, :2] = A; R[2:, 2:] = lam * Ait
        out = [[None, None] for _ in range(4)]
        for i in range(4):
            for j in range(2):
                s = Series([], [], [])
                for a in range(4):
                    for b in range(2):
                        coef = R[i, a] * Ai[b, j]
                        if coef != 0 and len(L[a][b].c):
                            s = s.lin(L[a][b], 1.0, coef)
                out[i][j] = s
        return out

    def _eval_L(self, Ls, y):
        N1, N2 = self.N1, self.N2
        V = np.zeros((N1, N2, 4, 2), complex)
        for i in range(4):
            for j in range(2):
                if len(Ls[i][j].c):
                    V[..., i, j] = Ls[i][j].grid(N1, N2, y)
        return V

    def _corners(self, A, rho):
        """base imaginary shifts of the distinguished boundary of the theta~-polystrip (up to conjugation)."""
        Ai = np.linalg.inv(A)
        return [tuple(Ai @ np.array([rho, rho])), tuple(Ai @ np.array([rho, -rho]))]

    def _hess(self, y, A, lam, c, N1=None, N2=None):
        """V derivatives in Q~ coordinates along K at the base shift y; DH~, Hess~ (4,4) on the grid."""
        N1 = N1 or self.N1; N2 = N2 or self.N2
        uu = self.u.grid(N1, N2, y)
        psi = np.arange(N1)[:, None] / N1 + 1j * y[0] + 0 * np.arange(N2)[None, :]
        phi = np.arange(N2)[None, :] / N2 + 1j * y[1] + 0 * np.arange(N1)[:, None]
        Q = [psi + uu, phi]
        Ait = np.linalg.inv(A).T
        g1 = np.zeros((N1, N2, 2), complex); g2 = np.zeros((N1, N2, 2, 2), complex)
        for m, s in self.shift.items():
            X = s[0] * Q[0] + s[1] * Q[1]
            st = Ait @ np.array(s, float)
            a = self.eps[m]
            sn, cs = np.sin(TP * X), np.cos(TP * X)
            for i in range(2):
                g1[..., i] += a * TP * st[i] * sn
                for j in range(2):
                    g2[..., i, j] += a * TP ** 2 * st[i] * st[j] * cs
        pp = self.p.grid(N1, N2, y)
        Hs = np.zeros((N1, N2, 4, 4), complex); DH = np.zeros((N1, N2, 4), complex)
        Hs[..., :2, :2] = c * lam * g2
        e1 = A @ np.array([1.0, 0.0])
        Hs[..., 2:, 2:] = (c / lam) * np.outer(e1, e1)
        DH[..., :2] = c * lam * g1
        for i in range(2):
            DH[..., 2 + i] = c * (A[i, 0] * (pp - 1) + A[i, 1])
        return DH, Hs

    def frame(self, A, lam):
        """Per-(frame, lam) precomputation: L~ series, B~ = G~^{-1} series, torsion average inverse (c = 1)."""
        key = (tuple(np.asarray(A).ravel()), lam)
        if key in self._frame_cache:
            return self._frame_cache[key]
        A = np.asarray(A, float)
        Ls = self.frame_L(A, lam)
        N1, N2 = self.N1, self.N2
        L0 = self._eval_L(Ls, (0.0, 0.0))
        G0 = np.einsum("...ki,...kj->...ij", L0, L0)
        B0 = np.linalg.inv(G0)
        Bs = [[series_from_grid(B0[..., i, j].real, N1, N2) for j in range(2)] for i in range(2)]
        # torsion (bordered, extended) on the real torus at c = 1, omega~ = A omega'
        N = np.einsum("ab,...bk,...kj->...aj", OM, L0, B0)
        DH, Hs = self._hess((0.0, 0.0), A, lam, 1.0)
        DX = np.einsum("ab,...bc->...ac", JX, Hs)
        kk = np.fft.fftfreq(N1, 1 / N1)[:, None] * np.ones((1, N2))
        ll = np.fft.fftfreq(N2, 1 / N2)[None, :] * np.ones((N1, 1))
        mult = 2j * math.pi * (self.om[0] * kk + self.om[1] * ll)
        DN = np.fft.ifft2(np.fft.fft2(N, axes=(0, 1)) * mult[:, :, None, None], axes=(0, 1))
        XN = np.einsum("...ab,...bj->...aj", DX, N) - DN
        T = np.einsum("...ai,ab,...bj->...ij", N, OM, XN)
        Y = np.einsum("...a,...aj->...j", DH, N)
        ext = np.zeros((N1, N2, 3, 3), complex)
        ext[..., :2, :2] = T; ext[..., :2, 2] = A @ self.om; ext[..., 2, :2] = Y
        avg = ext.mean(axis=(0, 1))
        tinv = float(np.abs(np.linalg.inv(avg)).sum(axis=1).max())
        Tsup = float(np.abs(T).sum(axis=-1).max())     # sup |T| on the real torus (row sums), c = 1
        out = dict(A=A, lam=lam, Ls=Ls, Bs=Bs, tinv=tinv, Tsup_real=Tsup, avg=avg)
        self._frame_cache[key] = out
        return out

    # ------------------------------------------------------------------ norms at (frame, lam, rho)
    def norms(self, A, lam, rho, mu=None, regimes=REGIMES):
        """dict regime -> dict(sK, sB, iota, P1m1, eta), c = 1 (scale with c outside); mu enters only through
        H_majorant.  The 'sup' regime (grids at the corners) is computed only when requested."""
        A = np.asarray(A, float)
        want_sup = "sup" in regimes
        fr = self.frame(A, lam)
        Ls, Bs = fr["Ls"], fr["Bs"]
        res = {r: {} for r in REGIMES}
        # DK row sums and Gram inverse row sums: l1 (row sums of entrywise l1), corner (max over vertices of the
        # row sum of vertex sums), sup (sampled max over the distinguished boundary of the row sums)
        for name, M, nr, nc in (("sK", Ls, 4, 2), ("sB", Bs, 2, 2)):
            l1rows = []; cor = {}
            for i in range(nr):
                row_l1 = 0.0
                for j in range(nc):
                    if len(M[i][j].c) == 0:
                        continue
                    l1, cr = M[i][j].norms(A, rho)
                    row_l1 += l1
                    for sg, x in cr.items():
                        cor[(i, sg)] = cor.get((i, sg), 0.0) + x
                l1rows.append(row_l1)
            res["l1"][name] = max(l1rows)
            res["corner"][name] = max(cor.values())
            sup = 0.0
            for y in (self._corners(A, rho) if want_sup else []):
                if name == "sK":
                    V = self._eval_L(Ls, y)
                else:                                   # the exact inverse G~(theta)^{-1} at the corner
                    Lc = self._eval_L(Ls, y)
                    V = np.linalg.inv(np.einsum("...ki,...kj->...ij", Lc, Lc))
                sup = max(sup, float(np.abs(V).sum(axis=-1).max()))
            res["sup"][name] = sup
        # domain data for the H-majorant: iota_i (Im of the angle displacement A u e1), discs of the actions
        Ait = np.linalg.inv(A).T
        ul1, ucor = self.u.norms(A, rho)
        dsum_l1 = sum(self.u.d(j).norms(A, rho)[0] for j in range(2))   # base-angle derivatives (approx. frame)
        im_sup = 0.0
        for y in (self._corners(A, rho) if want_sup else []):
            im_sup = max(im_sup, float(np.abs(self.u.grid(self.N1, self.N2, y).imag).max()))
        acol = np.abs(A[:, 0])
        iota_ck = float(acol.max()) * min(ul1, rho * dsum_l1)
        iota_cor = float(acol.max()) * min(max(ucor.values()), rho * dsum_l1)
        iota_sup = float(acol.max()) * im_sup
        # action deviations: P~ = lam A^{-T} P, P = (p, P2); P1 = p
        dev_l1 = []; dev_cor = []; dev_sup = []
        for i in range(2):
            s = self.p.scale(lam * Ait[i, 0]).lin(self.P2, 1.0, lam * Ait[i, 1])
            c0 = s.c[(s.k == 0) & (s.l == 0)].sum().real
            sd = Series(s.k, s.l, np.where((s.k == 0) & (s.l == 0), 0, s.c))
            l1, cr = sd.norms(A, rho)
            dev_l1.append(l1); dev_cor.append(max(cr.values()))
            sp = 0.0
            for y in (self._corners(A, rho) if want_sup else []):
                sp = max(sp, float(np.abs(sd.grid(self.N1, self.N2, y)).max()))
            dev_sup.append(sp)
        p0 = self.p.c[(self.p.k == 0) & (self.p.l == 0)].sum().real
        for r, io, dv in (("l1", iota_ck, dev_l1), ("corner", iota_cor, dev_cor), ("sup", iota_sup, dev_sup)):
            res[r]["iota"] = io
            # |P1 - 1| on the disc product (without the mu margin, added in H_majorant):
            # P1 = (A^T P~)_1 / lam, |P~_j - c~_j| <= dev_j
            res[r]["P1m1"] = abs(p0 - 1) + float(np.dot(np.abs(A[:, 0]), dv)) / lam
        # residual (action rows, theta~ frame): lam A^{-T} (R_P1, R_P2), plus the exp-witness part
        wpart = self.witness_part(A, rho)
        for r in REGIMES:
            res[r]["eta"] = 0.0
        for i in range(2):
            comb = self.R[0].scale(lam * Ait[i, 0]).lin(self.R[1], 1.0, lam * Ait[i, 1])
            l1, cr = comb.norms(A, rho)
            wp = lam * (abs(Ait[i, 0]) * wpart[0] + abs(Ait[i, 1]) * wpart[1])
            sp = 0.0
            for y in (self._corners(A, rho) if want_sup else []):
                sp = max(sp, float(np.abs(comb.grid(2048, 512, y)).max()))
            res["l1"]["eta"] = max(res["l1"]["eta"], l1 + wp)
            res["corner"]["eta"] = max(res["corner"]["eta"], max(cr.values()) + wp)
            res["sup"]["eta"] = max(res["sup"]["eta"], sp + wp)
        res["tinv"] = fr["tinv"]
        return res

    def witness_part(self, A, rho):
        """2 pi times the witness contributions to the P1, P2 rows (rot_build.bounds), base weights at the
        frame's l1 weights (an approximation for A != I: the witness theorem is applied in base angles)."""
        wd = self.wd
        def l1(t):
            return Series(*t).norms(A, rho)[0]
        B = 2 * l1(wd["v"])
        r = TP * (l1(wd["psi"]) + l1(wd["phi"]))
        Delta = math.exp(2 * B) * (wd["eps0"] + (0.5 + rho) * r)
        w = lambda s: math.exp(TP * rho * (abs(s[0]) + abs(s[1])))
        p1 = 2 * sum(abs(self.eps[m]) * w(s) for m, s in self.shift.items()) * Delta
        p2 = sum(abs(self.eps[m]) * abs(2 - m) * w(s) for m, s in self.shift.items()) * Delta
        return TP * p1, TP * p2

    # ------------------------------------------------------------------ H-majorant (checker construction)
    def H_majorant(self, A, lam, c, rho, mu, regime_norms, trig="cosh"):
        """The five H~ quantities on D = T_{rho_H} x discs, time scale c.  trig = 'disc': the landed ball
        arithmetic (Slp.balls compiles cos s.Q to (chi_s + chi_-s)/2 with |chi_s| <= w_H^{|s|_1}, so |cos| <= w_H^{|s|});
        trig = 'cosh': |cos|, |sin| <= cosh(2 pi |s|_1 rho_H) (rot_norms.py; a trig primitive in the ball pass)."""
        A = np.asarray(A, float)
        Ait = np.linalg.inv(A).T
        rhoH = rho + regime_norms["iota"] + mu
        g1 = np.zeros(2); g2 = np.zeros((2, 2)); g3 = np.zeros(2)
        for m, s in self.shift.items():
            st = np.abs(Ait @ np.array(s, float))
            ch = math.cosh(TP * st.sum() * rhoH) if trig == "cosh" else math.exp(TP * st.sum() * rhoH)
            a = abs(self.eps[m]) * ch
            g1 += a * TP * st
            g2 += a * TP ** 2 * np.outer(st, st)
            g3 += a * TP ** 3 * st * st.sum() ** 2
        pm = regime_norms["P1m1"] + float(np.abs(A[:, 0]).sum()) * mu / lam
        ang = np.abs(A[:, 0]) * pm + np.abs(A[:, 1])            # |(A (P1 - 1, 1))_i|
        col = np.abs(A[:, 0])
        dH = c * lam * g1.sum() + c * ang.sum()
        XH = c * max(ang.max(), lam * g1.max())
        DXH = c * max((col * col.sum()).max() / lam, lam * g2.sum(axis=1).max())
        D2XH = c * lam * g3.max()
        D2H = c * lam * g2.sum() + (c / lam) * np.outer(col, col).sum()
        parts = dict(dH=dH, XH=XH, DXH=DXH, D2XH=D2XH, D2H=D2H)
        return max(parts.values()), parts


def dioph_gamma(A, om, K=400):
    """Numerical inf_{k != 0} |k|_1 |k . A om| (tau = 1); exact for the lunar frequencies up to K (the infimum is
    attained at small k; scripts/certifier/smalldiv.py certifies the tail)."""
    w = np.asarray(A, float) @ np.asarray(om, float)
    best = math.inf
    for k1 in range(0, K + 1):
        if abs(w[1]) > 1e-12:
            x = -k1 * w[0] / w[1]
            cands = {math.floor(x) - 1, math.floor(x), math.ceil(x), math.ceil(x) + 1}
        else:
            cands = set(range(-K, K + 1))
        for k2 in cands:
            if k1 == 0 and k2 <= 0:
                continue
            v = (abs(k1) + abs(k2)) * abs(k1 * w[0] + k2 * w[1])
            best = min(best, v)
    return best


if __name__ == "__main__":
    cache = sys.argv[1] if len(sys.argv) > 1 else None
    for which in ("lower", "upper"):
        O = LunarOracle(which, cache)
        for name, A, rho, mu in (("rot", [[1, 0], [0, 1]], 1 / 70, 1 / 160), ("theta", [[1, 1], [0, 1]], 1 / 200, 1 / 160)):
            r = O.norms(A, 1.0, rho, mu)
            print(which, name, "rho %.5f" % rho, "tinv %.6f" % r["tinv"])
            for reg in REGIMES:
                M, parts = O.H_majorant(A, 1.0, 1.0, rho, mu, r[reg])
                print("   %-6s sK %.4f sB %.4f iota %.5f P1m1 %.4f eta %.4e | M %.4f %s" % (
                    reg, r[reg]["sK"], r[reg]["sB"], r[reg]["iota"], r[reg]["P1m1"], r[reg]["eta"], M,
                    {k: round(v, 4) for k, v in parts.items()}))
            print("   gamma(A omega') = %.6f" % dioph_gamma(A, O.om))
