"""High-precision (fixed point, P bits) chord-Newton iteration for R(v) = 0 on a Nx x Nt grid.

v is ODD and real, hence vhat is purely imaginary; vhat is stored as complex fixed point (re, im ints, scale 2^P).
The residual is evaluated in Fourier space from  E = exp(2 i v)  (grid DFT, folded): all modes of R are computed from
the shifted coefficients of E.  The linear solve uses the double-precision Jacobian at a nearby double solution
(chord iteration, linear rate ~1e-12 per step, residual evaluated in full precision each step).
"""
import numpy as np, mpmath, time
from fractions import Fraction as F
from hpfft import P, fft2, zeros
from model import A_EXACT, EPS, SHIFT, nu_minus_one
import dsolve

def fx(fr, prec=P):
    """Fraction -> fixed point int."""
    return (fr.numerator << prec) // fr.denominator if fr >= 0 else -((-fr.numerator << prec) // fr.denominator)

def to_int_array(x, prec=P):
    return np.array([[int(mpmath.nint(mpmath.mpf(v) * 2**prec)) if False else 0 for v in r] for r in x], dtype=object)

class HP:
    def __init__(self, nx, nt, which):
        self.nx, self.nt, self.which = nx, nt, which
        self.N = nx * nt
        self.logN = self.N.bit_length() - 1
        mpmath.mp.prec = P + 120
        x, y = nu_minus_one(which)
        s = mpmath.mpf(x.numerator) / x.denominator + mpmath.mpf(y.numerator) / y.denominator * mpmath.sqrt(5)
        self.s_mp = s
        k = np.fft.fftfreq(nx, 1.0 / nx).astype(int); l = np.fft.fftfreq(nt, 1.0 / nt).astype(int)
        self.k, self.l = k, l
        m = np.empty((nx, nt), dtype=object)
        for a in range(nx):
            for b in range(nt):
                d = s * int(k[a]) + int(l[b])
                m[a, b] = -int(mpmath.nint(d * d * 2**P))
        self.mult = m
        mask = np.ones((nx, nt), dtype=object); mask[nx // 2, :] = 0; mask[:, nt // 2] = 0
        self.mask = mask
        self.coef = {mm: fx(2 * EPS * A_EXACT[mm]) for mm in SHIFT}
        self.G = dsolve.Grid(nx, nt, which)

    # ---- conversions
    def float_to_fx(self, a):
        """double array -> fixed-point (exact for the double value)."""
        out = np.empty(a.shape, dtype=object)
        for idx in np.ndindex(a.shape):
            out[idx] = int(F(float(a[idx]))*2**P) if False else (int(float(a[idx]) * 2**53) << (P - 53))
        return out

    def vhat_from_double(self, v):
        vh = np.fft.fft2(v) / self.N * self.G.mask      # complex128
        re = self.float_to_fx(vh.real); im = self.float_to_fx(vh.imag)
        return re, im

    def vgrid(self, vre, vim):
        gr, gi = fft2(vre, vim, +1)
        return gr, gi

    def expj2(self, gr):
        """E = exp(2 i v) from v grid (real part ints)."""
        mpmath.mp.prec = P + 60
        er = np.empty(gr.shape, dtype=object); ei = np.empty(gr.shape, dtype=object)
        sc = mpmath.mpf(2) ** (1 - P)
        for idx in np.ndindex(gr.shape):
            z = mpmath.expj(int(gr[idx]) * sc)
            er[idx] = int(mpmath.nint(z.real * 2**P)); ei[idx] = int(mpmath.nint(z.imag * 2**P))
        return er, ei

    def expj2_update(self, dg, er, ei):
        """E *= exp(2 i dv), dg = fixed-point dv grid (real)."""
        tr = zeros(dg.shape); ti = zeros(dg.shape)
        tr = tr + (1 << P)          # term_0 = 1
        pr, pi_ = tr.copy(), zeros(dg.shape)
        sr, si = pr.copy(), pi_.copy()
        n = 1
        d2 = 2 * dg
        while True:
            # term_n = term_{n-1} * (i d2) / n
            nr = -((pi_ * d2) >> P); ni = (pr * d2) >> P
            pr = nr // n; pi_ = ni // n
            if not any(pr.ravel()) and not any(pi_.ravel()):
                break
            sr = sr + pr; si = si + pi_
            n += 1
        # E = E * S
        return (er * sr - ei * si) >> P, (er * si + ei * sr) >> P

    def residual_hat(self, vre, vim, er, ei):
        """Folded grid residual in Fourier space: returns (Rre, Rim) (unmasked)."""
        Fr, Fi = fft2(er, ei, -1)
        Fr = Fr >> self.logN; Fi = Fi >> self.logN        # Ehat (grid DFT / N)
        # idx reflection: a[-kappa]
        def refl(a): return np.roll(np.flip(a, (0, 1)), 1, axis=(0, 1))
        Rr = (self.mult * vre) >> P; Ri = (self.mult * vim) >> P
        Frr, Fir = refl(Fr), refl(Fi)
        for m, (sk, sl) in SHIFT.items():
            a_r = np.roll(Fr, (sk, sl), axis=(0, 1)); a_i = np.roll(Fi, (sk, sl), axis=(0, 1))   # Ehat_{kappa - s}
            b_r = np.roll(Frr, (-sk, -sl), axis=(0, 1)); b_i = np.roll(Fir, (-sk, -sl), axis=(0, 1))  # Ehat_{-kappa-s}
            # Q' = a - conj(b): re = a_r - b_r, im = a_i + b_i ; Q = Q'/(2i) => Q_re = Q'_im/2, Q_im = -Q'_re/2
            qr = (a_i + b_i) >> 1; qi = -((a_r - b_r) >> 1)
            c = self.coef[m]
            Rr = Rr + ((c * qr) >> P); Ri = Ri + ((c * qi) >> P)
        return Rr, Ri

    def fx_to_float(self, a, e):
        """fixed ints -> double array of a / 2^(P - e)... i.e. value * 2^e."""
        return np.array([[float(int(x) / 2**P) * 2.0**e if abs(int(x)) < 2**(P + 900) else 0.0 for x in r] for r in a])

    def maxabs(self, re, im):
        m = 0
        for a, b in zip(re.ravel(), im.ravel()):
            v = max(abs(int(a)), abs(int(b)))
            if v > m: m = v
        return m

    def chord_step(self, vre, vim, Rr, Ri, vbase, eps):
        """delta-hat = J_d^{-1} P R-hat (double); returns fixed-point (dre, dim)."""
        m = self.maxabs(Rr, Ri)
        e = max(m.bit_length() - P, -10**6)       # value magnitude ~ 2^e
        # scaled float arrays: value * 2^-e
        def sfl(a):
            out = np.empty(a.shape)
            for idx in np.ndindex(a.shape):
                x = int(a[idx]); out[idx] = (x >> max(0, -e + P - 60 - P + P)) if False else 0
            return out
        sh = P - 60 + e   # float(x * 2^(-e-P+...)) ; use exact big-int division
        def toflt(a):
            out = np.empty(a.shape)
            for idx in np.ndindex(a.shape):
                out[idx] = float(F(int(a[idx]), 1 << (P + e)))
            return out
        rh = toflt(Rr) + 1j * toflt(Ri)
        rh = rh * self.G.mask
        rg = np.real(np.fft.ifft2(rh * self.N)) if False else None
        rg = np.fft.ifft2(rh) * self.N
        rg = self.G.odd(np.real(rg))
        sol = self.G.solve_lin(vbase, eps, rg)
        dh = np.fft.fft2(sol) / self.N * self.G.mask
        def tofx(a):
            out = np.empty(a.shape, dtype=object)
            for idx in np.ndindex(a.shape):
                x = int(float(a[idx]) * 2**53)
                sh2 = P + e - 53
                out[idx] = x << sh2 if sh2 >= 0 else x >> (-sh2)
            return out
        return tofx(dh.real), tofx(dh.imag)

    def run(self, vre, vim, vbase, eps, iters, tag="", log=print, tol_exp=150):
        t0 = time.time()
        # enforce vhat purely imaginary and odd (the double-precision start is odd only to ~1e-17)
        refl = lambda a: np.roll(np.flip(a, (0, 1)), 1, axis=(0, 1))
        vim = (vim - refl(vim)) >> 1
        vre = zeros(vre.shape)
        gr, gi = self.vgrid(vre, vim)
        er, ei = self.expj2(gr)
        hist = []
        for it in range(iters):
            Rr, Ri = self.residual_hat(vre, vim, er, ei)
            Rrm = Rr * self.mask; Rim = Ri * self.mask
            mp_ = self.maxabs(Rrm, Rim); mfull = self.maxabs(Rr, Ri)
            # sup norm on the grid of the full residual
            rgr, _ = fft2(Rr, Ri, +1)
            sup = self.maxabs(rgr, zeros(rgr.shape))
            lg = lambda x: (float(mpmath.log10(mpmath.mpf(x) / 2**P)) if x else -999)
            hist.append((it, lg(mp_), lg(mfull), lg(sup)))
            log(f"{tag} it={it} log10 max|Rhat_proj|={lg(mp_):.2f} max|Rhat_full|={lg(mfull):.2f} grid sup|R|={lg(sup):.2f} t={time.time()-t0:.0f}s")
            if it == iters - 1 or lg(mp_) < -tol_exp: break
            dre, dim = self.chord_step(vre, vim, Rrm, Rim, vbase, eps)
            vre = vre - dre; vim = vim - dim
            vre = vre * self.mask; vim = vim * self.mask
            dgr, dgi = fft2(-dre, -dim, +1)
            er, ei = self.expj2_update(dgr, er, ei)
        return vre, vim, er, ei, hist
