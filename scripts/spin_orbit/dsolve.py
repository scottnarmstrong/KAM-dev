"""Double-precision continuation + Newton-GMRES solver for the scalar invariance equation (pi-free form).

Unknown: v real, ODD (v(-x) = -v(x)) -- this fixes the theta1-shift gauge of the torus parametrisation; Nyquist
modes are excluded.  Residual R(v) = Dt^2 v + 2 eps sum A_m sin(theta_m + 2 v) on the grid (model.py).
"""
import numpy as np
from scipy.sparse.linalg import LinearOperator, gmres
from model import A_EXACT, EPS, SHIFT, nu_minus_one

class Grid:
    def __init__(self, nx, nt, which):
        self.nx, self.nt, self.which = nx, nt, which
        x, y = nu_minus_one(which)
        self.s = float(x) + float(y) * np.sqrt(5.0)
        k = np.fft.fftfreq(nx, 1.0 / nx); l = np.fft.fftfreq(nt, 1.0 / nt)
        self.k, self.l = k, l
        self.mult = -((self.s * k[:, None] + l[None, :]) ** 2)      # Dt^2 symbol
        psi = np.arange(nx) / nx; phi = np.arange(nt) / nt
        self.theta = {m: 2 * np.pi * (SHIFT[m][0] * psi[:, None] + SHIFT[m][1] * phi[None, :]) for m in SHIFT}
        mask = np.ones((nx, nt)); mask[nx // 2, :] = 0; mask[:, nt // 2] = 0   # drop Nyquist rows/columns
        self.mask = mask
        self.A = {m: float(a) for m, a in A_EXACT.items()}

    def proj(self, f):
        return np.real(np.fft.ifft2(np.fft.fft2(f) * self.mask))

    def odd(self, f):
        return 0.5 * (f - np.roll(np.flip(f), 1, axis=(0, 1)))

    def resid(self, v, eps):
        d2 = np.real(np.fft.ifft2(self.mult * self.mask * np.fft.fft2(v)))
        f = sum(self.A[m] * np.sin(self.theta[m] + 2 * v) for m in self.A)
        return d2 + 2 * eps * f

    def gfun(self, v, eps):
        return 4 * eps * sum(self.A[m] * np.cos(self.theta[m] + 2 * v) for m in self.A)

    def jac_op(self, v, eps):
        g = self.gfun(v, eps)
        def mv(x):
            x = x.reshape(self.nx, self.nt)
            d = np.real(np.fft.ifft2(self.mult * self.mask * np.fft.fft2(x))) + g * x
            return self.odd(self.proj(d)).ravel()
        return LinearOperator((self.nx * self.nt,) * 2, matvec=mv, dtype=float)

    def precond(self, tau0=1e-4):
        d = 1.0 / np.maximum(np.abs(self.mult), tau0)
        def mv(x):
            x = x.reshape(self.nx, self.nt)
            return self.odd(np.real(np.fft.ifft2(d * self.mask * np.fft.fft2(x)))).ravel()
        return LinearOperator((self.nx * self.nt,) * 2, matvec=mv, dtype=float)

    def solve_lin(self, v, eps, rhs, tol=1e-12, restart=40, maxiter=40):
        J = self.jac_op(v, eps)
        sc = np.max(np.abs(rhs))
        if sc == 0: return np.zeros_like(rhs)
        x, info = gmres(J, (rhs / sc).ravel(), M=self.precond(), rtol=tol, restart=restart, maxiter=maxiter)
        return x.reshape(rhs.shape) * sc

    def newton(self, v, eps, tol=1e-14, maxit=30, verbose=False):
        for it in range(maxit):
            r = self.odd(self.proj(self.resid(v, eps)))
            rn = np.max(np.abs(r))
            if verbose: print("   newton", it, rn)
            if rn < tol: break
            v = v - self.solve_lin(v, eps, r)
        return v, rn

    def p_of(self, v):
        dv = np.real(np.fft.ifft2(1j * (self.s * self.k[:, None] + self.l[None, :]) * self.mask * np.fft.fft2(v)))
        return 1 + self.s + dv

def continuation(nx, nt, which, nsteps=40, verbose=False):
    G = Grid(nx, nt, which)
    v = np.zeros((nx, nt))
    for j in range(1, nsteps + 1):
        eps = float(EPS) * j / nsteps
        v, rn = G.newton(v, eps, tol=1e-13)
        if verbose: print(which, j, eps, rn)
    return G, v

if __name__ == "__main__":
    import sys, time
    for which in ("lower", "upper"):
        t = time.time()
        G, v = continuation(256, 64, which, verbose=False)
        p = G.p_of(v)
        r = G.odd(G.proj(G.resid(v, float(EPS))))
        print(which, "p range", p.min(), p.max(), "resid", np.max(np.abs(r)), "time", time.time() - t)
