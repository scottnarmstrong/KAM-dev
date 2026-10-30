"""Small-divisor sums S(delta) = sum_{k != 0} exp(-2|k|_1 delta)/|k.omega|^2 for the FH25 SJS frequency
(2pi-periodic angles), plus partial sums by shell, to estimate the sharp Russmann constant
c_R(delta) = sqrt(gamma^2 delta^(2tau) 2^d S(delta)).
"""
import numpy as np, sys, math

w = np.array([8.39549288702546301204e-2, 3.38240117059304358259e-2, -1.85007988077595e-5])
gam, tau, d = 1.69e-6, 2.4, 3
M = int(sys.argv[1]) if len(sys.argv) > 1 else 600
deltas = [0.1, 0.1 / 6, (tau / (tau + 1)) * 0.1 / 6, 0.1 / 12, (tau / (tau + 1)) * 0.1 / 12]

# accumulate per |k|_1 shell: sum 1/|k.w|^2 and min |k.w| |k|^tau
shell_inv2 = np.zeros(M + 1)
shell_mingam = np.full(M + 1, np.inf)
k2 = np.arange(-M, M + 1)
K2, K3 = np.meshgrid(k2, k2, indexing="ij")
A23 = np.abs(K2) + np.abs(K3)
base = K2 * w[1] + K3 * w[2]
for k1 in range(-M, M + 1):
    rem = M - abs(k1)
    mask = A23 <= rem
    n1 = abs(k1) + A23[mask]
    kw = k1 * w[0] + base[mask]
    nz = n1 > 0
    n1 = n1[nz]; kw = np.abs(kw[nz])
    np.add.at(shell_inv2, n1, 1.0 / kw**2)
    g = kw * n1.astype(float) ** tau
    np.minimum.at(shell_mingam, n1, g)

print("M =", M)
print("min over 0<|k|<=M of |k.w| |k|^tau =", shell_mingam[1:].min(), "at |k|=", 1 + shell_mingam[1:].argmin())
for dl in deltas:
    S = np.sum(shell_inv2 * np.exp(-2 * np.arange(M + 1) * dl))
    cR = gam * dl**tau * math.sqrt(2**d * S)
    # crude Diophantine tail bound for |k|_1 > M (FHL17-style counting, 2pi convention)
    a = 2**tau
    zeta = sum(1.0 / (a + j) ** 2 for j in range(200000)) + 1.0 / (a + 200000)
    from mpmath import gammainc
    tail = 2 ** (2 * tau + 1) * zeta / gam**2 * (2 * dl) ** (-2 * tau) * float(gammainc(2 * tau + 1, 2 * dl * (M + 1)))
    cRt = gam * dl**tau * math.sqrt(2**d * (S + tail))
    print(f"delta={dl:.6g}  S_partial={S:.4e}  cR_partial={cR:.4e}  tail={tail:.3e}  cR(delta,M)={cRt:.4e}")
# shell profile
for L in [1, 2, 5, 7, 10, 20, 50, 100, 200, 400, M]:
    if L <= M:
        print("shell", L, "sum 1/|kw|^2 =", f"{shell_inv2[L]:.3e}", " min|kw||k|^tau =", f"{shell_mingam[L]:.3e}")
np.save(sys.argv[2] if len(sys.argv) > 2 else "/dev/null", shell_inv2) if len(sys.argv) > 2 else None
