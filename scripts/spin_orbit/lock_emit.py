#!/usr/bin/env python3
"""LOCK-GEN part 2 (D45): emitter of the N = 65 librational certificate in the landed `TorusCertificate` format,
for the time-scaled polar Hamiltonian `.mul (.const κ) (lockHamExpr Ω cs)` (lock_ham.py; the landed lockHamExpr,
3116 ops bare, 3158 with the κ factor).  Untrusted tooling.

    SO_HP_BITS=192 OMP_NUM_THREADS=4 python3 lock_emit.py OUT.json [--Ks 56] [--Ls 12] [--shape diamond]
        [--rho 1/140] [--kappa 1] [--prec 96] [--form design] [--lean SAMPLE.lean]

Pipeline (high precision, from LOCK-GEN part 1's stage-B pickle B_N65_K160_L40.pkl, 192-bit sine coefficients of
V = 2πψ on the half diamond, residual 10^-51):
 1. grid (512 × 128, fixed point 2^-P): ψ = V/2π, p − 1 = Dt V, X = ψ − c, Y = p − 1 − c′, the polar data
    U = α − θ₁, P = I = π(ΩX² + Y²/Ω), the clock action J̃ = −(K − J̃)(θ₁ + U, θ₂, P) (energy E0 = 0), and the
    witness functions on the torus:  E = exp(2πiU) (character key (1, 0)),  exp(±iA∘K) = exp(±2iV) (A = 4π(c + X)
    = 4πψ on the torus), √(P/(πΩ)), √(PΩ/π) and their reciprocals;
 2. Fourier data by the fixed-point FFT, truncation to the support (diamond |k|/Ks + |l|/Ls ≤ 1 or rectangle),
    rounding to 2^-S;
 3. the invariance residual of the TRUNCATED embedding (rows α, φ, I, J̃ of X_H(K) − ∂_{sω*}K, H = κ K_lock) on the
    grid, its Fourier data and its weighted norm Σ|R̂_k| e^{2πρ|k|₁} (the err the checker sees, up to the witness
    and rounding radii), plus the energy error;
 4. the certificate: params (the lock package), ham (tree + Lean text), weightH, centre, radius, freqBox, emb,
    weight, wit (charWit (1,0) ↦ E; expWit in exp-slot order; invWit in inv-slot order: 2 for the constant
    `inv π` slots (π has 2π-degree 1), 1/√ for the others; sqrtWit keyed by sqrt slot), gramInv (approximate G⁻¹
    of the truncated DK, 48-bit), torsInv (from the double extended-torsion average; LOCK-DATA recomputes it from
    the models with sofx_gen.torsion_witness), cfgFull / cfgLow (advice books EMPTY: the packed advice is a
    performance artefact the sofx GENERATE pass builds once the mirror has the sqrt arm), piEnc.
All JSON mantissas are integers m denoting m / 2^prec (CertFixed prec).  The sqrt encoding of the witnesses lives in
`sqrt_witness` only.
"""
import os, sys, json, math, time, pickle, argparse, hashlib, subprocess, datetime
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
os.environ.setdefault("SO_HP_BITS", "192")
import numpy as np                    # noqa: E402
import mpmath as mp                   # noqa: E402
import hpfft as HF                    # noqa: E402
import lock_hp as LHP                 # noqa: E402
import lock_ham as LH                 # noqa: E402
import lock_jet as LJ                 # noqa: E402
from model import A_EXACT, EPS        # noqa: E402

GEN_VERSION = "lock-gen2-0.2"
DATA = os.environ.get("SO_LOCK_DIR", "/mnt/HC_Volume_106379410/kam-data/so-lock")
OMEGA_R = F(8, 65)
CENTRE = LHP.CENTRE
P = HF.P


# ------------------------------------------------------------------------------------------- 1. grid
class Grid:
    def __init__(self, N=65, K=160, L=40, nx=512, nt=128):
        st = pickle.load(open(os.path.join(DATA, "B_N%d_K%d_L%d.pkl" % (N, K, L)), "rb"))
        assert st["P"] == P, "SO_HP_BITS must equal the pickle's precision %d" % st["P"]
        G = LHP.Gal(K, L, nx, nt)
        self.H = LHP.HPT(G, N, HF)
        self.nx, self.nt, self.N = nx, nt, N
        H = self.H
        vim = H.vim_from_b(st["bfx"])
        z = HF.zeros(vim.shape)
        self.vg, _ = HF.fft2(z, vim, +1)
        self.dr, _ = HF.fft2(-((H.dmul * vim) >> P), z, +1)
        self.om = H.om
        self.kk, self.ll = H.kk, H.ll

    def mp(self, x):
        return mp.mpf(int(x)) / mp.mpf(2) ** P

    def fx(self, x):
        return int(mp.nint(x * mp.mpf(2) ** P))


def centre_mp(ph, deriv=0):
    tp = 2 * mp.pi
    out = mp.mpf(0)
    for j, c in enumerate(CENTRE):
        q = mp.mpf(c.numerator) / c.denominator
        w = tp * (j + 1)
        out += q * [mp.sin(w * ph), w * mp.cos(w * ph), -w ** 2 * mp.sin(w * ph), -w ** 3 * mp.cos(w * ph)][deriv]
    return out


def k_parts(al, ph, I, Om):
    """(K − J̃, ∂_α K, ∂_φ K, ∂_I K) of the unscaled lock Hamiltonian at a real point (mp)."""
    tp = 2 * mp.pi
    S, T = mp.sqrt(I / (mp.pi * Om)), mp.sqrt(I * Om / mp.pi)
    s1, c1 = mp.sin(tp * al), mp.cos(tp * al)
    X, Y = S * s1, T * c1
    c, cp, cpp, cppp = (centre_mp(ph, d) for d in range(4))
    A = 2 * tp * (c + X)
    V, VA, VAphi = mp.mpf(0), mp.mpf(0), mp.mpf(0)
    for m, a in A_EXACT.items():
        e = mp.mpf((EPS * a).numerator) / (EPS * a).denominator
        arg = A + tp * (2 - m) * ph
        V -= e * mp.cos(arg)
        VA += e * mp.sin(arg)
        VAphi += e * mp.sin(arg) * tp * (2 - m)
    Kv = Y * Y / 2 - cp * cp / 2 + X * cpp + V - mp.mpf(1) / 2
    Xa, Ya = tp * S * c1, -tp * T * s1
    Ka = Y * Ya + Xa * cpp + VA * 2 * tp * Xa
    Kphi = -cp * cpp + X * cppp + VA * 2 * tp * cp + VAphi
    KI = Y * Y / (2 * I) + X / (2 * I) * cpp + VA * 2 * tp * X / (2 * I)
    return Kv, Ka, Kphi, KI


def grid_functions(g, Om=OMEGA_R):
    """Fixed-point grids of U, P, J̃ and of the witness functions (re, im) on the torus."""
    t0 = time.time()
    Omm = mp.mpf(Om.numerator) / Om.denominator
    tp = 2 * mp.pi
    nx, nt = g.nx, g.nt
    names = ["U", "P", "J", "Er", "Ei", "Wr", "Wi", "S1", "S2", "R1", "R2"]
    out = {k: np.empty((nx, nt), dtype=object) for k in names}
    for a in range(nx):
        for c in range(nt):
            ph = mp.mpf(c) / nt
            psi = g.mp(g.vg[a, c]) / tp
            X = psi - centre_mp(ph)
            Y = g.mp(g.dr[a, c]) - centre_mp(ph, 1)
            I = mp.pi * (Omm * X ** 2 + Y ** 2 / Omm)
            al = mp.atan2(mp.sqrt(Omm) * X, Y / mp.sqrt(Omm)) / tp
            U = al - mp.mpf(a) / nx
            U -= mp.nint(U)
            Kv = k_parts(al, ph, I, Omm)[0]
            s1, s2 = mp.sqrt(I / (mp.pi * Omm)), mp.sqrt(I * Omm / mp.pi)
            E = mp.expj(tp * U)
            W = mp.expj(2 * tp * psi)
            vals = dict(U=U, P=I, J=-Kv, Er=E.real, Ei=E.imag, Wr=W.real, Wi=W.imag, S1=s1, S2=s2, R1=1 / s1,
                        R2=1 / s2)
            for k in names:
                out[k][a, c] = g.fx(vals[k])
    print("  grid functions %.0fs" % (time.time() - t0), flush=True)
    return out


def fourier(g, re, im=None):
    """Fourier coefficients (fixed point, dict key -> (re, im) ints) of a grid function."""
    im = HF.zeros(re.shape) if im is None else im
    Fr, Fi = HF.fft2(re, im, -1)
    lg = g.H.logN
    out = {}
    for a in range(g.nx):
        for c in range(g.nt):
            if a == g.nx // 2 or c == g.nt // 2:
                continue
            k = int(g.kk[a]); l = int(g.ll[c])
            out[(k, l)] = (int(Fr[a, c]) >> lg, int(Fi[a, c]) >> lg)
    return out


# ------------------------------------------------------------------------------------------- 2. truncation
def in_support(k, l, Ks, Ls, shape):
    if shape == "diamond":
        return abs(k) * Ls + abs(l) * Ks <= Ks * Ls
    return abs(k) <= Ks and abs(l) <= Ls


def truncate(co, Ks, Ls, shape, S, real=True):
    """Keep the support, round to 2^-S; returns key -> (re, im) integers at scale 2^-S."""
    sh = P - S
    rnd = lambda x: (x + (1 << (sh - 1))) >> sh
    out = {}
    for (k, l), (re, im) in co.items():
        if in_support(k, l, Ks, Ls, shape):
            r, i = rnd(re), rnd(im)
            if r or i:
                out[(k, l)] = (r, i)
    return out


def half(co):
    return sorted(((k, l), v) for (k, l), v in co.items() if (k, l) > (0, 0))


# ------------------------------------------------------------------------------------------- 3. residual
def synth(g, co, S, mult=None):
    """Grid values (fixed point 2^-P) of the real series with coefficients co (scale 2^-S), optionally times
    the symbol mult(k, l) (a Python complex in mp)."""
    nx, nt = g.nx, g.nt
    re, im = HF.zeros((nx, nt)), HF.zeros((nx, nt))
    sh = P - S
    for (k, l), (r, i) in co.items():
        if mult is not None:
            m = mult(k, l)
            mr, mi = int(mp.nint(m.real * 2 ** P)), int(mp.nint(m.imag * 2 ** P))
            r, i = (r * mr - i * mi) >> P, (r * mi + i * mr) >> P
        re[k % nx, l % nt] = r << sh
        im[k % nx, l % nt] = i << sh
    gr, _ = HF.fft2(re, im, +1)
    return gr


def residual(g, tr, S, rho, kappa, Om=OMEGA_R, rhos=()):
    """Rows (α, I, J̃) of the invariance residual of the truncated embedding, weighted norms on the strip rho, and
    the energy error (the φ row is identically 0: ∂_J̃ H = κ)."""
    t0 = time.time()
    Omm = mp.mpf(Om.numerator) / Om.denominator
    tp = 2 * mp.pi
    om = g.om
    D = lambda k, l: mp.mpc(0, tp * (om * k + l))
    U, Pg, Jg = (synth(g, tr[x], S) for x in ("U", "P", "J"))
    DU, DP, DJ = (synth(g, tr[x], S, D) for x in ("U", "P", "J"))
    nx, nt = g.nx, g.nt
    rows = {x: np.empty((nx, nt), dtype=object) for x in ("a", "I", "J", "E")}
    for a in range(nx):
        for c in range(nt):
            ph = mp.mpf(c) / nt
            al = mp.mpf(a) / nx + g.mp(U[a, c])
            I = g.mp(Pg[a, c])
            Kv, Ka, Kphi, KI = k_parts(al, ph, I, Omm)
            rows["a"][a, c] = g.fx(kappa * (KI - om - g.mp(DU[a, c])))
            rows["I"][a, c] = g.fx(kappa * (-Ka - g.mp(DP[a, c])))
            rows["J"][a, c] = g.fx(kappa * (-Kphi - g.mp(DJ[a, c])))
            rows["E"][a, c] = g.fx(kappa * (Kv + g.mp(Jg[a, c])))
    out = {}
    for x, arr in rows.items():
        co = fourier(g, arr)
        w = sum(math.hypot(r, i) / 2 ** P * math.exp(2 * math.pi * float(rho) * (abs(k) + abs(l)))
                for (k, l), (r, i) in co.items())
        out[x] = dict(weighted=w, sup_grid=max(abs(int(v)) for v in arr.ravel()) / 2 ** P)
        for r in rhos:
            out[x]["weighted_%s" % r] = sum(math.hypot(re_, im_) / 2 ** P * math.exp(2 * math.pi * float(F(r)) * (abs(k) + abs(l)))
                                            for (k, l), (re_, im_) in co.items())
    print("  residual %.0fs" % (time.time() - t0), flush=True)
    return out


# ------------------------------------------------------------------------------------------- 4. certificate
def prog_values(prog, z):
    """Slot values of a lock_jet program at one real point z = (alpha, phi, I, Jt) (floats)."""
    vals = []
    for op in prog:
        t = op[0]
        if t == "const":
            v = complex(float(op[1]), float(op[2])) * (2 * math.pi) ** op[3]
        elif t == "action":
            v = z[2 + op[1]]
        elif t == "char":
            v = complex(math.cos(2 * math.pi * (op[1][0] * z[0] + op[1][1] * z[1])),
                        math.sin(2 * math.pi * (op[1][0] * z[0] + op[1][1] * z[1])))
        elif t == "add":
            v = vals[op[1]] + vals[op[2]]
        elif t == "mul":
            v = vals[op[1]] * vals[op[2]]
        elif t == "exp":
            v = __import__("cmath").exp(vals[op[1]])
        elif t == "inv":
            v = 1 / vals[op[1]]
        else:
            v = __import__("cmath").sqrt(vals[op[1]])
        vals.append(v)
    return vals


def sqrt_witness(poly_half, poly_zero, anchor, margin):
    """The one encoding of a `SqrtWitness` (Model/SqrtWitness.lean, branch inp-locksqrt): the polynomial W (as
    a real series: zero mode and half-lattice coefficients), the rational anchor s and margin d (0 ≤ d < s)."""
    return dict(poly=dict(zero=str(poly_zero), half=poly_half), anchor=str(anchor), margin=str(margin))


def classify_witnesses(J, Om, kappa):
    """Map every exp / inv / sqrt slot of the program to its witness function, by evaluating the program at a
    sample point (robust to the tree's exact layout)."""
    prog = J["prog"]
    z = (0.137, 0.291, 0.0147, 0.4)
    vals = prog_values(prog, z)
    Omf = float(Om)
    A = 4 * math.pi * (sum(float(c) * math.sin(2 * math.pi * (j + 1) * z[1]) for j, c in enumerate(CENTRE))
                       + math.sqrt(z[2] / (math.pi * Omf)) * math.sin(2 * math.pi * z[0]))
    s1, s2 = math.sqrt(z[2] / (math.pi * Omf)), math.sqrt(z[2] * Omf / math.pi)
    exp_map, inv_map, sqrt_map = [], [], []
    for i, op in enumerate(prog):
        if op[0] == "exp":
            v = vals[op[1]]
            exp_map.append("W+" if abs(v - 1j * A) < 1e-9 else "W-" if abs(v + 1j * A) < 1e-9 else "?%s" % v)
        elif op[0] == "inv":
            v = vals[op[1]]
            tag = ("pi" if abs(v - math.pi) < 1e-12 else "R1" if abs(v - s1) < 1e-12 else "R2" if abs(v - s2) < 1e-12
                   else "?%s" % v)
            inv_map.append(tag)
        elif op[0] == "sqrt":
            v = vals[i]
            sqrt_map.append((i, "S1" if abs(v - s1) < 1e-12 else "S2" if abs(v - s2) < 1e-12 else "?%s" % v))
    assert not any(str(x).startswith("?") for x in exp_map + inv_map + [t for _, t in sqrt_map]), \
        (exp_map, inv_map, sqrt_map)
    return exp_map, inv_map, sqrt_map


def mant(x, S, prec):
    return int(x) << (prec - S)


def real_series(co, S, prec):
    """CertRealPoly of a real function: zero mode and half-lattice complex coefficients (mantissas at prec)."""
    z = co.get((0, 0), (0, 0))[0]
    return dict(zero=mant(z, S, prec), half=[[list(k), [mant(r, S, prec), mant(i, S, prec)]] for k, (r, i) in half(co)])


def cplx_poly(co, S, prec):
    return [[list(k), [mant(r, S, prec), mant(i, S, prec)]] for k, (r, i) in sorted(co.items())]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--Ks", type=int, default=56)
    ap.add_argument("--Ls", type=int, default=12)
    ap.add_argument("--shape", default="diamond")
    ap.add_argument("--rho", default="1/140")
    ap.add_argument("--kappa", default="1")
    ap.add_argument("--prec", type=int, default=96)
    ap.add_argument("--S", type=int, default=0, help="data scale bits (default 3.33 * digits + 24)")
    ap.add_argument("--digits", type=int, default=20)
    ap.add_argument("--wdigits", type=int, default=0, help="witness truncation digits (default = digits)")
    ap.add_argument("--form", default="design")
    ap.add_argument("--lean")
    ap.add_argument("--cache")
    ap.add_argument("--pkg", help="a row of lock_v2.py scan output (JSON file): the package and its exact check")
    ap.add_argument("--err", default="9/100000000000000000000")
    a = ap.parse_args()
    t0 = time.time()
    rho, kappa = F(a.rho), F(a.kappa)
    S = a.S or math.ceil(3.33 * a.digits) + 24
    g = Grid()
    cache = a.cache or os.path.join(DATA, "lock_emit_grid_P%d.pkl" % P)
    if os.path.exists(cache):
        co = pickle.load(open(cache, "rb"))
    else:
        gf = grid_functions(g)
        co = {k: fourier(g, gf[k]) for k in ("U", "P", "J", "S1", "S2", "R1", "R2")}
        co["E"] = fourier(g, gf["Er"], gf["Ei"])
        co["W"] = fourier(g, gf["Wr"], gf["Wi"])
        pickle.dump(co, open(cache, "wb"))
    print("grid + FFT %.0fs" % (time.time() - t0), flush=True)
    tr = {k: truncate(co[k], a.Ks, a.Ls, a.shape, S) for k in ("U", "P", "J")}
    thr = 2 ** (P - S)
    wd = a.wdigits or a.digits
    keep = lambda c: {kk: v for kk, v in c.items() if max(abs(v[0]), abs(v[1])) >= 10 ** (-wd) * 2 ** P}
    wit = {k: truncate(keep(co[k]), 10 ** 6, 10 ** 6, "rect", S) for k in ("E", "W", "S1", "S2", "R1", "R2")}
    res = residual(g, tr, S, rho, kappa)
    print("residual", json.dumps(res), flush=True)
    # ---- program and witnesses
    ham = LH.lock_ham_scaled(kappa, OMEGA_R, CENTRE, a.form)
    J = LJ.jet(2, ham)
    exp_map, inv_map, sqrt_map = classify_witnesses(J, OMEGA_R, kappa)
    prec = a.prec
    reflect = lambda c: {(-k, -l): (r, -i) for (k, l), (r, i) in c.items()}     # exp(-2iV) = conj-reflect
    Wm = {"W+": wit["W"], "W-": reflect(wit["W"])}
    expWit = [dict(poly=cplx_poly(Wm[t], S, prec), pinHalvings=0, pinOrder=70) for t in exp_map]
    invWit = [[[[0, 0], [2 << prec, 0]]] if t == "pi" else cplx_poly(wit[t], S, prec) for t in inv_map]
    sqrtWit = []
    for slot, t in sqrt_map:
        c = wit[t]
        zero = F(c[(0, 0)][0], 2 ** S)
        dev = sum(math.hypot(r, i) * math.exp(2 * math.pi * float(rho) * (abs(kk[0]) + abs(kk[1])))
                  for kk, (r, i) in c.items() if kk != (0, 0)) / 2 ** S
        anchor = F(round(float(zero) * 10 ** 6), 10 ** 6)
        margin = F(math.ceil((dev + abs(float(zero - anchor))) * 1.5 * 10 ** 6), 10 ** 6)
        sqrtWit.append([slot, sqrt_witness(real_series(c, S, prec)["half"], mant(c[(0, 0)][0], S, prec), anchor, margin)])
    emb = dict(angleDeg=[0, 0], angle=[real_series(tr["U"], S, prec), dict(zero=0, half=[])], actionDeg=[0, 0],
               action=[real_series(tr["P"], S, prec), real_series(tr["J"], S, prec)])
    nhalf = {k: len(half(tr[k])) for k in tr}
    cert = dict(
        precision=prec, mantissas="integers m denoting m / 2^%d (CertFixed %d)" % (prec, prec),
        ham=dict(lean=LH.to_lean(ham), form=a.form, kappa=str(kappa), Omega=str(OMEGA_R),
                 cs=[str(c) for c in CENTRE], program_length=len(J["prog"]),
                 lockHamExpr_length=len(LJ.jet(2, LH.lock_ham_expr(OMEGA_R, CENTRE, a.form))["prog"]),
                 slots=dict(exp=LJ.census(J)["exp_slots"], inv=LJ.census(J)["inv_slots"], sqrt=[s for s, _ in sqrt_map])),
        params=package_params(a, rho, kappa),
        freqBox="lunarBox upper at N = 65 scaled by kappa (coordinate 1 = (kappa, 0) exactly)",
        emb=emb,
        wit=dict(charWit=[[[1, 0], dict(poly=cplx_poly(wit["E"], S, prec), pinHalvings=0, pinOrder=70)]],
                 expWit=expWit, invWit=invWit, sqrtWit=sqrtWit, exp_order=exp_map, inv_order=inv_map),
        cfgFull=dict(book=[]), cfgLow=dict(book=[]),
        stats=dict(support=dict(Ks=a.Ks, Ls=a.Ls, shape=a.shape), S=S, half_terms=nhalf,
                   witness_terms={k: len(v) for k, v in wit.items()}, residual=res,
                   seconds=round(time.time() - t0)),
        metadata=dict(generator="scripts/spin_orbit/lock_emit.py", version=GEN_VERSION,
                      git_hash=subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True,
                                              cwd=HERE).stdout.strip(),
                      date=datetime.date.today().isoformat(), hp_bits=P))
    with open(a.out, "w") as fh:
        json.dump(cert, fh, separators=(",", ":"), default=str)
    print("half terms", nhalf, "witness terms", cert["stats"]["witness_terms"], "wrote", a.out,
          "%.0fs" % (time.time() - t0), flush=True)
    if a.lean:
        write_sample_lean(a.lean, cert, ham)


def package_params(a, rho, kappa):
    """CertParams of the lock package (lock_v2.lock_package) with err and the exact v2 witness check."""
    if not a.pkg:
        return dict(rho=str(rho), kappa=str(kappa), note="no --pkg: package not attached")
    import lock_v2 as L2
    row = json.load(open(a.pkg))
    chk = L2.final_check(row, F(a.err))
    p = L2.lock_package(F(row["rho"]), F(row["kappa"]), F(str(row["sK"])), F(str(row["sB"])), F(str(row["sT"])),
                        F(str(row["M"])), mu=F(row["mu"]))
    p.update(err=F(a.err), disp=F(chk["disp"]), E0=F(0))
    out = {k: str(v) for k, v in p.items()}
    out.update(refined_claim=row["claims"], v2_check=chk, log10_threshold=row["log10_thr"],
               domain=dict(rhoH=row["rhoH"], r1=row["r1"]))
    return out


def write_sample_lean(path, cert, ham):
    """A small sample of the Lean rendering (the Hamiltonian and the first coefficients); not a module of KAM/."""
    e = cert["emb"]
    lines = ["-- LOCK-GEN part 2 sample (generated by scripts/spin_orbit/lock_emit.py; not part of KAM/).",
             "-- The certificate's `ham` (lock_ham.lock_ham_scaled, form %s):" % cert["ham"]["form"],
             "def lockSampleHam : KAM.Certificate.HamExpr 2 :="]
    cur = " "
    for tok in LH.to_lean(ham).split(" "):
        if len(cur) + len(tok) + 1 > 98:
            lines.append(cur)
            cur = "   "
        cur += " " + tok
    lines.append(cur)
    lines.append("-- first half-lattice coefficients of U (angle 0), mantissas / 2^%d:" % cert["precision"])
    for kk, (r, i) in e["angle"][0]["half"][:6]:
        lines.append("--   ([%d, %d], ⟨%d, %d⟩)" % (kk[0], kk[1], r, i))
    open(path, "w").write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
