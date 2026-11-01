#!/usr/bin/env python3
"""V2-FIXES item 5: structured bounds of `hamComm` and route B's threshold (docs/campaign/studies/V2-STRUCTURED-B.md).

Untrusted tooling, report only.  The checker fixes c_Th = 2 M1, c_DTh = 2 M2 (RunBWit.num, KAM/CertificateSharp/V2/
RouteBCore.lean); the theorem (RefHypB.comm, .lip) accepts any bounds of ||A O0 - O0 A|| and of its segment Lipschitz
constant, A = DX_H.  With S the Hessian of H in (theta, I) and O0 = [[0, -1], [1, 0]],

    A O0 - O0 A = [[S_II - S_tt, -(S_It + S_tI)], [-(S_It + S_tI), S_tt - S_II]],

so every entry is +-(S_{a'b'} -+ S_{ab}), a' the conjugate index of a.  The bounds here are the checker's own slot balls
(`Slp.balls`, the mirror toy_arith.slp_balls, the balls of `ballsAux_sound`) combined entrywise BEFORE taking magnitudes:
ball arithmetic on S and on the third derivatives, then the row sums the matrix norm reads.  They hold on the whole
domain D for the reason the checker's own sums do.  A direct sampling of D checks them from below and shows how much
any sharper rigorous method could still gain.

Each certificate is then run through the exact rational mirror of `routeBOk` (route_b_lean_mirror.py) in the form
`RunBWit.num` gives it (iso, y0 = M s_N, Theta = sigma_omega |box|), changing only c_Th and c_DTh.

Inputs (read only): the N = 65 domains of KAM/SpinOrbit/Data/{Upper,Lower}/Cert.lean and their claims; the LG00 L = 20
domain, claim and chart from the worktree KAM_LG00_DIR (default /home/scott/KAM-dev-worktrees/lg00-cert).

Usage: python3 -B -I scripts/apost_sharp/structured_b.py [--json OUT]
       (internally: --lg00-bounds OUT, run in a subprocess on the LG00 worktree's own modules)
"""
import json, math, os, re, subprocess, sys, tempfile, time
from fractions import Fraction as F

sys.dont_write_bytecode = True
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
LG00 = os.environ.get("KAM_LG00_DIR", "/home/scott/KAM-dev-worktrees/lg00-cert")
TP = 2 * math.pi
ZERO = ((F(0), F(0)), F(0))
SEED, SAMPLES = 20261101, 4000


# ------------------------------------------------------------------------------------------- the commutator
def comm_entry_sign(a, b, n):
    """(sigma, eps): the entry (a, b) of A O0 - O0 A is sigma (S_{a'b'} + eps S_{ab})."""
    same = (a < n) == (b < n)
    return (1, -1) if same else (-1, 1)


def check_comm_formula(n=2, trials=20):
    """The sign table against the matrices themselves, on random symmetric Hessians (and third-derivative slices)."""
    rng = np.random.default_rng(SEED)
    O0 = np.block([[np.zeros((n, n)), -np.eye(n)], [np.eye(n), np.zeros((n, n))]])
    for _ in range(trials):
        S = rng.normal(size=(2 * n, 2 * n)); S = S + S.T
        # X_H = (dH/dI, -dH/dtheta): A_ab = d_b X^a
        A = np.block([[S[n:, :n], S[n:, n:]], [-S[:n, :n], -S[:n, n:]]])
        C = A @ O0 - O0 @ A
        for a in range(2 * n):
            for b in range(2 * n):
                sg, eps = comm_entry_sign(a, b, n)
                ap, bp = (a + n) % (2 * n), (b + n) % (2 * n)
                assert abs(C[a, b] - sg * (S[ap, bp] + eps * S[a, b])) < 1e-12


def ball(bs, i):
    return bs[i] if i < len(bs) else ZERO


def mag(b):
    (re, im), r = b
    return abs(re) + abs(im) + r


def combine(x, y, eps):
    (a, b), r = x
    (c, d), t = y
    return ((a + eps * c, b + eps * d), r + t)


def entry_mag(bs, ip, i, eps):
    """Magnitude bound of value(ip) + eps value(i); identical slots cancel exactly."""
    if ip == i and eps == -1:
        return F(0)
    return mag(combine(ball(bs, ip), ball(bs, i), eps))


def bounds(n, J, bs):
    """The checker's four sums (hamClaimOk) and the structured c_Th, c_DTh, all exact rationals."""
    m = 2 * n
    g = lambda L, a, d: L[a] if a < len(L) else d
    d1 = lambda a: g(J["d1"], a, 0)
    d2 = lambda a, b: g(g(J["d2"], a, []), b, 0)
    d3 = lambda a, b, e: g(g(g(J["d3"], a, []), b, []), e, 0)
    sw = lambda a: (a + n) % m
    R = dict(dh=sum(mag(ball(bs, d1(a))) for a in range(m)),
             dx=max(sum(mag(ball(bs, d2(a, b))) for b in range(m)) for a in range(m)),
             d2x=max(sum(mag(ball(bs, d3(a, b, e))) for b in range(m) for e in range(m)) for a in range(m)),
             d2h=sum(mag(ball(bs, d2(a, b))) for a in range(m) for b in range(m)))
    eps = lambda a, b: comm_entry_sign(a, b, n)[1]
    R["cTh"] = max(sum(entry_mag(bs, d2(sw(a), sw(b)), d2(a, b), eps(a, b)) for b in range(m)) for a in range(m))
    R["cDTh"] = max(sum(entry_mag(bs, d3(sw(a), sw(b), e), d3(a, b, e), eps(a, b)) for b in range(m) for e in range(m))
                    for a in range(m))
    return R


def sampled(n, J, ops, rhoH, centre, radius, N=SAMPLES):
    """Sup over N points of D (random and boundary) of the row sum of the commutator and of the same row sum of its
    gradients: lower bounds of the best c_Th and of the structured c_DTh formula."""
    rng = np.random.default_rng(SEED)
    th = [rng.uniform(0, 1, N) + 1j * rhoH * rng.choice([-1.0, 1.0, 0.5, -0.5], N) * rng.uniform(.9, 1, N)
          for _ in range(n)]
    ac = [float(centre[j]) + float(radius[j]) * rng.uniform(.9, 1, N) * np.exp(1j * rng.uniform(0, TP, N))
          for j in range(n)]
    v = []
    for op in ops:
        t = op[0]
        if t == "C":
            v.append(np.full(N, (float(op[1]) + 1j * float(op[2])) * TP ** int(op[3]), complex))
        elif t == "A":
            v.append(ac[op[1]] + 0j)
        elif t == "X":
            v.append(np.exp(2j * math.pi * sum(k * th[j] for j, k in enumerate(op[1]))))
        elif t == "+":
            v.append(v[op[1]] + v[op[2]])
        elif t == "*":
            v.append(v[op[1]] * v[op[2]])
        elif t == "I":
            v.append(1 / v[op[1]])
        elif t == "S":
            v.append(np.sqrt(v[op[1]]))
        elif t == "E":
            v.append(np.exp(v[op[1]]))
        else:
            raise ValueError(op)
    m = 2 * n
    sw = lambda a: (a + n) % m
    eps = lambda a, b: comm_entry_sign(a, b, n)[1]
    rows = [sum(np.abs(v[J["d2"][sw(a)][sw(b)]] + eps(a, b) * v[J["d2"][a][b]]) for b in range(m)) for a in range(m)]
    rows3 = [sum(np.abs(v[J["d3"][sw(a)][sw(b)][e]] + eps(a, b) * v[J["d3"][a][b][e]]) for b in range(m) for e in range(m))
             for a in range(m)]
    hess = [sum(np.abs(v[J["d2"][a][b]]) for b in range(m)) for a in range(m)]
    return float(np.max(rows)), float(np.max(rows3)), float(np.max(hess))


# ------------------------------------------------------------------------------------------- the data
def lean_rat(s):
    m = re.fullmatch(r"\s*\(?\s*(-?\d+)\s*(?:/\s*(\d+))?\s*(?::\s*ℚ)?\s*\)?\s*", s)
    return F(int(m.group(1)), int(m.group(2) or 1))


def lunar_inputs(which):
    """The N = 65 torus: claim and domain literals of the landed Lean data, parameters of `lunarR2`."""
    src = open(os.path.join(ROOT, "KAM/SpinOrbit/Data/%s/Cert.lean" % which.capitalize()), encoding="utf-8").read()
    wit = open(os.path.join(ROOT, "KAM/SpinOrbit/Data/%s/Witness.lean" % which.capitalize()), encoding="utf-8").read()
    wh = re.search(r"def weightH : CertWeight :=\s*⟨\(([^)]*)\),\s*\(([^)]*)\)", src)
    ce = re.search(r"centre := \[\(([^)]*)\), \(([^)]*)\)\]", src)
    ra = re.search(r"radius := \[\(([^)]*)\), \(([^)]*)\)\]", src)
    claim = {k: lean_rat(re.search(r"\b%s := ([^\n]*)" % k, wit).group(1))
             for k in ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt", "bT")}
    return dict(rhoH=lean_rat(wh.group(1)), w=lean_rat(wh.group(2)), centre=[lean_rat(ce.group(i)) for i in (1, 2)],
                radius=[lean_rat(ra.group(i)) for i in (1, 2)], claim=claim)


def lunar_bounds(which):
    sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
    import adv_jet, toy_arith as TA
    import sofx_lunar as L
    I = lunar_inputs(which)
    epsA = {m: L.MD.EPS * L.MD.A_EXACT[m] for m in L.MD.M_MODES}
    J = adv_jet.jet(2, adv_jet.so_rot_ham_expr_scaled(F(2), epsA))
    J["prog"] = [tuple(op) if op[0] != "char" else ("char", tuple(op[1])) for op in J["prog"]]
    ops = L.toy_ops(J["prog"])
    t0 = time.time()
    bs = TA.slp_balls(2, ops, I["w"], I["centre"], I["radius"], 30)
    t1 = time.time()
    R = bounds(2, J, bs)
    t2 = time.time()
    s = sampled(2, J, ops, float(I["rhoH"]), I["centre"], I["radius"])
    return dict(sums={k: R[k] for k in R}, sampled=s, claim=I["claim"], slots=len(ops),
                seconds=dict(balls=t1 - t0, sums=t2 - t1))


def lg00_child(out):
    """Runs on the LG00 worktree's own modules (sqrt primitive included); nothing is written there."""
    for p in (os.path.join(LG00, "scripts", "sjs", "lg00"), os.path.join(LG00, "scripts", "spin_orbit")):
        sys.path.insert(0, p)
    import pickle
    import adv_jet, toy_arith as TA
    import lg00_chart as CH
    import lg00_gen as G
    d3 = open(os.path.join(LG00, "KAM/LG00Cert/Data/DCoeffs.lean"), encoding="utf-8").read()
    dm = re.search(r"def lgD3 : ℚ :=\s*\(\(\((\d+)\) : ℤ\) : ℚ\)\s*/\s*\(\(\((\d+)\) : ℕ\) : ℚ\)", d3)
    w = F(int(dm.group(1)), int(dm.group(2)))
    src = open(os.path.join(LG00, "KAM/LG00Cert/Data/Cert.lean"), encoding="utf-8").read()
    rhoH = lean_rat(re.search(r"def lg00WH : CertWeight := ⟨\(([^)]*)\)", src).group(1))
    ce = re.search(r"def lg00Centre : List ℚ := \[(.*?), (\(.*?\))\]", src)
    ra = re.search(r"def lg00Radius : List ℚ := \[(.*?), (\(.*?\))\]", src)
    centre, radius = [lean_rat(ce.group(i)) for i in (1, 2)], [lean_rat(ra.group(i)) for i in (1, 2)]
    rep = json.load(open(os.path.join(LG00, "scripts/sjs/lg00/results/lg00_dryrun_sqrt_L20.json")))
    pkl = os.environ.get("KAM_LG00_PKL", "/home/scott/KAM-dev-worktrees/lg00-prep/scripts/sjs/lg00/results/"
                         "lg00_hptorus_sqrt_N512h.pkl")
    p = pickle.load(open(pkl, "rb"))
    ch = CH.Chart(F(p["kappa"]), F(p["ell"]), [F(x) for x in p["s"]], p["K"], form=p.get("form", "taylor"))
    J = adv_jet.jet(2, ch.hamexpr())
    J["prog"] = [tuple(o) if o[0] != "char" else ("char", tuple(o[1])) for o in J["prog"]]
    ops = G.toy_ops(J["prog"])
    t0 = time.time()
    bs = TA.slp_balls(2, ops, w, centre, radius, 30)
    t1 = time.time()
    R = bounds(2, J, bs)
    t2 = time.time()
    s = sampled(2, J, ops, float(rhoH), centre, radius)
    box = [(str(c), str(r)) for c, r in G.freq_box(F(160000) / F(rep["params"]["s"]))]
    json.dump(dict(sums={k: str(v) for k, v in R.items()}, sampled=s, claim=rep["claim"], params=rep["params"], box=box,
                   slots=len(ops), seconds=dict(balls=t1 - t0, sums=t2 - t1), pkl=pkl), open(out, "w"))


def lg00_bounds():
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, "lg00.json")
        env = dict(os.environ, LG00_PB="128")
        r = subprocess.run([sys.executable, "-B", "-I", os.path.abspath(__file__), "--lg00-bounds", out], env=env,
                           capture_output=True, text=True)
        if r.returncode:
            raise RuntimeError(r.stderr[-1500:])
        d = json.load(open(out))
    d["sums"] = {k: F(v) for k, v in d["sums"].items()}
    d["claim"] = {k: F(v) for k, v in d["claim"].items()}
    d["box"] = [(F(a), F(b)) for a, b in d["box"]]
    return d


# ------------------------------------------------------------------------------------------- route B
def setup_mirror():
    sys.path.insert(0, HERE)
    import route_b_lean_mirror as RB
    import thresholds_v2 as T2
    memo, c_freq = {}, T2.sd.c_freq                         # the frequency sums are the slow step: once per bite

    def cached(om, gam, tau, d, n=2, N=None):
        key = (tuple(om), gam, tau, d, n, N)
        if key not in memo:
            memo[key] = c_freq(om, gam, tau, d, n=n, N=N)
        return memo[key]
    T2.sd.c_freq = cached
    return RB, T2


def float_constants(N):
    """The constants of `stepConstsB` are computed exactly once per stage; the bisection then runs in double precision
    (thresholds are reported to three decimals)."""
    exact, cache = N.k, {}

    def k(s):
        s = min(s, N.kp)
        if s not in cache:
            cache[s] = {a: float(v) for a, v in exact(s).items()}
        return cache[s]
    N.k = k


def run_inputs(pkg, sites, kp, RB, T2, theta=F(1, 16), ts=F(1, 10)):
    """`NumB`, `InitB`, caps of `RunBWit.num` at the claim R: free caps +5 %, least Fits weights, iso."""
    R, p = pkg["R"], pkg["p"]
    mu = p["mu"]
    D = dict(n=2, tau=1, kappa=1, rho=p["rho"], rhoinf=p["rhoInf"], gamma=p["gamma"], gbar=p["gbar"], mu=mu, nu=p["nu"],
             M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"], M0=R["dx"], M1=R["dx"], M2=R["d2x"], Mh1=R["dh"], Mh2=R["d2h"],
             sLt=R["bL"] + mu, sN=R["bN"] + mu, sNt=R["bNt"] + mu, Tsup=R["bT"], cTh=2 * R["dx"],
             Theta_omega=T2.Fr(float(p["som"] * pkg["boxUp"]), 15), omega_star=pkg["omega"])
    Dv = T2.with_caps(D, F(1, 20))
    st, ct = T2.c_stages(Dv, sites, kp)
    N, I, sig, _ = RB.from_design(D, st, ct, kp, theta)
    N.iso = True
    N.Θ = D["Theta_omega"]
    N.Mh2 = D["Mh2"]
    N.y0 = p["M"] * N.sN
    N.ts = ts
    pb = RB.pbar(N, I)
    N.lam0, N.ePer0 = I["iNt"] / pb, 1 / pb
    N.lamW0 = 1 / pb
    sig["ν"] = p["nu"]
    float_constants(N)
    return N, I, sig


def ok_at(N, I, sig, Xs, RB):
    try:
        x = N.xS(Xs, N.kp)
        N.bF = max(max(N.Bloc(s) * x[s] for s in range(N.kp + 1)), F(1, 10 ** 30))
        return RB.routeBOk(N, RB.capB(N, sig["σT"], sig["μ"], sig["ν"]), RB.initB(I, sig["σK"], sig["σB"], sig["μ"]),
                           sig["μ"] / 2, F(Xs))
    except OverflowError:                                  # double precision: far above any threshold
        return ["overflow"]


def threshold(N, I, sig, RB, iters=36):
    lo, hi = -60.0, 20.0
    for _ in range(iters):
        mid = (lo + hi) / 2
        if ok_at(N, I, sig, F(10 ** mid).limit_denominator(10 ** 60), RB):
            hi = mid
        else:
            lo = mid
    return lo


def freq_sum(N, x):
    kp = N.kp
    return (sum(N.k(s)["sCnu"] * N.γb * RB_ipow(N.δ(s), N.τ + 1) * x[s] for s in range(kp))
            + N.k(kp)["sCnu"] * N.γb * RB_ipow(N.δ(kp), N.τ + 1) * x[kp] / (1 - N.ybar))


def RB_ipow(x, e):
    return F(x) ** int(e)


def evaluate(pkg, sites, cases, RB, T2, kp=5, theta=F(1, 16), ts=F(1, 10)):
    out = []
    p = pkg["p"]
    for name, cTh, cDTh, y0 in cases:
        N, I, sig = run_inputs(pkg, sites, kp, RB, T2, theta, ts)
        N.cTh, N.cDTh = cTh, cDTh
        if y0 is not None:
            N.y0 = y0 * N.sN
        t0 = time.time()
        lx = threshold(N, I, sig, RB)
        Xs = F(10 ** lx).limit_denominator(10 ** 60)
        c1 = RB.c1B(N, I, Xs)
        le = RB.log10(p["gamma"] ** 4 * RB.ipow(N.ρ, 4 * N.τ) / c1)
        x = N.xS(Xs, N.kp)
        above = ok_at(N, I, sig, F(10 ** (lx + 0.02)).limit_denominator(10 ** 60), RB)
        e = p["gamma"] ** 4 * RB.ipow(N.ρ, 4 * N.τ) / c1
        c2 = RB.c2B(N, I, Xs)
        pref = RB.ipow(N.ρ, 2 * N.τ) * max(I["iLt"], RB.pN(N, I) * N.γb * RB.ipow(N.δ0(), N.τ)) / (
            Xs * RB.ipow(N.δ0(), 2 * N.τ + 1))
        c3 = pref * freq_sum(N, x)
        disp = max(c2, c3) * e / (p["gamma"] ** 2 * p["rho"] ** 2)
        k0 = N.k(0)
        t = cTh * N.sNt * N.sN + N.ts
        out.append(dict(case=name, cTh=float(cTh), cDTh=float(cDTh), t=float(t), log10_Xs=lx, log10_e=le, disp=float(disp),
                        binding=above, Q0=float(k0["sQ"]), kp=kp, seconds=round(time.time() - t0, 1)))
        print("    [%s %s: %.1fs]" % (name, sites, time.time() - t0), flush=True)
    return out


def lunar_pkg(which, B):
    sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
    import v2_r2 as VR
    import v2_q as VQ
    p = VR.package(65)
    p = dict(p, som=F(2))
    box = VR.box_of(p, which)
    om = (float(p["kappa"]) * VR.nu_minus_one(65, which), float(p["kappa"]))
    return dict(p=p, R=B["claim"], box=box, boxUp=VQ.boxNormUp(box), omega=om, tag="lunar N=65 %s" % which, VR=VR)


def lg00_pkg(B):
    sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
    import v2_q as VQ
    q = {k: F(v) for k, v in B["params"].items()}
    p = dict(q, tau=1, kappa=F(160000))
    box = B["box"]
    return dict(p=p, R=B["claim"], box=box, boxUp=VQ.boxNormUp(box), omega=(float(box[0][0]), float(box[1][0])),
                tag="LG00 L=20")


def tuned(pkg, sites, c0, d0, cS, dS, RB, T2):
    """The free numbers of the run at each (c_Th, c_DTh): a small grid over ts and kp, so a gain cannot be an artefact
    of the fixed defaults; thresholds only."""
    best = {}
    for name, cTh, cDTh in (("checker", c0, d0), ("structured", cS, dS)):
        top = (-1e9, None)
        for kp in (3, 4, 5):
            for ts in (F(1, 10), F(1), F(10), F(100)):
                for theta in (F(1, 16), F(1, 8)):
                    N, I, sig = run_inputs(pkg, sites, kp, RB, T2, theta, ts)
                    N.cTh, N.cDTh = cTh, cDTh
                    lx = threshold(N, I, sig, RB, iters=26)
                    Xs = F(10 ** lx).limit_denominator(10 ** 60)
                    le = RB.log10(pkg["p"]["gamma"] ** 4 * RB.ipow(N.ρ, 4 * N.τ) / RB.c1B(N, I, Xs))
                    if le > top[0]:
                        top = (le, dict(kp=kp, ts=str(ts), theta=str(theta)))
        best[name] = dict(log10_e=top[0], at=top[1])
    return best


def route_a(pkg, sites, kp=3, th=F(1, 8), J=20):
    """Route A refined at the same claim (v2_r2.max_Xs): log10 of the threshold, as v2_r2.evaluate reports it."""
    import v2_r2 as VR
    p = pkg["p"]
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    Xs = VR.max_Xs("refined", p, pkg["box"], kp, th, J, pkg["R"], sites)
    return VR.lg(Xs * p["gamma"] ** 4 * d0 ** 4)


def classical_sites(p, kp, J=20):
    import v2_q as VQ
    d0 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    out = {}
    for s in range(kp):
        d = F(1, 2) ** s * d0
        r = min(p["rho"] - 6 * d0 * (1 - F(1, 2) ** s), F(1))
        out[("d", s)] = VQ.classical_c(2, 1, J, d)
        out[("b", s)] = VQ.classical_c(2, 1, J, r)
    return out


def main():
    check_comm_formula()
    print("commutator sign table: checked against the matrices")
    RB, T2 = setup_mirror()
    res = dict(cases={})
    data = [("lower", lunar_bounds("lower")), ("upper", lunar_bounds("upper")), ("lg00", lg00_bounds())]
    for tag, B in data:
        S = B["sums"]
        print("\n== %s: %d slots; balls %.2fs, sums %.3fs" % (tag, B["slots"], B["seconds"]["balls"], B["seconds"]["sums"]), flush=True)
        chk = {k: (float(S[k]), float(B["claim"][k])) for k in ("dh", "dx", "d2x", "d2h")}
        print("checker sums vs landed claim:", {k: "%.6g <= %.6g" % v for k, v in chk.items()})
        assert all(S[k] <= B["claim"][k] for k in chk), "the reconstructed sums exceed the landed claim"
        pkg = lg00_pkg(B) if tag == "lg00" else lunar_pkg(tag, B)
        R = pkg["R"]
        cS, dS = S["cTh"], S["cDTh"]
        c0, d0 = 2 * R["dx"], 2 * R["d2x"]
        sc, sd_ = F(B["sampled"][0]).limit_denominator(10 ** 9), F(B["sampled"][1]).limit_denominator(10 ** 9)
        print("cTh: checker 2 M1 = %.6g, structured = %.6g, sampled sup = %.6g (factor %.3f; tightness %.3f)" % (
            float(c0), float(cS), float(sc), float(c0 / cS), float(sc / cS)))
        print("cDTh: checker 2 M2 = %.6g, structured = %.6g, sampled sup = %.6g (factor %.3f; tightness %.3f)" % (
            float(d0), float(dS), float(sd_), float(d0 / dS), float(sd_ / dS)))
        print("evaluator check: sampled Hessian row sum %.6g <= checker dx sum %.6g" % (B["sampled"][2], float(S["dx"])))
        assert sc <= cS and sd_ <= dS and B["sampled"][2] <= S["dx"], "a sampled value above a claimed bound"
        cases = [("checker 2M1, 2M2", c0, d0, None), ("structured cTh only", cS, d0, None),
                 ("structured cDTh only", c0, dS, None), ("structured both", cS, dS, None),
                 ("sampled both (not rigorous)", sc, sd_, None),
                 ("cTh = cDTh = 0 (limit)", F(0), F(0), None)]
        if pkg["R"]["dh"] < pkg["p"]["M"]:
            cases += [("checker, y0 = dh sN (improvement 2)", c0, d0, R["dh"]),
                      ("structured, y0 = dh sN (improvement 2)", cS, dS, R["dh"])]
        res["cases"][tag] = dict(bounds={k: float(v) for k, v in S.items()}, sampled=B["sampled"], claim={k: float(v) for k, v in R.items()},
                                 seconds=B["seconds"], slots=B["slots"], route_b={})
        for sites in ("classical", "freq"):
            rows = evaluate(pkg, sites, cases, RB, T2)
            res["cases"][tag]["route_b"][sites] = rows
            print("-- route B, %s sites, kp = 5" % sites)
            base = rows[0]["log10_e"]
            for r in rows:
                print("  %-40s cTh %9.5g cDTh %9.5g t %9.5g  log10 e* %8.3f (%+.3f)  disp %.3g  binding %s" % (
                    r["case"], r["cTh"], r["cDTh"], r["t"], r["log10_e"], r["log10_e"] - base, r["disp"],
                    ", ".join(r["binding"][:6])))
            tu = tuned(pkg, sites, c0, d0, cS, dS, RB, T2)
            res["cases"][tag]["route_b"][sites + "_tuned"] = tu
            print("-- tuned (kp, ts, theta grid): checker %.3f %s; structured %.3f %s; gain %+.3f" % (
                tu["checker"]["log10_e"], tu["checker"]["at"], tu["structured"]["log10_e"], tu["structured"]["at"],
                tu["structured"]["log10_e"] - tu["checker"]["log10_e"]), flush=True)
        st = classical_sites(pkg["p"], 3)
        res["cases"][tag]["route_a_classical"] = route_a(pkg, st)
        print("-- route A refined, classical sites, kp = 3: log10 e* %.3f" % res["cases"][tag]["route_a_classical"])
        if tag != "lg00":
            sf = pkg["VR"].site_constants(pkg["p"], tag, 3)
            res["cases"][tag]["route_a_freq"] = route_a(pkg, sf)
            print("-- route A refined, frequency sites, kp = 3: log10 e* %.3f" % res["cases"][tag]["route_a_freq"])
    if "--json" in sys.argv:
        json.dump(res, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=str)
    return 0


if __name__ == "__main__":
    if "--lg00-bounds" in sys.argv:
        lg00_child(sys.argv[sys.argv.index("--lg00-bounds") + 1])
    else:
        sys.exit(main())
