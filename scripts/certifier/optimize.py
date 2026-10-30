#!/usr/bin/env python3
"""SHARP-CERTSIDE: free-parameter optimizer of a KAM certificate (lunar spin-orbit instance).

Untrusted design tooling (numbers for docs/campaign/design/CERTIFIER-SHARPNESS.md, not a certificate).

Given a Hamiltonian and a candidate torus (here: the two lunar candidates of SO-GEN2, through
scripts/certifier/lunar_oracle.py), choose the free parameters of the certificate
    frame A in GL(2, Z) (a unimodular symplectic linear change of variables, relative to the rotated frame),
    action scaling lam, time scaling c, strip width rho, rho_inf, margin mu, ray scalar s (and nu, sigma_omega),
to maximize  threshold / invariance error  (equivalently log10 T - log10 e) under a theorem mirror:
    v0      the sealed iso theorem KAM.Iso.Apost.g1_explicit (one size m; scripts/apost_sharp/thresholds.py
            current_iso, the transcription used by scripts/spin_orbit/exact_constants.py);
    v1      the sharp iso theorem (Russmann data, separate M, sK, sB, sT; thresholds.sharp(iso=True));
    v1L2    v1 with the frequency-specific small-divisor constant emulated: c_R -> c_R,eff = Gamma_spec(delta0)
            gamma delta0 (Gamma_spec = (2 pi)^-1 2^{n/2} S(omega*, 2 delta0)^{1/2}, scripts/certifier/smalldiv.py);
            an ESTIMATE of lever L2 of SHARP-PLUS, not a mirror of a theorem;
    v2      the mirror of SHARP-PLUS, when it exists: --v2 PATH loads a module with
            `log10_threshold(pkg) -> float` (pkg: the dict built by `package()` below).
Majorant regimes (lunar_oracle.REGIMES): 'l1' (current checker), 'corner' (vertex bound), 'sup' (sampled sup
x 1.01, what grid + interpolation enclosures reach).  The Diophantine constant is the proved one (1/42 in the
rotated frame, 1/21 in the theta frame, other frames by transfer) in regime 'l1' and the certified infimum
(smalldiv.py) otherwise.

Usage:
  python3 -I scripts/certifier/optimize.py --cache DIR reproduce        # P0, R1, emitted R1 under v0 and v1
  python3 -I scripts/certifier/optimize.py --cache DIR search [--which lower] [--quick] [--json OUT] [--v2 PATH]
"""
import os, sys, math, json, time, argparse, itertools, importlib.util
import numpy as np
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "apost_sharp"))
import thresholds as TH                                      # noqa: E402  (read-only use)
from lunar_oracle import LunarOracle, REGIMES, dioph_gamma   # noqa: E402

CR_R = float(TH.cohConstR_lean(2, 1))
TP = 2 * math.pi
ROT = ((1, 0), (0, 1))
THETA = ((1, 1), (0, 1))


# ------------------------------------------------------------------------------------------ theorems
def log10_threshold(theorem, pkg, v2mod=None):
    g = pkg["gamma"]
    base = dict(n=2, tau=1, mu=pkg["mu"], rho=pkg["rho"], rhoinf=pkg["rhoinf"], gbar=g)
    if theorem == "v0":
        k = TH.current_iso(M=pkg["M"], sK=pkg["sK"], sB=pkg["sB"], sT=pkg["sT"], nu=pkg["nu"], **base)
    elif theorem in ("v1", "v1L2", "v1fixed"):
        cR = CR_R if theorem != "v1L2" else pkg["cR_eff"]
        k = TH.sharp(kappa=1, cR=cR, M=pkg["M"], sK=pkg["sK"], sB=pkg["sB"], sT=pkg["sT"], nu=pkg["nu"],
                     iso=(theorem != "v1fixed"), **base)
    elif theorem == "v2":
        return v2mod.log10_threshold(pkg), "v2"
    else:
        raise ValueError(theorem)
    C1n = max(k["gbar"] ** 4, k["c_star"] / k["delta0"] ** int(2 * k["a"]))
    return 4 * math.log10(g) - math.log10(C1n), k["active"]


# ------------------------------------------------------------------------------------------ S(omega, delta)
def S_omega(w, delta, nl=60):
    """sum_{k != 0} e^{-2 pi delta |k|_1} / |k.w|^2 for w in R^2 (finite rows |k1| <= K, the l-sum exact within
    nl of the near-resonant l and bounded beyond; tail beyond K negligible: e^{-2 pi delta K} <= e^-40)."""
    K = int(math.ceil(40 / (TP * delta)))
    k1 = np.arange(-K, K + 1)[:, None]
    l0 = np.floor(-k1 * w[0] / w[1])
    off = np.arange(-nl, nl + 2)[None, :]
    l = l0 + off
    d = np.abs(k1 * w[0] + l * w[1])
    wt = np.exp(-TP * delta * (np.abs(k1) + np.abs(l)))
    mask = ~((k1 == 0) & (l == 0))
    s = float(np.sum(np.where(mask, wt / np.where(d > 0, d, 1) ** 2, 0.0)))
    s += float(np.sum(2 * np.exp(-TP * delta * np.abs(k1[:, 0])))) / (nl * abs(w[1]) ** 2)
    return s


_GS = {}


def gamma_spec(w, delta):
    """(2 pi)^-1 2^{n/2} S(w, 2 delta)^{1/2}; homogeneous of degree -1 in w (cached on the direction)."""
    w = np.asarray(w, float)
    t = float(np.abs(w).max())
    key = (round(w[0] / t, 14), round(w[1] / t, 14), round(delta, 14))
    if key not in _GS:
        _GS[key] = (2 * math.pi) ** -1 * 2.0 * math.sqrt(S_omega(w / t, 2 * delta))
    return _GS[key] / t


# ------------------------------------------------------------------------------------------ packages
_FG = {}


def frame_gamma(A, om, regime):
    """Diophantine constant of A om' (tau = 1): proved (regime 'l1') or certified infimum (cached)."""
    A = tuple(map(tuple, A))
    key = (A, regime == "l1", tuple(np.round(om, 15)))
    if key not in _FG:
        _FG[key] = _frame_gamma(A, om, regime)
    return _FG[key]


def _frame_gamma(A, om, regime):
    if regime == "l1":
        if A == ROT:
            return 1 / 42
        if A == THETA:
            return 1 / 21
        # transfer from the theta frame (gamma = 1/21) along k -> A_theta^{-T} A^T k: |T k|_1 <= C |k|_1
        At = np.array(THETA, float); Am = np.array(A, float)
        Tm = np.linalg.inv(At).T @ Am.T
        C = np.abs(Tm).sum(axis=0).max()
        return (1 / 21) / C
    return dioph_gamma(A, om)


def package(O, norms, regime, A, lam, c, rho, mu, s1=1e-6, rhoinf_frac=1e-3, sup_margin=1.01, theorem=None):
    r = norms[regime]
    fac = sup_margin if regime == "sup" else 1.0
    M, parts = O.H_majorant(A, lam, c, rho, mu, r, trig="disc" if regime == "l1" else "cosh")
    s = 1 + s1
    om = np.array(A, float) @ O.om
    gam0 = frame_gamma(A, O.om, regime)
    gamma = c * gam0 / s
    nrm = c * np.abs(om).max() / s
    pkg = dict(A=[list(a) for a in A], lam=lam, c=c, rho=rho, rhoinf=rho * rhoinf_frac, mu=mu, s=s,
               nu=s1 * nrm * (1 - 1e-9), sigma_omega=2.0, gamma=gamma,
               M=M * fac, sK=r["sK"] * fac + mu, sB=r["sB"] * fac + mu, sT=norms["tinv"] / c * (1.0005 if regime != "l1" else 1.0) + mu,
               e=c * r["eta"] * fac, regime=regime, Hparts={k: float(v) for k, v in parts.items()})
    if theorem == "v1L2":
        d0 = (rho - pkg["rhoinf"]) / 6
        pkg["cR_eff"] = gamma_spec(c * om / s, d0) * gamma * d0
    return pkg


def evaluate(pkg, theorem, v2mod=None):
    T, br = log10_threshold(theorem, pkg, v2mod)
    return T, math.log10(pkg["e"]), T - math.log10(pkg["e"]), br


# ------------------------------------------------------------------------------------------ frames
def frames(maxe=2):
    """GL(2, Z) matrices with entries in [-maxe, maxe] modulo signed row permutations (left action: a signed
    permutation of the coordinates Q~ is symplectic with the matching action change and preserves every norm)."""
    seen = set(); out = []
    rng = range(-maxe, maxe + 1)
    for a, b, cc, d in itertools.product(rng, rng, rng, rng):
        if abs(a * d - b * cc) != 1:
            continue
        rows = [(a, b), (cc, d)]
        variants = []
        for perm in ((0, 1), (1, 0)):
            for s0 in (1, -1):
                for s1 in (1, -1):
                    r0 = tuple(s0 * x for x in rows[perm[0]]); r1 = tuple(s1 * x for x in rows[perm[1]])
                    variants.append((r0, r1))
        key = max(variants)
        if key in seen:
            continue
        seen.add(key)
        out.append(key)
    # rotated and theta first
    out.sort(key=lambda A: (A != ROT and A != ((0, 1), (1, 0)), A != THETA, sum(abs(x) for r in A for x in r)))
    return out


# ------------------------------------------------------------------------------------------ search
def search(O, theorems, regimes, frame_list, lams, rhos, mus, cs, s1s=(1e-6,), v2mod=None, log=print):
    best = {(t, r): None for t in theorems for r in regimes}
    for A in frame_list:
        for lam in lams:
            for rho in rhos:
                nm = O.norms(np.array(A, float), lam, rho, regimes=regimes)
                for mu in mus:
                    for c, s1 in itertools.product(cs, s1s):
                        for r in regimes:
                            for t in theorems:
                                pkg = package(O, nm, r, A, lam, c, rho, mu, s1=s1, theorem=t)
                                try:
                                    T, le, ratio, br = evaluate(pkg, t, v2mod)
                                except (ValueError, ZeroDivisionError, OverflowError):
                                    continue
                                b = best[(t, r)]
                                if b is None or ratio > b["ratio"]:
                                    best[(t, r)] = dict(pkg, T=T, log10e=le, ratio=ratio, branch=br, theorem=t)
        log("  frame %s done; best so far: %s" % (A, {"%s/%s" % k: (None if v is None else round(v["ratio"], 2))
                                                        for k, v in best.items()}))
    return best


def fmt(b):
    return ("A=%s lam=%.2f c=%.3f rho=%.5f mu=%.5f s-1=%.0e | M %.3f sK %.3f sB %.3f sT %.3f gamma %.5f | "
            "log10 T %.2f (%s)  log10 e %.2f  T/e %+.2f orders" % (
                b["A"], b["lam"], b["c"], b["rho"], b["mu"], b["s"] - 1, b["M"], b["sK"], b["sB"], b["sT"], b["gamma"],
                b["T"], b["branch"], b["log10e"], b["ratio"]))


# ------------------------------------------------------------------------------------------ reproduction
def reproduce(O):
    """The packages of CONSTANTS-STUDY and of the emitted certificate, re-evaluated (exact mirrors where the
    package fixes the norms; the oracle's l1 norms otherwise)."""
    out = {}
    lg = TH.lg
    # P0 pilot: theta frame, m = 4, rho = 1/200, rho_inf = 1/400, mu = 1/1000, gamma = gbar = 1/42, nu = 1/4
    k = TH.current_iso(n=2, tau=1, M=F(4), sK=F(4), sB=F(4), sT=F(4), mu=F(1, 1000), nu=F(1, 4), rho=F(1, 200),
                       rhoinf=F(1, 400), gbar=F(1, 42))
    out["P0 pilot (v0)"] = lg(TH.threshold(k, F(1, 42)))
    # R1 of CONSTANTS-STUDY: m = 39/20, c = 7/4, gamma = c/(42 s)
    s = 1 + F(1, 10 ** 6); c = F(7, 4); g = c / (42 * s)
    k = TH.current_iso(n=2, tau=1, M=F(39, 20), sK=F(39, 20), sB=F(39, 20), sT=F(39, 20), mu=F(1, 160),
                       nu=F(1, 10 ** 6), rho=F(1, 70), rhoinf=F(1, 70000), gbar=g)
    out["R1 CONSTANTS-STUDY (v0)"] = lg(TH.threshold(k, g))
    # emitted lower_rot.json: m = 1987/1000, c = 237/125
    c = F(237, 125); g = F(316000, 7000007)
    k = TH.current_iso(n=2, tau=1, M=F(1987, 1000), sK=F(1987, 1000), sB=F(1987, 1000), sT=F(1987, 1000),
                       mu=F(1, 160), nu=F(1, 10 ** 6), rho=F(1, 70), rhoinf=F(1, 70000), gbar=g)
    out["R1 emitted lower_rot.json (v0)"] = lg(TH.threshold(k, g))
    # the same packages through the oracle (l1 regime) and the sharp mirror
    for name, A, rho, mu, c, lam in (("R1 oracle", ROT, 1 / 70, 1 / 160, 237 / 125, 1.0),
                                    ("P4 theta oracle", THETA, 1 / 160, 1 / 160, 1.25, 1.0)):
        nm = O.norms(np.array(A, float), lam, rho, mu)
        for t in ("v0", "v1", "v1fixed"):
            pkg = package(O, nm, "l1", A, lam, c, rho, mu, theorem=t)
            T, le, ratio, br = evaluate(pkg, t)
            out["%s (%s)" % (name, t)] = dict(T=T, log10e=le, ratio=ratio, branch=br, M=pkg["M"], sK=pkg["sK"],
                                              sB=pkg["sB"], sT=pkg["sT"], gamma=pkg["gamma"])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["reproduce", "search"])
    ap.add_argument("--cache", default=None)
    ap.add_argument("--which", default="lower")
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", default=None)
    ap.add_argument("--v2", default=None)
    ap.add_argument("--theorems", default="v0,v1,v1L2")
    ap.add_argument("--regimes", default="l1,corner,sup")
    ap.add_argument("--maxe", type=int, default=2)
    a = ap.parse_args()
    v2mod = None
    theorems = a.theorems.split(",")
    if a.v2:
        spec = importlib.util.spec_from_file_location("v2mirror", a.v2)
        v2mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(v2mod)
        theorems.append("v2")
    O = LunarOracle(a.which, a.cache)
    if a.mode == "reproduce":
        res = reproduce(O)
        for k, v in res.items():
            print("%-36s %s" % (k, v if not isinstance(v, dict) else
                                "log10 T %.2f (%s) log10 e %.2f T/e %+.2f | M %.4f sK %.4f sB %.4f sT %.4f gamma %.5f" % (
                                    v["T"], v["branch"], v["log10e"], v["ratio"], v["M"], v["sK"], v["sB"], v["sT"],
                                    v["gamma"])))
        if a.json:
            json.dump(res, open(a.json, "w"), indent=1, default=float)
        return
    regimes = a.regimes.split(",")
    t0 = time.time()
    if a.quick:
        best = search(O, theorems, regimes, [ROT, THETA], [1.0, 2.0], list(np.geomspace(0.006, 0.04, 8)),
                      list(np.geomspace(1e-3, 0.05, 8)), list(np.geomspace(0.8, 6, 16)), v2mod=v2mod)
    else:
        # stage A: rank every frame (v1, corner regime, coarse grids)
        stageA = {}
        for A in frames(a.maxe):
            b = search(O, ["v1"], ["corner"], [A], [0.5, 1.0, 2.0], list(np.geomspace(0.002, 0.05, 9)),
                       list(np.geomspace(5e-4, 0.05, 6)), list(np.geomspace(0.5, 40, 12)), v2mod=v2mod,
                       log=lambda *x: None)[("v1", "corner")]
            stageA[A] = None if b is None else b["ratio"]
            print("  stage A frame %s: %s" % (A, None if b is None else "%.2f (lam %.2f c %.2f rho %.4f)" % (
                b["ratio"], b["lam"], b["c"], b["rho"])), flush=True)
        ranked = sorted((A for A in stageA if stageA[A] is not None), key=lambda A: -stageA[A])
        top = list(dict.fromkeys([ROT, THETA] + ranked[:3]))
        print("stage A (%.0fs): top frames %s" % (time.time() - t0, top), flush=True)
        # stage B: fine grids on the top frames, every theorem, cheap regimes (l1, corner)
        cheap = [r for r in regimes if r != "sup"]
        best = search(O, theorems, cheap, top, [0.5, 0.7, 1.0, 1.4, 2.0, 2.8, 4.0],
                      list(np.geomspace(0.002, 0.05, 18)), list(np.geomspace(3e-4, 0.08, 12)),
                      list(np.geomspace(0.5, 60, 22)), s1s=(1e-6, 1e-4, 1e-2), v2mod=v2mod)
        # stage C: coordinate refinement of each optimum (rho, mu, c, lam, s - 1), norms cached
        cacheN = {}

        def nrm(A, lam, rho, regs):
            key = (A, round(lam, 12), round(rho, 14), tuple(regs))
            if key not in cacheN:
                cacheN[key] = O.norms(np.array(A, float), lam, rho, regimes=regs)
            return cacheN[key]

        def refine(t, r, b, regs):
            cur = dict(rho=b["rho"], mu=b["mu"], c=b["c"], lam=b["lam"], s1=b["s"] - 1)
            A = tuple(map(tuple, b["A"]))
            val = None; bb = b
            trials = [("rho", 1.0)] + [(nm_, f) for nm_ in ("rho", "mu", "c", "lam", "s1")
                                       for f in (0.85, 0.95, 1.05, 1.18)]
            for it in range(12):
                improved = False
                for name, f in trials:
                    trial = dict(cur); trial[name] = cur[name] * f
                    try:
                        nm = nrm(A, trial["lam"], trial["rho"], regs)
                        pkg = package(O, nm, r, A, trial["lam"], trial["c"], trial["rho"], trial["mu"],
                                      s1=trial["s1"], theorem=t)
                        T, le, ratio, br = evaluate(pkg, t, v2mod)
                    except (ValueError, ZeroDivisionError, OverflowError, np.linalg.LinAlgError):
                        continue
                    if val is None or ratio > val + 1e-3:
                        val, cur, improved = ratio, trial, True
                        bb = dict(pkg, T=T, log10e=le, ratio=ratio, branch=br, theorem=t)
                if not improved:
                    break
            return bb

        for key, b in list(best.items()):
            if b is not None:
                best[key] = refine(key[0], key[1], b, [key[1]])
        # the sampled-sup regime: start from the corner optimum and refine (grids at the corners)
        if "sup" in regimes:
            for t in theorems:
                b = best.get((t, "corner"))
                if b is not None:
                    best[(t, "sup")] = refine(t, "sup", b, ["sup"])
    print("\n== best packages (%s, %.0fs)" % (a.which, time.time() - t0))
    for (t, r), b in best.items():
        if b:
            print("%-5s %-6s %s" % (t, r, fmt(b)))
    if a.json:
        json.dump({"%s/%s" % k: v for k, v in best.items()}, open(a.json, "w"), indent=1, default=float)


if __name__ == "__main__":
    main()
