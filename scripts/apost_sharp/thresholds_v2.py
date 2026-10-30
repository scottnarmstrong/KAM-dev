#!/usr/bin/env python3
"""Thresholds of the v2 design (docs/campaign/design/APOST-SHARP-V2.md), cumulative from v1, on R1 and H50.

Untrusted tooling (design numbers, not a certificate).  Constants are exact rationals (fractions.Fraction) built from
rational inputs; irrational small-divisor constants enter as rational upper bounds (10 significant digits, rounded
up).  The threshold of a variant is the largest invariance error e for which every smallness condition of the
corresponding theorem holds; the conditions are monotone in e, so it is found by bisection on X0 = e/(gamma^4
delta0^{2a}) (additive route) or on the weighted error (modified route), to 3 significant digits.

Two Newton routes are modelled:
  route A  (additive, v1's scheme = HL19 Lemma 5.2): K_bar = K + L xi^L + N xi^N; step error O(e^2/(gamma^4 delta^{4 kappa})).
  route B  (modified, Figueras-Haro 2024 Lemma 3.6, arXiv:2304.10205): K_bar = (K + N xi^N) o (id + xi^L); the
           weighted error mu = max{|eta^L|, |eta^N|/(gamma delta^kappa)} contracts with gamma^{-1} delta^{-kappa-1}.
Levers (APOST-SHARP-V2.md section 3): L1 finer data, L2 small divisors, L3 no absorption, L4 schedule/bites,
L5 the modified route, L6 measured step-0 objects, L8 engine budgets and sums.

Usage:  python3 -I scripts/apost_sharp/thresholds_v2.py [--json OUT]
"""
from fractions import Fraction as F
import json, math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import thresholds as v1  # noqa: E402
import smalldiv as sd    # noqa: E402

lg = v1.lg
up = v1.up


def Fr(x, digits=10):
    """Rational upper bound of a positive float/mpf."""
    return up(x, digits)


# =============================================================================================================
# the engine: k exact prefix stages (stage constants), then a uniform tail (v1 engine, Proposition bp:p2s:engine-
# iteration, with constants valid for every bite delta <= delta_k)
# =============================================================================================================

def engine_A(stage, tail, k, X0, a, gamma, gbar, delta0, budgets, lam, absorb_sums=False, diag=False,
             keep=False):
    """Additive route.  stage(s) -> dict(CE, cond=[(coef, bound)], rates={name: (rho, j)});  tail likewise (uniform).
    Errors: x_s = eps_s/(gamma^4 delta_s^{2a}), x_{s+1} = 2^{2a} C_E(s) x_s^2 (Lemma bp:p2s:decay, stage form).
    Returns True iff every condition holds at X0."""
    x = X0
    used = {nm: F(0) for nm in budgets}
    fails = []
    maxB = 0
    for s in range(k):
        st = stage(s)
        ds = delta0 / 2 ** s
        for i, (coef, bound) in enumerate(st["cond"]):
            if coef * x > bound:
                fails.append("stage%d cond%d" % (s, i))
        maxB = max(maxB, st.get("B_loc", 0) * x)
        for nm, (rho, j) in st["rates"].items():
            wgt = gamma ** 2 * ds ** (a - j) if keep else gbar ** 2   # eps_s/(gamma^2 delta_s^{a+j}) = x_s gamma^2 delta_s^{a-j}
            if nm in used:
                used[nm] += rho * x * wgt
        try:
            x = 2 ** (2 * a) * st["CE"] * x ** 2
        except OverflowError:                                  # float data: far above any threshold
            fails.append("overflow"); x = 1e300
        if not isinstance(x, F) and x > 1e300:
            x = 1e300
    # tail (v1 engine from stage k): (I1)-(I4) with e := eps_k, delta_0 := delta_k
    dk = delta0 / 2 ** k
    tl = tail
    # tail decay (audit F5): x_{s+1} = 2^{4 kappa} C_E x_s^2 (route A's own normalisation); y = 2^{4 kappa} C_E x_k <= 1
    # with the geometric delta-weights gamma^2 delta^{a-j} (a - j >= 1) gives sums <= 2 rho w(delta_k) x_k: this is B9's
    # SchemeA (KAM/Sharp2/RouteA/Engine.lean, routeAOk.J2), proved
    ytail = F(1)
    if 2 ** (2 * a) * tl["CE"] * x > ytail:
        fails.append("tail E")
    for i, (coef, bound) in enumerate(tl["cond"]):
        if coef * x > bound:
            fails.append("tail cond%d" % i)
    maxB = max(maxB, tl.get("B_loc", 0) * x)
    for nm, (rho, j) in tl["rates"].items():
        w = gbar ** 2 if absorb_sums else gamma ** 2 * dk ** (a - j)   # v1's G1 step absorbs gamma^2 delta^{a-j} <= gbar^2
        if nm in used:
            used[nm] += 2 * rho * x * w                          # Lemma bp:p2s:decay: sum <= 2 eps_k/delta_k^{a+j}
    for nm in ("Tab", "Tsup"):
        if nm in used and "Tab" in used:
            used[nm] += 2 * maxB
    fails += ["sum " + nm for nm in budgets if used[nm] > budgets[nm]]
    return fails if diag else not fails


def bisect(pred, lo, hi, iters=60):
    """Largest X in [lo, hi] (log scale) with pred(X), assuming monotone; lo must satisfy pred."""
    lo, hi = math.log10(lo), math.log10(hi)
    for _ in range(iters):
        mid = (lo + hi) / 2
        if pred(Fr(10 ** mid)):
            lo = mid
        else:
            hi = mid
    return lo


# =============================================================================================================
# route A: stage constants (generalises Definition bp:p2s:constants / bpI:p2s:constants)
# =============================================================================================================

def stageA(D, o, delta, r, c, ch, cr, iso=False):
    """Stage constants of the additive route at the bite delta, strip r, small-divisor constants c = c(delta),
    ch = c(delta/2), cr = c(r).  D: data (rationals).  o: options (levers).  Returns the dict used by engine_A."""
    n = D["n"]; kap = D["kappa"]; a = 2 * kap
    gb = D["gbar"]
    keep = o.get("keep_delta", False)                     # L3: gamma^i delta^j <= gbar^i delta^j (else gbar^i)
    G = lambda i, j: gb ** i * (delta ** j if keep else 1)
    eta = o.get("eta", F(1))                              # L4: Cauchy bite eta*delta for the frame (lam = 2 + eta)
    th = o.get("theta", F(1, 8)); thh = 1 / (1 - th)
    qS = o.get("qS", F(1, 2)); tX = F(1, 2)
    sK, sB, sT = D["sK"], D["sB"], D["sT"]
    if o.get("L1", False):
        M1, M2, Lt, Nn, Nt = D["M1"], D["M2"], D["sLt"], D["sN"], D["sNt"]
        Mh1, Mh2 = D["Mh1"], D["Mh2"]
    else:
        M1 = M2 = Mh1 = Mh2 = D["M"]
        Lt, Nn, Nt = 2 * n * sK, sK * sB, 2 * n * sK * sB
    Theta = D["Theta_omega"] if (iso and o.get("L1", False)) else 2 * n * sK * sB * (D["M"] + 1)
    # geometry (Lemma bp:p2s:geometry; L2/FH24 Lemma 3.1: d_omega Omega_K = antisym(D eta^N))
    C_Om = 2 * (n - 1) * c * Lt if o.get("omega_eta", False) else c * (2 * n * sK + n * Lt)
    C_sym = max(F(1), sB ** 2) * C_Om
    C_red = n * max(Nt, Lt + 2 * Nn)
    # torsion (Lemma bp:p2s:torsion-bound or a supplied cap, L1)
    w = 2 * M1 * Lt * sK + (2 * n * sK + n * Lt)
    C_Omh = (2 * (n - 1) * ch * Lt if o.get("omega_eta", False) else ch * (2 * n * sK + n * Lt))
    C_T1 = n * Nt * sB
    C_T2 = 2 ** int(kap + 1) * sB ** 3 * w * C_Omh
    tslack = o.get("tslack", F(1))
    if o.get("torsion_cap") is not None:
        H = o["torsion_cap"]
    else:
        H = 2 * M1 * Nt * Nn + tslack
    t0 = o.get("torsion_real", H)
    c_avg = cr * (delta / min(r, 1)) ** int(kap) if o.get("avg_full_bite", False) else c   # bite min(r, 1) (B9 flag)
    # correction (Lemma bp:p2s:correction / bpI:p2s:correction)
    if not iso:
        C_S = sT * (Nt * G(1, kap) + t0 * c_avg * Lt)
        C_xiN = C_S + c * Lt
        C_g = H * C_xiN + Nt * G(1, kap)
    else:
        HY = Mh1 * Nn
        C_S = sT * max(Nt * G(1, kap) + t0 * c_avg * Lt, G(1, kap) + c_avg * HY * Lt)
        C_xiN = C_S + c * Lt
        C_g = H * C_xiN + Theta * C_S + Nt * G(1, kap)
    C_dxi = max(C_g, Lt * G(1, kap))
    C_xi = max(c * C_g, G(1, kap) * C_xiN)
    C_DK = sK * c * C_g + Nn * G(1, kap) * C_xiN
    # new error (Lemma bp:p2s:newton-error / bpI:p2s:newton-error)
    C_lin = C_red * C_xi + C_sym * C_dxi
    P = sK + Nn
    if not iso:
        C_E = P / (1 - qS) * G(2, a - 1) * C_lin + tX * M2 * C_DK ** 2
        C_Dw = None
    else:
        C_Dw = Theta * G(1, kap) * C_S
        C_P = (M1 * sK + n) * (1 + sB) + Nn * ((Lt * M1 + 2 * n) * sK + Lt * (M1 * sK + n)) * sB
        C_dK = C_P * C_xi + P * G(1, kap) * C_dxi
        C_lin = C_lin + Theta * C_Om * C_S
        C_E1 = P / (1 - qS) * G(2, a - 1) * C_lin + tX * M2 * C_DK ** 2 + G(1, kap) * C_S * C_dK
        C_E2 = G(1, kap - 1) * n * (Lt * G(1, kap) + Theta * C_Om) * c * C_g + tX * Mh2 * C_DK ** 2
        C_E = max(C_E1, C_E2)
    # perturbation and rates (Lemma bp:p2s:perturbation; caps-based variant, L8)
    caps = o.get("caps_tilde", False)
    if caps:
        C_G = n * Lt + 2 * n * sK
        C_B = sB ** 2 * C_G / (1 - th)
        C_Nd = n * sB + sK * C_B
        C_Ntd = C_B * Lt + 2 * n * sB
        C_Dab = 2 * M1 * (C_Ntd * Nn + Nt * C_Nd) + 2 * M2 * Nt * Nn * eta * (delta if keep else 1)
        C_Dcd = sB ** 3 * w * (2 * n * sK + n * Lt)
        C_DT = (C_Dab + C_Dcd) * C_DK / eta + n * Nt * sB * (1 + 1 / eta) * G(2, a) + 2 * sB ** 3 * w * C_Om * G(1, kap)
        rho_T = sT ** 2 / (1 - th) * C_DT
    else:
        C_G = 2 * n * sK * (n * (1 + th) + 1)
        C_B = thh * sB ** 2 * C_G
        C_Dab = 2 * thh ** 4 * 2 * n * M1 * sK ** 2 * sB ** 2 * (2 * C_B / sB + (n + 1) / sK + 1)
        C_Dc = thh ** 5 * sB ** 3 * w * 2 * n * sK * (n + thh)
        C_DT = (C_Dab + C_Dc) * C_DK / eta + (1 + thh ** 3) * C_T1 * G(2, a) + (thh ** 5 + 1) * sB ** 3 * w * C_Om * G(1, kap)
        C_Nd = C_Ntd = None
        rho_T = thh * sT ** 2 * C_DT
    if iso:
        D1 = delta if keep else 1
        C_DT = max(C_DT + C_Dw * D1, n * C_Dw * D1 + n * (1 + (1 if caps else thh ** 2)) * Nt * G(2, a))
        rho_T = (sT ** 2 / (1 - th) if caps else thh * sT ** 2) * C_DT
    rates = {"ball": (C_DK, 0), "DK": (n * C_DK / eta, 1), "B": (C_B * C_DK / eta, 1), "Tinv": (rho_T, 1)}
    if caps:
        rates.update({"Lt": (2 * n * C_DK / eta, 1), "N": (C_Nd * C_DK / eta, 1), "Nt": (C_Ntd * C_DK / eta, 1)})
    if o.get("torsion_cap") is not None:
        rates["Tsup"] = (C_DT, 1)
    if iso:
        rates["nu"] = (C_Dw, 0)
    B_loc = 0
    tref = o.get("tref", False)
    if tref:
        # audit F8 (Lemma bp:p2s2:torsion-ref): only T_ab is telescoped; T_F + T_c is bounded at each stage by its own
        # data (|T_F| <= s_Nt s_B n eps/delta, |T_c| <= s_B^3 w |Omega_K|) and <T_s> is compared with <T_0>
        rate_ab = C_Dab * C_DK / eta
        B_loc = C_T1 * G(4, 2 * a - 1) + C_T2 * G(3, 2 * a - kap - 1)
        if iso:
            D1 = delta if keep else 1
            rate_ab = max(rate_ab + C_Dw * D1, n * C_Dw * D1)
            B_loc = max(B_loc, n * Nt * G(4, 2 * a))           # the eta^L row of the bordered torsion
        del rates["Tinv"]
        rates["Tab"] = (rate_ab, 1)
        if o.get("torsion_cap") is not None:
            rates["Tsup"] = (rate_ab, 1)
    # step smallness (Proposition bp:p2s:step): coef * X <= bound
    cond = [(G(4, 2 * a - 1), F(1)),                                    # eps <= delta
            (C_sym * G(3, 3 * kap - 1), qS),                             # |E_sym| <= qS
            (C_E, eta if caps else F(1))]                                 # eps_bar <= eta*eps (caps) / eps
    if not tref:
        cond.append((sT * C_DT * G(2, a - 1), th))                       # Neumann for <T_bar> (v1)
    if o.get("torsion_cap") is None:
        cond.append((C_T1 * G(4, 2 * a - 1) + C_T2 * G(3, 2 * a - kap - 1), tslack))
    if caps:
        cond.append((sB * C_G * C_DK * G(2, a - 1) / eta, th))           # Neumann for B
    else:
        cond += [(n * C_DK * G(2, a - 1) / (eta * sK), th), (sB * C_G * C_DK * G(2, a - 1) / eta, th)]
    return dict(CE=C_E, cond=cond, rates=rates, C_DK=C_DK, C_Dw=C_Dw, C_E=C_E, H=H, B_loc=B_loc)


def thresholdA(D, o, iso, k=0, c_stage=None, c_tail=None):
    """Threshold (log10 e*) of route A with k prefix stages.
    c_stage(s) -> (c(delta_s), c(delta_s/2), c(r_s)); c_tail -> uniform constant for the tail (valid for every bite)."""
    a = 2 * D["kappa"]
    eta = o.get("eta", F(1)); lam = 2 + eta
    delta0 = min(F(1), (D["rho"] - D["rhoinf"]) / (2 * lam))
    gamma, gbar, mu = D["gamma"], D["gbar"], D["mu"]
    r = lambda s: D["rho"] - 2 * lam * delta0 * (1 - F(1, 2 ** s))

    if k >= 1:
        o = dict(o, tref=True)                             # torsion against the initial torus (audit F8)
    check_data(D)

    def stage(s):
        ds = delta0 / 2 ** s
        c, ch, cr = c_stage(s)
        return stageA(D, o, ds, r(s), c, ch, cr, iso)
    if k == 0:                                             # the v1 engine from stage 0, uniform constants
        assert not o.get("keep_delta", False) and not o.get("avg_full_bite", False)
        tail = stageA(D, o, delta0, D["rho"], *c_stage(0), iso)
    else:                                                  # tail: absorbed constants, valid for every bite <= 1
        ot = dict(o, keep_delta=False, avg_full_bite=False)
        ctA = c_tail[0] if isinstance(c_tail, tuple) else c_tail     # route-A tail: average at the small bite
        tail = stageA(D, ot, delta0 / 2 ** k, r(k), ctA, ctA, ctA, iso)
    budgets = budgets_for(D, o, iso)
    if o.get("tref"):
        budgets.pop("Tinv")
        budgets["Tab"] = torsion_budget(D, o.get("free_budgets", False))
    keep = o.get("keep_delta", False)
    pred = lambda X: engine_A(stage, tail, k, X, a, gamma, gbar, delta0, budgets, lam, absorb_sums=(k == 0),
                              keep=keep)
    lx = bisect(pred, 1e-60, 1e30)
    why = engine_A(stage, tail, k, Fr(10 ** (lx + 0.01)), a, gamma, gbar, delta0, budgets, lam,
                   absorb_sums=(k == 0), diag=True, keep=keep)
    return lx + math.log10(float(gamma ** 4 * delta0 ** (2 * a))), delta0, why


def with_caps(D, f):
    """Free budgets (L8): every internal cap is set to (measured value)(1 + f); the frozen ones keep sigma - mu/2
    for |DK| and the ball mu/2 (conclusion of the frozen statement).  Returns a data dict whose sigma's are the caps."""
    E = dict(D)
    mu = D["mu"]
    for k_, meas in (("sB", D["sB"] - mu), ("sT", D["sT"] - mu), ("sLt", D["sLt"] - mu), ("sN", D["sN"] - mu),
                     ("sNt", D["sNt"] - mu)):
        E[k_] = meas * (1 + f)
        E["bud_" + {"sB": "B", "sT": "Tinv", "sLt": "Lt", "sN": "N", "sNt": "Nt"}[k_]] = meas * f
    E["Tsup_cap"] = D["Tsup"] * (1 + f); E["bud_Tsup"] = D["Tsup"] * f
    return E


def torsion_budget(D, free):
    """Neumann budget of the torsion average against the initial torus (Lemma bp:p2s2:torsion-ref): with the initial
    |<T_0>^{-1}| <= m and the cap s (= m + budget), |<T_s> - <T_0>| <= (s - m)/(s m) gives |<T_s>^{-1}| <= s."""
    cap = D["sT"]
    bud = D["bud_Tinv"] if free else D["mu"]                  # frozen: |<T_0>^{-1}| <= sigma_T - mu, cap sigma_T
    init = cap - bud
    assert init > 0 and bud > 0
    return bud / (cap * init)


def check_data(D):
    """Audit F1: a well-formed numerical package (positive caps and weights, nonnegative Hamiltonian bounds, initial
    values strictly below the caps)."""
    for k_ in ("sK", "sB", "sT", "sLt", "sN", "sNt", "gamma", "gbar", "mu", "rho"):
        assert D[k_] > 0, k_
    for k_ in ("M", "M1", "M2", "Mh1", "Mh2", "cTh"):
        assert D.get(k_, 0) >= 0, k_
    assert D["gamma"] <= D["gbar"] and 0 < D["rhoinf"] < D["rho"]
    for k_ in ("B", "Tinv", "Lt", "N", "Nt"):
        if "bud_" + k_ in D:
            assert D["bud_" + k_] > 0, k_
    assert D["sK"] > D["mu"] / 2 and D["sT"] > D["mu"]


def budgets_for(D, o, iso):
    mu = D["mu"]
    if o.get("free_budgets", False):
        b = {"ball": mu / 2, "DK": mu / 2, "B": D["bud_B"], "Tinv": D["bud_Tinv"]}
        if o.get("caps_tilde", False):
            b.update({"Lt": D["bud_Lt"], "N": D["bud_N"], "Nt": D["bud_Nt"]})
        if o.get("torsion_cap") is not None:
            b["Tsup"] = D["bud_Tsup"]
    else:
        b = {"ball": mu / 4, "DK": mu / 2, "B": mu / 2, "Tinv": mu / 2}
        if o.get("caps_tilde", False):
            b.update({"Lt": mu / 2, "N": mu / 2, "Nt": mu / 2})
        if o.get("torsion_cap") is not None:
            b["Tsup"] = mu / 2
    if iso:
        b["nu"] = D["nu"] / 2
    return b



# =============================================================================================================
# route B: the modified step (blueprint p2s2-modified / p2s2-iso-modified; FH24 Lemma 3.6 with the v2 deltas)
# weighted error mu = max{|eta^L|, |eta^N|/(gamma delta^kappa), |E^omega| (iso)}, X = mu/(gamma delta^{kappa+1})
# =============================================================================================================

def stageB(D, o, delta, r, c, c1, cr, iso=False, stage0=None, lamL=F(1), lamW=F(1)):
    """Stage constants of the modified step at the bite delta, strip r: small-divisor constants c (bite delta), c1
    (Russmann-Cauchy, Corollary bp:p2s2sd:rc), cr (full bite r, real points).  Returns Q (X_{s+1} <= 2^{kappa+1} Q X_s^2),
    conditions [(coef, bound)] meaning coef*X <= bound, rates {name: (rho, w)} (cap increment rho*w*X), C_DK, C_0."""
    n = D["n"]; kap = D["kappa"]
    gb = D["gbar"]
    keep = o.get("keep_delta", True)
    gd = gb * (delta ** kap if keep else 1)                 # bound of gamma delta^kappa
    gd1 = gd * (delta if keep else 1)                       # bound of gamma delta^{kappa+1}
    th = o.get("theta", F(1, 8)); thx = o.get("theta_xi", F(1, 8)); thO = o.get("theta_om", F(1, 8))
    q = o.get("q", F(1, 8))
    sK, sB, sT = D["sK"], D["sB"], D["sT"]
    if o.get("L1", True):
        M1, M2, Lt, Nn, Nt, Mh1, Mh2 = D["M1"], D["M2"], D["sLt"], D["sN"], D["sNt"], D["Mh1"], D["Mh2"]
    else:
        M1 = M2 = Mh1 = Mh2 = D["M"]
        Lt, Nn, Nt = 2 * n * sK, sK * sB, 2 * n * sK * sB
    Theta = D["Theta_omega"] if (iso and o.get("L1", True)) else 2 * n * sK * sB * (D["M"] + 1)
    tslack = o.get("tslack", F(1, 10))
    cTh = o.get("cTh", 2 * M1)                               # |T_h| = |Om0 A - A Om0| <= 2 M1, or a certified c_Th (L1)
    t = o.get("torsion_cap") or (cTh * Nt * Nn + tslack)     # T = T_ab + T_F + T_c, |T_ab| = |N^T T_h N| <= c_Th s_Nt s_N
    t0 = o.get("torsion_real", t)
    sKt = (1 + th) * sK; sLtt = (1 + th) * Lt                 # intermediate frame of K~ (conditions below)
    # (1) Lagrangian defect and recovery of E (FH24 Lemmas 3.1, 3.3)
    C_Om = 2 * (n - 1) * c1
    C_EL = (sK + Nn * q) / (1 - q ** 2); C_EN = (Nn + sK * q) / (1 - q ** 2)
    # anisotropic weight (lever L3b): mu = max{|eta^L|/lamL, |eta^N|/(gamma delta^kappa), |E^omega|/lamW}
    C_E = lamL * C_EL + gd * C_EN
    if stage0 is not None:
        C_E = min(C_E, stage0["e_over_mu"])
    C_DE = n * (sK + Nn) * (max(lamL, gd) + (Lt + Nt) * C_E) / (1 - q)
    if stage0 is not None:                                     # stage 0: |E| <= e on T_rho, Cauchy for DE directly
        C_DE = min(C_DE, n * stage0["e_over_mu"])
    C_NN = n * (lamL + Nt * C_E)                               # |E_red^NN| = |(N^T Om0 DE)^T| <= C_NN mu/delta
    # (3) normal correction (full-bite average, Lemma bp:p2s2sd:avg)
    avgf = cr * (delta / min(r, 1)) ** kap if o.get("avg_full_bite", True) else c   # full bite min(r, 1) <= r
    if not iso:
        C_0 = sT * (lamL + t0 * avgf)
    else:
        y0 = Mh1 * Nn
        C_0 = sT * max(lamL + t0 * avgf, lamW + y0 * avgf)
    C_xiN = C_0 + c
    C_Kt = Nn * C_xiN                                          # |K~ - K| <= C_Kt mu
    C_DLt = n * Nn * (C_0 + c1)                                # |L~ - L| <= C_DLt mu/delta
    C_DLtt = 2 * n * Nn * (C_0 + c1)
    # (4) intermediate error and normal error of K~
    C_dN = (M1 * sK + n) * sB + Nn * ((Lt * M1 + 2 * n) * sK + Lt * (M1 * sK + n)) * sB
    C_XN = M1 * Nn + C_dN
    C_Et = C_E + C_XN * C_xiN + Nn * gd + M2 / 2 * C_Kt
    if iso:
        C_Et += sKt * Theta * C_0
    Qt_N = C_DLtt * C_Et + C_NN * C_xiN + (delta if keep else 1) * Lt * M2 / 2 * C_Kt ** 2
    # (5) tangential correction by composition
    C_gL = lamL + t * C_xiN + (Theta * C_0 if iso else 0)
    C_xiL = c * C_gL                                          # |xi^L| <= C_xiL mu/(gamma delta^kappa)
    C_DK = sKt * C_xiL + gd * C_Kt                             # |K_bar - K| <= C_DK mu/(gamma delta^kappa)
    # iso (audit iso F5): d_{omega_bar} xi^L = (1 - xi^omega) d_omega xi^L, |xi^omega| <= C_0 mu <= C_0 g1 X <= theta_om2
    # (step condition below), so |1 - xi^omega| <= a := 1 + theta_om2; a = 1 at fixed frequency
    a_w = 1 + o.get("theta_w", F(1, 8)) if iso else F(1)
    C_Eb = C_Et + a_w * sKt * C_gL                             # |E_bar| <= C_Eb mu (crude)
    # (8) frames of K_bar
    C_Lb = n * C_DK; C_Lbt = 2 * n * C_DK
    C_G = n * Lt + 2 * n * sK
    C_Bb = sB ** 2 * C_G * C_DK / (1 - th)
    C_Nb = n * C_DK * sB + sK * C_Bb
    C_Nbt = C_Bb * Lt + 2 * n * C_DK * sB
    w = 2 * M1 * Lt * sK + (2 * n * sK + n * Lt)
    # torsion (audit F8, Lemma bp:p2s2:torsion-ref): T = T_ab + T_F + T_c (bp:p2s:torsion-identity).  Only T_ab is
    # telescoped (rate C_ab, the cap "Tab"); T_F + T_c is bounded at each stage by its own data, B_loc X (on T_{r-delta}),
    # and <T_s> is compared with the INITIAL <T_0>: |<T_s> - <T_0>| <= sum_j C_ab,j X_j + B_s + B_0 (no barred-torus
    # estimate, no next-bite certificate).  iso: the bordered torsion adds the frequency (rate) and the eta^L row (local).
    cDTh = o.get("cDTh", 2 * M2)                             # |D T_h| <= 2 |D^2 X_h|, or a certified c_DTh (L1)
    C_ab = cTh * (C_Nbt * Nn + Nt * C_Nb) + cDTh * Nt * Nn * C_DK * (delta if keep else 1)
    B_sup = (Nt * sB * C_DE + sB ** 3 * w * C_Om) * gd        # |T_F| + |T_c| <= B_sup X on T_{r-delta}
    B_loc = B_sup
    # (6), (7) new errors
    Qb_N = (1 + n * thx) * (1 + thO) * Qt_N
    QL1 = (Nt * M2 / 2 * C_Kt ** 2 * gd1 + sB ** 2 * C_Om * gd * gd + Nt * n * C_Et * C_xiL
           + a_w * Nt * C_gL * (n * sKt * C_xiL + gd * C_DLt))         # Q'_L: the bound of N^T Om0 E_bar
    rates = {"ball": (C_DK, "delta"), "DK": (C_Lb, 1), "B": (C_Bb, 1), "Tab": (C_ab, 1),
             "Lt": (C_Lbt, 1), "N": (C_Nb, 1), "Nt": (C_Nbt, 1)}
    if o.get("torsion_cap") is not None:
        rates["Tsup"] = (C_ab, 1)
    Qw = None
    if iso:
        # audit iso F5 / B3 signal: Omega_K~ (xi^omega omega - d_omega_bar xi^L), |.| <= C_Omega (Theta C_0 + a C_gL) X Q~_N mu^2/delta
        # <= (1 + a) theta_Omega Q~_N mu^2/delta since Theta C_0 <= C_gL: polynomial, no 1/C_xiL
        Qb_N = (1 + n * thx) * (1 + (1 + a_w) * thO) * Qt_N
        QL1 += C_0 * C_gL * gd1 + C_0 * Nt * C_DLt * Theta * gd
        Qw = Mh2 / 2 * C_Kt ** 2 * gd1 + n * Qt_N * thx * (Theta * C_Om + gd1)
        rates["Tab"] = (max(C_ab + Theta * C_0 * gd1, n * Theta * C_0 * gd1), 1)
        B_loc = max(B_sup, n * gd1)                            # |eta^L_s| <= mu_s <= g1 X_s in the row Y = omega^T - (eta^L)^T
        rates["nu"] = (Theta * C_0, "gd1")
    QL = QL1 + C_Nbt * C_Eb                                    # crude: |(N_bar - N)^T Om0 E_bar| <= C_Nbt X C_Eb mu
    QL_sc = None
    if o.get("selfcons", True):
        # self-consistent tangential error (L10, step:p2s2:selfcons): |E_bar| <= C_EL |eta_bar^L| + C_EN |eta_bar^N| (recovery for
        # K_bar on T_{r-3delta}; Omega_K_bar = D phi^T (Omega_K~ o phi) D phi, |Omega_K_bar| <= (1 + n th_xi)^2 C_Omega Q~_N g X^2)
        thN = o.get("theta_N", F(1, 8))
        QL_sc = (QL1 + thN * (C_EN / C_EL) * Qb_N * gd) / (1 - thN)
        QL = min(QL, QL_sc)
    if iso:
        QL = max(QL, Qw)
    a_r = o.get("ratio", 2)                                    # next bite delta/a: eta^N divided by gamma (delta/a)^kappa
    Q = max(QL, a_r ** kap * Qb_N)
    cond = [(max(F(1), sB ** 2) * C_Om * gd, q),               # |Omega_K|, |Omega_N| <= q
            (C_DE * gd, F(n)),                                 # |DE| <= n
            (C_xiL, thx),                                      # |xi^L| <= theta_xi delta (composition)
            (C_Om * C_gL, thO),
            (C_Kt * gd1, F(1)),
            (C_DLt * gd / sK, th), (C_DLtt * gd / Lt, th),     # intermediate frame of K~
            (sB * C_G * C_DK, th)]                             # Neumann for B_bar
    if iso:
        cond.append((C_0 * gd1, a_w - 1))                      # |xi^omega| <= theta_w (iso F5)
    if QL_sc is not None:
        cond.append((C_Nbt * C_EL, o.get("theta_N", F(1, 8))))  # |N_bar - N|^T C_EL <= th_N (self-consistent eta_bar^L)
        cond.append((max(F(1), sB ** 2) * (1 + n * thx) ** 2 * C_Om * Qt_N * gd, q, 2))   # |Omega_K_bar| <= q (X^2)
    if o.get("torsion_cap") is None:                           # derived torsion cap t: |T_F| + |T_c| <= tslack
        cond.append((B_sup, tslack))
    return dict(Q=Q, cond=cond, rates=rates, C_DK=C_DK, C_0=C_0, C_xiL=C_xiL, Qt_N=Qt_N, QL=QL, gd=gd, gd1=gd1,
                B_loc=B_loc)


def _pw(x, p):
    try:
        return x ** p
    except OverflowError:                                      # float data far above any threshold
        return float("inf")


def engine_B(stage, tail, k, X0, kap, delta0, gamma, gbar, budgets, diag=False, ratio=2, ymax=F(1, 2)):
    """Weighted recursion X_{s+1} = 2^{kappa+1} Q_s X_s^2 (X_s = mu_s/(gamma delta_s^{kappa+1})); k prefix stages, then a
    uniform tail with the critical sums bounded by X_k/(1 - y_k), y_k = 2^{kappa+1} Q_tail X_k (Proposition bp:p2s2:engine)."""
    x = X0
    used = {nm: F(0) for nm in budgets}
    fails = []
    maxB = 0                                                   # max_s B_loc,s X_s (local torsion parts, F8)
    for s in range(k):
        st = stage(s)
        ds = delta0 / ratio ** s
        for i, cnd in enumerate(st["cond"]):
            if cnd[0] * _pw(x, cnd[2] if len(cnd) > 2 else 1) > cnd[1]:
                fails.append("stage%d cond%d" % (s, i))
        # no local contraction premise: the repaired step (torsion against the initial torus, iso Y row local) does
        # not use 2^{kappa+1} Q X <= 1 (audit F8); X_s may grow inside the finite prefix
        maxB = max(maxB, st.get("B_loc", 0) * x)
        for nm, (rho, wk) in st["rates"].items():
            wv = ds if wk == "delta" else (st["gd1"] if wk == "gd1" else 1)
            if nm in used:
                used[nm] += rho * wv * x
        try:
            x = ratio ** (kap + 1) * st["Q"] * x ** 2
        except OverflowError:                                  # float data (FH25): far above any threshold
            fails.append("overflow"); x = 1e300
        if not isinstance(x, F) and x > 1e300:
            x = 1e300
    tl = tail
    y = ratio ** (kap + 1) * tl["Q"] * x                       # the tail continues the schedule delta_s = delta_k a^{k-s}
    # J2 with a free decay bound ymax < 1 (FH24's kappa): tail sums <= X_k/(1 - ymax)
    if y > ymax:
        fails.append("tail decay")
    for i, cnd in enumerate(tl["cond"]):
        if cnd[0] * _pw(x, cnd[2] if len(cnd) > 2 else 1) > cnd[1]:
            fails.append("tail cond%d" % i)
    maxB = max(maxB, tl.get("B_loc", 0) * x)                   # tail stages: X_s <= X_k, B_loc <= tail value
    dk = delta0 / ratio ** k
    for nm, (rho, wk) in tl["rates"].items():
        wv = dk if wk == "delta" else (tl["gd1"] if wk == "gd1" else 1)
        if nm in used:
            used[nm] += rho * wv * x / (1 - ymax)
    # torsion against the initial torus: sum of the T_ab increments + B_s + B_0 <= the Neumann budget beta_T
    for nm in ("Tab", "Tsup"):
        if nm in used:
            used[nm] += 2 * maxB
    fails += ["sum " + nm for nm in budgets
              if (used[nm] >= budgets[nm] if nm == "ball" else used[nm] > budgets[nm])]
    return fails if diag else not fails


def thresholdB(D, o, iso, k, c_stage, c_tail, e_from_mu=True):
    """log10 of the largest e (frozen hypothesis |E| <= e on T_rho) admitted by route B with k prefix stages;
    mu_0 = max{sigma_N^T e, sigma_L^T e/(gamma delta_0^kappa), e (iso)} (or measured eta's, L6)."""
    kap = D["kappa"]
    lam = 3
    a_r = o.get("ratio", 2)                                    # L4: prefix schedule delta_s = delta0 a^{-s}
    delta0 = min(F(1), (D["rho"] - D["rhoinf"]) * (a_r - 1) / (lam * a_r))
    gamma, gbar = D["gamma"], D["gbar"]
    r = lambda s: D["rho"] - lam * delta0 * (1 - (1 / a_r) ** s) / (1 - 1 / a_r)

    Lt = D["sLt"] if o.get("L1", True) else 2 * D["n"] * D["sK"]
    Nt = D["sNt"] if o.get("L1", True) else 2 * D["n"] * D["sK"] * D["sB"]
    if o.get("eta_measured"):
        etaL, etaN = o["eta_measured"]
        per_e = max(etaL, etaN / (gamma * delta0 ** kap), F(1) if iso else F(0))
    else:
        per_e = max(Nt, Lt / (gamma * delta0 ** kap), F(1) if iso else F(0))

    def stage(s):
        ds = delta0 / a_r ** s
        c, ch, cr = c_stage(ds, r(s)) if (a_r != 2 or getattr(c_stage, "by_bite", False)) else c_stage(s)
        # Russmann-Cauchy split (Corollary bp:p2s2sd:rc): c1 = c(s delta)/(s^kappa (1 - s)), ch = c at the split bite
        # s delta; s = kappa/(kappa + 1) is optimal for flat c ((kappa+1)^{kappa+1}/kappa^kappa; = 2^{kappa+1}, s = 1/2,
        # at kappa = 1)
        sp = o.get("split", F(kap, kap + 1) if isinstance(kap, int) else kap / (kap + 1))
        c1 = ch / (sp ** kap * (1 - sp))
        if s == 0 and o.get("aniso", False):                   # stage-0 weights from the measured/derived eta's
            gd0 = gamma * delta0 ** kap
            lamL = min(F(1), (o["eta_measured"][0] if o.get("eta_measured") else Nt) / per_e)
            lamW = min(F(1), F(1) / per_e) if iso else F(1)
        else:
            lamL = lamW = F(1)
        return stageB(D, o, ds, r(s), c, c1, cr, iso,
                      stage0=(dict(e_over_mu=1 / per_e) if (s == 0 and not o.get("no_e")) else None),
                      lamL=lamL, lamW=lamW)
    # tail: constants at the bite delta_k, valid for every bite <= delta_k (monotone in delta), uniform c.  Full-strip
    # averages (audit F9): either c_tail = (ct, cbar_inf) with cbar_inf certified at EVERY full-strip bite r_j <= r_k
    # (classical: c^nat(min(r_k, 1)), monotone), used with the factor (delta_k/r_k)^kappa, valid for every later stage
    # since r_j - rho_inf = 3 delta_j a/(a-1) makes delta_j/r_j increasing in delta_j; or a scalar ct: average at the
    # small bite, avg = ct (no factor)
    if isinstance(c_tail, tuple):
        ct, cbt = c_tail
        ot = dict(o, avg_full_bite=True)
    else:
        ct = cbt = c_tail
        ot = dict(o, avg_full_bite=False)
    tail = stageB(D, ot, delta0 / a_r ** k, r(k), ct, ct * (kap + 1) ** (kap + 1) / kap ** kap, cbt, iso)
    if o.get("aniso"):
        assert k >= 1, "anisotropic stage-0 weights need kpre >= 1 (the tail has weights 1; audit iso F2)"
    check_data(D)
    budgets = budgets_for(D, dict(o, caps_tilde=True, free_budgets=o.get("free_budgets", False)), iso)
    budgets["ball"] = D["mu"] / 2                              # d < beta with D_s <= mu/2 (route B ball budget)
    if o.get("torsion_cap") is None:
        budgets.pop("Tsup", None)
    budgets.pop("Tinv")
    budgets["Tab"] = torsion_budget(D, o.get("free_budgets", False))
    ym = o.get("ymax", F(1, 2))
    pred = lambda X: engine_B(stage, tail, k, X, kap, delta0, gamma, gbar, budgets, ratio=a_r, ymax=ym)
    lx = bisect(pred, 1e-60, 1e10)
    why = engine_B(stage, tail, k, Fr(10 ** (lx + 0.01)), kap, delta0, gamma, gbar, budgets, diag=True, ratio=a_r,
                   ymax=ym)
    # mu_0 from e: X0 = mu_0/(gamma delta0^{kappa+1}), mu_0 = e * max{s_Nt, s_Lt/(gamma delta0^kappa), 1 (iso)}
    le = lx + math.log10(float(gamma * delta0 ** (kap + 1))) - math.log10(float(per_e))
    return le, delta0, why

# =============================================================================================================
# packages
# =============================================================================================================

def package_H50():
    """H50 (scripts/apost_sharp/h50_package.py): lower barrier nu = 1 - 1/(50+g), rotated frame, rho' = 1/83,
    c = 7/4, gamma = c/(52 s) (gamma' = 1/52), sampled sups x 1.05 (+ mu for the frozen sigma's)."""
    mu = F(1, 160); c = F(7, 4); s = 1 + F(1, 10 ** 6)
    gamma = c / (52 * s)
    rho = F(1, 83)
    g = (math.sqrt(5) - 1) / 2
    D = dict(n=2, tau=1, kappa=1, rho=rho, rhoinf=rho / 1000, gamma=gamma, gbar=gamma, mu=mu, nu=F(1, 10 ** 6),
             M=F(9617, 5000), sK=F(105, 100) * F(14721, 10000) + mu, sB=F(105, 100) * F(25906, 10000) + mu,
             sT=F(105, 100) * F(5803, 10000) + mu,
             M0=F(105, 100) * F(175, 100), M1=F(105, 100) * F(175, 100), M2=F(105, 100) * F(10270, 10000),
             Mh1=F(105, 100) * F(18175, 10000), Mh2=F(105, 100) * F(18317, 10000),
             sLt=F(105, 100) * F(15003, 10000) + mu, sN=F(105, 100) * F(16097, 10000) + mu,
             sNt=F(105, 100) * F(16399, 10000) + mu, Tsup=F(105, 100) * F(46781, 10000),
             cTh=F(105, 100) * F(18202, 10000), Theta_omega=2 * c / s, omega_star=(-float(c / s) / (50 + g), float(c / s)))
    for k_, base in (("B", D["sB"]), ("Tinv", D["sT"]), ("Lt", D["sLt"]), ("N", D["sN"]), ("Nt", D["sNt"]),
                     ("Tsup", D["Tsup"])):
        D["bud_" + k_] = base / 10
    return D


def package(name="R1"):
    """R1 (thresholds.package_R1, CONSTANTS-STUDY 2.2) with the measured separate majorants of r1_norms.py
    (sampled sup x 1.05, + mu where the frozen hypothesis carries the margin)."""
    p, gamma = v1.package_R1()
    mu = p["mu"]
    c = F(7, 4); s = 1 + F(1, 10 ** 6)
    D = dict(n=2, tau=1, kappa=1, rho=p["rho"], rhoinf=p["rhoinf"], gamma=gamma, gbar=gamma, mu=mu, nu=p["nu"],
             M=p["M"], sK=p["sK"], sB=p["sB"], sT=p["sT"],
             M0=F(105, 100) * F(175, 100), M1=F(105, 100) * F(175, 100), M2=F(105, 100) * F(10342, 10000),
             Mh1=F(105, 100) * F(18228, 10000), Mh2=F(105, 100) * F(18323, 10000),
             sLt=F(105, 100) * F(13268, 10000) + mu, sN=F(105, 100) * F(13540, 10000) + mu,
             sNt=F(105, 100) * F(13787, 10000) + mu, Tsup=F(105, 100) * F(33130, 10000),
             cTh=F(105, 100) * F(18202, 10000),               # |T_h| on the domain (benchmark_fh24.py: T_h = diag(A - C, C - A))
             Theta_omega=2 * c / s * s,                      # |omega| <= sigma_omega |omega*| = 2 c/s, times s <= sigma_omega
             omega_star=(-(79 - math.sqrt(5)) / 3118 * float(c / s), float(c / s)))
    D["Theta_omega"] = 2 * c / s                           # sigma_omega |omega*|, sigma_omega = 2
    # free budgets (L8): the internal caps are free; budget = 10% of the measured value
    for k_, base in (("B", D["sB"]), ("Tinv", D["sT"]), ("Lt", D["sLt"]), ("N", D["sN"]), ("Nt", D["sNt"]),
                     ("Tsup", D["Tsup"])):
        D["bud_" + k_] = base / 10
    return D


def c_stages(D, which, k=5):
    """Small-divisor constants per stage: which in {'v1', 'classical', 'freq'}; the tail constant is valid at every bite
    <= delta_k (k = the number of prefix stages; the tail starts at stage k)."""
    n, tau = D["n"], int(D["tau"])
    if which == "v1":
        cv = v1.cohConstR_lean(n, tau)
        return (lambda s: (cv, cv, cv)), cv
    lam = 3
    delta0 = (D["rho"] - D["rhoinf"]) / (2 * lam)
    ccl = lambda d: Fr(sd.c_classical(n, tau, float(d)))           # Proposition bp:p2s2sd:classical at the bite d
    ctail = ccl(delta0 / 2 ** k)                                  # every bite <= delta_k (monotone; Proposition bp:p2s2:engine)
    rk = D["rho"] - 2 * lam * delta0 * (1 - F(1, 2 ** k))
    ctail = (ctail, ccl(min(rk, F(1))))                           # + full-strip constant at every r_j <= r_k (F9)
    if which == "classical":
        def stc(s):
            ds = delta0 / 2 ** s
            r = D["rho"] - 2 * lam * delta0 * (1 - F(1, 2 ** s))
            return ccl(ds), ccl(ds / 2), ccl(min(r, F(1)))
        return stc, ctail
    gam = float(D["gamma"])
    om = D["omega_star"]
    cache = {}

    def cf(d):
        d = float(d)
        if d not in cache:
            cache[d] = min(Fr(sd.c_freq(om, gam, tau, d)[0]), ccl(d))
        return cache[d]

    def st(s):
        ds = delta0 / 2 ** s
        r = D["rho"] - 2 * lam * delta0 * (1 - F(1, 2 ** s))
        return cf(ds), cf(ds / 2), cf(r)
    return st, ctail


def routeA_variants(D):
    Tc = D["Tsup"]
    base = dict(L1=True, torsion_cap=Tc, torsion_real=Tc)
    return [
        ("A0 v1 sharp design (reproduction)", dict(), "v1", 0),
        ("A1 + L1 finer data (M1, M2, |L^T|, |N|, |N^T|, Theta_omega)", dict(L1=True), "v1", 0),
        ("A2 + L1 torsion cap (measured sup |T|)", dict(base), "v1", 0),
        ("A3 + L2a classical constant (full-strip Bessel, ordered divisors)", dict(base), "classical", 5),
        ("A4 + L2b Omega_K through eta^N, average at full bite", dict(base, omega_eta=True, avg_full_bite=True), "classical", 5),
        ("A5 + L3 delta powers kept", dict(base, omega_eta=True, avg_full_bite=True, keep_delta=True), "classical", 5),
        ("A6 + L2c frequency-specific stage data (k = 5)", dict(base, omega_eta=True, avg_full_bite=True,
                                                                keep_delta=True), "freq", 5),
        ("A7 + L8 caps for tilde objects, free budgets", dict(base, omega_eta=True, avg_full_bite=True,
                                                              keep_delta=True, caps_tilde=True, free_budgets=True), "freq", 5),
    ]


def run_routeA(D, label="", only_last=False):
    out = []
    vs = routeA_variants(D)
    if only_last:
        vs = [vs[0], vs[-1]]
    for name, o, cw, k in vs:
        Dv = with_caps(D, F(1, 20)) if o.get("free_budgets") else D
        if o.get("torsion_cap") is not None:                # cap = initial sup|T| + its budget ((R3) with margin)
            o = dict(o); o["torsion_cap"] = Dv.get("Tsup_cap", D["Tsup"] + D["mu"] / 2)
            o["torsion_real"] = o["torsion_cap"]
        st, ct = c_stages(Dv, cw, max(k, 1))
        for iso in (False, True):
            lx, d0, why = thresholdA(Dv, o, iso, k=k, c_stage=st, c_tail=ct)
            out.append(dict(package=label, variant=name, form="iso" if iso else "fixed", log10_threshold=round(lx, 2),
                            binding=why))
            print("| %s | %s | %s | %.2f | %s |" % (label, name, "iso" if iso else "fixed", lx, ", ".join(why)))
    return out


def hybrid(D, label, A_meas):
    """L6: step 0 measured (new error eps_1 <= A_meas e^2 on T_{rho-2 delta0}; the measured increments of step 0 are
    O(e) and negligible), the derived scheme from stage 1 (best route-A and route-B variants started at the strip
    r_1 = rho - 3 delta0, bite delta0/2).  e* = sqrt(e_1*/A_meas)."""
    lam = 3
    delta0 = min(F(1), (D["rho"] - D["rhoinf"]) / (2 * lam))
    D1 = dict(D, rho=D["rho"] - 3 * delta0)
    out = []
    for route in ("A", "B"):
        for iso in (False, True):
            if route == "A":
                name, o, cw, k = routeA_variants(D1)[-1]
                Dv = with_caps(D1, F(1, 20))
                o = dict(o); o["torsion_cap"] = Dv["Tsup_cap"]; o["torsion_real"] = o["torsion_cap"]
                st, ct = c_stages(Dv, cw, max(k, 1))
                le1, _, why = thresholdA(Dv, o, iso, k=k, c_stage=st, c_tail=ct)
            else:
                Dv = with_caps(D1, F(1, 20))
                o = dict(L1=True, keep_delta=True, avg_full_bite=True, cTh=Dv["cTh"], theta=F(1, 16),
                         free_budgets=True, aniso=True)
                st, ct = c_stages(Dv, "freq", 5)
                le1, _, why = thresholdB(Dv, o, iso, 5, st, ct)
            le = (le1 - math.log10(A_meas)) / 2
            out.append(dict(package=label, variant="L6 hybrid (measured step 0), route %s from stage 1" % route,
                            form="iso" if iso else "fixed", log10_threshold=round(le, 2), log10_eps1=round(le1, 2)))
            print("| %s | L6 hybrid, route %s from stage 1 | %s | %.2f | eps_1* = 10^%.2f |" % (
                label, route, "iso" if iso else "fixed", le, le1))
    return out


A_MEAS_R1 = 7.28e-4      # |E_bar| <= 7.28e-4 e^2 on T_{rho-2 delta0} (scripts/apost_sharp/step0_actual.py, bound form)


def main():
    rows = []
    print("| package | variant | form | log10 threshold | binding |")
    print("|---|---|---|---:|---|")
    R1, H50 = package("R1"), package_H50()
    rows += run_routeA(R1, "R1")
    rows += run_routeB(R1, "R1 ")
    rows += hybrid(R1, "R1", A_MEAS_R1)
    rows += run_routeA(H50, "H50", only_last=True)
    rows += [dict(r, package="H50") for r in run_routeB(H50, "H50 ")[-2:]]
    if len(sys.argv) > 2 and sys.argv[1] == "--json":
        json.dump(dict(rows=rows), open(sys.argv[2], "w"), indent=1, default=str)



def run_routeB(D, label=""):
    """Cumulative table of route B on the package D."""
    out = []
    Tc = D["Tsup"]
    cT = D["cTh"]
    th = F(1, 16)
    common = dict(keep_delta=True, avg_full_bite=True, theta=th, selfcons=False)
    variants = [
        ("B0 modified step (L5), v1 data, cohConstR (FH24 structure)", dict(common, L1=False), "v1", 1),
        ("B1 + L1 finer data (incl. c_Th >= |T_h|)", dict(common, L1=True, cTh=cT), "v1", 1),
        ("B3 + L2a classical constant", dict(common, L1=True, cTh=cT), "classical", 5),
        ("B4 + L2c frequency-specific stage data (k = 5)", dict(common, L1=True, cTh=cT), "freq", 5),
        ("B5 + L8 free budgets (internal caps +5%)", dict(common, L1=True, cTh=cT, free_budgets=True), "freq", 5),
        ("B6 + L3b anisotropic stage-0 weight", dict(common, L1=True, cTh=cT, free_budgets=True, aniso=True), "freq", 5),
    ]
    for name, o, cw, k in variants:
        Dv = with_caps(D, F(1, 20)) if o.get("free_budgets") else D
        if o.get("torsion_cap") is not None:
            o = dict(o); o["torsion_cap"] = Dv.get("Tsup_cap", D["Tsup"]); o["torsion_real"] = o["torsion_cap"]
        st, ct = c_stages(Dv, cw, max(k, 1))
        for iso in (False, True):
            le, d0, why = thresholdB(Dv, o, iso, k, st, ct)
            out.append(dict(variant=name, form="iso" if iso else "fixed", log10_threshold=round(le, 2), binding=why))
            print("| %s%s | %s | %.2f | %s |" % (label, name, "iso" if iso else "fixed", le, ", ".join(why)))
    # B7: the levers of the fair comparison (design section 11): schedule ratio a, tail decay bound, L10; the best
    # admissible choice (each is a free parameter of the theorem), floating point
    Dv = with_caps(D, F(1, 20))
    Dvf = {k_: (float(v) if isinstance(v, F) else v) for k_, v in Dv.items()}
    gam = float(D["gamma"]); om = D["omega_star"]; n_, tau_ = D["n"], int(D["tau"])
    cache = {}

    def cf(d):
        d = float(d)
        if d not in cache:
            cache[d] = min(sd.c_freq(om, gam, tau_, d)[0], sd.c_classical(n_, tau_, d))
        return cache[d]
    stf = lambda ds, r: (cf(ds), cf(ds * tau_ / (tau_ + 1)), cf(min(r, 1.0)))
    stf.by_bite = True
    for iso in (False, True):
        best = (-1e9, None, None)
        for a, k in ((F(2), 5), (F(3, 2), 9)):
            for ym in (F(1, 2), F(9, 10)):
                for sc in (False, True):
                    d0 = float((D["rho"] - D["rhoinf"]) * (a - 1) / (3 * a))
                    rk = float(D["rho"]) - 3 * d0 * (1 - float(a) ** -k) / (1 - 1 / float(a))
                    ct = (sd.c_classical(n_, tau_, d0 / float(a) ** k), sd.c_classical(n_, tau_, min(rk, 1.0)))
                    o = dict(common, L1=True, cTh=Dvf["cTh"], free_budgets=True, aniso=True, ratio=a, ymax=ym,
                             selfcons=sc)
                    le, _, why = thresholdB(Dvf, o, iso, k, stf, ct)
                    if le > best[0]:
                        best = (le, why, (float(a), k, float(ym), sc))
        name = "B7 + L4' schedule ratio, J2 decay bound, L10 self-consistent eta^L (best choice %s)" % (best[2],)
        out.append(dict(variant=name, form="iso" if iso else "fixed", log10_threshold=round(best[0], 2),
                        binding=best[1]))
        print("| %s%s | %s | %.2f | %s |" % (label, name, "iso" if iso else "fixed", best[0], ", ".join(best[1])))
    return out


if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "--routeB":
    run_routeB(package("R1"))


if __name__ == "__main__" and (len(sys.argv) == 1 or sys.argv[1] == "--json"):
    main()
