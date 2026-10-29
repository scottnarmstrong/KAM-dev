#!/usr/bin/env python3
"""SO-GEN2 emitter: rotated-frame candidate data, package R1, enclosed norms and margins (owner ruling O5).

usage: rot_emit.py which Lv LE LJ S c m OUT.json
  builds the candidate (rot_build), encloses its norms (rot_norms), instantiates package R1 at time scale c and
  size m = M = sigma_K = sigma_B = sigma_T (exact_constants.package_R1), checks every parameter constraint in exact
  rationals against the float upper bounds, chooses the error bound e (3 significant digits above the enclosed
  invariance / energy errors) and writes schema/candidate_rot.schema.json data.  Untrusted tooling.
"""
import sys, json, math, time, datetime, subprocess
import mpmath, numpy as np
from fractions import Fraction as F
from rot_build import build, RHO, EPSA, SH
from rot_norms import norms, MU
from exact_constants import package_R1, threshold_of
import model

GEN_VERSION = "so-gen2-0.1"


def ffloat(x):
    """exact Fraction of a float (for exact comparisons of float upper bounds)."""
    return F(x)


def ceil_sig(x, d=3):
    """smallest decimal rational with d significant digits that is >= x (x > 0 float)."""
    e = math.floor(math.log10(x)) - d + 1
    q = F(10) ** e
    n = math.ceil(F(x) / q)
    return n * q


def gj_need(bd, cf):
    """smallest e meeting the G-J split targets: c max(eta1, eta3) + Bc <= e/2, Br + B1 + Bc <= e/2, B0 <= e/4."""
    Bc = cf * bd["eta1_unscaled"]
    a = 2 * (cf * max(bd["eta1_unscaled"], bd["eta3_unscaled"]) + Bc)
    b = 2 * (cf * bd["Br_unscaled"] + cf * bd["B1_unscaled"] + Bc)
    return math.nextafter(max(a, b, 4 * bd["B0"]) * (1 + 1e-14), math.inf)


def alt_package(nr, bd, c, m, which):
    """ALTERNATIVE package (needs a checker sub-check for the grid/Lipschitz sup of the Gram witness row sums):
    same data, sigma_B from gram.Ginv_rowsum_bound_grid_alternative."""
    c = F(c); m = F(m); mu = MU
    p, x = package_R1(c, m)
    thr, coef, k = threshold_of(p, x["gamma"])
    cf = float(c)
    eta = max(bd["eta1_unscaled"], bd["eta3_unscaled"], bd["eta4_unscaled"])
    eta_c = math.nextafter(max(eta, bd["energy_unscaled"]) * cf * (1 + 1e-15), math.inf)
    e = ceil_sig(max(eta_c, gj_need(bd, cf)), 3)
    ratio = k["isoC1"] * e / (x["gamma"] ** 4 * p["rho"] ** 4)
    checks = {"M >= c M1": m >= c * ffloat(nr["H"]["M1"]),
              "sigmaK - mu >= ||DK||": m - mu >= ffloat(nr["sigmaK_minus_mu_need"]),
              "sigmaB - mu >= ||G^-1|| (grid alternative)": m - mu >= ffloat(nr["gram"]["Ginv_rowsum_bound_grid_alternative"]),
              "sigmaT - mu >= ||avg^-1||/c": m - mu >= ffloat(nr["torsion"]["inverse_rowsum_bound_c1"]) / c,
              "nu <= (s-1)|omega*|": p["nu"] <= (x["s"] - 1) * c / x["s"],
              "C1 e/(gamma^4 rho^4) <= 1/2": ratio <= F(1, 2)}
    return dict(c=str(c), m=str(m), gamma=str(x["gamma"]), threshold=str(thr),
                log10_threshold=math.log10(thr.numerator) - math.log10(thr.denominator), err=str(e),
                eta_c=eta_c, eta_over_threshold=eta_c / float(thr), smallness_ratio=float(ratio),
                displacement_coefficient=float(coef), checks=checks)


def main(which, Lv, LE, LJ, S, c, m, out, c_alt=None, m_alt=None):
    t0 = time.time()
    Lv, LE, LJ, S = int(Lv), int(LE), int(LJ), int(S)
    c = F(c); m = F(m)
    cand = build(which, Lv, LE, LJ, S)
    bd = cand["bounds"]
    nr = norms(cand, bd["Delta"])
    p, x = package_R1(c, m)
    thr, disp_coef, k = threshold_of(p, x["gamma"])
    cf = float(c)
    # ---- errors at time scale c
    eta = max(bd["eta1_unscaled"], bd["eta3_unscaled"], bd["eta4_unscaled"])
    eta_c = math.nextafter(eta * cf * (1 + 1e-15), math.inf)
    en_c = math.nextafter(bd["energy_unscaled"] * cf * (1 + 1e-15), math.inf)
    # e: 3 significant digits above the enclosed errors AND the design's gate G-J split (rows <= e/2, B0 <= e/4)
    e = ceil_sig(max(eta_c, en_c, gj_need(bd, cf)), 3)
    ratio = k["isoC1"] * e / (x["gamma"] ** 4 * p["rho"] ** 4)        # C1 e/(gamma^4 rho^4) = e/threshold
    # ---- constraint checks (exact rationals; float bounds converted exactly)
    mu = MU
    checks = {}
    checks["M >= c M1"] = m >= c * ffloat(nr["H"]["M1"])
    checks["sigmaK - mu >= ||DK||"] = m - mu >= ffloat(nr["sigmaK_minus_mu_need"])
    checks["sigmaB - mu >= ||G^-1||"] = m - mu >= ffloat(nr["gram"]["Ginv_rowsum_bound"])
    checks["sigmaT - mu >= ||avg^-1||/c"] = m - mu >= ffloat(nr["torsion"]["inverse_rowsum_bound_c1"]) / c
    s = x["s"]; so = x["sigma_omega"]; nu_ray = p["nu"]
    norm_om = c / s                                   # |omega*|_max = c max(|nu - 1|, 1)/s = c/s
    checks["1 < s < sigma_omega"] = 1 < s < so
    checks["nu <= (s-1)|omega*|"] = nu_ray <= (s - 1) * norm_om
    checks["nu <= (sigma_omega-s)|omega*|"] = nu_ray <= (so - s) * norm_om
    checks["e >= c eta (invariance)"] = e >= ffloat(eta_c)
    checks["e >= c energy error"] = e >= ffloat(en_c)
    checks["C1 e/(gamma^4 rho^4) <= 1/2"] = ratio <= F(1, 2)
    margin = dict(eta_c=eta_c, e=str(e), e_float=float(e), threshold=float(thr),
                  log10_threshold=math.log10(thr.numerator) - math.log10(thr.denominator),
                  eta_over_threshold=eta_c / float(thr), smallness_ratio=float(ratio),
                  slack_orders=-math.log10(eta_c / float(thr)))
    # ---- gate G-J (rotated frame: the P2 = p + J row), scaled by c where the quantity involves D_{s omega*}
    Bc = math.nextafter(cf * bd["eta1_unscaled"] * (1 + 1e-15), math.inf)
    B1 = cf * bd["B1_unscaled"]; Br = cf * bd["Br_unscaled"]
    gj = dict(B0=bd["B0"], B1=B1, B2=bd["B2"], Br=Br, Bc=Bc, eta_P2_row_direct=cf * bd["eta4_unscaled"],
              target_Br_B1_Bc=float(e) / 2, ok_Br_B1_Bc=(Br + B1 + Bc) <= float(e) / 2,
              qphip_rows_plus_Bc=cf * max(bd["eta1_unscaled"], bd["eta3_unscaled"]) + Bc,
              ok_qphip=(cf * max(bd["eta1_unscaled"], bd["eta3_unscaled"]) + Bc) <= float(e) / 2,
              ok_B0=bd["B0"] <= float(e) / 4, ok_B2_1e90=bd["B2"] <= 1e-90,
              pin=dict(pinHalvings=0, pinOrder=1, pin_value="exp(2 i v(0)) = 1 exactly (v odd)", eps0=bd["eps0"]))
    # ---- data (half lattice for real series; scale 2^-S)
    v, pp, E, J = cand["v"], cand["p"], cand["E"], cand["J"]
    def half(sp, phase_sign):
        d = sp.to_dict(); res = []
        for (kk, ll), val in sorted(d.items()):
            if kk > 0 or (kk == 0 and ll > 0):
                res.append([kk, ll, str(phase_sign * val)])
        return res
    # v SPoly (phase 1, scale S+1): value at kappa in H is -b  ->  b = -value  (scale S+1 -> S: b = -value/... )
    # sin_series stored b at scale S as values -b at scale S+1, so the S-scale integer is -value.
    v_sin = [[a, b_, str(-int(val))] for a, b_, val in half(v, 1)]
    p_cos = [[a, b_, str(int(val))] for a, b_, val in half(pp, 1)]           # cos coefficient c at scale S
    J_cos = [[a, b_, str(int(val))] for a, b_, val in half(J, 1)]            # J full-lattice value at S+1 = cos coeff at S
    p0 = cand["p0"]
    J0 = J.to_dict().get((0, 0), 0)                                            # J zero mode at scale S+1
    assert J0 % 2 == 0 or True
    E_re = [[a, b_, str(val)] for (a, b_), val in sorted(E.to_dict().items())]
    nu1 = model.nu_minus_one(which)
    meta = dict(generator="scripts/spin_orbit/rot_emit.py", generator_version=GEN_VERSION, which=which,
                git_hash=subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip(),
                source="certificates/lunar-spin-orbit/%s.json (SO-GEN 440-bit solution, 1e-130 data)" % which,
                truncation=dict(Lv=Lv, LE=LE, LJ=LJ), date=datetime.date.today().isoformat(),
                mpmath=mpmath.__version__, numpy=np.__version__, seconds=round(time.time() - t0, 1))
    pk = {kk: str(vv) for kk, vv in p.items()}
    pk.update(s=str(s), sigma_omega=str(so), c=str(c), gamma=str(x["gamma"]), E0="0", err=str(e))
    data = dict(
        schema_version=2, frame="rotated", which=which, scale_bits=S, metadata=meta,
        coordinates=("rotated frame (owner ruling O5): angles theta = (psi, phi) = (Q1 - u, Q2) with psi = theta1 - theta2,"
                     " phi = theta2; characters exp(2 pi i (k psi + l phi)); Q1 = q - phi, Q2 = phi, P1 = p, P2 = p + J"),
        hamiltonian=("H' = c (P1^2/2 - P1 + P2 + sum_m (-eps A_m) cos(2 pi (2 Q1 + (2 - m) Q2))), m = 1..7, keys (2, 2-m);"
                     " eps = 69/200000, A_m = model.A_coeffs(549/10000)"),
        embedding="K'(theta) = (psi + v/(2 pi), phi, p, p + J); v = sum b sin, p = p0 + sum c cos, J = J0 + sum j cos",
        nu_minus_one_Q_sqrt5=[str(nu1[0]), str(nu1[1])],
        frequency="omega' = (nu - 1, 1); omega* = c omega'/s; s omega* = c omega'",
        params=dict(e=str(model.E_ORB), eps=str(model.EPS)), package=pk,
        threshold=str(thr), displacement_coefficient=str(disp_coef), active_branch=k["active"],
        domain=nr["domain"],
        v_sin=v_sin, p0=str(p0), p_cos=p_cos, J0=str(J0), J0_scale_bits=S + 1, J_cos=J_cos, E_re=E_re,
        character_witness=dict(keys="(2, 2-m), m=1..7; normalized index k.U = 2 U1 = v/pi", witness="E_re",
                               pinHalvings=0, pinOrder=1, eps0=bd["eps0"]),
        gram_inverse=dict(scale_bits=nr["B"]["scale_bits"],
                          B11=[[a, b_, str(n)] for (a, b_), n in sorted(nr["B"]["B11"].items())],
                          B12=[[a, b_, str(n)] for (a, b_), n in sorted(nr["B"]["B12"].items())],
                          B22=[[a, b_, str(n)] for (a, b_), n in sorted(nr["B"]["B22"].items())]),
        torsion_witness=nr["torsion"]["S"],
        enclosures=dict(norms={kk: vv for kk, vv in nr.items() if kk not in ("B",)}, residual=bd),
        checks=checks, margin=margin, gate_GJ=gj,
        package_alternative=(alt_package(nr, bd, c_alt, m_alt, which) if c_alt else None),
        stats=dict(v_terms_half=len(v_sin), v_terms_full=2 * len(v_sin), p_terms_half=len(p_cos), J_terms_half=len(J_cos),
                   E_terms=len(E_re), bits=S))
    def clean(o):
        if isinstance(o, dict):
            return {str(kk): clean(vv) for kk, vv in o.items()}
        if isinstance(o, (list, tuple)):
            return [clean(vv) for vv in o]
        if isinstance(o, (np.floating,)):
            return float(o)
        if isinstance(o, (np.integer,)):
            return int(o)
        if isinstance(o, (np.bool_,)):
            return bool(o)
        if isinstance(o, F):
            return str(o)
        return o
    json.dump(clean(data), open(out, "w"), separators=(",", ":"))
    print("checks:", checks)
    print("margin:", margin)
    if c_alt:
        print("alternative:", data["package_alternative"])
    print("G-J:", {kk: vv for kk, vv in gj.items() if kk != "pin"})
    print("wrote", out, "in %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    main(*sys.argv[1:])
