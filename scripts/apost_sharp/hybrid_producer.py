#!/usr/bin/env python3
"""The hybrid producer (package SHARP2-C8D, C8d first part; format docs/campaign/design/hybrid/format.md).

Untrusted tooling.  Writes `kam-hybrid` v1 files: the finite candidate K^, the finite step DK^, the composition witness W,
the Gram and torsion witnesses of K^, the (advisory) models of E and E_lin~, the step claims, and the restart numbers
(`params1`, `witness1`) of the restarted route-A' run, all consistent with the exact mirror (hybrid_mirror.py), whose
transfer this producer calls.

  R1-L8   R1's L = 8 finite candidate in the design package (c = 7/4, `r1Params`, `r1Claim`, `r1RefinedWitR`):
          K^ = (psi + v^/(2 pi), phi, P1^, P2^) with v^ = R1's v cut at 10^-8 and rounded to 2^-S (the stored angle,
          degree -1), P1^ = nu + D_t U rounded, P2^ = P1^ + J^ (J truncated at 10^-3 e, rounded); DK^ the isoenergetic
          step of K^ (truncated at 10^-3 e^2, rounded; angle components stored with degree -1).  Floating measurements on
          512 x 128 shifted grids (hybrid_cert_r1.py); polynomial claims exact (the mirror's norms); kernel-only claims are
          the floating values x 1.10.
  T2      the toy T2 (KAM/Certificate/Tests/Toy2Data.lean, toyRefinedWitR) with the zero step: its residual is the width
          of its frequency box, which no step can reduce (format.md, design note F3: the hybrid branch is not claimed to
          reproduce the plain one; the mirror shows the cost).

Also writes the Lean data of the R1-scale kernel test (kernel-tests/CertificateSharp/V2/HybridR1L8Data.lean; not
built; module KAM.CertificateSharp.V2.Tests.HybridR1L8Data when placed back under KAM/, as kernel-tests/README.md says).

Usage:  python3 -I scripts/apost_sharp/hybrid_producer.py [--out DIR] [--lean DIR] [--only R1-L8|T2]
"""
import json, math, os, sys, time
from fractions import Fraction as F
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hybrid_cert_r1 as H        # noqa: E402  finite pipeline (FinTorus, step_fin, coef_from_corners, trunc_tail)
import hybrid_mirror as HM        # noqa: E402  exact transfer and norms
import hybrid_numq as NQ          # noqa: E402  exact route-A' port
import step0_actual as S0         # noqa: E402
import r1_norms                   # noqa: E402

S = 60
TWO_PI = 2 * math.pi


def mant(x):
    return str(int(round(F(x) * 2 ** S))) if isinstance(x, F) else str(int(round(x * 2 ** S)))


def fq(x):
    return str(x.numerator) if x.denominator == 1 else "%d/%d" % (x.numerator, x.denominator)


def rup(x, digits=12):
    """a rational upper bound of x >= 0 with `digits` significant digits."""
    x = F(x)
    if x <= 0:
        return F(0) if x == 0 else x
    e = math.floor(math.log10(float(x))) - digits
    return F(math.ceil(x / F(10) ** e)) * F(10) ** e


def rdown(x, digits=12):
    x = F(x)
    if x <= 0:
        return x
    e = math.floor(math.log10(float(x))) - digits
    return F(math.floor(x / F(10) ** e)) * F(10) ** e


def realpoly(C, G, scale=1.0):
    """a real function's full-lattice coefficient array (conjugate-symmetric) -> CertRealPoly of scale*C."""
    N1, N2 = G.N1, G.N2
    half = []
    for i in range(N1):
        for j in range(N2):
            k, l = int(G.kk[i, j]), int(G.ll[i, j])
            if (k > 0 or (k == 0 and l > 0)) and C[i, j] != 0:
                c = C[i, j] * scale
                half.append([[k, l], [mant(c.real), mant(c.imag)]])
    return {"zero": mant(C[0, 0].real * scale), "half": half}


def certpoly(C, G, real_only=False):
    out = []
    for i in range(G.N1):
        for j in range(G.N2):
            if C[i, j] != 0:
                c = C[i, j]
                out.append([[int(G.kk[i, j]), int(G.ll[i, j])], [mant(c.real), "0" if real_only else mant(c.imag)]])
    return out


def round_dyadic(C, scale=1.0):
    """C such that scale*C is dyadic at 2^-S (the stored data define the object)."""
    s = 2.0 ** S
    return (np.round(C.real * scale * s) + 1j * np.round(C.imag * scale * s)) / s / scale


def weight(r):
    w = HM.exp_up(2 * HM.PI_HI * F(r))
    return {"rho": fq(F(r)) if r else "0", "w": fq(rup(w, 15))}


# ============================================================================================ R1, L = 8
def produce_r1(Ld=8, out_dir=None, lean_dir=None, log=print):
    t0 = time.time()
    rho, rhoinf = S0.RHO, S0.RHOINF
    G = S0.Grid(512, 128)
    co = r1_norms.load("lower", 10.0 ** (-Ld))
    N1, N2 = G.N1, G.N2
    V = np.zeros((N1, N2), complex)                       # v = sum b sin: coefficient b/(2i) on k, -b/(2i) on -k
    for k, l, b in co:
        V[k % N1, l % N2] += b / 2j
        V[(-k) % N1, (-l) % N2] += -b / 2j
    V = round_dyadic(V)                                   # the stored angle v^ (degree -1)
    U = V / TWO_PI
    lam = (G.cand.nu - 1) * G.kk + G.ll
    P1 = 2j * math.pi * lam * U
    P1[0, 0] += G.cand.nu
    P1 = round_dyadic(P1)
    K0 = H.FinTorus(G, U, P1, P1)
    Ef = []
    Js = []
    for y in ((rho, rho), (rho, -rho)):
        g = K0.geom(y)
        Js.append(-g["p"] ** 2 / 2 - g["V"])
    CJ = H.coef_from_corners(G, Js[0], Js[1], rho)
    Kf = H.FinTorus(G, U, P1, P1 + CJ)                    # J whole: the analytic residual scale
    for y in ((rho, rho), (rho, -rho)):
        Ef.append(Kf.objects(y)["E"])
    e_an = H.vec_norm(H.l1w(G, Ef[0], Ef[1]))
    CJh = H.trunc_tail(G, CJ, rho, 1e-3 * e_an, S)
    K = H.FinTorus(G, U, P1, round_dyadic(P1 + CJh))
    # the step, emitted as a finite polynomial
    _, consts, o0 = H.step_fin(K, (0.0, 0.0))
    xiw = float(np.round(np.real(consts[1]) * 2.0 ** S) / 2.0 ** S)
    dKc = [H.step_fin(K, y, consts)[0] for y in ((rho, rho), (rho, -rho))]
    CdK = H.trunc_tail(G, H.coef_from_corners(G, dKc[0], dKc[1], rho), rho, 1e-3 * e_an ** 2, S)
    for i in (0, 1):                                      # angle components stored as 2 pi dQ (degree -1)
        CdK[..., i] = round_dyadic(CdK[..., i], TWO_PI)
    for i in (2, 3):
        CdK[..., i] = round_dyadic(CdK[..., i])
    # floating measurements with the stored objects (hybrid_cert_r1.finite_measure's formulas)
    tk = (2j * math.pi * G.kk)[..., None]; tl = (2j * math.pi * G.ll)[..., None]
    meas = {}
    for name, r in (("rho1", rho), ("real", 0.0)):
        if r == 0.0:
            ob = K.objects((0.0, 0.0)); dK = K.eval4(CdK, (0.0, 0.0))
            L1 = ob["L"] + np.stack([K.eval4(CdK * tk, (0.0, 0.0)), K.eval4(CdK * tl, (0.0, 0.0))], axis=-1)
            OmK = S0.mm(np.swapaxes(ob["L"], -1, -2), S0.mm(H.OM, ob["L"]))
            OmK1 = S0.mm(np.swapaxes(L1, -1, -2), S0.mm(H.OM, L1))
            meas[name] = dict(DE=H.mat_norm(H.l1w_real(G, H.deriv(G, ob["E"]))), OmK=H.mat_norm(H.l1w_real(G, OmK)),
                              OmK1=H.mat_norm(H.l1w_real(G, OmK1)))
            meas["energy_lin"] = abs(G.coef_at(ob["H"])[0, 0] + np.mean(np.einsum("...a,...a->...", ob["DH"], dK)))
            continue
        res = []
        for y in ((r, r), (r, -r)):
            ob = K.objects(y)
            dK = K.eval4(CdK, y)
            dwdK = K.eval4(CdK * G.mult[..., None], y)
            DdK = np.stack([K.eval4(CdK * tk, y), K.eval4(CdK * tl, y)], axis=-1)
            Elin = ob["E"] + S0.mv(ob["A"], dK) - dwdK + xiw * (ob["dwK"] + dwdK)
            E1 = ob["E"] + H.dXH(ob["g"], dK) - dwdK + xiw * (ob["dwK"] + dwdK)
            L1 = ob["L"] + DdK
            res.append(dict(E=ob["E"], Elin=Elin, E1=E1, DE=H.deriv(G, ob["E"]),
                            OmK=S0.mm(np.swapaxes(ob["L"], -1, -2), S0.mm(H.OM, ob["L"])),
                            OmK1=S0.mm(np.swapaxes(L1, -1, -2), S0.mm(H.OM, L1))))
        a, b = res
        meas[name] = dict(e=H.vec_norm(H.l1w(G, a["E"], b["E"])), Elin=H.vec_norm(H.l1w(G, a["Elin"], b["Elin"])),
                          E1_sup=H.sup_vec(a["E1"], b["E1"]), DE=H.mat_norm(H.l1w(G, a["DE"], b["DE"])),
                          OmK=H.mat_norm(H.l1w(G, a["OmK"], b["OmK"])), OmK1=H.mat_norm(H.l1w(G, a["OmK1"], b["OmK1"])))
        CE = H.coef_from_corners(G, a["E"], b["E"], r)
        CEl = H.coef_from_corners(G, a["Elin"], b["Elin"], r)
    # witnesses of K^
    Wc = [np.exp(2j * K.geom(y)["u"] * TWO_PI) for y in ((rho, rho), (rho, -rho))]
    CW = H.trunc_tail(G, H.coef_from_corners(G, Wc[0], Wc[1], rho), rho, 2e-13, S)
    Bc = [K.objects(y)["B"] for y in ((rho, rho), (rho, -rho))]
    CB = H.coef_from_corners(G, Bc[0], Bc[1], rho)
    CB = np.stack([np.stack([H.trunc_tail(G, CB[..., i, j], rho, 1e-12, S) for j in range(2)], axis=-1)
                   for i in range(2)], axis=-2)
    ext = np.zeros((3, 3), complex)
    ext[:2, :2] = G.coef_at(o0["T"])[0, 0]; ext[:2, 2] = G.omega; ext[2, :2] = G.coef_at(o0["Y"])[0, 0]
    extinv = np.linalg.inv(ext)
    log("  R1-L%d: v^ %d, J^ %d, DK^ %s terms; e %.4g (analytic %.4g); E_lin~ %.4g, E1 sup %.4g (%.0fs)" % (
        Ld, len(co), int(np.count_nonzero(CJh)), [int(np.count_nonzero(CdK[..., i])) for i in range(4)],
        meas["rho1"]["e"], e_an, meas["rho1"]["Elin"], meas["rho1"]["E1_sup"], time.time() - t0))
    # the data
    emb = {"angleDeg": [-1, 0], "angle": [realpoly(V, G), realpoly(np.zeros_like(V), G)], "actionDeg": [0, 0],
           "action": [realpoly(K.P1, G), realpoly(K.P2, G)]}
    dKe = {"angleDeg": [-1, -1], "angle": [realpoly(CdK[..., 0], G, TWO_PI), realpoly(CdK[..., 1], G, TWO_PI)],
           "actionDeg": [0, 0], "action": [realpoly(CdK[..., 2], G), realpoly(CdK[..., 3], G)]}
    dl1 = min(1.0, (rho - rhoinf) / 6)
    Wt = {"rho1": weight(F(1, 70)), "rhoinf": weight(F(1, 70000)), "real": {"rho": "0", "w": "1"},
          "torsion": weight(F(1, 70) - min(F(1), (F(1, 70) - F(1, 70000)) / 6))}
    s0 = 1 + F(1, 10 ** 6)
    xiw_q = F(int(round(xiw * 2 ** S)), 2 ** S)
    s1 = s0 * (1 - xiw_q)
    n = 2
    exact_dK = HM.emb_from(dKe, S)
    v1, D1, D1t = HM.step_norms(exact_dK, n, F(Wt["rho1"]["w"]))
    vi, _, _ = HM.step_norms(exact_dK, n, F(Wt["rhoinf"]["w"]))
    vR, DR, DRt = HM.step_norms(exact_dK, n, F(1))
    k10 = lambda x: rup(F(x) * F(110, 100))
    claims = dict(d0=rup(v1), dinf=rup(vi), d1=rup(D1), d1t=rup(D1t), d0R=rup(vR), d1R=rup(DR), d1tR=rup(DRt),
                  lE=k10(meas["rho1"]["Elin"]), dE0=k10(meas["rho1"]["DE"]), o0=k10(meas["rho1"]["OmK"]),
                  dE0R=k10(meas["real"]["DE"]), o0R=k10(meas["real"]["OmK"]), o1=k10(meas["rho1"]["OmK1"]),
                  o1R=k10(meas["real"]["OmK1"]), lH=k10(meas["energy_lin"]) + F(1, 10 ** 30),
                  dw=rup(abs(s1 - s0) * NQ.box_norm_up(NQ.R1_BOX)))
    base_p = NQ.r1_params(rup(F(meas["rho1"]["e"]) * F(110, 100)), F(1, 300))
    mu = base_p["mu"]
    mu1 = mu - rup(2 * max(claims["d0"], claims["d1"])) - F(1, 10 ** 12)
    data = assemble("R1-L8", "R1 design package (c = 7/4; r1Params, r1Claim, r1RefinedWitR, r1Box)", n, base_p,
                    NQ.R1_BOX, NQ.R1_CLAIM, emb, dKe, Wt, claims, F(1, 70), mu1, s1, NQ.R1_WIT_R, log)
    data["base"]["witnesses"] = {"exp": certpoly(CW, G, real_only=True),
                                 "gramInv": [[certpoly(CB[..., i, j], G) for j in range(2)] for i in range(2)],
                                 "torsInv": [[[str(F(float(np.real(extinv[i, j]))).limit_denominator(10 ** 12)), "0"]
                                              for j in range(3)] for i in range(3)]}
    data["models"] = {"E": model(CE, G, rho, 1e-13), "Elin": model(CEl, G, rho, 1e-15),
                      "note": "advisory: floating models on T_rho1 (support, rounded coefficients, tail mass); the kernel "
                              "computes its own"}
    data["measured"] = {k: ({kk: float(vv) for kk, vv in v.items()} if isinstance(v, dict) else float(v))
                        for k, v in meas.items()}
    data["measured"]["e_analytic"] = e_an
    data["measured"]["supports"] = dict(v=len(co), J=int(np.count_nonzero(CJh)), U=int(np.count_nonzero(V)),
                                        P1=int(np.count_nonzero(K.P1)), P2=int(np.count_nonzero(K.P2)),
                                        dK=[int(np.count_nonzero(CdK[..., i])) for i in range(4)],
                                        W=int(np.count_nonzero(CW)),
                                        gramInv=[[int(np.count_nonzero(CB[..., i, j])) for j in range(2)]
                                                 for i in range(2)])
    write(data, out_dir, "hybrid-R1-L%d.json" % Ld, log)
    if lean_dir:
        write_lean(data, lean_dir, log)
    return data


def model(C, G, r, tol):
    out = []
    for i in range(C.shape[-1]):
        Ci = H.trunc_tail(G, C[..., i], r, tol, S)
        w = H.wts(G, r)
        tail = float((np.abs(C[..., i] - Ci) * w).sum())
        out.append({"deg": 0, "poly": certpoly(Ci, G), "rad": fq(rup(F(tail) + F(1, 10 ** 30)))})
    return out


# ============================================================================================ assembly (shared)
def assemble(name, package, n, base_p, box, claim, emb, dKe, Wt, claims, rho1, mu1, s1, plain_wit, log):
    """the restart numbers from the exact transfer (hybrid_mirror.transfer), and the file."""
    tr, sl = HM.transfer(n, base_p, claim, claims, rho1, mu1, iso=True)
    if tr is None:
        raise SystemExit("%s: transfer fails: %s" % (name, {k: v for k, v in sl.items() if not v}))
    p1 = dict(base_p)
    p1.update(rho=rho1, mu=mu1, sK=tr["sK1"], sB=rup(tr["sB1"]), sT=rup(tr["sT1"]), err=rup(tr["e1"]),
              nuRay=rdown(tr["nuRay1"]), s=s1)
    core = dict(plain_wit["base"]["core"])
    R1 = dict(claim)
    R1.update(bL=rup(tr["bL1"]), bN=rup(tr["bN1"]), bNt=rup(tr["bNt1"]), bT=rup(tr["bT1"]))
    # the |T| cap of the restarted run follows its initial value (budgetOk: iH + bT + 2 bF <= t)
    core["t"] = core["t"] + (R1["bT"] - claim["bT"])
    w1 = dict(base=dict(core=core, R=R1, kappa=plain_wit["base"]["kappa"], sites=plain_wit["base"]["sites"]),
              bF=plain_wit["bF"], bT=plain_wit["bT"])
    p1["disp"] = F(1)                                     # provisional, for X*_max
    Xmax, Q1 = NQ.max_xs(n, p1, box, w1, lo=core["Xs"] / 4)
    core["Xs"] = rdown(Xmax * F(999, 1000), 8)
    c23 = max(Q1.c2Q(core["Xs"]), Q1.c3Q(core["Xs"]))
    p1["disp"] = rup(c23 * p1["err"] / (p1["gamma"] ** 2 * p1["rho"] ** (2 * p1["tau"])))
    base_p = dict(base_p)
    base_p["disp"] = rup(max(claims["dinf"], claims["dw"]) + p1["disp"])
    enc = lambda d: {k: (str(v) if k == "tau" else fq(F(v))) for k, v in d.items()}
    encw = lambda w: {"base": {"core": {k: ([fq(x) for x in v] if isinstance(v, list) else
                                            (str(v) if k in ("kp", "J") else fq(v)))
                                        for k, v in w["base"]["core"].items()},
                               "R": {k: fq(v) for k, v in w["base"]["R"].items()}, "kappa": fq(w["base"]["kappa"]),
                               "sites": w["base"]["sites"]}, "bF": fq(w["bF"]), "bT": fq(w["bT"])}
    return {"format": "kam-hybrid", "version": 1, "name": name, "package": package, "n": n, "scale_bits": S,
            "base": {"params": enc(base_p), "freqBox": [[fq(c), fq(r)] for c, r in box],
                     "emb": emb, "claim": {k: fq(v) for k, v in claim.items()}},
            "step": {"iso": True, "dK": dKe, "s1": fq(s1), "rho1": fq(rho1), "mu1": fq(mu1), "weights": Wt,
                     "claims": {k: fq(v) for k, v in claims.items()},
                     "kernel_only": ["lE", "dE0", "dE0R", "o0", "o0R", "o1", "o1R", "lH"]},
            "restart": {"params1": enc(p1), "witness1": encw(w1),
                        "sites": "reuse-base" if rho1 == base_p["rho"] else "list",
                        "transferred": {k: fq(v) for k, v in tr.items()}},
            "plain_witness": encw(plain_wit)}


def write(data, out_dir, fname, log):
    if out_dir:
        os.makedirs(out_dir, exist_ok=True)
        p = os.path.join(out_dir, fname)
        json.dump(data, open(p, "w"), indent=None, separators=(",", ":"))
        log("  wrote %s (%d bytes)" % (p, os.path.getsize(p)))


# ============================================================================================ T2
def produce_t2(out_dir=None, log=print):
    p = dict(NQ.TOY_PARAMS)
    n = 2
    zero = {"zero": "0", "half": []}
    emb = {"angleDeg": [0, 0], "angle": [zero, zero], "actionDeg": [0, 0],
           "action": [{"zero": mant(NQ.TOY_NU), "half": []},
                      {"zero": mant(-NQ.TOY_NU ** 2 / 2), "half": []}]}
    # the exact action values are not dyadic: the toy's own emb (Toy2Data.lean) is exact; this field is the
    # 2^-60 rounding, marked in `note`; the hybrid test reads only the step and the claims
    dKe = {"angleDeg": [0, 0], "angle": [zero, zero], "actionDeg": [0, 0], "action": [zero, zero]}
    Wt = {"rho1": weight(F(9)), "rhoinf": weight(F(1)), "real": {"rho": "0", "w": "1"}, "torsion": weight(F(8))}
    err = p["err"]
    dl1 = min(F(1), (p["rho"] - p["rhoInf"]) / 6)
    claims = dict(d0=F(0), dinf=F(0), d1=F(0), d1t=F(0), d0R=F(0), d1R=F(0), d1tR=F(0), lE=err,
                  dE0=n * err / dl1, o0=F(0), dE0R=n * err / dl1, o0R=F(0), o1=F(0), o1R=F(0), lH=F(0), dw=F(0))
    mu1 = p["mu"] * (1 - F(1, 10 ** 6))
    data = assemble("T2", "toy T2 (KAM/Certificate/Tests/Toy2Data.lean; toyRefinedWitR)", n, p, NQ.TOY_BOX,
                    NQ.TOY_WIT_R["base"]["R"], emb, dKe, Wt, claims, p["rho"], mu1, p["s"], NQ.TOY_WIT_R, log)
    data["note"] = ("zero step: the toy's residual is the width of its frequency box (no step reduces it); the base "
                    "embedding's actions are the 2^-60 roundings of the toy's exact rationals (the hybrid test reads only "
                    "the step, the claims and the numbers)")
    write(data, out_dir, "hybrid-T2.json", log)
    return data


# ============================================================================================ Lean data (kernel test)
def lean_q(x):
    x = F(x)
    return "(%d : ℚ)" % x.numerator if x.denominator == 1 else "(%d / %d : ℚ)" % (x.numerator, x.denominator)


CHUNK = 40     # terms per Lean declaration: heartbeats are per declaration (hard rule 1: split, never raise)


def lean_m(m):
    """A mantissa at 2^S through the exposed helper `q60`."""
    return "0" if m == "0" else ("q%d %s" % (S, m) if not m.startswith("-") else "q%d (%s)" % (S, m))


def lean_emb_defs(name, e, doc):
    """Lean lines for an embedding: one declaration per chunk of terms, then the embedding itself."""
    out, comps = [], []
    for kind, tag in (("angle", "Ang"), ("action", "Act")):
        for i, p in enumerate(e[kind]):
            parts = []
            for j in range(0, len(p["half"]), CHUNK):
                nm = "%s%s%dP%d" % (name, tag, i, j // CHUNK)
                parts.append(nm)
                out += ["/-- Terms %d to %d of the %s component %d of `%s`. -/" % (
                            j, min(j + CHUNK, len(p["half"])) - 1, kind, i, name),
                        "def %s : List (CertKey × CC ℚ) :=" % nm,
                        "  [" + ",\n   ".join("([%d, %d], ⟨%s, %s⟩)" % (k[0], k[1], lean_m(v[0]), lean_m(v[1]))
                                                for k, v in p["half"][j:j + CHUNK]) + "]",
                        ""]
            comps.append((kind, "⟨%s, %s⟩" % (lean_m(p["zero"]), " ++ ".join(parts) if parts else "[]")))
    ang = ",\n     ".join(c for k, c in comps if k == "angle")
    act = ",\n     ".join(c for k, c in comps if k == "action")
    out += ["/-- %s -/" % doc, "def %s : CertEmbedding ℚ where" % name,
            "  angleDeg := [%s]" % ", ".join(str(d) for d in e["angleDeg"]),
            "  angle :=\n    [%s]" % ang,
            "  actionDeg := [%s]" % ", ".join(str(d) for d in e["actionDeg"]),
            "  action :=\n    [%s]" % act, ""]
    return out


def write_lean(data, lean_dir, log):
    os.makedirs(lean_dir, exist_ok=True)
    pr = data["restart"]["params1"]
    w = data["restart"]["witness1"]
    core, R = w["base"]["core"], w["base"]["R"]
    cl = data["step"]["claims"]
    pq = lambda d: "\n".join("  %s := %s" % ({"sK": "σK", "sB": "σB", "sT": "σT", "mu": "μ", "gbar": "γbar",
                                              "sigma_omega": "σω", "gamma": "γ", "rhoInf": "rhoInf"}.get(k, k),
                                             (d[k] if k == "tau" else lean_q(d[k])))
                             for k in ("tau", "rho", "rhoInf", "M", "sK", "sB", "sT", "mu", "gbar", "sigma_omega",
                                       "nuRay", "gamma", "s", "err", "E0", "disp"))
    lines = ["/-",
             "Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.",
             "Authors: Scott Armstrong, Zohar Komargodski",
             "-/",
             "module",
             "",
             "public import KAM.CertificateSharp.V2.RouteARefinedRef",
             "",
             "/-!",
             "# Data of the hybrid kernel test on R1's L = 8 finite candidate (generated; not built)",
             "",
             "Generated by `scripts/apost_sharp/hybrid_producer.py` from",
             "`docs/campaign/design/hybrid/hybrid-R1-L8.json` (format `docs/campaign/design/hybrid/format.md`).",
             "`r1HybEmb` is the finite candidate K̂, `r1HybStep` the finite step ΔK̂ (degrees as in the format),",
             "`r1HybParams1`, `r1HybCore`, `r1HybClaim` the restarted route-A′ run, and `r1HybClaims` the step",
             "claims in the order of `r1HybClaimNames`. Under `kernel-tests/`: never built; it compiles as",
             "`KAM.CertificateSharp.V2.Tests.HybridR1L8Data` when placed back under `KAM/`.",
             "-/",
             "",
             "@[expose] public section",
             "",
             "namespace KAM.CertificateSharp.HybridR1Test",
             "",
             "open KAM.Certificate KAM.CertificateSharp.V2",
             "",
             "/-- A mantissa at scale `2^%d`: `q%d m = m / 2^%d`. -/" % (S, S, S),
             "def q%d (m : ℤ) : ℚ := m / 2 ^ %d" % (S, S),
             ""] + lean_emb_defs("r1HybEmb", data["base"]["emb"], "The finite candidate K̂ (R1, L = 8).") \
          + lean_emb_defs("r1HybStep", data["step"]["dK"], "The finite step ΔK̂.") + [
             "/-- The parameters of the restarted run. -/",
             "def r1HybParams1 : CertParams where",
             pq(pr),
             "",
             "/-- The restarted route-A′ witness (sites: those of `r1RefinedWitR`, ρ₁ = ρ). -/",
             "def r1HybCore : FrozenWit where",
             "\n".join("  %s := %s" % (k, ("[" + ",\n    ".join(lean_q(F(x)) for x in core[k]) + "]")
                                       if isinstance(core[k], list)
                                       else (core[k] if k in ("kp", "J") else lean_q(F(core[k]))))
                       for k in ("Xs", "kp", "th", "c", "cbar", "ctail", "sB", "sT", "sLt", "sN", "sNt", "t", "J")),
             "",
             "/-- The transferred claims of the restarted run. -/",
             "def r1HybClaim : RefClaim where",
             "\n".join("  %s := %s" % (k, lean_q(F(R[k]))) for k in ("dh", "dx", "d2x", "d2h", "bL", "bN", "bNt", "bT")),
             "",
             "/-- The step claims, in the order of `r1HybClaimNames`. -/",
             "def r1HybClaims : List ℚ :=",
             "  [" + ",\n   ".join(lean_q(F(cl[k])) for k in cl) + "]",
             "",
             "/-- The names of the step claims (format.md, section 3). -/",
             "def r1HybClaimNames : List String :=",
             "  [" + ",\n   ".join(", ".join('"%s"' % k for k in list(cl)[i:i + 8]) for i in range(0, len(cl), 8)) + "]",
             "",
             "end KAM.CertificateSharp.HybridR1Test",
             "",
             "end",
             ""]
    p = os.path.join(lean_dir, "HybridR1L8Data.lean")
    text = "\n".join(lines)
    open(p, "w").write(text)
    log("  wrote %s (%d lines)" % (p, len(text.splitlines())))


def main():
    args = sys.argv[1:]
    out = args[args.index("--out") + 1] if "--out" in args else None
    lean = args[args.index("--lean") + 1] if "--lean" in args else None
    only = args[args.index("--only") + 1] if "--only" in args else None
    if not NQ.validate(log=lambda *a: None):
        raise SystemExit("hybrid_numq does not reproduce the kernel facts")
    if only in (None, "T2"):
        produce_t2(out)
    if only in (None, "R1-L8"):
        produce_r1(8, out, lean)


if __name__ == "__main__":
    main()
