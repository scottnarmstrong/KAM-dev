#!/usr/bin/env python3
"""SJS-LG00 item 4: the LG00 torus in the landed checker's representation, operation counts, kernel cost.

Untrusted design tooling.
1. HamExpr.  h~(theta, a) = c/(2 pi ell) sum_{(m,k)} C (2 I_1)^{m_1/2} (2 I_2)^{m_2/2} cos(2 pi k.theta), I = I0 + ell a.
   Even m_j: (2 I0_j + 2 ell a_j)^{m_j/2} is a polynomial (`pow`, `add`, `mul`, `action`).  Odd m_1, m_2 (always
   together): sqrt(2 I_1) sqrt(2 I_2) has no HamExpr node.  Variant "taylor": sqrt(2 I0_j) T_K(ell a_j / I0_j) with
   T_K the degree-K Taylor polynomial of sqrt(1 + x) (Horner) -- a different, polynomial Hamiltonian, within the
   remainder of the true one; a hypothetical `sqrt` node is approximated by the K = 1 count (one node; its witness
   check, about 2 model x model products, comes on top).  Terms are grouped by (m1, m2), even groups in A, odd ones
   in B: h = A + sqrt(4 I1 I2) B, so the square root occurs once (HamExpr is a tree: no sharing).
2. Jet counts by the Python mirror of the landed jet compiler (scripts/spin_orbit/adv_jet.py, read-only): slots,
   model ops, genuine model x model products (MM) per call (invariance d1, energy v0, torsion d1 + d2).
3. Support geometry: the kept set of the torus at the route-A digits, box / support of the 2-D layout (beta).
4. Cost: per-slot constants of SJS-FEAS (kernel_probes.md; ~D34) and the lunar D34 calibration (one blockRows-32
   shard +45 s kernel, ~190 s literal elaboration; 1 157 shards per torus, OVERNIGHT 11:19-11:29).
Usage: python3 -I lg00_cost.py [--json OUT]
"""
import os, sys, math, json
import numpy as np
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts", "spin_orbit"))
import adv_jet                         # noqa: E402  (read-only use)
import lg00_torus as TT                # noqa: E402
import lg00_model as MM                # noqa: E402

TP = 2 * math.pi


def fr(x, d=10 ** 12):
    return F(float(x)).limit_denominator(d)


def taylor_sqrt(x_expr, K):
    """sum_{i <= K} binom(1/2, i) x^i in Horner form (x a HamExpr)."""
    b = [F(1)]
    for i in range(1, K + 1):
        b.append(b[-1] * (F(1, 2) - (i - 1)) / i)
    e = ("const", b[K])
    for i in range(K - 1, -1, -1):
        e = ("add", ("const", b[i]), ("mul", x_expr, e))
    return e


def lg00_hamexpr(c, ell, I0, variant="taylor", K=19):
    Q, lam = MM.normal_modes()
    form = TT.action_angle_form(Q)
    KM = TT.KM
    pre = fr(c / (TP * ell))
    two_I = [("add", ("const", fr(2 * I0[j])), ("mul", ("const", fr(2 * ell)), ("action", j))) for j in range(2)]
    if variant == "taylor":
        x = [("mul", ("const", fr(ell / I0[j])), ("action", j)) for j in range(2)]
        s12 = ("mul", ("const", fr(math.sqrt(4 * I0[0] * I0[1]))), ("mul", taylor_sqrt(x[0], K), taylor_sqrt(x[1], K)))
    else:
        s12 = ("sqrt", ("mul", two_I[0], two_I[1]))
    A = ("const", 0)                                     # even (m1, m2) groups
    B = ("const", 0)                                     # odd groups, without the common factor s12
    nterms = 0
    for (m1, m2), C in sorted(form.items()):
        trig = None
        for i1 in range(2 * KM + 1):
            for i2 in range(2 * KM + 1):
                k = (i1 - KM, i2 - KM)
                if k < (0, 0) or abs(C[i1, i2]) < 1e-30:
                    continue
                coef = C[i1, i2].real * (1 if k == (0, 0) else 2)
                t = ("const", fr(coef, 10 ** 30)) if k == (0, 0) else ("mul", ("const", fr(coef, 10 ** 30)),
                                                                        ("cosMode", k))
                trig = t if trig is None else ("add", trig, t)
                nterms += 1
        if trig is None:
            continue
        rad = None
        for j, m in enumerate((m1, m2)):
            if m >= 2:
                p = ("pow", two_I[j], m // 2) if m // 2 > 1 else two_I[j]
                rad = p if rad is None else ("mul", rad, p)
        term = trig if rad is None else ("mul", rad, trig)
        if m1 % 2 == 1:
            B = ("add", B, term)
        else:
            A = ("add", A, term)
    total = ("add", A, ("mul", s12, B))                  # the square root occurs once
    return ("mul", ("const", pre), total), nterms


def jet_counts(e):
    J = adv_jet.jet(2, e)
    prog = J["prog"]
    kd, src, cls = adv_jet.kinds(prog)
    d1 = [x for x in J["d1"] if x]
    d2 = [x for r in J["d2"] for x in r if x]
    wanted = {"invariance (d1)": d1, "energy (v0)": [J["v0"]], "inv+energy (v0::d1)": [J["v0"]] + d1,
              "torsion (d1, d2)": d1 + d2, "whole program": list(range(len(prog)))}
    out = dict(program_length=len(prog), per_call={})
    for name, w in wanted.items():
        sl = adv_jet.closure(prog, w)
        c = adv_jet.count(prog, sl, cls)
        heavy = sum(1 for i in sl if kd[i] == "M" and prog[i][0] in ("add", "mul"))
        out["per_call"][name] = dict(slots=len(sl), model_ops=heavy,
                                     chars=sum(1 for i in sl if prog[i][0] == "char"), **c)
    return out


def support_geometry(npz, L_list, rho=0.02, ell=1e-5):
    """kept set {k : max_comp |c_k| e^{2 pi rho |k|_1} >= 10^-L ref}: count, bounding box, box / count."""
    d = np.load(npz)
    u, v = d["u"], d["v"]
    N = u.shape[0]
    k = np.fft.fftfreq(N, 1 / N)
    k1, k2 = np.meshgrid(k, k, indexing="ij")
    U = np.fft.fft2(u, axes=(0, 1)) / N ** 2; V = np.fft.fft2(v, axes=(0, 1)) / N ** 2
    comps = [U[..., 0] / TP, U[..., 1] / TP, V[..., 0] / ell, V[..., 1] / ell]
    w = np.exp(TP * rho * (np.abs(k1) + np.abs(k2)))
    A0 = np.max([np.abs(x) / np.abs(x).max() for x in comps], axis=0)
    A = np.max([np.abs(x) for x in comps], axis=0) * w
    ref = A.max()
    out = []
    for L in L_list:
        keep = (A >= 10.0 ** (-L) * ref) & (A0 > 1e-14)
        n = int(keep.sum())
        bx = (k1[keep].max() - k1[keep].min() + 1) * (k2[keep].max() - k2[keep].min() + 1)
        out.append(dict(L=L, S=n, box=int(bx), beta=float(bx / n), k1=(int(k1[keep].min()), int(k1[keep].max())),
                        k2=(int(k2[keep].min()), int(k2[keep].max()))))
    return out


# per-slot constants (SJS-FEAS kernel_probes.md, D34-like prototype; one declaration per product at this size)
C_SLOT, C_TERM, C_OP = 1.0e-3, 1.4e-3, 1.26e-3
NU2 = 7.7                       # advice slots per factor term, 2-D box layout (measured)
# landed checker (pre-D34, this worktree): probe lg00_Lshard_d2b_K27_b160_r4 -- the middle shard of 27 of a
# 3 025-term product (23 517 advice slots): 14.1 s kernel, 4.96 GB; edge shards lighter (factor 0.75 assumed)
LANDED_MS_PER_SLOT = (14.1 * 27 * 0.75 / 23517 * 1e3, 14.1 * 27 / 23517 * 1e3)
ELAB_MS = (0.18, 0.6)           # data elaboration per element (SJS-FEAS)
# char witnesses: Compose.charResolve caches per key and reflects -k, so one check per +-pair of distinct modes:
# |k|_1 in {2, 4, 6}, k1 + k2 even -> 4 + 8 + 12 = 24 pairs; each check (Model/Exp.expWitnessRadiusOf) is n = 2
# derivative residuals, i.e. 2 model x model products
CHAR_MM = 24 * 2


def cost(S, beta, N_MM, N_ops, S_low, N_MM_low, N_ops_low, chars):
    slots = NU2 * beta * (N_MM * S + N_MM_low * S_low)
    terms = 2 * (N_MM * S + N_MM_low * S_low)
    ops = (N_ops * S + N_ops_low * S_low) * C_OP
    d34 = (slots * C_SLOT + terms * C_TERM + ops) / 3600
    landed = tuple((slots * m / 1e3 + ops) / 3600 for m in LANDED_MS_PER_SLOT)
    data = slots + chars * S + 4 * S                      # advice + char witnesses + the embedding
    elab = tuple(data * m / 1e3 / 3600 for m in ELAB_MS)
    side = math.sqrt(beta * S)
    shards_landed = (N_MM + N_MM_low) * max(1, int(2 * side / 4))
    # D34-like: one declaration per product while it fits 6 GB over the 3.1 GB import (82 kB per advice slot, 260 kB
    # per factor term, SJS-FEAS); otherwise that many shards (factors pre-packed as certificate data)
    def nsh(s_):
        mem = NU2 * beta * s_ * 82e3 + 2 * s_ * 260e3
        return max(1, math.ceil(mem / 6e9))
    decls = N_MM * nsh(S) + N_MM_low * nsh(S_low)
    peak = min(6.0, (NU2 * beta * S * 82e3 + 2 * S * 260e3) / 1e9) + 3.1
    return dict(cpu_h_d34=d34, cpu_h_landed=landed, advice_slots=slots, data_elements=data, elab_cpu_h=elab,
                decls_d34=decls, decls_landed=shards_landed, peak_gb_d34=peak, shards_per_product_d34=nsh(S))


def main():
    out = {}
    res = os.path.join(HERE, "results")
    thr = json.load(open(os.path.join(res, "lg00_thresholds.json")))["best"] if os.path.exists(
        os.path.join(res, "lg00_thresholds.json")) else {}
    d = np.load(os.path.join(res, "lg00_torus_N128.npz"))
    I0 = d["I0"]
    print("HamExpr of LG00 (action-angle form (15) of eq. (11), grouped by (m1, m2)):")
    for variant, K in (("taylor", 19), ("taylor", 10), ("taylor", 1), ("sqrt", 0)):
        if variant == "sqrt":
            continue                                        # the mirror has no sqrt node; counted by hand below
        e, nterms = lg00_hamexpr(1e4, 1e-5, I0, variant, K)
        jc = jet_counts(e)
        out["jet_%s_K%d" % (variant, K)] = jc
        pc = jc["per_call"]
        print("  %s K=%d: %d cosine terms; program %d slots" % (variant, K, nterms, jc["program_length"]))
        for name, r in pc.items():
            print("    %-22s slots %5d  model ops %5d  MM %4d  CM %4d  chars %3d" % (
                name, r["slots"], r["model_ops"], r["MM"], r["CM"], r["chars"]))
    # Taylor remainder of sqrt(1 + x) at the domain size
    for K in (10, 19, 30):
        for x in (0.05, 0.1, 0.2):
            b = abs(math.comb(2 * (K + 1), K + 1) / ((1 - 2 * (K + 1)) * 4 ** (K + 1)))
            out.setdefault("taylor_remainder", {})["K%d_x%.2f" % (K, x)] = b * x ** (K + 1) / (1 - x)
    print("  Taylor remainder bound |binom(1/2, K+1)| x^{K+1}/(1-x):",
          {k: "%.1e" % v for k, v in out["taylor_remainder"].items()})
    geo = support_geometry(os.path.join(res, "lg00_torus_N128.npz"), (8, 10, 12, 13))
    out["support_geometry"] = geo
    print("support geometry (rho 0.02): " + "; ".join("L %d: S %d, box %d, beta %.2f" % (g["L"], g["S"], g["box"], g["beta"])
                                                       for g in geo))
    if thr:
        print("\ncost per torus (MM/ops from the jet mirror, Taylor K = 19, + %d char-witness products per stage; Gram/torsion "
              "stage on the 17-digit support):" % CHAR_MM)
        jc = out["jet_taylor_K19"]["per_call"]
        ie, to = jc["inv+energy (v0::d1)"], jc["torsion (d1, d2)"]
        beta = float(np.mean([g["beta"] for g in geo]))
        rows = {}
        print("| theorem | L | bits | S | S_low | D34-like CPU-h | landed CPU-h | data elab CPU-h | decls D34 / landed | peak GB (D34) | advice slots |")
        print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
        for t in ("v0", "v0fixed", "v1", "v1fixed", "A", "Aiso", "Afreq", "Aisofreq"):
            if t not in thr:
                continue
            b = thr[t]
            S = b["S"]
            if "S_low" not in b:
                import lg00_oracle as OR
                if "_O" not in globals():
                    globals()["_O"] = OR.Oracle(os.path.join(res, "lg00_torus_N128.npz"))
                r = OR.evaluate(_O, b["rho"], b["mu"], b["c"], b["ell"], ())
                b["S_low"] = float(r["trunc"]["S_of"](17.0))
            S_low = min(S, b["S_low"])
            cst = cost(S, beta, ie["MM"] + CHAR_MM, ie["model_ops"], S_low, to["MM"] + CHAR_MM, to["model_ops"], ie["chars"])
            rows[t] = dict(L=b["L"], S=S, S_low=S_low, beta=beta, **cst)
            print("| %s | %.0f | %.0f | %.3g | %.3g | %.3g | %.3g-%.3g | %.3g-%.3g | %d / %d | %.1f | %.3g |" % (
                t, b["L"], 3.33 * b["L"] + 24, S, S_low, cst["cpu_h_d34"], cst["cpu_h_landed"][0], cst["cpu_h_landed"][1],
                cst["elab_cpu_h"][0], cst["elab_cpu_h"][1], cst["decls_d34"], cst["decls_landed"], cst["peak_gb_d34"],
                cst["advice_slots"]))
        out["cost"] = rows
        out["beta"] = beta
        jk = out["jet_taylor_K1"]["per_call"]
        ie1, to1 = jk["inv+energy (v0::d1)"], jk["torsion (d1, d2)"]
        print("with a sqrt node (K = 1 counts + 2 witness products per call):")
        for t in ("v0", "v1", "Aiso", "Aisofreq"):
            if t in rows:
                r_ = rows[t]
                cst = cost(r_["S"], beta, ie1["MM"] + 2 + CHAR_MM, ie1["model_ops"], r_["S_low"], to1["MM"] + 2 + CHAR_MM,
                           to1["model_ops"], ie1["chars"])
                rows[t]["sqrt_node"] = cst
                print("  %-9s D34-like %.3g CPU-h, landed %.3g-%.3g CPU-h" % (t, cst["cpu_h_d34"], *cst["cpu_h_landed"]))
    if "--json" in sys.argv:
        json.dump(out, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=float)


if __name__ == "__main__":
    main()
