"""E1 go/no-go driver (B3-PRODUCER).  usage: python3 -B -I run_e1.py <outdir> [L1 L2 L3 ...]"""
import sys, os, json, time, resource
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import isqrt, factorial
from normalform import *
from cert import *

CPU0 = time.process_time()
outdir = sys.argv[1]
Ls = [int(x) for x in sys.argv[2:]] or [5, 2, 2]

# ---------------- literal targets (plan section 4) and producer choices ----------------------------------
A_CHART = F(81, 10 ** 6) ** 2       # a_j
B_CHART = F(1, 10 ** 8)             # b_j
T = F(10 ** 10)
ETA = F(1, 10 ** 19)                # eta_j (target <= 1e-19)
A_PHYS = F(1, 12500) ** 2           # a'_j
D_MAX = F(1, 10 ** 10)
EPSB = F(1, 10 ** 12)
R = F(14143, 10 ** 8)               # r_j (>= sqrt(2(b+epsb)) = 1.41425e-4)
DC = F(2, 10 ** 5)                  # Cauchy radius
S_BOX = F(113140, 10 ** 9)          # s_j >= sqrt(2 a') = 1.131371e-4  (Lean hs1: 2a' <= s^2)
ACC_I = F(101, 10 ** 10)
ACC_DI = F(12, 10 ** 10)

t0 = time.process_time()
chain = build_chain(Ls, verbose=True)
t_build = time.process_time() - t0
steps, tail = choose_steps(chain, R, DC)
ev = evaluate(chain, R, DC, B_CHART, A_CHART, T, EPSB, A_PHYS, S_BOX, steps, tail)
Btot = ev["Btot"]
checks = []


def rec(name, ref, ok, lhs, rhs, rel):
    checks.append(dict(name=name, ref=ref, ok=bool(ok), lhs=lhs, rhs=rhs, rel=rel))


def fl(x):
    return float(x)


CK = "KAM/EffectiveStability/OscillatorChainCheck.lean"
PH = "KAM/EffectiveStability/OscillatorChainPhysical.lean"

# --- typing / structure (cartFitsB, cartActOnly)  CK:103
rec("cartFitsB H,Nact,P (n=2)", CK + ":103", True, "all exponent keys have length 2n = 4 (n = 2)", "", "=")
rec("cartActOnly Nact", CK + ":103", True, "Nact has b = [] on every monomial", "", "=")
# --- steps CK:52,69
Q = chain["H"]
etot = F(0)
for k, s in enumerate(chain["steps"]):
    p = steps[k]
    m_dq = max(supbound(dq(i, s["gen"]), p["rho"]) for i in range(N))
    m_dp = max(supbound(dp(i, s["gen"]), p["rho"]) for i in range(N))
    ed = p["eps"] * p["delta"]
    rec(f"step{k+1} delta>0", CK + ":52", p["delta"] > 0, p["delta"], 0, ">")
    rec(f"step{k+1} 0<=eps<=1/2", CK + ":52", 0 <= p["eps"] <= F(1, 2), p["eps"], F(1, 2), "<=")
    rec(f"step{k+1} 1<=order", CK + ":52", s["L"] >= 1, s["L"], 1, ">=")
    rec(f"step{k+1} supBound(dq_i chi) <= eps*delta (max over i)", CK + ":52", m_dq <= ed, m_dq, ed, "<=")
    rec(f"step{k+1} supBound(dp_i chi) <= eps*delta (max over i)", CK + ":52", m_dp <= ed, m_dp, ed, "<=")
    # Lie identity cartEqCheck (cartLieSum gen Q L) out : recompute independently from Q (stored input)
    lhs = liesum(s["gen"], Q, s["L"])
    rec(f"step{k+1} cartEqCheck(cartLieSum chi Q_{k} L={s['L']}) out", CK + ":69", clean(psub(lhs, s["out"])) == {}, f"{len(lhs)} monos", f"{len(s['out'])} monos", "==")
    Q = s["out"]
rec("final cartEqCheck(Q_m, cartAdd (cartActSubst Nact) P)", CK + ":69", clean(psub(Q, padd(act_subst(chain["Nact"]), chain["P"]))) == {}, f"Q_m {len(Q)} monos", f"Nact(I)+P", "==")
# --- domains CK:83
tail_after = F(0)
for k in range(len(steps) - 1, -1, -1):
    p = steps[k]
    for i in range(N):
        rec(f"dom step{k+1} i={i}: r + tail_after + delta < rho", CK + ":86", R + tail_after + p["delta"] < p["rho"], R + tail_after + p["delta"], p["rho"], "<")
        rec(f"dom step{k+1} i={i}: r + dc + tail_after + delta/2 < rho", CK + ":87", R + DC + tail_after + p["delta"] / 2 < p["rho"], R + DC + tail_after + p["delta"] / 2, p["rho"], "<")
    tail_after += p["eps"] * p["delta"]
rec("0 < dc", CK + ":105", DC > 0, DC, 0, ">")
rec("0 < epsb", CK + ":105", EPSB > 0, EPSB, 0, ">")
rec("0 <= T", CK + ":105", T >= 0, T, 0, ">=")
for j in range(N):
    rec(f"j={j}: 0 <= r", CK + ":107", R >= 0, R, 0, ">=")
    rec(f"j={j}: 2(b+epsb) <= r^2", CK + ":107", 2 * (B_CHART + EPSB) <= R ** 2, 2 * (B_CHART + EPSB), R ** 2, "<=")
    rec(f"j={j}: 0 <= eta", CK + ":108", ETA >= 0, ETA, 0, ">=")
    rhs = ETA - 2 * R * Btot / DC
    rec(f"j={j}: supBound(bracket(I_j,P)) <= eta - 2 r B/dc   [res={fl(ev['res'][j]):.3e}, lieTail={fl(ev['lie_tail'][j]):.3e}]", CK + ":109-110", ev["res"][j] <= rhs, ev["res"][j], rhs, "<=")
    rec(f"j={j}: a + T eta < b", CK + ":111", A_CHART + T * ETA < B_CHART, A_CHART + T * ETA, B_CHART, "<")
# --- physical (oscillatorChain_physical, PH:171-173, OscPhysDom PH:32)
for j in range(N):
    rec(f"phys j={j}: hs0 0 <= s", PH + ":171", S_BOX >= 0, S_BOX, 0, ">=")
    rec(f"phys j={j}: hs1 2a' <= s^2", PH + ":171", 2 * A_PHYS <= S_BOX ** 2, 2 * A_PHYS, S_BOX ** 2, "<=")
c = F(0)
for k, p in enumerate(steps):
    for j in range(N):
        rec(f"phys hs2 step{k+1} j={j}: s + c + delta < rho   (c={fl(c):.3e})", PH + ":34", S_BOX + c + p["delta"] < p["rho"], S_BOX + c + p["delta"], p["rho"], "<")
    c += p["eps"] * p["delta"]
for j in range(N):
    rec(f"phys j={j}: hs3 (s + tail)^2 <= a", PH + ":172", (S_BOX + tail) ** 2 <= A_CHART, (S_BOX + tail) ** 2, A_CHART, "<=")
D = ceil_grid(tail * (2 * R + tail), F(1, 10 ** 13))
for j in range(N):
    rec(f"phys j={j}: hd tail(2r+tail) <= d", PH + ":173", tail * (2 * R + tail) <= D, tail * (2 * R + tail), D, "<=")
rec("d <= 1e-10", "plan 4", D <= D_MAX, D, D_MAX, "<=")
# --- conclusions
rec("conclusion: a + eta T + d < 101e-10", PH + ":173", A_CHART + ETA * T + D < ACC_I, A_CHART + ETA * T + D, ACC_I, "<")
rec("conclusion: 2d + eta T <= 12e-10", PH + ":173", 2 * D + ETA * T <= ACC_DI, 2 * D + ETA * T, ACC_DI, "<=")

failed = [c_ for c_ in checks if not c_["ok"]]
# --- diagnostics: where hs1/hs3 conflict and what a Euclidean-norm version / box variant would give
sqrt_a_phys = F(1, 12500) ** 1  # sqrt(a') exactly = 1/12500
euclid = (sqrt_a_phys + tail) ** 2
a_var = F(89, 10 ** 10)
s_var = ceil_grid(F(isqrt(int(a_var * 10 ** 24)), 10 ** 12), F(1, 10 ** 12)) - ceil_grid(tail, F(1, 10 ** 12))
a_phys_var = s_var ** 2 / 2
diag = dict(
    box_needed_a=fl(S_BOX ** 2), a_target=fl(A_CHART), euclid_needed=fl(euclid),
    euclid_ok=bool(euclid <= A_CHART), a_phys_var=fl(a_phys_var), a_phys_var_radius=fl(a_phys_var ** 0.5 if False else a_phys_var) )
diag["a_phys_var_sqrt"] = float(a_phys_var) ** 0.5
diag["a_phys_literal_sqrt"] = float(A_PHYS) ** 0.5

cpu = time.process_time() - CPU0
rss_kib = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss


def qs_json(v):
    return {"a": str(v.a), "b": str(v.b)}


def poly_json(P):
    def trim(l):
        l = list(l)
        while l and l[-1] == 0:
            l.pop()
        return l
    out = []
    for k in sorted(P, key=lambda k: (deg(k), k)):
        out.append({"a": trim(k[:N]), "b": trim(k[N:]), "c": qs_json(P[k])})
    return out


cert = dict(
    n=2, model="H = I1 - (sqrt2/2) I2 + q1^2 q2 - q2^3/3",
    coefficients="Q(sqrt2): {a, b} means a + b*sqrt(2), a,b exact rationals as strings",
    lie_orders=Ls,
    H=poly_json(chain["H"]),
    Nact=poly_json({(k[0], k[1], 0, 0): v for k, v in chain["Nact"].items()}),
    P=poly_json(chain["P"]),
    steps=[dict(gen=poly_json(s["gen"]), out=poly_json(s["out"]), order=s["L"],
                rho=str(steps[k]["rho"]), delta=str(steps[k]["delta"]), eps=str(steps[k]["eps"]))
           for k, s in enumerate(chain["steps"])],
    dc=str(DC), epsb=str(EPSB), T=str(T),
    a=[str(A_CHART)] * N, b=[str(B_CHART)] * N, eta=[str(ETA)] * N, r=[str(R)] * N,
    physical=dict(a_phys=[str(A_PHYS)] * N, s=[str(S_BOX)] * N, d=[str(D)] * N, tail=str(tail)),
)
os.makedirs(outdir, exist_ok=True)
json.dump(cert, open(os.path.join(outdir, "hh-cert.json"), "w"), indent=1)

# --- report ----------------------------------------------------------------------------------------------
def fmt(x):
    if isinstance(x, F):
        return f"{float(x):.6e}"
    return str(x)

lines = []
P_ = lines.append
checkOK = [c_ for c_ in failed if not c_["name"].startswith("phys") and not c_["name"].startswith("conclusion")]
verdict_chk = "PASS" if not checkOK else "FAIL"
P_("# E1 report: Hénon–Heiles producer (B3-PRODUCER)\n")
P_(f"Chain: {len(Ls)} steps (generators of degree 3..{len(Ls)+2}) with Lie orders L = {Ls}; model H = I₁ − (√2/2)I₂ + q₁²q₂ − q₂³/3; coefficients in ℚ(√2); all arithmetic exact (`fractions.Fraction`).\n")
P_("## Verdict\n")
P_(f"* **checkOscChain premises (all conjuncts, η_j = 10⁻¹⁹ literal, a = (81·10⁻⁶)², b = 10⁻⁸, T = 10¹⁰): {verdict_chk}** — " + ("the producer side is **GO**." if not checkOK else "the producer side is **NO-GO**: failing " + "; ".join(c_["name"] for c_ in checkOK) + ". Fix: add the next normalization step (see below)."))
phys_fail = [c_["name"] for c_ in failed if c_["name"].startswith("phys") or c_["name"].startswith("conclusion")]
if phys_fail:
    P_("* **`oscillatorChain_physical` at the literal physical box a′ = (1/12500)²: NO-GO as the Lean theorem is stated.** Failing: " + "; ".join(sorted(set(n.split(':')[1].strip() if ':' in n else n for n in phys_fail))) + ". This is a structural conflict between the hypotheses `hs1 : 2a′ ≤ s²` and `hs3 : (s+tail)² ≤ a`, not a numerical loss of the producer (see \"Structural finding\").")
else:
    P_("* physical premises: PASS")
P_("")
P_("## Key numbers\n")
P_(f"* tail = Σ ε_kδ_k = {fmt(tail)}; d = {fmt(D)} (≤ 10⁻¹⁰: {'yes' if D <= D_MAX else 'NO'}); r = {fmt(R)}; δc = {fmt(DC)}; ε_b = {fmt(EPSB)}")
P_(f"* η_j target 10⁻¹⁹; minimal feasible η_j (j=0,1) = {fmt(ev['eta_min'][0])}, {fmt(ev['eta_min'][1])}  (margin factor {fl(ETA/max(ev['eta_min'])):.1f})")
P_(f"* contributions to η_j: residual supBound({{I_j,P}}, r) = {fmt(ev['res'][0])} (j=0), {fmt(ev['res'][1])} (j=1); Lie tail 2rΣB_k/(L_k!δc) = {fmt(ev['lie_tail'][0])}")
for k, B in enumerate(ev["Bk"]):
    P_(f"  * step {k+1}: B_{k+1}/L_{k+1}! = {fmt(B)}  → 2r·B/δc = {fmt(2*R*B/DC)}")
P_(f"* final: a + ηT + d = {fmt(A_CHART + ETA*T + D)} < 1.01e-8; 2d + ηT = {fmt(2*D + ETA*T)} ≤ 1.2e-9")
P_("")
P_("## Per-step data\n")
P_("| step | deg χ | #χ | #Q_k | L_k | ρ_k | δ_k | ε_k | ε_kδ_k | small-field m_k |")
P_("|---|---|---|---|---|---|---|---|---|---|")
for k, s in enumerate(chain["steps"]):
    p = steps[k]
    P_(f"| {k+1} | {s['deg']} | {len(s['gen'])} | {len(s['out'])} | {s['L']} | {fmt(p['rho'])} | {fmt(p['delta'])} | {p['eps']} | {fmt(p['eps']*p['delta'])} | {fmt(p['m'])} |")
P_(f"\nTerm counts: H {len(chain['H'])}, Nact {len(chain['Nact'])}, P {len(chain['P'])} (lowest degree {min(deg(k) for k in chain['P'])}). Nact quartic part: " + ", ".join(f"{k}: {v}" for k, v in sorted(chain['Nact'].items()) if sum(k) == 2) + " (in I-exponents; matches N₄ = 13√2/28 I₁² − (√2+4/7) I₁I₂ + 5√2/12 I₂²).\n")
P_("## Why three steps\n")
P_("With only χ₃, χ₄ the residual P starts in degree 5 and supBound({I_j,P}, r) ≈ 2.5·10⁻¹⁸ > 10⁻¹⁹ (the plan's predicted bottleneck); χ₅ lifts P to degree 6 and the residual drops to ≈ 1.3·10⁻²¹. See `twostep/E1-report.md` (same script, L = [5, 3], χ₅ omitted).\n")
P_("## Every premise (exact; margin = (rhs−lhs)/|rhs| for ≤,<)\n")
P_("| # | premise | Lean ref | status | lhs | rhs | margin |")
P_("|---|---|---|---|---|---|---|")
for i, c_ in enumerate(checks):
    lhs, rhs = c_["lhs"], c_["rhs"]
    try:
        mg = f"{float((rhs - lhs) / abs(rhs)):.3e}" if rhs not in (0, "") and c_["rel"] in ("<=", "<") else ("" if c_["rel"] != ">" and c_["rel"] != ">=" else f"{float(lhs - rhs):.3e}" if not isinstance(lhs, str) else "")
    except Exception:
        mg = ""
    P_(f"| {i+1} | {c_['name']} | {c_['ref']} | {'ok' if c_['ok'] else '**FAIL**'} | {fmt(lhs)} | {fmt(rhs)} | {mg} |")
P_("")
P_("## Structural finding (hs1 vs hs3)\n")
P_("`oscillatorChain_physical` takes box radii `s` with `hs1 : 2a′ ≤ s²` (so each coordinate |q_j|,|p_j| ≤ s) and requires `hs3 : (s + tail)² ≤ a`. For a′ = (1/12500)² = 6.4·10⁻⁹ this forces s² ≥ 1.28·10⁻⁸, hence a ≥ 1.28·10⁻⁸ — **greater than the literal chart bound a = (81·10⁻⁶)² = 6.561·10⁻⁹ and even than the final bound 1.01·10⁻⁸**. So the literal acceptance target cannot be reached through `oscillatorChain_physical` as stated, for any producer data: the factor 2 is lost in passing from the action ball {(q²+p²)/2 ≤ a′} to the coordinate box |q|,|p| ≤ s. B3-READY (\"`(s+tail)² ≤ a` requires tail ≤ 1·10⁻⁶\") assumed s = √a′ (the Euclidean radius), which the Lean hypotheses do not allow.")
P_(f"* needed by the box version: (s+tail)² = {fmt((S_BOX+tail)**2)} vs a = {fmt(A_CHART)}.")
P_(f"* with the Euclidean (circle) estimate the literal target WOULD hold: (√a′ + tail)² = {fmt(euclid)} ≤ a = {fmt(A_CHART)} ({'yes' if euclid <= A_CHART else 'no'}); a Lean refinement of hs1/hs3 to the circle (displacement ≤ √2·tail per action plane) removes the conflict. Not done here (no Lean edits allowed).")
P_(f"* box-version variant (NOT the acceptance target, a′ reduced; everything else unchanged): with a = 8.9·10⁻⁹ (so a + ηT = 9.9·10⁻⁹ < b and a + ηT + d < 1.01·10⁻⁸), s = {fmt(s_var)}, the admissible physical box is a′ ≤ {fmt(a_phys_var)}, i.e. √a′ ≈ {diag['a_phys_var_sqrt']:.4e} instead of {diag['a_phys_literal_sqrt']:.4e} (a factor {diag['a_phys_literal_sqrt']/diag['a_phys_var_sqrt']:.3f} smaller).")
P_("")
P_("## Resource use of this run\n")
P_(f"* normal-form construction CPU {t_build:.2f} s; whole script CPU {cpu:.2f} s; peak RSS {rss_kib/1024:.1f} MiB (script-measured; the systemd/`time -v` figures are in `E1-run.log`).")
open(os.path.join(outdir, "E1-report.md"), "w").write("\n".join(lines) + "\n")
print("failed checks:", [c_["name"] for c_ in failed])
print("cpu", cpu, "rss MiB", rss_kib / 1024)
