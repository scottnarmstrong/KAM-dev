# Track LP, wave 4 (streamlined, D65; owner ruling relayed by the orchestrator on the D64 landing): the LP3 slices.
# Rendered as two packets LP3-a (LP3-PLAN L1-L258) and LP3-b (L259-L506) from this one spec file (the fill tool is
# called with LP3-a and LP3-b; SLICE_PART selects the nodes). The LP3 source is LP3-PLAN.md, pinned in
# CORPUS.sha256 (sha256 1b58b704...ba06ba, the SPEC §2 candidate pin); no separate LP3 source note exists (SPEC Q1
# deviation, D65). The drift supplier of LP3 is the sealed track-N theorem partialConvex_nekhoroshev (IMPORTED node
# N:bpN:p0:partial) in place of Lemmas 12/13; LP3 drops (5), so it does not use lpM:L14 (whose hypotheses include the
# data of §1 with (5) and whose improvement step owns the L12/L13 routes): the first exit is the LP3 step
# lp3:s3#first-exit, which reuses Lemma 14's route-independent steps.
import sys

P = "docs/tracks/LP/lp3/LP3-PLAN.md"


def L(unit, x, y=None):
    return f"{P}#{unit}@L{x}-L{y or x}"


DATA = "the data n ≥ 2, ν_i > 0 with max ν = 1, 𝒜 compact and ordered, δ > 0 (no γ, τ, no (5))"
NR = "N:bpN:p0:partial"
EXP = [("lp3:s1.1#planetaryTimeExponent", "the time exponent a_n = 2/(6n² - 3n + 14)"),
       ("lp3:s1.1#planetaryDriftExponent", "the drift exponent b_n = 3/(6n² - 3n + 14)")]

A_NODES = {
    "lp3:s2.3": dict(
        kind="step", title="fixed data F1-F7 and the cell-by-cell discharge of the premises of partialConvex_nekhoroshev",
        stmt=L("s2.2", 177, 201), proof=L("s2.3", 203, 257),
        H=DATA + "; planar (the spatial version is §2.5)",
        Q="fixed before μ and the initial state",
        C="the shared tube (U, r_g, Ω_B(4r_g) ≤ δ/16), the uniform holomorphic extension of the chart and perturbation, "
          "widths, a finite cover of 𝓛_δ by centres c_j with fast cells G_j ⊂ G'_j and slow sets D_j = {¦y¦²/2 < B(c_j) - "
          "5δ/16}, the Kepler constants and the slow erosion gap are fixed; on every cell the premises of "
          "partialConvex_nekhoroshev hold (holomorphic, C², real, bounded Hessian, definite fast part of the Kepler h, "
          "partial perturbation P = fc/B_0, the Hamiltonian identity with the chart Hamiltonian); thresholds ν_0, μ_0, "
          "r(μ) = (B_0μ)^{b_n}, T(μ) ≤ the frozen horizon T_0 exp(cμ^{-a_n})",
        S="all constants and the cover depend only on (n, ν, 𝒜, δ)",
        deps=[(NR, 154, "the premises of the imported theorem are read from its frozen interface (§2.1)"),
              ("lpM:L8#shared-tube", 181, "F1: the shared tube U, r_g and Ω_B(4r_g) ≤ δ/16 (N2)"),
              ("lpM:L8", 184, "F2/F3: the uniform holomorphic extension, bounds and widths of Lemma 8"),
              ("lpM:L5", 198, "F6: the Kepler constants of the safe compact set"),
              ("lpM:s1:fast", 215, "the Kepler fast part h and its definite Hessian (∂ω_i/∂I_i = -3ν_i³/I_i⁴)"),
              ("lpM:ext-compact-cover", 190, "F4: a finite cover of the compact 𝓛_δ by centres"),
              ("lpM:s1:thresholds#orderedStrongThreshold", 194, "F5: the slow levels B(c_j) - 5δ/16")]
        + [(t, 248, why) for t, why in EXP],
        note="LP3-PLAN §2.2-§2.3 (F1-F7 and the discharge cells) folded into one step (D65 minimal model)"),
}
B_NODES = {
    "lp3:s2.4": dict(
        kind="lemma", title="the LP3 drift supplier in the exact hstop shape (planar): drift <= r/2 on stopped orbits",
        stmt=L("s2.4", 261, 265), proof=L("s2.4", 267, 303),
        H=DATA + "; planar; 0 < μ ≤ μ_0; r = r(μ) = (B_0μ)^{b_n}",
        Q="for every 0 < μ ≤ μ_0, every stopped orbit (a moving solution z on an order-connected J ∋ 0 with z(0) = z_0, "
          "stopped on [0, t]) and every t ∈ J with ¦t¦ ≤ T(μ)",
        C="‖Λ(z(t)) - Λ(z_0)‖ ≤ r/2 (the stopped-drift premise of the first exit), forward and backward in time",
        S="μ_0, T(μ) and the cover depend only on (n, ν, 𝒜, δ)",
        deps=[("lp3:s2.3", 275, "the cell of I^0 and the discharged premises"),
              (NR, 294, "the imported theorem gives the fast drift ≤ μ^{b_n}/2 = r/2"),
              ("lpM:L7", 269, "the chart lift of the stopped orbit (Lemma 7's chart)"),
              ("lpM:L14#stopped-membership", 278, "stopped states satisfy C < B(c_j) - 3δ/8 (the sharp sublevel, §3)"),
              ("lpM:L6#shared-U", 278, "within a cell B varies by at most Ω_B(4r_g) ≤ δ/16")],
        note="LP3-PLAN §2.4 with §3 'how the whole sharp sublevel enters' (L333-L351); uniformity L302-L303"),
    "lp3:s2.5": dict(
        kind="step", title="spatial version of the drift supplier (k = 2n slow pairs, Lemma 17 chart)",
        stmt=L("s2.5", 305, 328), proof=L("s2.5", 305, 328),
        H=DATA + "; spatial; 0 < μ ≤ μ_0; r = (B_0μ)^{b_n}", Q="as in lp3:s2.4",
        C="the conclusion of lp3:s2.4 for the spatial chart: ‖Λ(z(t)) - Λ(z_0)‖ ≤ r/2 on stopped spatial orbits",
        S="as in lp3:s2.4",
        deps=[("lp3:s2.4", 305, "the planar argument with k = 2n"),
              (NR, 305, "the imported theorem with k = 2n slow pairs"),
              ("lpM:L17", 305, "the spatial chart"), ("lpM:L18", 305, "the spatial whole-sublevel domain")]),
    "lp3:s3#first-exit": dict(
        kind="step", title="the stopped first exit (Lemma 14's argument) with r = (B_0 mu)^{b_n}, T = T(mu) and the LP3 drift supplier",
        stmt=L("s3", 352, 362), proof=L("s3", 352, 362),
        H=DATA + "; the chart premises of Lemma 14 (any dimension); a stopped-drift supplier in the hstop shape "
          "(premise, supplied by lp3:s2.4 in the plane and lp3:s2.5 in space)",
        Q="for every 0 < μ ≤ μ_0 and every initial state with q_i ≠ 0, E_i < 0, a(0) ∈ 𝒜, C(0) ≤ B(I^0) - δ",
        C="with U the shared tube, r = (B_0μ)^{b_n}, T = T(μ), the budget nr + Ω_B(r) ≤ δ/4 and hstop the supplier, the "
          "unique maximal solution exists on [-T, T]; the action bound improves from < r to ≤ r/2 and the AMD margin to "
          "3δ/4; on [-T, T] the state is elliptic, I(t) ∈ Q, C(t) ≤ B(I(t)) - δ/2, the drifts are ≤ A_Λ μ^{b_n}, "
          "A_a μ^{b_n}, nA_Λ μ^{b_n}, and (9) and the star and pair distances hold with Lemma 5's constants (m = δ/2)",
        S="the constants depend only on (n, ν, 𝒜, δ) and precede μ and the state",
        deps=[("lpM:L14#centers", 352, "the admissible centres lie in 𝓛_δ"),
              ("lpM:L14#choices", 357, "U and the budget (39) with r = (B_0μ)^{b_n}"),
              ("lpM:L14#maximal-solution", 352, "the unique maximal solution"),
              ("lpM:L14#stopped-membership", 359, "the stopped interval in the whole ball"),
              ("lpM:L3#dynamic", 362, "the identity of (13)"),
              ("lpM:L6#moving-threshold", 362, "(17) with the improved radius r/2"),
              ("lpM:L6", 352, "continuation through a finite maximal endpoint"),
              ("lpM:L5", 352, "Lemma 5 with m = δ/2: the compact safe set and (9)"),
              ("lpM:L5#perihelion", 352, "d_⋆ (41)"), ("lpM:L5#pair-distances", 352, "star and pair distances"),
              ("lpM:s1:thresholds#actionAxis", 364, "the action-to-axis estimate"),
              ("lp3:s2.3", 355, "r(μ), T(μ) and the budget radius")],
        note="LP3 drops (5), so this is not lpM:L14 (whose source hypotheses include (5) and whose improvement step "
             "owns the L12/L13 routes): Lemma 14's route-independent steps are reused with the LP3 drift supplier"),
}

INV = {  # disposition of every LP3-PLAN inventory item (draft/coverage-lp3plan.md)
    "lp3:review-note": "NODE lpM:T15#planar_strongAMD_exponentialSafety_noArith, lpM:T19#spatial_strongAMD_exponentialSafety_noArith",
    "lp3:s1.1#exponents": "NODE lp3:s1.1#planetaryTimeExponent, lp3:s1.1#planetaryDriftExponent",
    "lp3:LP3-1": "NODE lpM:T15#planar_strongAMD_exponentialSafety_noArith",
    "lp3:LP3-2": "NODE lpM:T19#spatial_strongAMD_exponentialSafety_noArith",
    "lp3:s2.1": "NODE N:bpN:p0:partial",
    "lp3:s2.5": "NODE lp3:s2.5", "lp3:s3#first-exit": "NODE lp3:s3#first-exit",
    "lp3:s3#sublevel": "NODE lp3:s2.4",
    "lp3:s3#assembly": "NODE lpM:T15#planar_strongAMD_exponentialSafety_noArith, lpM:T19#spatial_strongAMD_exponentialSafety_noArith",
}


def inventory(lo, hi):
    import re
    t = open("docs/graph/LP/draft/coverage-lp3plan.md").read()
    out = []
    for b in re.split(r"\n\s*\n(?=ITEM: )", t):
        if not b.startswith("ITEM:"):
            continue
        f = dict(re.findall(r"^([A-Z_]+): ?(.*)$", b, re.M))
        x = int(re.search(r"@L(\d+)-", f["SOURCE"]).group(1))
        if not lo <= x <= hi:
            continue
        iid = f["ITEM"]
        disp = INV.get(iid) or ("EXCLUDED" if f["DISPOSITION"] == "EXCLUDED" else
                                "NODE lp3:s2.3" if iid.startswith(("lp3:s2.2", "lp3:s2.3")) else
                                "NODE lp3:s2.4" if iid.startswith("lp3:s2.4") else None)
        reason = f["REASON"] + "; D65 minimal model: " + ("excluded as in the inventory" if disp == "EXCLUDED"
                                                           else "mapped to " + disp[5:])
        out.append((iid, f["KIND"], f["SOURCE"], disp, reason))
    return out


part = SLICE_PART if "SLICE_PART" in globals() else None
