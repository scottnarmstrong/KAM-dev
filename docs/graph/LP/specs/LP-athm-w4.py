# Track LP, packet LP-athm-w4 (wave 4): the LP3 headline anchors LP3-1 (planar) and LP3-2 (spatial), roots (Q2).
# Statement-symbol edges are mechanical (frozen imports named in the declaration); the source steps are LP3-PLAN's
# drift supplier and first exit plus the MAIN assembly steps that do not involve (5).
exec(open("docs/graph/LP/specs/_lp_anchor_util.py").read())
P = "docs/tracks/LP/lp3/LP3-PLAN.md"
H = ("n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ > 0 (no "
     "Diophantine hypothesis, no γ, τ)")
Q = ("∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then "
     "∀ 0 < μ ≤ μ_0, ∀ phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ "
     "B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-a_n}): ∃ z, and ∀ t ∈ [-T, T]")
C = ("as LP1/LP2 (the moving solution, uniqueness, Newtonian reconstruction, ellipticity, Λ(t) ∈ Q, C(t) ≤ B(Λ(t)) - δ/2, "
     "(9), star and pair distances, osculating clauses and half gaps) with the drifts ‖Λ(t) - Λ(0)‖ ≤ A_Λ μ^{b_n}, "
     "‖a(t) - a(0)‖ ≤ A_a μ^{b_n}, ¦C(t) - C(0)¦ ≤ nA_Λ μ^{b_n}; a_n = planetaryTimeExponent n, b_n = "
     "planetaryDriftExponent n")
S = "the constants depend only on (n, ν, 𝒜, δ) and are chosen before μ and z_0"


def anchor(node, stmt, extra, title, note):
    r = BY_NODE[node]
    return dict(kind="theorem", title=title, stmt=stmt, proof=f"{P}#s3@L363-L370",
                H=H + ("; planar (d = 2)" if "T15" in node else "; spatial (d = 3)"), Q=Q, C=C, S=S,
                deps=extra + [(t, stmt.split("@L")[1].split("-")[0], "the statement uses " + t.split("#")[-1])
                      for t in imports(r["path"])], note=note)


COMMON = [("lp3:s3#first-exit", 363, "the stopped first exit with the LP3 drift supplier"),
          ("lpM:L1", 363, "Newtonian reconstruction (Lemma 1)"),
          ("lpM:L16", 363, "Lemma 16: the osculating elements on Lemma 5's compact set (m = δ/2)"),
          ("lpM:L16#mu0-choice", 363, "A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)"),
          ("lpM:L16#half-gaps", 363, "the osculating half gaps")]
NODES = {
    "lpM:T15#planar_strongAMD_exponentialSafety_noArith": anchor(
        "lpM:T15#planar_strongAMD_exponentialSafety_noArith", f"{P}#s1.2@L85-L126",
        COMMON + [("lp3:s2.4", 359, "hstop: the planar drift supplier (§2.4)"),
                  ("lpM:T15#orientation", 366, "the orientation reduction (reused verbatim)"),
                  ("lpM:T15#chart-cover", 366, "the Lemma 7 charts cover; C = ¦z¦²/2 in the prograde region"),
                  ("lpM:L8", 363, "the planar analytic domain (m = n)"),
                  ("lpM:L16#sourceOscAxis_pos", 363, "a^osc > 0"),
                  ("lpM:L16#sourceOscPeri_le_planeLength", 363, "a^osc(1 - e^osc) ≤ ¦q_i¦"),
                  ("lpM:L16#planeLength_le_sourceOscApo", 363, "¦q_i¦ ≤ a^osc(1 + e^osc)")],
        "LP3-1: planar strong-AMD exponential safety without arithmetic hypothesis",
        "Anchor LP3-1 (D64). MAIN T15 without (5), the drift supplier Lemmas 12/13 replaced by the sealed "
        "partialConvex_nekhoroshev (LP3-PLAN §1-§3); the source is LP3-PLAN (D65 minimal model; no separate LP3 source note)"),
    "lpM:T19#spatial_strongAMD_exponentialSafety_noArith": anchor(
        "lpM:T19#spatial_strongAMD_exponentialSafety_noArith", f"{P}#s1.3@L128-L134",
        COMMON + [("lp3:s2.5", 359, "hstop: the spatial drift supplier (§2.5)"),
                  ("lpM:T19#align", 366, "the spatial rotation reduction (reused verbatim)"),
                  ("lpM:L17#deficit-identity", 366, "C_{e_3} = ¦z¦²/2"),
                  ("lpM:L18#rotation-invariance", 366, "back to the original frame"),
                  ("lpM:L16#spatialSourceOscAxis_pos", 363, "a^osc > 0"),
                  ("lpM:L16#spatialSourceOscPeri_le_length", 363, "a^osc(1 - e^osc) ≤ ¦q_i¦"),
                  ("lpM:L16#spatialSourceOscApo_ge_length", 363, "¦q_i¦ ≤ a^osc(1 + e^osc)"),
                  ("lpM:L16#spatialSourceOscEnergy_neg", 363, "E^osc < 0"),
                  ("lpM:L16#spatialSourceOscEcc_lt_one", 363, "e^osc < 1")],
        "LP3-2: spatial strong-AMD exponential safety without arithmetic hypothesis",
        "Anchor LP3-2 (D64). MAIN T19 without (5), drift supplier replaced as in LP3-1 (LP3-PLAN §2.5, §3)"),
}
