# Track LP, packet LP-athm-w3 (streamlined extraction, D65): the wave-3 frozen theorem anchors of slice LP-athm: LP2,
# LP2-H and the 20 spatial characterizations (owners lpM:L2, lpM:L3, lpM:L16). All are roots (Q2). The source step
# of each characterization is chosen by hand; the statement-symbol edges are the bound frozen definitions that the
# frozen file imports directly (mechanical, SPEC §5), at the statement line.
exec(open("docs/graph/LP/specs/_lp_anchor_util.py").read())

CAN_H = ("spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i "
         "(SpatialSourceCanonicalPhase n ν)")
OSC_H = ("spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 "
         "(SpatialSourceOsculatingPhase n ν μ)")


def char(node, stmt, proof, H, C, src):
    r = BY_NODE[node]
    unit, rng = stmt.split(":")
    line = rng.split("-")[0]
    return dict(kind="lemma", title=C + " (d = 3)", stmt=stmt, proof=proof, H=H,
                Q="for every n, ν" + (", μ" if "Osc" in node else "") + ", carrier point z" +
                ("" if "StrongAMD" in node or "mul_eccDeficit" in node else " and i"),
                C=C, S="none",
                deps=src + [(t, line, "the statement uses " + t.split("#")[-1], unit) for t in imports(r["path"])],
                note="spatial characterization (d = 3), frozen with its definition as one semantic unit")


E = ("lpM:s1:elements", "31")
NODES = {
    "lpM:L2#spatialSourceKeplerAxis_pos": char("lpM:L2#spatialSourceKeplerAxis_pos", "s1:31-33", "s1:31-33", CAN_H,
        "0 < a_i", [("lpM:s1:elements", "31", "when E_i < 0, a_i = -1/(2E_i) > 0 by (2)", "s1")]),
    "lpM:L2#spatialSourceKeplerAction_pos": char("lpM:L2#spatialSourceKeplerAction_pos", "s1:33-33", "s1:33-33",
        CAN_H, "0 < Λ_i", [("lpM:s1:elements", "33", "Λ_i = ν_i √a_i with ν_i, a_i > 0", "s1")]),
    "lpM:L2#spatialSourceKeplerAction_sq": char("lpM:L2#spatialSourceKeplerAction_sq", "s1:33-33", "s1:33-33",
        CAN_H, "Λ_i^2 = ν_i^2 a_i", [("lpM:s1:elements", "33", "Λ_i = ν_i √a_i, (2)", "s1")]),
    "lpM:L2#spatialSourceKeplerEcc_sq": char("lpM:L2#spatialSourceKeplerEcc_sq", "L2:112-115", "L2:124-124", CAN_H,
        "e_i^2 = 1 - ¦L_i¦^2/Λ_i^2", [("lpM:L2", "124", "(11): e^2 = 1 - ¦q × v¦^2/a and ¦q × p¦ = I√(1 - e^2)")]),
    "lpM:L2#spatialSourceKeplerEcc_nonneg": char("lpM:L2#spatialSourceKeplerEcc_nonneg", "s1:34-34", "s1:34-34",
        CAN_H, "0 ≤ e_i", [("lpM:s1:elements", "34", "e_i = ¦e_i¦ is a length", "s1")]),
    "lpM:L2#spatialSourceKeplerEcc_le_one": char("lpM:L2#spatialSourceKeplerEcc_le_one", "L2:112-115", "L2:124-124",
        CAN_H, "e_i ≤ 1", [("lpM:L2", "124", "(11) gives e^2 = 1 - ¦q × v¦^2/a ≤ 1")]),
    "lpM:L2#spatialSourcePlanetAngularMomentum_length": char("lpM:L2#spatialSourcePlanetAngularMomentum_length",
        "L2:112-115", "L2:124-124", CAN_H, "¦L_i¦ = Λ_i √(1 - e_i^2)",
        [("lpM:L2", "124", "(11): ¦q × p¦ = I √(1 - e^2)")]),
    "lpM:L2#spatialSourcePlanetAngularMomentum_length_le": char(
        "lpM:L2#spatialSourcePlanetAngularMomentum_length_le", "L2:112-115", "L2:124-124", CAN_H, "¦L_i¦ ≤ Λ_i",
        [("lpM:L2", "124", "(11): ¦q × p¦ = I √(1 - e^2) ≤ I")]),
    "lpM:L2#spatialSourceKeplerPeri_le_length": char("lpM:L2#spatialSourceKeplerPeri_le_length", "L2:118-122",
        "L2:124-128", CAN_H, "a_i(1 - e_i) ≤ ¦q_i¦", [("lpM:L2", "128", "(12): a(1 - e) ≤ ¦q¦")]),
    "lpM:L2#spatialSourceKeplerApo_ge_length": char("lpM:L2#spatialSourceKeplerApo_ge_length", "L2:118-122",
        "L2:124-128", CAN_H, "¦q_i¦ ≤ a_i(1 + e_i)", [("lpM:L2", "128", "(12): ¦q¦ ≤ a(1 + e)")]),
    "lpM:L3#spatialSourceStrongAMD_nonneg": char("lpM:L3#spatialSourceStrongAMD_nonneg", "L3:132-132", "L3:139-139",
        CAN_H, "0 ≤ C", [("lpM:L3#amd-nonneg", "139", "¦L¦ ≤ Σ¦L_i¦ ≤ Σ I_i")]),
    "lpM:L3#spatialSourceAction_mul_eccDeficit_le": char("lpM:L3#spatialSourceAction_mul_eccDeficit_le", "L3:133-135",
        "L3:139-139", CAN_H, "Σ_i Λ_i(1 - √(1 - e_i^2)) ≤ C",
        [("lpM:L3#deficit", "139", "for L ≠ 0: the inequality of (13)"),
         ("lpM:L3#deficit-zero-L", "139", "the case L = 0, which the frozen statement includes")]),
    "lpM:L16#spatialSourceOscParam_pos": char("lpM:L16#spatialSourceOscParam_pos", "L16:512-512", "L16:527-527", OSC_H,
        "0 < k_i", [("lpM:L16:defs", "512", "k_i = 1 + μν_i with μ, ν_i > 0", "L16")]),
    "lpM:L16#spatialSourceOscEnergy_neg": char("lpM:L16#spatialSourceOscEnergy_neg", "L16:520-520", "L16:527-527",
        OSC_H, "E_i^osc < 0", [("lpM:L16:defs", "515", "E^osc of (42), negative on the carrier", "L16")]),
    "lpM:L16#spatialSourceOscEcc_lt_one": char("lpM:L16#spatialSourceOscEcc_lt_one", "L16:520-520", "L16:527-527",
        OSC_H, "e_i^osc < 1", [("lpM:L16:defs", "518", "e^osc of (42), below one on the carrier", "L16")]),
    "lpM:L16#spatialSourceOscEcc_nonneg": char("lpM:L16#spatialSourceOscEcc_nonneg", "L16:518-518", "L16:527-527",
        OSC_H, "0 ≤ e_i^osc", [("lpM:L16:defs", "518", "e^osc = ¦e^osc¦ is a length", "L16")]),
    "lpM:L16#spatialSourceOscAxis_pos": char("lpM:L16#spatialSourceOscAxis_pos", "L16:520-520", "L16:527-527", OSC_H,
        "0 < a_i^osc", [("lpM:L16:defs", "516", "a^osc = -k_i/(2E^osc) with k_i > 0, E^osc < 0", "L16")]),
    "lpM:L16#spatialSourceOscPeri_pos": char("lpM:L16#spatialSourceOscPeri_pos", "L16:520-520", "L16:527-527", OSC_H,
        "0 < a_i^osc(1 - e_i^osc)", [("lpM:L16#spatialSourceOscAxis_pos", "527", "a^osc > 0"),
                                    ("lpM:L16#spatialSourceOscEcc_lt_one", "527", "e^osc < 1")]),
    "lpM:L16#spatialSourceOscPeri_le_length": char("lpM:L16#spatialSourceOscPeri_le_length", "L16:525-525",
        "L16:527-527", OSC_H, "a_i^osc(1 - e_i^osc) ≤ ¦q_i¦",
        [("lpM:L16#tangent-ellipse", "527", "Lemma 2 with parameter k_i: the ellipse contains the position")]),
    "lpM:L16#spatialSourceOscApo_ge_length": char("lpM:L16#spatialSourceOscApo_ge_length", "L16:525-525",
        "L16:527-527", OSC_H, "¦q_i¦ ≤ a_i^osc(1 + e_i^osc)",
        [("lpM:L16#tangent-ellipse", "527", "Lemma 2 with parameter k_i: the ellipse contains the position")]),
}

LP2_H = ("n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; "
         "τ > n - 1; spatial (d = 3)")
LP2_Q = ("∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); "
         "then ∀ 0 < μ ≤ μ_0, ∀ spatial phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i, "
         "Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-EXP}): ∃ z : ℝ → spatial "
         "phases, and ∀ t ∈ [-T, T]")
LP2_C = ("z(0) = z_0; z solves the spatial (1) on [-T, T] without collision and agrees with every local solution; the "
         "barycentric reconstruction solves Newton's equations with masses (1, μν_i); for every t: elliptic, Λ(t) ∈ Q, "
         "C(t) ≤ B(Λ(t)) - δ/2, the drift bounds A_Λ√μ, A_a√μ, nA_Λ√μ of (8), (9) with d_⋆, d_pair, star distances ≥ d_⋆, "
         "pair distances ≥ d_pair; nondegenerate osculating elements with a^osc > 0, e^osc < 1, a^osc(1 - e^osc) ≤ ¦q_i¦ ≤ "
         "a^osc(1 + e^osc), ¦a^osc - a¦ + ¦e^osc - e¦ ≤ A_elem μ, perihelion and aphelion errors ≤ A_osc μ, osculating "
         "gaps ≥ d_⋆/2, d_pair/2 (as in LP1, spatial carriers)")
LP2_S = ("μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ, τ) and are chosen before μ "
         "and z_0")
CHARS = [("lpM:L16#spatialSourceOscAxis_pos", "a^osc > 0"), ("lpM:L16#spatialSourceOscPeri_le_length",
          "a^osc(1 - e^osc) ≤ ¦q_i¦"), ("lpM:L16#spatialSourceOscApo_ge_length", "¦q_i¦ ≤ a^osc(1 + e^osc)"),
         ("lpM:L16#spatialSourceOscEnergy_neg", "E^osc < 0"), ("lpM:L16#spatialSourceOscEcc_lt_one", "e^osc < 1")]


def lp2(node, stmt, H, Q, S, deps):
    r = BY_NODE[node]
    unit, rng = stmt.split(":")
    line = rng.split("-")[0]
    return dict(H=H, Q=Q, C=LP2_C, S=S, stmt=stmt, proof=stmt,
                deps=deps + [(t, line, "the statement uses " + t.split("#")[-1], unit) for t in imports(r["path"])])


NODES["lpM:T19#spatial_strongAMD_exponentialSafety"] = dict(
    kind="theorem", title="LP2: spatial strong-AMD exponential safety (Theorem 19 with Lemma 16)",
    note="Anchor LP2. Spatial instance of the §1 conclusion (Theorem 19), with Lemma 16's clauses and N10's constant "
         "relations; A_elem is the constant A of (43). AMENDED: N8, N10.",
    **lp2("lpM:T19#spatial_strongAMD_exponentialSafety", "T19:601-601", LP2_H, LP2_Q.replace("EXP", "1/(2(τ+1))"), LP2_S,
          [("lpM:T19", "603", "LP2 is Theorem 19 (the §1 conclusion in d = 3)", "T19"),
           ("lpM:T19#reconstruction", "603", "the Newtonian reconstruction clause", "T19"),
           ("lpM:T19#osculating", "603", "the osculating clauses, including A_elem", "T19"),
           ("lpM:L16#mu0-choice", "528", "A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)", "L16")]
          + [(t, "525", why, "L16") for t, why in CHARS]))
NODES["lpM:T19#spatial_strongAMD_exponentialSafety"]["proof"] = "T19:603-603"
NODES["lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger"] = dict(
    kind="corollary", title="LP2-H: LP2 at tau = n - 1/2 (exponent 1/(2n+1))",
    note="Anchor LP2-H: the half-integer corollary (MAIN §1 L93) of LP2",
    **lp2("lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger", "s1:93-93",
          LP2_H.replace("; τ > n - 1", "") + "; τ = n - 1/2 fixed", LP2_Q.replace("EXP", "1/(2n+1)"),
          LP2_S.replace("(n, ν, 𝒜, δ, γ, τ)", "(n, ν, 𝒜, δ, γ)"),
          [("lpM:T19#spatial_strongAMD_exponentialSafety", "93", "LP2 with τ = n - 1/2", "s1"),
           ("lpM:s1:half-integer", "93", "τ = n - 1/2 > n - 1 and 1/(2(τ+1)) = 1/(2n+1)", "s1")]))
