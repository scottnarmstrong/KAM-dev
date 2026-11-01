# Track LP, packet LP-athm-w2: the wave-2 frozen theorem anchors (slice LP-athm, kept in its own packet so that the
# reviewed wave-1 packet is not re-rendered): LP1, LP1-H and the 4 planar osculating characterizations (owner
# lpM:L16). All are roots (Q2). Statement-level uses of frozen definitions are edges at the statement line (SPEC §5).

SOP = ("lpM:L16:defs#SourceOsculatingPhase", "the statement quantifies over source osculating phases")
LEN = ("lpM:s1:data#planeLength", "Euclidean lengths ¦·¦ occur in the statement")
BV = ("lpM:s1:model#bodyVector", "the position q_i occurs in the statement")
OSC_H = ("planar source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 "
         "(SourceOsculatingPhase n ν μ)")
OSC_Q = "for every n, ν, μ, source osculating phase z and i"


def sym(line, unit, pairs):
    return [(t, line, why, unit) for t, why in pairs]


# the frozen definitions that the LP1 / LP1-H statements use (their direct imports), with the use
LP1_SYMS = [
    ("lpM:s1:dioph#IsDiophantine", "the Diophantine premise (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i"),
    ("lpM:s1:model#actualMasses", "the Newtonian masses (1, μν_i)"),
    ("lpM:L1#barycentricPositions", "the reconstructed barycentric positions"),
    ("lpM:L1#barycentricVelocities", "the reconstructed barycentric velocities"),
    ("lpM:s1:model#bodyVector", "the positions q_i"),
    ("lpM:s1:model#IsMovingSolutionOn", "z solves (1) on [-T, T] without collision"),
    ("lpM:L1#IsNewtonSolutionOn", "the reconstructed motion solves Newton's equations"),
    ("lpM:s1:elements#keplerAction", "the actions Λ(z)"),
    ("lpM:s1:elements#keplerAxis", "the axes a_i"),
    ("lpM:s1:elements#keplerEccVector", "the eccentricities e_i = ¦e_i¦"),
    ("lpM:s1:elements#keplerEnergy", "negative Kepler energies"),
    ("lpM:s1:model#MovingUniqueOn", "uniqueness against every local solution"),
    ("lpM:s1:model#Phase", "planar phases"),
    ("lpM:s1:data#planeLength", "Euclidean lengths"),
    ("lpM:s1:thresholds#AdjIdx", "the adjacent pairs of (9)"),
    ("lpM:s1:thresholds#AdjIdx.upperIdx", "the upper index of an adjacent pair"),
    ("lpM:s1:chamber#chamber", "I(t) ∈ Q"),
    ("lpM:s1:thresholds#orderedStrongThreshold", "B(I) in (6) and (8)"),
    ("lpM:L16:defs#oscEcc", "the osculating carrier condition e^osc < 1"),
    ("lpM:L16:defs#oscEnergy", "the osculating carrier condition E^osc < 0"),
    ("lpM:s1:elements#SourceCanonicalPhase", "the canonical carrier"),
    ("lpM:s1:elements#sourceKeplerApo", "canonical aphelia"),
    ("lpM:s1:elements#sourceKeplerPeri", "canonical perihelia"),
    ("lpM:L16:defs#sourceOscApo", "osculating aphelia"),
    ("lpM:L16:defs#sourceOscAxis", "osculating axes"),
    ("lpM:L16:defs#sourceOscEcc", "osculating eccentricities"),
    ("lpM:L16:defs#sourceOscEccVector", "osculating eccentricity vectors"),
    ("lpM:L16:defs#sourceOscEnergy", "osculating energies"),
    ("lpM:L16:defs#sourceOscPeri", "osculating perihelia"),
    ("lpM:L16:defs#SourceOsculatingPhase", "the osculating carrier"),
    ("lpM:s1:elements#sourceStrongAMD", "C in (6) and (8)"),
]
LP1_H = ("n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; "
         "τ > n - 1; planar (d = 2)")
LP1_Q = ("∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (all positive, with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ "
         "d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ planar phase z_0 with ¦q_i¦ > 0, E_i < 0 for every i, a(z_0) ∈ 𝒜, (5) at "
         "ω(I^0) = (ν_i^3/Λ_i^3)_i, Λ(z_0) ∈ Q (a typing binder; it follows from a(z_0) ∈ 𝒜) and C(z_0) ≤ B(Λ(z_0)) - δ; "
         "with T = T_0 exp(cμ^{-EXP}): ∃ z : ℝ → phases, and ∀ t ∈ [-T, T]")
LP1_C = ("z(0) = z_0; z solves (1) on [-T, T] without collision (IsMovingSolutionOn) and agrees with every local solution "
         "(MovingUniqueOn); the barycentric reconstruction solves Newton's equations with masses (1, μν_i) on [-T, T]; for "
         "every t: ¦q_i¦ > 0, E_i < 0; Λ(t) ∈ Q and C(t) ≤ B(Λ(t)) - δ/2; ‖Λ(t) - Λ(0)‖ ≤ A_Λ√μ; ‖a(t) - a(0)‖ ≤ A_a√μ; "
         "¦C(t) - C(0)¦ ≤ nA_Λ√μ; a_i(1 - e_i) ≥ d_⋆; a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair; ¦q_i¦ ≥ d_⋆; "
         "¦q_i - q_j¦ ≥ d_pair for i ≠ j; the osculating elements are nondegenerate (E^osc < 0, e^osc < 1, a source "
         "osculating phase) with E_i^osc < 0, a_i^osc > 0, e_i^osc < 1, a_i^osc(1 - e_i^osc) ≤ ¦q_i¦ ≤ a_i^osc(1 + "
         "e_i^osc), ¦a_i^osc - a_i¦ + ¦e_i^osc - e_i¦ ≤ A_elem μ; ¦a_i^osc(1 ∓ e_i^osc) - a_i(1 ∓ e_i)¦ ≤ A_osc μ; "
         "a_i^osc(1 - e_i^osc) ≥ d_⋆/2; adjacent osculating gaps ≥ d_pair/2")
LP1_S = ("μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ, τ) and are chosen before μ "
         "and z_0")

NODES = {
    "lpM:T15#planar_strongAMD_exponentialSafety": dict(
        kind="theorem", title="LP1: planar strong-AMD exponential safety (Theorem 15 with Lemma 16)",
        stmt="T15:502-506", proof="T15:506-506",
        H=LP1_H, Q=LP1_Q.replace("EXP", "1/(2(τ+1))"), C=LP1_C, S=LP1_S,
        deps=[("lpM:T15", "506", "LP1 is Theorem 15 (the §1 conclusion in d = 2)"),
              ("lpM:T15#reconstruction", "506", "the Newtonian reconstruction clause (Lemma 1)"),
              ("lpM:T15#osculating", "506", "the osculating clauses, including the first estimate of (43) (A_elem)"),
              ("lpM:L16#mu0-choice", "528", "the stated constant relations A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)",
               "L16"),
              ("lpM:L16#sourceOscAxis_pos", "525", "a_i^osc > 0 on the osculating carrier", "L16"),
              ("lpM:L16#sourceOscPeri_le_planeLength", "525", "a_i^osc(1 - e_i^osc) ≤ ¦q_i¦", "L16"),
              ("lpM:L16#planeLength_le_sourceOscApo", "525", "¦q_i¦ ≤ a_i^osc(1 + e_i^osc)", "L16")]
        + sym("69", "s1", LP1_SYMS),
        note="Anchor LP1. Planar instance of the §1 conclusion (Theorem 15), with Lemma 16's elliptic, tangency and (43) "
             "clauses and N10's constant relations; A_elem is the constant A of (43) (MAIN's §1 list omits it). The "
             "premise Λ(z_0) ∈ Q is a typing binder that the source derives from a(0) ∈ 𝒜. AMENDED: N8, N10."),
    "lpM:T15#planar_strongAMD_exponentialSafety_halfInteger": dict(
        kind="corollary", title="LP1-H: LP1 at tau = n - 1/2 (exponent 1/(2n+1))",
        stmt="s1:93-93", proof="s1:93-93",
        H=LP1_H.replace("; τ > n - 1", "") + "; τ = n - 1/2 fixed",
        Q=LP1_Q.replace("EXP", "1/(2n+1)").replace("(5) at", "(5) with τ = n - 1/2 at"), C=LP1_C, S=LP1_S.replace(
            "(n, ν, 𝒜, δ, γ, τ)", "(n, ν, 𝒜, δ, γ)"),
        deps=[("lpM:T15#planar_strongAMD_exponentialSafety", "93", "LP1 with τ = n - 1/2"),
              ("lpM:s1:half-integer", "93", "τ = n - 1/2 > n - 1 and 1/(2(τ+1)) = 1/(2n+1)")]
        + sym("93", "s1", LP1_SYMS),
        note="Anchor LP1-H: the half-integer corollary (MAIN §1 L93) of LP1"),
    # ---- osculating characterizations (Lemma 16)
    "lpM:L16#sourceOscAxis_pos": dict(
        kind="lemma", title="a_i^osc > 0 on source osculating phases", stmt="L16:520-520", proof="L16:527-527",
        H=OSC_H, Q=OSC_Q, C="0 < a_i^osc", S="none",
        deps=[("lpM:L16:defs", "516", "a^osc = -k_i/(2E^osc) with k_i = 1 + μν_i > 0 and E^osc < 0", "L16")]
        + sym("520", "L16", [SOP, ("lpM:L16:defs#sourceOscAxis", "a^osc occurs")])),
    "lpM:L16#sourceOscPeri_pos": dict(
        kind="lemma", title="a_i^osc(1 - e_i^osc) > 0 on source osculating phases", stmt="L16:520-520",
        proof="L16:527-527", H=OSC_H, Q=OSC_Q, C="0 < a_i^osc(1 - e_i^osc)", S="none",
        deps=[("lpM:L16#sourceOscAxis_pos", "527", "a^osc > 0"),
              ("lpM:L16:defs", "518", "e^osc < 1 on the carrier", "L16")]
        + sym("520", "L16", [SOP, ("lpM:L16:defs#sourceOscPeri", "the osculating perihelion occurs")])),
    "lpM:L16#sourceOscPeri_le_planeLength": dict(
        kind="lemma", title="a_i^osc(1 - e_i^osc) <= |q_i| on source osculating phases", stmt="L16:525-525",
        proof="L16:527-527", H=OSC_H, Q=OSC_Q, C="a_i^osc(1 - e_i^osc) ≤ ¦q_i¦", S="none",
        deps=[("lpM:L16#tangent-ellipse", "527", "Lemma 2 with parameter k_i: the ellipse contains the position")]
        + sym("525", "L16", [SOP, ("lpM:L16:defs#sourceOscPeri", "the osculating perihelion occurs"), LEN, BV])),
    "lpM:L16#planeLength_le_sourceOscApo": dict(
        kind="lemma", title="|q_i| <= a_i^osc(1 + e_i^osc) on source osculating phases", stmt="L16:525-525",
        proof="L16:527-527", H=OSC_H, Q=OSC_Q, C="¦q_i¦ ≤ a_i^osc(1 + e_i^osc)", S="none",
        deps=[("lpM:L16#tangent-ellipse", "527", "Lemma 2 with parameter k_i: the ellipse contains the position")]
        + sym("525", "L16", [SOP, ("lpM:L16:defs#sourceOscApo", "the osculating aphelion occurs"), LEN, BV])),
}
