# Track LP, slice LP-adef-pl, wave 1: the planar and dimension-free frozen definition anchors (36 D62 definitions)
# and the 12 reused frozen definitions that the wave-1 anchors import (rule Q6). Writer spec, rendered by
# tools/lp_depgraph_fill.py. Each anchor's DEPS are the frozen definitions its declaration uses (read from the frozen
# declaration file); EDGE locators are the MAIN line that the definition transcribes.

T = "typing data"


def d(stmt, title, H, Q, C, deps=(), note="-"):
    line = stmt.split(":")[-1].split("-")[0]
    unit = stmt.split(":")[-2]
    return dict(kind="definition", title=title, stmt=stmt, proof="-", H=H, Q=Q, C=C, S="none",
                deps=[(t, line, why, unit) for t, why in deps], note=note)


PH = ("lpM:s1:model#Phase", "the phase type Phase (n*2) of planar positions and momenta")
BV = ("lpM:s1:model#bodyVector", "planet i's coordinates q_i or p_i are extracted by bodyVector")
LEN = ("lpM:s1:data#planeLength", "the Euclidean length ¦·¦ of a planar vector")
SQ = ("lpM:s1:data#planeSq", "the squared Euclidean length ¦·¦^2")
DOT = ("lpM:s1:data#planeDot", "the Euclidean scalar product of planar vectors")
OA = ("lpM:s1:chamber#OrderedActions", "the carrier: action vectors in the chamber Q")
SCP = ("lpM:s1:elements#SourceCanonicalPhase", "the carrier of source canonical phases")
SOP = ("lpM:L16:defs#SourceOsculatingPhase", "the carrier of source osculating phases")
OSC_H = "n : ℕ; ν : Fin n → ℝ; μ : ℝ; z : Phase (n*2); i : Fin n (" + T + "; total formula, source meaning on the source osculating phases)"
OSC_Q = "for every n, ν, μ, z, i"
SRC_OSC_H = "z : SourceOsculatingPhase n ν μ; i : Fin n (" + T + ")"

NODES = {
    # ---- dimension-free: chamber and thresholds (MAIN §1 L41-L55)
    "lpM:s1:thresholds#actionAxis": d("s1:45-45", "action axis a_i(I) = (I_i/nu_i)^2",
        "n : ℕ; ν, I : Fin n → ℝ; i : Fin n (" + T + ")", "for every n, ν, I, i",
        "a_i(I) = (I_i/ν_i)^2 (MAIN §1 L45), a total formula; MAIN uses it for I in the chamber Q"),
    "lpM:s1:chamber#chamber": d("s1:41-44", "the action chamber Q",
        "n : ℕ; ν : Fin n → ℝ (" + T + ")", "for every n, ν",
        "Q = {I : I_i > 0 for every i, and (I_1/ν_1)^2 < ... < (I_n/ν_n)^2}, written as a_i(I) < a_j(I) for i < j",
        [("lpM:s1:thresholds#actionAxis", "the ordering (I_i/ν_i)^2 is a_i(I)")]),
    "lpM:s1:thresholds#eccDeficit": d("s1:45-45", "eccentricity deficit D(u) = 1 - sqrt(1 - u^2)",
        "u : ℝ (" + T + ")", "for every u", "D(u) = 1 - √(1 - u^2) (MAIN §1 L45), used on u ∈ [0,1]"),
    "lpM:s1:thresholds#pairFeasible": d("s1:47-48", "pair feasible set {(u,v) in [0,1]^2 : a_i(1+u) >= a_j(1-v)}",
        "n : ℕ; ν, I : Fin n → ℝ; i, j : Fin n (" + T + ")", "for every n, ν, I, i, j",
        "the feasible set {(u,v) : 0 ≤ u, v ≤ 1, a_i(I)(1+u) ≥ a_j(I)(1-v)} of the minimum B_ij in (3)",
        [("lpM:s1:thresholds#actionAxis", "the constraint is written with a_i(I), a_j(I)")]),
    "lpM:s1:thresholds#pairObjective": d("s1:49-49", "pair objective I_i D(u) + I_j D(v)",
        "n : ℕ; I : Fin n → ℝ; i, j : Fin n; (u,v) : ℝ × ℝ (" + T + ")", "for every n, I, i, j, (u,v)",
        "the objective I_i D(u) + I_j D(v) of the minimum B_ij in (3)",
        [("lpM:s1:thresholds#eccDeficit", "the objective is built from D")]),
    "lpM:s1:thresholds#pairThreshold": d("s1:47-50", "pair threshold helper: sInf of the objective over the feasible set",
        "n : ℕ; ν, I : Fin n → ℝ; i, j : Fin n (" + T + ")", "for every n, ν, I, i, j",
        "internal helper: the literal infimum of I_i D(u) + I_j D(v) over the feasible set (total in I); its source "
        "meaning is B_ij(I) of (3) only on its carrier I ∈ Q, i < j, where Lemma 4 shows the infimum is attained",
        [("lpM:s1:thresholds#pairFeasible", "the infimum runs over the feasible set"),
         ("lpM:s1:thresholds#pairObjective", "the infimum is of the pair objective")],
        note="internal helper (FREEZE-PROPOSAL draft 7 role 'internal'); source meaning only on its carrier"),
    "lpM:s1:thresholds#AdjIdx": d("s1:52-52", "index type of adjacent pairs (i, i+1)",
        "n : ℕ (" + T + ")", "for every n",
        "the indices i with i + 1 < n, indexing the adjacent pairs (i, i+1) of B_cross = min_{i<n} B_{i,i+1}",
        note="internal helper (typing of the adjacent-pair family); source meaning only through B_cross"),
    "lpM:s1:thresholds#AdjIdx.upperIdx": d("s1:52-52", "upper index i+1 of an adjacent pair",
        "a : AdjIdx n (" + T + ")", "for every n and adjacent index a", "the upper index i + 1 of the adjacent pair (i, i+1)",
        [("lpM:s1:thresholds#AdjIdx", "defined on the adjacent index type")],
        note="internal helper; source meaning only through B_cross and the gaps of (9)"),
    "lpM:s1:chamber#OrderedActions": d("s1:41-44", "the carrier of action vectors in the chamber Q",
        "n : ℕ; ν : Fin n → ℝ (" + T + ")", "for every n, ν",
        "the subtype of action vectors I ∈ Q, the carrier on which the thresholds (3) are defined (MAIN L55: 'on their "
        "indicated carriers, without arbitrary values outside the action chamber')",
        [("lpM:s1:chamber#chamber", "the carrier is the chamber Q")]),
    "lpM:s1:thresholds#orderedPairThreshold": d("s1:47-50", "pair threshold B_ij(I) on the chamber carrier",
        "n : ℕ; ν : Fin n → ℝ; I ∈ Q (OrderedActions); i, j : Fin n with i < j (the ordering proof is " + T + ")",
        "for every n, ν, I ∈ Q, i < j",
        "B_ij(I) = min over the feasible set of I_i D(u) + I_j D(v), (3), on the carrier I ∈ Q, i < j (the helper value)",
        [OA, ("lpM:s1:thresholds#pairThreshold", "the value is the pair-threshold helper at I")]),
    "lpM:s1:thresholds#orderedCrossThreshold": d("s1:52-52", "cross threshold B_cross(I) = min_{i<n} B_{i,i+1}(I)",
        "n ≥ 2 (" + T + "); ν : Fin n → ℝ; I ∈ Q (OrderedActions)", "for every n ≥ 2, ν, I ∈ Q",
        "B_cross(I) = min_{i<n} B_{i,i+1}(I), (3), as the infimum over the adjacent pairs",
        [("lpM:s1:thresholds#AdjIdx", "the minimum runs over the adjacent pairs (i, i+1)"),
         ("lpM:s1:thresholds#AdjIdx.upperIdx", "the second index of each adjacent pair is i + 1"), OA,
         ("lpM:s1:thresholds#orderedPairThreshold", "the minimum is of the pair thresholds B_{i,i+1}")]),
    "lpM:s1:thresholds#orderedStrongThreshold": d("s1:52-53", "strong threshold B(I) = min(B_cross(I), B_star(I))",
        "n ≥ 2 (" + T + "); ν : Fin n → ℝ; I ∈ Q (OrderedActions)", "for every n ≥ 2, ν, I ∈ Q",
        "B(I) = min(B_cross(I), B_⋆(I)) with B_⋆(I) = min_i I_i, (3)",
        [OA, ("lpM:s1:thresholds#orderedCrossThreshold", "B is the minimum of B_cross and B_star")]),
    # ---- canonical elements (MAIN §1 L26-L37, (9))
    "lpM:s1:elements#strongAMD": d("s1:32-36", "strong AMD C = sum Lambda_i - |L|",
        "n : ℕ; ν : Fin n → ℝ; z : Phase (n*2) (" + T + "; total formula, source meaning on negative-energy states)",
        "for every n, ν, z", "C = Σ_i Λ_i - |L|, (2), with Λ_i the Kepler action and |L| the absolute value of the "
        "total (scalar planar) angular momentum; orientation-free (amendment N8, ruling OD-1/D59)",
        [("lpM:s1:elements#keplerAction", "Λ_i = I_i is the Kepler action"),
         ("lpM:s1:elements#totalMomentum", "L is the total angular momentum"), PH],
        note="AMENDED: N8 (AMENDMENTS.md L17): the orientation-free convention C = ΣΛ - |L| is the frozen one (OD-1)"),
    "lpM:s1:elements#keplerPeri": d("s1:88-89", "canonical perihelion radius a_i(1 - e_i)",
        "n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (" + T + ")", "for every n, ν, z, i",
        "the canonical perihelion radius a_i(1 - e_i) of (9), with a_i the Kepler axis and e_i = |e_i| the length of the "
        "eccentricity vector",
        [("lpM:s1:elements#keplerAxis", "a_i is the Kepler axis"),
         ("lpM:s1:elements#keplerEccVector", "e_i is the length of the eccentricity vector"), PH, LEN]),
    "lpM:s1:elements#keplerApo": d("s1:88-89", "canonical aphelion radius a_i(1 + e_i)",
        "n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (" + T + ")", "for every n, ν, z, i",
        "the canonical aphelion radius a_i(1 + e_i) of (9)",
        [("lpM:s1:elements#keplerAxis", "a_i is the Kepler axis"),
         ("lpM:s1:elements#keplerEccVector", "e_i is the length of the eccentricity vector"), PH, LEN]),
    "lpM:s1:elements#SourceCanonicalPhase": d("s1:26-37", "source canonical phases (nu > 0, q_i != 0, E_i < 0)",
        "n : ℕ; ν : Fin n → ℝ (" + T + ")", "for every n, ν",
        "the planar phases z with ν_i > 0 for every i and, for every planet, |q_i| > 0 and negative Kepler energy "
        "(E_i < 0): the region where (2) is defined",
        [PH, BV, LEN, ("lpM:s1:elements#keplerEnergy", "the carrier requires negative Kepler energy")]),
    "lpM:s1:elements#sourceStrongAMD": d("s1:32-36", "strong AMD C on source canonical phases",
        "z : SourceCanonicalPhase n ν (" + T + ")", "for every n, ν, z", "C(z) = strongAMD ν z on the carrier",
        [SCP, ("lpM:s1:elements#strongAMD", "the value is the strong AMD")]),
    "lpM:s1:elements#sourceKeplerPeri": d("s1:88-89", "canonical perihelion on source canonical phases",
        "z : SourceCanonicalPhase n ν; i : Fin n (" + T + ")", "for every n, ν, z, i", "a_i(1 - e_i) on the carrier",
        [SCP, ("lpM:s1:elements#keplerPeri", "the value is the canonical perihelion")]),
    "lpM:s1:elements#sourceKeplerApo": d("s1:88-89", "canonical aphelion on source canonical phases",
        "z : SourceCanonicalPhase n ν; i : Fin n (" + T + ")", "for every n, ν, z, i", "a_i(1 + e_i) on the carrier",
        [SCP, ("lpM:s1:elements#keplerApo", "the value is the canonical aphelion")]),
    # ---- actual-velocity osculating elements (MAIN L16 (42)-(43), (10))
    "lpM:L16:defs#oscVelocity": d("L16:512-512", "actual heliocentric velocity V_i = p_i/nu_i + mu sum_j p_j",
        OSC_H, OSC_Q, "V_i = p_i/ν_i + μ Σ_j p_j, the actual velocity q̇_i of (10)", [BV, PH]),
    "lpM:L16:defs#oscParam": d("L16:512-512", "gravitational parameter k_i = 1 + mu nu_i",
        "n : ℕ; ν : Fin n → ℝ; μ : ℝ; i : Fin n (" + T + ")", "for every n, ν, μ, i", "k_i = 1 + μ ν_i"),
    "lpM:L16:defs#oscEnergy": d("L16:515-515", "osculating energy E_i^osc = |V_i|^2/2 - k_i/|q_i|",
        OSC_H, OSC_Q, "E_i^osc = ¦V_i¦^2/2 - k_i/¦q_i¦, (42)",
        [BV, PH, LEN, SQ, ("lpM:L16:defs#oscParam", "k_i occurs in the energy"),
         ("lpM:L16:defs#oscVelocity", "V_i occurs in the energy")]),
    "lpM:L16:defs#oscAxis": d("L16:516-516", "osculating axis a_i^osc = -k_i/(2 E_i^osc)",
        OSC_H, OSC_Q, "a_i^osc = -k_i/(2 E_i^osc), (42)",
        [PH, ("lpM:L16:defs#oscEnergy", "the axis is built from E_i^osc"), ("lpM:L16:defs#oscParam", "k_i occurs in the axis")]),
    "lpM:L16:defs#oscEccVector": d("L16:517-517", "osculating eccentricity vector",
        OSC_H, OSC_Q, "e_i^osc = ((¦V_i¦^2 - k_i/¦q_i¦) q_i - (q_i·V_i) V_i)/k_i, (42)",
        [BV, PH, DOT, LEN, SQ, ("lpM:L16:defs#oscParam", "k_i occurs in the vector"),
         ("lpM:L16:defs#oscVelocity", "V_i occurs in the vector")]),
    "lpM:L16:defs#oscEcc": d("L16:518-518", "osculating eccentricity e_i^osc = |e_i^osc|",
        OSC_H, OSC_Q, "e_i^osc = ¦e_i^osc vector¦, (42)",
        [PH, LEN, ("lpM:L16:defs#oscEccVector", "the eccentricity is the length of the vector")]),
    "lpM:L16:defs#oscPeri": d("L16:523-523", "osculating perihelion a_i^osc(1 - e_i^osc)",
        OSC_H, OSC_Q, "the osculating perihelion radius a_i^osc(1 - e_i^osc) of (43)",
        [PH, ("lpM:L16:defs#oscAxis", "a_i^osc occurs"), ("lpM:L16:defs#oscEcc", "e_i^osc occurs")]),
    "lpM:L16:defs#oscApo": d("L16:523-523", "osculating aphelion a_i^osc(1 + e_i^osc)",
        OSC_H, OSC_Q, "the osculating aphelion radius a_i^osc(1 + e_i^osc) of (43)",
        [PH, ("lpM:L16:defs#oscAxis", "a_i^osc occurs"), ("lpM:L16:defs#oscEcc", "e_i^osc occurs")]),
    "lpM:L16:defs#SourceOsculatingPhase": d("L16:510-520",
        "source osculating phases (nu > 0, mu > 0, q_i != 0, E^osc < 0, e^osc < 1)",
        "n : ℕ; ν : Fin n → ℝ; μ : ℝ (" + T + ")", "for every n, ν, μ",
        "the planar phases with ν_i > 0, μ > 0 and, for every planet, ¦q_i¦ > 0, E_i^osc < 0 and e_i^osc < 1: the "
        "nondegenerate elliptic actual-velocity elements of Lemma 16",
        [BV, PH, LEN, ("lpM:L16:defs#oscEcc", "the carrier requires e_i^osc < 1"),
         ("lpM:L16:defs#oscEnergy", "the carrier requires E_i^osc < 0")]),
}
for name, what, base, line in [
        ("sourceOscVelocity", "actual velocity V_i", "oscVelocity", "512"),
        ("sourceOscParam", "gravitational parameter k_i", "oscParam", "512"),
        ("sourceOscEnergy", "osculating energy", "oscEnergy", "515"),
        ("sourceOscAxis", "osculating axis", "oscAxis", "516"),
        ("sourceOscEccVector", "osculating eccentricity vector", "oscEccVector", "517"),
        ("sourceOscEcc", "osculating eccentricity", "oscEcc", "518"),
        ("sourceOscPeri", "osculating perihelion", "oscPeri", "523"),
        ("sourceOscApo", "osculating aphelion", "oscApo", "523")]:
    NODES["lpM:L16:defs#" + name] = d(f"L16:{line}-{line}", what + " on source osculating phases", SRC_OSC_H,
        "for every n, ν, μ, z, i", f"the {what} of Lemma 16 on the carrier", [SOP, ("lpM:L16:defs#" + base, f"the value is the {what}")])

# ---- reused frozen definitions (rule Q6; existing manifest entries bound as LP anchor nodes)
NODES.update({
    "lpM:s1:model#Phase": d("s1:17-17", "phase type: positions and scaled momenta",
        "d : ℕ (" + T + ")", "for every d",
        "canonical coordinates (q, p) ∈ (Fin d → ℝ) × (Fin d → ℝ); the planar LP phases are Phase (n*2): heliocentric "
        "positions q_i and scaled canonical momenta p_i of MAIN §1 L17",
        note="reused frozen definition planetary.Phase.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:model#bodyVector": d("s1:17-17", "planet i's planar coordinate vector",
        "n : ℕ; q : Fin (n*2) → ℝ; i : Fin n (" + T + ")", "for every n, q, i",
        "the two Cartesian coordinates of planet i in a stacked planar vector (q_i or p_i)",
        note="reused frozen definition planetary.bodyVector.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:model#NoCollision": d("s1:24-24", "collision-free configurations: q_i != 0, q_i != q_j",
        "n : ℕ; q : Fin (n*2) → ℝ (" + T + ")", "for every n, q",
        "¦q_i¦ > 0 for every i and ¦q_i - q_j¦ > 0 for i ≠ j: the open physical domain of (1) excludes q_i = 0 and q_i = q_j",
        [BV, LEN], note="reused frozen definition planetary.NoCollision.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:elements#keplerEnergy": d("s1:28-28", "Kepler term nu_i E_i = |p_i|^2/(2 nu_i) - nu_i/|q_i|",
        "n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (" + T + ")", "for every n, ν, z, i",
        "¦p_i¦^2/(2ν_i) - ν_i/¦q_i¦, the Kepler term of (1), equal to ν_i E_i with E_i = ¦v_i¦^2/2 - 1/¦q_i¦, v_i = p_i/ν_i "
        "(MAIN L28); for ν_i > 0 it has the sign of E_i",
        [BV, PH, LEN, SQ],
        note="reused frozen definition planetary.d25.keplerEnergy.v1 (track P), bound as an LP anchor node (Q6); "
             "convention watch: the frozen value is ν_i E_i, not the specific energy E_i"),
    "lpM:s1:elements#keplerAxis": d("s1:33-33", "Kepler axis a_i = -1/(2 E_i)",
        "n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (" + T + ")", "for every n, ν, z, i",
        "a_i = -ν_i/(2 ν_i E_i) = -1/(2E_i), (2); meaningful when E_i < 0 and ν_i > 0",
        [PH, ("lpM:s1:elements#keplerEnergy", "a_i is built from the Kepler term ν_i E_i")],
        note="reused frozen definition planetary.d25.keplerAxis.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:elements#keplerAction": d("s1:33-33", "Kepler action I_i = Lambda_i = nu_i sqrt(a_i)",
        "n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (" + T + ")", "for every n, ν, z, i", "I_i = Λ_i = ν_i √a_i, (2)",
        [PH, ("lpM:s1:elements#keplerAxis", "Λ_i is built from a_i")],
        note="reused frozen definition planetary.d25.keplerAction.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:elements#keplerEccVector": d("s1:29-29", "eccentricity vector e_i",
        "n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (" + T + ")", "for every n, ν, z, i",
        "e_i = (¦v_i¦^2 - 1/¦q_i¦) q_i - (q_i·v_i) v_i with v_i = p_i/ν_i (MAIN L29), written with p_i and ν_i^2",
        [BV, PH, DOT, LEN, SQ],
        note="reused frozen definition planetary.d25.keplerEccVector.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:elements#planeCross": d("s1:34-37", "planar angular momentum q x p (oriented scalar determinant)",
        "q, p : Fin 2 → ℝ (" + T + ")", "for every q, p",
        "q × p = q_0 p_1 - q_1 p_0, the oriented scalar determinant of MAIN L37 (L_i = q_i × p_i)",
        note="reused frozen definition planetary.d25.planeCross.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:elements#totalMomentum": d("s1:34-34", "total planar angular momentum L = sum_i q_i x p_i",
        "n : ℕ; z : Phase (n*2) (" + T + ")", "for every n, z", "L = Σ_i L_i = Σ_i q_i × p_i (scalar, signed), (2)",
        [BV, PH, ("lpM:s1:elements#planeCross", "L_i = q_i × p_i")],
        note="reused frozen definition planetary.d25.totalMomentum.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:data#planeSq": d("s1:15-15", "squared Euclidean length |v|^2",
        "v : Fin 2 → ℝ (" + T + ")", "for every v", "¦v¦^2 = Σ_k v_k^2, the physical Euclidean square of MAIN L15",
        note="reused frozen definition planetary.planeSq.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:data#planeLength": d("s1:15-15", "Euclidean length |v|",
        "v : Fin 2 → ℝ (" + T + ")", "for every v",
        "¦v¦ = √(¦v¦^2), the physical Euclidean length of MAIN L15 (distinct from the max norm on action vectors)",
        [SQ], note="reused frozen definition planetary.planeLength.v1 (track P), bound as an LP anchor node (Q6)"),
    "lpM:s1:data#planeDot": d("s1:29-29", "Euclidean scalar product q . v",
        "v, w : Fin 2 → ℝ (" + T + ")", "for every v, w", "v·w = Σ_k v_k w_k, the scalar product q_i·v_i of MAIN L29",
        note="reused frozen definition planetary.planeDot.v1 (track P), bound as an LP anchor node (Q6)"),
})
