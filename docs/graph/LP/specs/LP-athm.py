# Track LP, slice LP-athm, wave 1: the frozen theorem anchors of the LP0 closure.
# LP0 (planar_strongAMD_barrier) and the 10 characterization theorems whose MAIN locus lies in the wave-1 slices
# (thresholds: L4; AMD: L3; Kepler elements: L2 and (2)). All are roots (rule Q2). Source fields are reconstructed
# from the MAIN statement and checked against the frozen declaration's statement (binders, carriers, order).
# Statement-level symbol uses of frozen definitions are edges at the statement line (SPEC §5, symbol rule).

SCP = ("lpM:s1:elements#SourceCanonicalPhase", "the statement quantifies over source canonical phases")
OA = ("lpM:s1:chamber#OrderedActions", "the statement is on the chamber carrier I ∈ Q")
LEN = ("lpM:s1:data#planeLength", "Euclidean lengths ¦·¦ occur in the statement")
BV = ("lpM:s1:model#bodyVector", "the position q_i occurs in the statement")
CHAR_H = "planar source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SourceCanonicalPhase n ν)"


def sym(line, unit, pairs):
    return [(t, line, why, unit) for t, why in pairs]


NODES = {
    "lpM:L5#planar_strongAMD_barrier": dict(
        kind="lemma", title="LP0: the planar sharp strong barrier (planar case of Lemma 5)",
        stmt="L5:164-164", proof="L5:166-175",
        H="n ≥ 2; ν_i > 0 for every i; U ⊂ Q compact; m > 0; planar (d = 2)",
        Q="for every n ≥ 2, ν > 0, compact U ⊂ Q and m > 0: there exist d_⋆ > 0 and d_pair > 0, then (a) for every "
          "I ∈ U and every e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m, and (b) there exists a compact set K of planar "
          "phases such that for every planar phase z with ¦q_i¦ > 0, E_i < 0, Λ(z) ∈ U and C(z) ≤ B(Λ(z)) - m",
        C="(a) a_i(I)(1 - e_i) ≥ d_⋆ for every i and a_{i+1}(I)(1 - e_{i+1}) - a_i(I)(1 + e_i) ≥ d_pair for every "
          "adjacent pair; (b) K is compact and every point of K is collision-free with all Kepler energies negative; "
          "every such z satisfies a_i(1 - e_i) ≥ d_⋆, a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair, ¦q_i¦ ≥ d_⋆ for "
          "every i, ¦q_i - q_j¦ ≥ d_pair for i ≠ j, z ∈ K, and ¦L_i¦ ≥ m with L_i L > 0 for every i (H_i ≥ m in the "
          "invariable frame)",
        S="d_⋆, d_pair and K depend only on (n, ν, U, m) and are chosen before I, e and z (N11 order: d_⋆ is fixed "
          "before the momentum bound)",
        deps=[("lpM:L5", "166-175", "LP0 is the planar case d = 2 of Lemma 5; its proof is that of Lemma 5"),
              ("lpM:L5#pair-distances", "175", "the star and pair distance bounds ¦q_i¦ ≥ d_⋆, ¦q_j - q_i¦ ≥ d_pair "
               "are proved in the proof of Lemma 5 (also restated at §1 L91)")]
        + sym("164", "L5", [
            ("lpM:s1:chamber#chamber", "U ⊂ Q"), ("lpM:s1:thresholds#orderedStrongThreshold", "B(I) occurs"),
            ("lpM:s1:thresholds#eccDeficit", "the deficit Σ I_i D(e_i) occurs"),
            ("lpM:s1:thresholds#actionAxis", "the element-list clause uses a_i(I)"),
            ("lpM:s1:thresholds#AdjIdx", "the adjacent pairs (i, i+1) index the gaps"),
            ("lpM:s1:thresholds#AdjIdx.upperIdx", "the gap of the pair (i, i+1) uses the index i + 1"),
            SCP, ("lpM:s1:elements#sourceStrongAMD", "C occurs on source canonical phases"),
            ("lpM:s1:elements#keplerAxis", "the perihelia and gaps use a_i"),
            ("lpM:s1:elements#keplerEccVector", "the perihelia and gaps use e_i = ¦e_i¦"),
            ("lpM:s1:elements#keplerAction", "the actions Λ(z) ∈ U occur"),
            ("lpM:s1:elements#keplerEnergy", "negative-energy states"), BV, LEN,
            ("lpM:s1:elements#planeCross", "H_i ≥ m is stated through L_i = q_i × p_i"),
            ("lpM:s1:elements#totalMomentum", "the invariable frame is that of L"),
            ("lpM:s1:model#NoCollision", "the compact set lies in the nonsingular physical region"),
            ("lpM:s1:model#Phase", "states are planar phases")]),
        note="Anchor LP0. Planar instance (d = 2) of the d-generic MAIN Lemma 5 (node lpM:L5), bound as its own anchor "
             "node so that the spatial consumers of Lemma 5 do not depend on a planar declaration (SPEC §1). The "
             "distance clauses are proved at L175 and restated at §1 L91. Q3: Lemma 5 consumes only the static part of "
             "Lemma 3. AMENDED: N11 (AMENDMENTS.md L20)."),
    # ---- threshold characterizations (MAIN §1 (3), Lemma 4)
    "lpM:L4#orderedPairThreshold_isLeast": dict(
        kind="lemma", title="B_ij(I) is the attained minimum of the pair objective over the feasible set",
        stmt="s1:47-55", proof="L4:149-149",
        H="I ∈ Q (OrderedActions ν); i < j", Q="for every n, ν, I ∈ Q and i < j",
        C="B_ij(I) is the least element of {I_i D(u) + I_j D(v) : (u,v) feasible}: an attained minimum",
        S="none",
        deps=[("lpM:L4#feasible-compact", "149", "the feasible set is compact and nonempty and the objective is "
               "continuous, so the minimum is attained")]
        + sym("47", "s1", [OA, ("lpM:s1:thresholds#orderedPairThreshold", "B_ij occurs"),
                           ("lpM:s1:thresholds#pairFeasible", "the feasible set occurs"),
                           ("lpM:s1:thresholds#pairObjective", "the objective occurs")]),
        note="L4 says 'for all positive masses'; the frozen statement has no positive-mass premise and rests on the "
             "carrier I ∈ Q, which gives I_i > 0 and 0 ≤ a_i(I) < a_j(I) for i < j (so α = a_i/a_j ∈ [0,1))"),
    "lpM:L4#orderedPairThreshold_existsUnique_value": dict(
        kind="lemma", title="the pair minimum value is the unique least value",
        stmt="s1:47-55", proof="L4:149-149",
        H="I ∈ Q (OrderedActions ν); i < j", Q="for every n, ν, I ∈ Q and i < j; there exists a unique b",
        C="there is exactly one b that is the least element of {I_i D(u) + I_j D(v) : (u,v) feasible}",
        S="none",
        deps=[("lpM:L4#feasible-compact", "149", "existence: the minimum of the pair objective is attained; "
               "uniqueness of a least element is order-theoretic")]
        + sym("47", "s1", [OA, ("lpM:s1:thresholds#pairFeasible", "the feasible set occurs"),
                           ("lpM:s1:thresholds#pairObjective", "the objective occurs")])),
    "lpM:L4#orderedCrossThreshold_isLeast": dict(
        kind="lemma", title="B_cross(I) is the attained minimum of the adjacent pair thresholds",
        stmt="s1:52-55", proof="L4:156-156",
        H="n ≥ 2; I ∈ Q (OrderedActions ν)", Q="for every n ≥ 2, ν and I ∈ Q",
        C="B_cross(I) is the least element of {B_{i,i+1}(I) : i + 1 < n}",
        S="none",
        deps=sym("52", "s1", [OA, ("lpM:s1:thresholds#orderedCrossThreshold", "B_cross occurs"),
                              ("lpM:s1:thresholds#orderedPairThreshold", "the pair thresholds B_{i,i+1} occur")])
        + [("lpM:s1:data", "11", "n ≥ 2 makes the adjacent family nonempty, so the finite minimum is attained", "s1")],
        note="MAIN L55 asserts that the minima of (3) are attained and points to Lemma 4; for the finite minimum over "
             "the n - 1 adjacent pairs this is elementary (L4 L156: 'Finite minima preserve continuity and positivity')"),
    "lpM:L4#orderedStrongThreshold_isLeast": dict(
        kind="lemma", title="B(I) is the attained minimum of the adjacent thresholds and the actions",
        stmt="s1:52-55", proof="L4:156-156",
        H="n ≥ 2; I ∈ Q (OrderedActions ν)", Q="for every n ≥ 2, ν and I ∈ Q",
        C="B(I) = min(B_cross(I), min_i I_i) is the least element of {B_{i,i+1}(I) : i + 1 < n} ∪ {I_i}",
        S="none",
        deps=[("lpM:L4#orderedCrossThreshold_isLeast", "156", "B_cross(I) is attained among the adjacent thresholds")]
        + sym("52", "s1", [OA, ("lpM:s1:thresholds#orderedStrongThreshold", "B occurs"),
                           ("lpM:s1:thresholds#orderedPairThreshold", "the pair thresholds B_{i,i+1} occur")])),
    # ---- AMD characterizations (MAIN Lemma 3)
    "lpM:L3#sourceStrongAMD_nonneg": dict(
        kind="lemma", title="C >= 0 on source canonical phases", stmt="L3:132-132", proof="L3:139-139",
        H=CHAR_H, Q="for every n, ν and source canonical phase z", C="0 ≤ C(z)", S="none",
        deps=[("lpM:L3#amd-nonneg", "139", "¦L¦ ≤ Σ¦L_i¦ ≤ Σ I_i, so C ≥ 0")]
        + sym("132", "L3", [SCP, ("lpM:s1:elements#sourceStrongAMD", "C occurs")])),
    "lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD": dict(
        kind="lemma", title="the deficit bound sum Lambda_i D(e_i) <= C on source canonical phases",
        stmt="L3:133-135", proof="L3:139-139",
        H=CHAR_H, Q="for every n, ν and source canonical phase z", C="Σ_i Λ_i D(e_i) ≤ C(z), with e_i = ¦e_i¦",
        S="none",
        deps=[("lpM:L3#deficit", "139", "for L ≠ 0: H_i ≤ I_i √(1 - e_i^2) and C = Σ(I_i - H_i) give the inequality "
               "of (13)"),
              ("lpM:L3#deficit-zero-L", "139", "the case L = 0, which the frozen statement includes")]
        + sym("134", "L3", [SCP, ("lpM:s1:elements#sourceStrongAMD", "C occurs"),
                            ("lpM:s1:elements#keplerAction", "Λ_i = I_i occurs"),
                            ("lpM:s1:elements#keplerEccVector", "e_i = ¦e_i¦ occurs"), LEN,
                            ("lpM:s1:thresholds#eccDeficit", "D occurs")]),
        note="MAIN states the inequality of (13) on orbits with C < B_⋆; the frozen characterization states it on "
             "every source canonical phase, so it also depends on the gap step lpM:L3#deficit-zero-L"),
    # ---- Kepler-element characterizations (MAIN (2), Lemma 2)
    "lpM:L2#sourceKepler_axis_pos": dict(
        kind="lemma", title="a_i > 0 on source canonical phases", stmt="s1:31-33", proof="s1:31-33",
        H=CHAR_H, Q="for every n, ν, source canonical phase z and i", C="0 < a_i", S="none",
        deps=[("lpM:s1:elements", "31", "when E_i < 0, a_i = -1/(2E_i) > 0 by (2)")]
        + sym("33", "s1", [SCP, ("lpM:s1:elements#keplerAxis", "a_i occurs")])),
    "lpM:L2#sourceKepler_ecc_le_one": dict(
        kind="lemma", title="e_i <= 1 on source canonical phases", stmt="L2:112-115", proof="L2:124-124",
        H=CHAR_H, Q="for every n, ν, source canonical phase z and i", C="e_i = ¦e_i¦ ≤ 1", S="none",
        deps=[("lpM:L2", "124", "(11) gives e^2 = 1 - ¦q × v¦^2/a ≤ 1")]
        + sym("114", "L2", [SCP, ("lpM:s1:elements#keplerEccVector", "the eccentricity vector occurs"), LEN])),
    "lpM:L2#sourceKeplerPeri_le_planeLength": dict(
        kind="lemma", title="a_i(1 - e_i) <= |q_i| on source canonical phases", stmt="L2:118-122",
        proof="L2:124-128", H=CHAR_H, Q="for every n, ν, source canonical phase z and i",
        C="a_i(1 - e_i) ≤ ¦q_i¦", S="none",
        deps=[("lpM:L2", "128", "(12): a(1 - e) ≤ ¦q¦")]
        + sym("119", "L2", [SCP, ("lpM:s1:elements#sourceKeplerPeri", "the canonical perihelion occurs"), LEN, BV])),
    "lpM:L2#planeLength_le_sourceKeplerApo": dict(
        kind="lemma", title="|q_i| <= a_i(1 + e_i) on source canonical phases", stmt="L2:118-122",
        proof="L2:124-128", H=CHAR_H, Q="for every n, ν, source canonical phase z and i",
        C="¦q_i¦ ≤ a_i(1 + e_i)", S="none",
        deps=[("lpM:L2", "128", "(12): ¦q¦ ≤ a(1 + e)")]
        + sym("119", "L2", [SCP, ("lpM:s1:elements#sourceKeplerApo", "the canonical aphelion occurs"), LEN, BV])),
}
