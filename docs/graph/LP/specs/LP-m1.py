# Track LP, slice LP-m1, wave 1: MAIN §1 (L1-L93), data, model, elements, fast part, Diophantine condition and the
# half-integer exponent. The chamber and threshold definitions are fully realized by frozen anchors (slice
# LP-adef-pl), so the planned plain nodes lpM:s1:chamber and lpM:s1:thresholds are not rendered: their inventory
# items map to the anchors. The common conclusion (L69-L93) is the statement content of the headline anchors
# LP1/LP2 (waves 2 and 3); its items are deferred until those nodes exist.

THR = ("lpM:s1:thresholds#actionAxis, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#pairFeasible, "
       "lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#pairThreshold, lpM:s1:thresholds#AdjIdx, "
       "lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:thresholds#orderedPairThreshold, "
       "lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold")

NODES = {
    "lpM:s1:data": dict(
        kind="definition", title="fixed data of track LP (n, nu, A, delta, gamma, tau, d; the two norms)",
        stmt="s1:11-15", proof="-",
        H="none", Q="fixed once: n, ν, 𝒜, δ, γ, τ, d",
        C="an integer n ≥ 2; ν_i > 0 with max_i ν_i = 1; a compact set 𝒜 ⊂ {a ∈ ℝ^n : 0 < a_1 < ... < a_n} (possibly "
          "empty, giving a vacuous assertion); δ, γ > 0; τ > n - 1; space dimension d ∈ {2, 3}; physical Euclidean "
          "lengths ¦·¦ are distinguished from the max norm ‖·‖_∞ on action and complex coordinate vectors",
        S="none",
        note="hypothesis package (SPEC §3): not a global standing assumption; a result that assumes part of it names "
             "that part in SOURCE_HYPOTHESES and depends on this node"),
    "lpM:s1:model": dict(
        kind="definition", title="the exact model: units, masses, symplectic form, Hamiltonian (1), domain, time",
        stmt="s1:17-24", proof="-",
        H="the data of lpM:s1:data (n, ν, d); μ > 0", Q="for every μ > 0",
        C="G = 1 and stellar mass 1; planet masses m_i = μν_i; heliocentric positions q_i and scaled canonical momenta "
          "p_i with symplectic form Σ_i dp_i ∧ dq_i and ι_{X_H}Ω = -dH; the exact Hamiltonian (1) H_μ = Σ_i(¦p_i¦^2/(2ν_i) "
          "- ν_i/¦q_i¦) + μ f, f = ¦Σ_i p_i¦^2/2 - Σ_{i<j} ν_iν_j/¦q_i - q_j¦, on the open domain q_i ≠ 0, q_i ≠ q_j; "
          "solutions use physical time; physical angular momentum and AMD are μL and μC, so δ is a normalized margin; "
          "the splitting (1) uses central Kepler parameter one (L39)",
        S="none",
        deps=[("lpM:s1:data", "17", "the data ν, n, d and the Euclidean length ¦·¦ enter (1)", "s1")]),
    "lpM:s1:elements": dict(
        kind="definition", title="canonical Kepler elements and the strong AMD (2), in dimension d",
        stmt="s1:26-37", proof="-",
        H="the data of lpM:s1:data; a state (q, p) of the model", Q="for every state and every i",
        C="v_i = p_i/ν_i, E_i = ¦v_i¦^2/2 - 1/¦q_i¦, e_i = (¦v_i¦^2 - 1/¦q_i¦) q_i - (q_i·v_i) v_i; when E_i < 0: "
          "a_i = -1/(2E_i), I_i = Λ_i = ν_i √a_i, e_i = ¦e_i¦, L_i = q_i × p_i, L = Σ_i L_i, C = Σ_i I_i - ¦L¦ (2); in "
          "the plane × is the oriented scalar determinant and ¦L¦ its absolute value; a nondegenerate elliptic "
          "canonical state has E_i < 0 and e_i < 1",
        S="none",
        deps=[("lpM:s1:model", "28", "q_i, p_i and ν_i are the variables of the model", "s1"),
              ("lpM:s1:data", "28", "the Euclidean length ¦·¦ and the dimension d", "s1")],
        note="d-generic source definition (d ∈ {2,3}); the planar frozen realizations are the anchors "
             "lpM:s1:elements#* (LP-adef-pl), the spatial ones come in wave 3 (SPEC §5, dimension rule). AMENDED: N8 "
             "(AMENDMENTS.md L17): C = ΣI - ¦L¦ is the frozen convention (OD-1)."),
    "lpM:s1:fast": dict(
        kind="definition", title="fast Hamiltonian h(I) and radian frequencies omega(I) (4)",
        stmt="s1:57-61", proof="-",
        H="the data of lpM:s1:data (n, ν)", Q="for every action vector I with I_i > 0",
        C="h(I) = -Σ_i ν_i^3/(2 I_i^2) and ω_i(I) = ν_i^3/I_i^3 = a_i(I)^{-3/2}, (4)", S="none",
        deps=[("lpM:s1:data", "59", "the masses ν_i enter h and ω", "s1"),
              ("lpM:s1:thresholds#actionAxis", "60", "ω_i(I) = a_i(I)^{-3/2} uses the action axis", "s1")]),
    "lpM:s1:dioph": dict(
        kind="definition", title="the Diophantine condition (5) at omega(I^0); angles of period 2 pi",
        stmt="s1:62-67", proof="-",
        H="the data of lpM:s1:data (γ > 0, τ > n - 1); an initial action vector I^0",
        Q="for every I^0 and every 0 ≠ k ∈ ℤ^n",
        C="¦k·ω(I^0)¦ ≥ γ ¦k¦_1^{-τ} for every 0 ≠ k ∈ ℤ^n (5); all angles of the proof have period 2π (Lemma 13 "
          "records the conversion to period one)",
        S="none",
        deps=[("lpM:s1:fast", "64", "the frequencies ω(I^0) of (4)", "s1"),
              ("lpM:s1:data", "64", "γ and τ are fixed data", "s1")]),
    "lpM:s1:half-integer": dict(
        kind="claim", title="tau = n - 1/2 is admissible and gives exponent 1/(2n+1)",
        stmt="s1:93-93", proof="s1:93-93",
        H="n ≥ 2 (lpM:s1:data)", Q="for every n ≥ 2",
        C="τ = n - 1/2 satisfies τ > n - 1, and a = 1/(2(τ + 1)) = 1/(2n + 1)", S="none",
        deps=[("lpM:s1:data", "93", "admissibility is the condition τ > n - 1 of the data", "s1")],
        note="arithmetic step of the half-integer corollary anchors LP1-H and LP2-H (waves 2 and 3); the exponent "
             "a = 1/(2(τ+1)) is defined in (7)"),
}
DELETE = {
    "lpM:s1:chamber": "fully realized by the anchors lpM:s1:chamber#chamber and #OrderedActions (LP-adef-pl)",
    "lpM:s1:thresholds": "fully realized by the threshold anchors lpM:s1:thresholds#* (LP-adef-pl); B_⋆ is inline",
}
COV = {
    "lpM:s1:chamber": ("NODE lpM:s1:chamber#chamber, lpM:s1:chamber#OrderedActions",
                       "the chamber Q and its carrier are frozen definition anchors (slice LP-adef-pl)"),
    "lpM:s1:thresholds": ("NODE " + THR, "a_i(I), D, the pair feasible set and objective, B_ij, B_cross and B are "
                          "frozen definition anchors (LP-adef-pl); B_⋆ = min_i I_i is inline in B; L55's 'Lemma 4 "
                          "proves this' is a forward pointer, not an edge"),
    "lpM:eq3": ("NODE " + THR, "display (3) is realized by the threshold anchors"),
    "lpM:eq2": ("NODE lpM:s1:elements, lpM:s1:elements#strongAMD",
                "display (2): the d-generic definition node and the frozen strong AMD (orientation-free, N8/OD-1)"),
}
DEFER = {it: "its disposition names the headline anchors of LP1/LP2 (lpM:T15#..., lpM:T19#...), which are wave-2/3 "
             "nodes; it enters the coverage with them"
         for it in ("lpM:s1:conclusion", "lpM:eq6", "lpM:eq7", "lpM:eq8", "lpM:eq9", "lpM:s1:no-crossing")}
