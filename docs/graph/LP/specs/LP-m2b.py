# Track LP, slice LP-m2b, wave 1: MAIN L161-L189, Lemmas 5-6.
# lpM:L5 is the d-generic Lemma 5; LP0 is its planar instance, the anchor node lpM:L5#planar_strongAMD_barrier
# (slice LP-athm). Lemma 5 consumes only the static part of Lemma 3 (Q3). Lemma 6 serves the dynamic anchors.

L5H = ("context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and "
       "C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m")
L5Q = "for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited)"
L6H = ("context of the proof of lpM:L6: the model (1) with its data (n, ν, d, μ > 0); compact 𝓛 ⊂ Q; δ > 0; a solution "
       "with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ, whose actions stay within r of I^0 inside U")
L6Q = "for every compact 𝓛 ⊂ Q, δ > 0, r > 0 and every such solution (inherited from lpM:L6)"

NODES = {
    # ---------------- Lemma 5
    "lpM:L5": dict(
        kind="lemma", title="Lemma 5: the uniform strong barrier (any dimension d)", stmt="L5:164-164",
        proof="L5:166-175",
        H="n ≥ 2 and ν_i > 0 (lpM:s1:data); U ⊂ Q compact; m > 0",
        Q="for every compact U ⊂ Q and m > 0: there exist d_⋆ > 0 and d_pair > 0, then for every negative-energy state "
          "with I ∈ U and C ≤ B(I) - m and every list e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m",
        C="perihelia a_i(1 - e_i) ≥ d_⋆ and adjacent-annulus gaps a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair, for "
          "these states and for these lists; all these states belong to a compact subset of the nonsingular physical "
          "region and satisfy H_i ≥ m in their invariable frame",
        S="d_⋆ and d_pair are uniform: they depend only on (n, ν, U, m)",
        deps=[("lpM:L5#gap-positive", "166", "every adjacent gap is positive"),
              ("lpM:L5#Km-compact", "166-170", "the compact set K_m and d_pair"),
              ("lpM:L5#empty-case", "170", "the empty case"),
              ("lpM:L5#perihelion", "170-175", "the perihelion bound d_⋆ (16)"),
              ("lpM:L5#compact-physical", "175", "the compact nonsingular physical set"),
              ("lpM:L5#projection", "175", "H_i ≥ m"),
              ("lpM:s1:data", "164", "n ≥ 2 and the masses ν are fixed data", "L5"),
              ("lpM:s1:elements", "164", "C, the elements a_i, e_i and H_i of (2)", "L5"),
              ("lpM:s1:chamber#chamber", "164", "U ⊂ Q", "L5"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "164", "B(I) occurs", "L5"),
              ("lpM:s1:thresholds#eccDeficit", "164", "Σ I_i D(e_i) occurs", "L5")],
        note="d-generic source lemma (d ∈ {2,3}); its planar instance is the anchor LP0 "
             "(lpM:L5#planar_strongAMD_barrier); the spatial consumers (Lemma 6, Lemma 16, wave 3) use this node. "
             "AMENDED: N11 (AMENDMENTS.md L20)."),
    "lpM:L5#gap-positive": dict(
        kind="step", title="a nonpositive adjacent gap would be feasible, so C >= B_{i,i+1} >= B: contradiction",
        stmt="L5:164-164", proof="L5:166-166", H=L5H, Q=L5Q,
        C="every adjacent gap a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) is positive: otherwise (e_i, e_{i+1}) is feasible for "
          "B_{i,i+1}(I), and Σ_k I_k D(e_k) ≥ B_{i,i+1}(I) ≥ B(I) (for states via C ≥ Σ_k I_k D(e_k)) contradicts "
          "≤ B(I) - m", S="none",
        deps=[("lpM:L3#static", "166", "the inequality of (13), C ≥ Σ I_k D(e_k); its premise C < B_⋆ holds because "
               "C ≤ B(I) - m < B(I) ≤ B_⋆(I)"),
              ("lpM:s1:thresholds#pairFeasible", "166", "a nonpositive gap makes the pair feasible"),
              ("lpM:s1:thresholds#orderedPairThreshold", "166", "the feasible pair costs at least B_{i,i+1}(I)"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "166", "B_{i,i+1}(I) ≥ B(I)"),
              ("lpM:s1:thresholds#actionAxis", "166", "the constraint uses a_i(I) = (I_i/ν_i)^2"),
              ("lpM:s1:elements", "166", "the Kepler axis of a state equals a_i(I) since I_i = ν_i √a_i")]),
    "lpM:L5#Km-compact": dict(
        kind="step", title="K_m is compact by Lemma 4; d_pair is the minimum of the gaps over K_m",
        stmt="L5:167-169", proof="L5:166-170", H=L5H + "; local data: K_m = {(I,e) ∈ U × [0,1]^n : Σ_i I_i D(e_i) ≤ "
        "B(I) - m}", Q=L5Q,
        C="K_m is compact; every state of the hypothesis gives (I, e) ∈ K_m; every adjacent gap is positive on K_m; "
          "if K_m ≠ ∅, d_pair(U,m) := the minimum over K_m of the finitely many adjacent gaps is positive",
        S="d_pair depends only on (n, ν, U, m)",
        deps=[("lpM:L4", "170", "K_m is compact by the continuity of B (Lemma 4)"),
              ("lpM:L5#gap-positive", "170", "every adjacent gap is positive on K_m"),
              ("lpM:L3#static", "166", "states satisfy Σ I_i D(e_i) ≤ C ≤ B(I) - m, so (I, e) ∈ K_m"),
              ("lpM:ext-compact-min", "170", "the continuous gaps attain their minimum on the compact K_m"),
              ("lpM:s1:thresholds#eccDeficit", "168", "K_m is defined with D"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "168", "K_m is defined with B"),
              ("lpM:s1:thresholds#actionAxis", "170", "the gaps a_{i+1}(I)(1 - e_{i+1}) - a_i(I)(1 + e_i)")]),
    "lpM:L5#empty-case": dict(
        kind="step", title="K_m empty: any positive constants, the assertions are vacuous", stmt="L5:164-164",
        proof="L5:170-170", H=L5H + "; K_m = ∅", Q=L5Q,
        C="if K_m is empty, any positive constants d_⋆, d_pair work and all assertions are vacuous", S="none",
        deps=[("lpM:L5#Km-compact", "170", "the case split is on K_m, which contains every state and list of the "
               "hypothesis")]),
    "lpM:L5#perihelion": dict(
        kind="step", title="(16): sqrt(1 - e_i^2) >= m/I_max and a_i(1 - e_i) >= a_min m^2/(2 I_max^2) =: d_star",
        stmt="L5:171-174", proof="L5:170-175",
        H=L5H + "; K_m ≠ ∅; local data: I_max = max_{I∈U,i} I_i, a_min = min_{I∈U,i} a_i(I) > 0, a_max = max_{I∈U,i} "
        "a_i(I)", Q=L5Q,
        C="the deficit bound I_i D(e_i) ≤ B(I) - m ≤ I_i - m gives √(1 - e_i^2) ≥ m/I_i ≥ m/I_max, and with "
          "1 - e ≥ (1 - e^2)/2, a_i(1 - e_i) ≥ a_min m^2/(2 I_max^2) =: d_⋆ (16); in the nonempty case m ≤ I_max",
        S="d_⋆ depends only on (n, ν, U, m) and is defined before the momentum bound (N11)",
        deps=[("lpM:L5#Km-compact", "170", "every state and list gives a point of K_m"),
              ("lpM:ext-compact-min", "170", "I_max, a_min, a_max are extrema over the compact U"),
              ("lpM:s1:thresholds#eccDeficit", "172", "D(e) = 1 - √(1 - e^2)"),
              ("lpM:s1:thresholds#actionAxis", "170", "a_i(I) on U"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "172", "B(I) ≤ B_⋆(I) ≤ I_i"),
              ("lpM:s1:chamber#chamber", "170", "a_min > 0 because U ⊂ Q")],
        note="AMENDED: N11 (AMENDMENTS.md L20): define d_⋆ := a_min m^2/(2 I_max^2) first, then bound ¦p_i¦"),
    "lpM:L5#bounds": dict(
        kind="step", title="|q_i| <= 2 a_max and |p_i| <= nu_i sqrt(2/d_star) by (12)", stmt="L5:164-164",
        proof="L5:175-175", H=L5H + "; K_m ≠ ∅", Q=L5Q + " (states)",
        C="for every state of the hypothesis, ¦q_i¦ ≤ a_i(1 + e_i) ≤ 2 a_max and ¦p_i¦ ≤ ν_i √(2/d_⋆)", S="none",
        deps=[("lpM:L2", "175", "(12): ¦q¦ ≤ a(1 + e) and ¦p¦^2 = ν^2(2/¦q¦ - 1/a)"),
              ("lpM:L5#perihelion", "175", "¦q_i¦ ≥ a_i(1 - e_i) ≥ d_⋆ and the extrema a_max")],
        note="AMENDED: N11 (AMENDMENTS.md L20)"),
    "lpM:L5#pair-distances": dict(
        kind="step", title="|q_i| >= d_star and ordered radial intervals give |q_j - q_i| >= d_pair",
        stmt="L5:164-164", proof="L5:175-175", H=L5H + "; K_m ≠ ∅", Q=L5Q + " (states); for all i < j",
        C="for every state of the hypothesis, ¦q_i¦ ≥ a_i(1 - e_i) ≥ d_⋆, and ¦q_j - q_i¦ ≥ d_pair for all i < j, by "
          "summing intervening gaps of the ordered radial intervals [a_i(1 - e_i), a_i(1 + e_i)] or by ordering the "
          "endpoints", S="none",
        deps=[("lpM:L2", "175", "(12): ¦q_i¦ lies in its radial interval [a_i(1 - e_i), a_i(1 + e_i)]"),
              ("lpM:L5#perihelion", "175", "a_i(1 - e_i) ≥ d_⋆"),
              ("lpM:L5#Km-compact", "175", "every adjacent gap is at least d_pair")],
        note="the star-distance and pair-distance bounds are proved here and restated at §1 L91; LP0 states them"),
    "lpM:L5#compact-physical": dict(
        kind="step", title="energies <= -1/(2 a_max): a compact nonsingular physical set", stmt="L5:164-164",
        proof="L5:175-175", H=L5H + "; K_m ≠ ∅", Q=L5Q + " (states)",
        C="every state of the hypothesis has energies E_i = -1/(2a_i) ≤ -1/(2a_max); closing the bounded inequalities "
          "(¦q_i¦ ≤ 2a_max, ¦q_i¦ ≥ d_⋆, ¦q_j - q_i¦ ≥ d_pair, ¦p_i¦ ≤ ν_i √(2/d_⋆), E_i ≤ -1/(2a_max)) gives a "
          "compact physical set with no zero denominator and no zero energy that contains all these states",
        S="the compact set depends only on (n, ν, U, m)",
        deps=[("lpM:L5#bounds", "175", "the position and momentum bounds"),
              ("lpM:L5#pair-distances", "175", "the star and pair distance bounds"),
              ("lpM:s1:model", "175", "the nonsingular physical region excludes q_i = 0 and q_i = q_j"),
              ("lpM:s1:elements", "175", "E_i = -1/(2a_i)")]),
    "lpM:L5#projection": dict(
        kind="step", title="H_i >= m by Lemma 3", stmt="L5:164-164", proof="L5:175-175", H=L5H, Q=L5Q + " (states)",
        C="every state of the hypothesis satisfies H_i ≥ m in its invariable frame", S="none",
        deps=[("lpM:L3#static", "175", "Lemma 3: C ≤ B_⋆(I) - m gives H_i ≥ m"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "175", "C ≤ B(I) - m ≤ B_⋆(I) - m")]),
    # ---------------- Lemma 6
    "lpM:L6": dict(
        kind="lemma", title="Lemma 6: the moving threshold (17) and continuation", stmt="L6:179-187",
        proof="L6:189-189",
        H="the model (1) with its data (n, ν, d, μ > 0); 𝓛 ⊂ Q compact; δ > 0",
        Q="for every compact 𝓛 ⊂ Q and δ > 0: there exist a compact neighborhood U ⊂ Q of 𝓛 and the modulus Ω_B; then "
          "for every r > 0 and every solution with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ, whose actions stay within r of I^0 with "
          "that tube in U, and every t",
        C="Ω_B(r) = sup{¦B(I) - B(J)¦ : I, J ∈ U, ‖I - J‖_∞ ≤ r} → 0 as r ↓ 0; C(t) ≤ B(I(t)) - δ + nr + Ω_B(r) (17); "
          "if nr + Ω_B(r) ≤ δ/2, the solution cannot terminate at a finite time while those action and ellipticity "
          "conditions hold; the same holds backwards in time",
        S="U and Ω_B depend only on 𝓛 and the fixed data (chosen before the solution)",
        deps=[("lpM:L6#shared-U", "189", "the neighborhood U and the modulus Ω_B"),
              ("lpM:L6#moving-threshold", "189", "(17)"),
              ("lpM:L6#continuation", "189", "no finite-time termination"),
              ("lpM:L6#backward", "189", "the backward assertion"),
              ("lpM:s1:chamber#chamber", "179", "𝓛, U ⊂ Q", "L6"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "181", "B and Ω_B", "L6")],
        note="AMENDED: N2 (AMENDMENTS.md L11): U is the one compact set shared with Lemmas 8 and 14; it contains the "
             "closed 4r_g sup-norm tube about 𝓛_δ, its modulus Ω_B serves (17), Lemma 8 and (39), and r ≤ r_g (the "
             "consumers in wave 2 record where these requirements are used)"),
    "lpM:L6#shared-U": dict(
        kind="step", title="compact neighborhood U of the compact set inside the chamber; modulus Omega_B -> 0",
        stmt="L6:179-182", proof="L6:189-189", H=L6H, Q=L6Q,
        C="a sufficiently small closed neighborhood U of 𝓛 inside the open chamber is compact, and uniform continuity "
          "of B on U gives Ω_B(r) → 0 as r ↓ 0", S="U depends only on 𝓛 and the fixed data",
        deps=[("lpM:L4", "189", "B is continuous on Q"),
              ("lpM:ext-heine-cantor", "189", "uniform continuity on the compact U"),
              ("lpM:s1:chamber#chamber", "189", "U lies in the open chamber Q"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "189", "the modulus of B")],
        note="AMENDED: N2 (AMENDMENTS.md L11): the closed neighborhood is the one shared compact U containing the "
             "closed 4r_g-tube about 𝓛_δ"),
    "lpM:L6#moving-threshold": dict(
        kind="step", title="(17) from the identity of (13) and B(I^0) <= B(I(t)) + Omega_B(r)",
        stmt="L6:183-186", proof="L6:189-189", H=L6H, Q=L6Q,
        C="C(t) = C_0 + Σ_i(I_i(t) - I_i^0) ≤ C_0 + nr and B(I^0) ≤ B(I(t)) + Ω_B(r), hence C(t) ≤ B(I(t)) - δ + nr + "
          "Ω_B(r) (17)", S="none",
        deps=[("lpM:L3#dynamic", "189", "the action identity of (13)"),
              ("lpM:L6#shared-U", "189", "I^0 and I(t) lie in U within r, so the modulus applies"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "189", "B occurs")]),
    "lpM:L6#local-existence": dict(
        kind="step", title="Lemma 5 compact set, bounded field and derivative, Picard contraction, uniqueness",
        stmt="L6:187-187", proof="L6:189-189", H=L6H + "; nr + Ω_B(r) ≤ δ/2", Q=L6Q,
        C="by (17), C ≤ B(I) - δ/2 along the solution, so Lemma 5 (with U and m = δ/2) supplies a compact nonsingular "
          "physical set with bounded momenta and energies separated from zero; the vector field of (1) and its "
          "derivative are bounded on a neighborhood of it; at every point of that set a local solution exists and is "
          "unique: on a small closed ball, z(t) = z_* + ∫_0^t X_H(z(u)) du is a contraction for times below the ball "
          "radius divided by the field bound and the inverse derivative bound (Picard iteration), and the same "
          "Lipschitz bound gives uniqueness by iterating the integral inequality", S="none",
        deps=[("lpM:L5", "189", "Lemma 5 supplies the compact nonsingular physical set (its premise C ≤ B(I) - δ/2 "
               "comes from (17))"),
              ("lpM:L6#moving-threshold", "189", "(17) gives C ≤ B(I) - δ/2 along the solution"),
              ("lpM:s1:model", "189", "the vector field X_H of (1)"),
              ("lpM:ext-picard", "189", "contraction mapping and Picard iteration"),
              ("lpM:ext-gronwall", "189", "uniqueness by iterating the integral inequality")]),
    "lpM:L6#continuation": dict(
        kind="step", title="limit at a finite endpoint, local solution there and gluing; ellipticity is not lost",
        stmt="L6:187-187", proof="L6:189-189", H=L6H + "; nr + Ω_B(r) ≤ δ/2", Q=L6Q,
        C="the field bound makes the trajectory Lipschitz in time, so at a finite endpoint it has a limit in the compact "
          "set; the local solution there glues to extend the solution; bounded actions keep the energies a fixed "
          "distance below zero, so ellipticity cannot be lost unnoticed; hence the solution cannot terminate at a "
          "finite time while the action and ellipticity conditions hold", S="none",
        deps=[("lpM:L6#local-existence", "189", "local existence and uniqueness at the limit point"),
              ("lpM:L5", "189", "the limit lies in the compact set of Lemma 5")]),
    "lpM:L6#backward": dict(
        kind="step", title="replacing the vector field by its negative gives the backward assertion",
        stmt="L6:187-187", proof="L6:189-189", H=L6H, Q=L6Q + "; t ≤ 0",
        C="the assertions hold backwards in time", S="none",
        deps=[("lpM:L6#continuation", "189", "the forward argument applied to the negated field"),
              ("lpM:L6#moving-threshold", "189", "(17) holds for negative times as well")]),
}
COV = {
    "lpM:L5": ("NODE lpM:L5", "the d-generic Lemma 5; LP0 is its planar instance, the anchor node "
               "lpM:L5#planar_strongAMD_barrier (slice LP-athm, own coverage item)"),
}
