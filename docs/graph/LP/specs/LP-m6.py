# Track LP, slice LP-m6, wave 3: MAIN L530-L603, Lemma 17 (spatial chart), Lemma 18 (spatial domain), Theorem 19.
# Spatial (d = 3). Theorem 19 discharges the chart premises of the d-generic Lemma 14 with Lemmas 17-18 (m = 2n);
# the drift supplier is a route inside Lemma 14 (N7). The headline anchors LP2/LP2-H are in packet LP-athm-w3.

L17H = ("context of the proof of lpM:L17: a reference unit vector e_3; ν > 0; the region (44) I > 0, λ ∈ 𝕋, "
        "(x, y, u, v) ∈ ℝ^4, Γ = (x^2 + y^2)/2, Z = (u^2 + v^2)/2, Γ + Z < I")
L17Q = "for every ν > 0 and every point of (44) (inherited from lpM:L17)"
L18H = ("context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : "
        "¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)")
L18Q = "for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)"
T19H = ("context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, "
        "E_i < 0 and (6)")
T19Q = "for every such μ and initial state (inherited from lpM:T19)"
BS = "lpM:s1:thresholds#orderedStrongThreshold"

NODES = {
    # ---------------- Lemma 17
    "lpM:L17": dict(
        kind="lemma", title="Lemma 17: regular spatial Poincare coordinates on the prograde region (44)-(45)",
        stmt="L17:535-546", proof="L17:548-578",
        H="a reference unit vector e_3; ν > 0 (one planet, d = 3)", Q="for every e_3 and ν > 0",
        C="the map (46) with (18)-(19) is a real analytic symplectic diffeomorphism from the region (44) onto the "
          "negative-energy spatial states with (q × p)·e_3 > 0, with form dI ∧ dλ + dx ∧ dy + du ∧ dv, energy "
          "-ν^3/(2I^2), angular-momentum magnitude G = I - Γ and projection H = I - Γ - Z (45); it is regular at "
          "circular and coplanar orbits; for n bodies the fixed-plane deficit is C_{e_3} = Σ_i I_i - L·e_3 = "
          "½Σ_i(x_i^2 + y_i^2 + u_i^2 + v_i^2)",
        S="none",
        deps=[("lpM:L17#rotation", "548-558", "the rotation R of (46) and (45)"),
              ("lpM:L17#symplectic", "560-571", "symplecticity"),
              ("lpM:L17#inverse", "573-578", "the analytic inverse onto the prograde region"),
              ("lpM:L17#deficit-identity", "578", "the fixed-plane deficit identity"),
              ("lpM:s1:elements", "541", "energy and angular momentum of (2)", "L17")]),
    "lpM:L17#rotation": dict(
        kind="step", title="(46): R from t = (u,-v,0)/(2 sqrt G); R orthogonal, det 1, q x p = G R e_3 gives (45)",
        stmt="L17:548-558", proof="L17:548-558", H=L17H, Q=L17Q,
        C="with Q, P of (19) embedded in the plane, G = I - Γ > 0, t = (u, -v, 0)/(2√G), c = √(1 - ¦t¦^2), R = (1 - 2¦t¦^2)Id "
          "+ 2tt^T + 2c[t]_×, q = RQ, p = RP (46); ¦t¦^2 = Z/(2G) < 1/2 makes the roots analytic; [t]_×^2 = tt^T - ¦t¦^2 Id "
          "gives R^TR = Id, det R = 1, Re_3 = (-cv/√G, -cu/√G, 1 - Z/G), hence q × p = G Re_3 and (45); (46) is the "
          "definition also at Γ = 0 or Z = 0",
        S="none",
        deps=[("lpM:L7", "548", "the planar chart (18)-(19) with angular momentum G = I - Γ"),
              ("lpM:L7#chart-formula", "548", "Q, P are (19)")]),
    "lpM:L17#symplectic": dict(
        kind="step", title="p.dq = I dlambda + Gamma d(-varpi) + Z d(-h_n) + d(2Ie sin E); density of e > 0, Z > 0",
        stmt="L17:541-541", proof="L17:560-571", H=L17H, Q=L17Q,
        C="where e > 0 and Z > 0, with node longitude h_n, inclination ι and perihelion longitude ϖ, R = R_z(h_n)R_x(ι)R_z(-h_n); "
          "the varying rotations contribute G dg and H dh_n (zero about the line of nodes), so with Lemma 7's "
          "computation p·dq = I dλ + Γ d(-ϖ) + Z d(-h_n) + d(2Ie sin E); exterior differentiation gives the form; the set "
          "e > 0, Z > 0 is dense and both sides are analytic, so equality extends to the circular and coplanar loci",
        S="none",
        deps=[("lpM:L17#rotation", "566", "the rotation R and q × p = G Re_3"),
              ("lpM:L7#symplectic", "566", "the unrotated calculation of Lemma 7"),
              ("lpM:ext-identity-theorem", "571", "analytic equality extends from a dense set")]),
    "lpM:L17#inverse": dict(
        kind="step", title="inverse from w-hat = (q x p)/G: c, u, v reconstruct R; Lemma 7's inverse gives x, y, lambda",
        stmt="L17:573-578", proof="L17:573-578", H=L17H, Q=L17Q,
        C="for ŵ = (q × p)/G with ŵ_3 > 0: recover I, G from energy and angular momentum, c = √((1 + ŵ_3)/2), u = -√G ŵ_2/c, "
          "v = -√G ŵ_1/c reconstruct R; R^{-1}q, R^{-1}p are planar with positive angular momentum and Lemma 7's inverse "
          "recovers x, y, λ: onto, unique modulo 2π, analytically invertible, image exactly the prograde negative-energy "
          "region",
        S="none",
        deps=[("lpM:L7#inverse", "578", "Lemma 7's explicit inverse"),
              ("lpM:L17#rotation", "576", "R and q × p = G Re_3")]),
    "lpM:L17#deficit-identity": dict(
        kind="claim", title="fixed-plane deficit C_{e_3} = sum I_i - L.e_3 = |z|^2/2 (summing (45))",
        stmt="L17:545-546", proof="L17:578-578", H=L17H + "; n bodies", Q="for every point of the n-fold product chart",
        C="C_{e_3} = Σ_i I_i - L·e_3 = Σ_i(Γ_i + Z_i) = ½Σ_i(x_i^2 + y_i^2 + u_i^2 + v_i^2)", S="none",
        deps=[("lpM:L17#rotation", "578", "(45): H_i = I_i - Γ_i - Z_i is the e_3-projection of L_i")]),
    # ---------------- Lemma 18
    "lpM:L18": dict(
        kind="lemma", title="Lemma 18: spatial whole-sublevel complex domain (47), m = 2n", stmt="L18:582-586",
        proof="L18:588-597",
        H="the data (n, ν, 𝒜, δ) of lpM:s1:data, spatial (d = 3); 𝓛_δ as in Lemma 8",
        Q="there exist r_*, s, b, M > 0 (fixed first, independent of the reference direction); then for every I^0 ∈ 𝓛_δ, "
          "with Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)",
        C="the conclusions of Lemma 8 hold spatially with m = 2n slow pairs and the product chart of Lemma 17; the domain "
          "includes all states allowed by (6) after aligning e_3 with the initial total angular momentum",
        S="r_*, s, b, M depend only on (n, ν, 𝒜, δ), not on the reference direction",
        deps=[("lpM:L18#margins", "588-593", "the fixed positive margins"),
              ("lpM:L18#whole-ball-safe", "593", "Lemma 5 on the whole ball"),
              ("lpM:L18#extension", "595", "the complex extension (Lemma 8's argument in 6n coordinates)"),
              ("lpM:L18#rotation-invariance", "595", "independence of the reference direction"),
              ("lpM:L18#alignment", "597", "the alignment of e_3 with L"),
              (BS, "584", "B occurs in (47)", "L18")],
        note="AMENDED: N2, N3 (via Lemma 8's construction), N12 (AMENDMENTS.md L21: the spatial tube typing is "
             "engineering only, no graph obligation)"),
    "lpM:L18#margins": dict(
        kind="step", title="Gamma_i + Z_i <= I_i - 3 delta/16: G_i, H_i >= 3 delta/16, c_i^2 > 1/2",
        stmt="L18:582-586", proof="L18:588-593", H=L18H + "; real ‖I - I^0‖_∞ ≤ 4r_g and z ∈ (47)", Q=L18Q,
        C="Γ_i + Z_i ≤ B(I^0) - δ/4 ≤ B(I) - 3δ/16 ≤ I_i - 3δ/16, hence G_i ≥ 3δ/16, H_i ≥ 3δ/16, c_i^2 = 1 - Z_i/(2G_i) > 1/2: "
          "all new radicands and denominators in (46) have a fixed positive margin",
        S="none",
        deps=[("lpM:L8#shared-tube", "590", "the real action neighborhood of Lemma 8 with Ω_B(4r_g) ≤ δ/16"),
              ("lpM:L17", "593", "(45): G = I - Γ, H = I - Γ - Z"), (BS, "590", "B(I) ≤ B_⋆(I) ≤ I_i")]),
    "lpM:L18#whole-ball-safe": dict(
        kind="step", title="fixed-plane deficit = |z|^2/2 >= sum I_i D(e_i): Lemma 5 applies on the whole ball",
        stmt="L18:586-586", proof="L18:593-593", H=L18H, Q=L18Q,
        C="the fixed-plane deficit equals ¦z¦_2^2/2 and each I_i - H_i ≥ I_i - ¦L_i¦ = I_i D(e_i); hence Lemma 5 applies to "
          "every point of the ball, including points whose total angular momentum is not parallel to e_3",
        S="none",
        deps=[("lpM:L17#deficit-identity", "593", "C_{e_3} = ¦z¦^2/2"),
              ("lpM:L2", "593", "¦L_i¦ = I_i √(1 - e_i^2) by (11)"),
              ("lpM:L5", "593", "Lemma 5 in its list form Σ I_i D(e_i) ≤ B(I) - m"),
              ("lpM:L18#margins", "593", "Σ(Γ_i + Z_i) ≤ B(I) - 3δ/16"),
              ("lpM:s1:thresholds#eccDeficit", "593", "D(e) = 1 - √(1 - e^2)")]),
    "lpM:L18#extension": dict(
        kind="step", title="Lemma 8's gluing, uniform widths and complex denominators verbatim in 6n coordinates",
        stmt="L18:582-586", proof="L18:595-595", H=L18H, Q=L18Q,
        C="the family over compact 𝓛_δ, the real action neighborhood and a full angle cell is compact; (18)-(19) and (46) "
          "with the margins give holomorphic local extensions; the gluing, uniform-width and complex-denominator "
          "arguments of Lemma 8 apply verbatim in 6n coordinates; every (q_i - q_j)·(q_i - q_j) has positive real part "
          "on the chosen complex tube",
        S="the widths depend only on (n, ν, 𝒜, δ)",
        deps=[("lpM:L18#margins", "595", "the positive margins of (46)"),
              ("lpM:L18#whole-ball-safe", "595", "the real phases are safe (Lemma 5)"),
              ("lpM:L8#newton-extension", "595", "the local extension argument"),
              ("lpM:L8#gluing", "595", "the gluing and finite-subcover argument"),
              ("lpM:L8#denominators", "595", "the complex-denominator estimate"),
              ("lpM:L8#widths", "595", "the uniform widths and bounds"),
              ("lpM:L8#exact-split", "595", "the product chart gives the exact split h + μf"),
              ("lpM:L17", "595", "the chart (46) is analytic on its region")]),
    "lpM:L18#rotation-invariance": dict(
        kind="step", title="scalar products and potentials are invariant under a simultaneous rotation: bounds independent of the frame",
        stmt="L18:584-586", proof="L18:595-595", H=L18H, Q=L18Q,
        C="the exact scalar products and Newtonian potentials are invariant under a simultaneous real orthogonal rotation "
          "of positions and momenta, so the domain bounds can be chosen for an abstract orthonormal frame, independently "
          "of its orientation", S="none",
        deps=[("lpM:s1:model", "595", "(1) is rotation invariant"),
              ("lpM:L18#extension", "595", "the bounds being made frame-independent")]),
    "lpM:L18#alignment": dict(
        kind="step", title="one fixed rotation per solution takes L/|L| to e_3; C_{e_3} = C along it; Lemma 17 covers it",
        stmt="L18:586-586", proof="L18:597-597", H=L18H + "; an actual initial state with (6)", Q=L18Q,
        C="Lemma 3 gives L ≠ 0; a fixed orientation-preserving orthogonal map taking L/¦L¦ to e_3, applied to q and p, is "
          "symplectic (one per solution, constants rotation invariant); conservation of L gives C_{e_3} = C along the "
          "solution; positive individual projections let Lemma 17 cover it until the stopped boundary",
        S="none",
        deps=[("lpM:L3", "597", "Lemma 3: L ≠ 0 and positive projections H_i under C < B_⋆ (supplied by (6)), and "
               "conservation of L"),
              ("lpM:L18#rotation-invariance", "597", "constants are rotation invariant"),
              ("lpM:L17", "597", "the chart covers the prograde states")]),
    # ---------------- Theorem 19
    "lpM:T19": dict(
        kind="theorem", title="Theorem 19: spatial nonresonant exponential safety (the §1 conclusion for d = 3)",
        stmt="T19:601-601", proof="T19:603-603",
        H="d = 3; n ≥ 2; ν_i > 0 with max_i ν_i = 1; 𝒜 ⊂ {0 < a_1 < ... < a_n} compact; δ, γ > 0; τ > n - 1",
        Q="there exist μ_0, c, T_0, A_I, A_a, d_⋆, d_pair, A_osc > 0; then for every 0 < μ ≤ μ_0 and every spatial initial "
          "state with q_i ≠ 0, E_i < 0 and (6), including circular or coplanar initial orbits",
        C="the conclusion of §1 in d = 3: the unique maximal solution exists on [-T_μ, T_μ] (7), with ellipticity, I(t) ∈ Q, "
          "(8), (9), the star and all pair distances, and the osculating radii and half gaps",
        S="the constants depend only on (n, ν, 𝒜, δ, γ, τ) (d = 3) and precede μ and the initial state; N10",
        deps=[("lpM:T19#align", "603", "alignment, the ball (47), the symplectic chart"),
              ("lpM:T19#apply-L14", "603", "Lemma 14 with m = 2n"),
              ("lpM:T19#osculating", "603", "Lemma 16 in dimension three"),
              ("lpM:T19#reconstruction", "603", "Lemma 1"),
              ("lpM:T19#unrotate", "603", "back to the original frame"),
              ("lpM:s1:data", "70", "the fixed data", "s1"), ("lpM:s1:dioph", "72", "(6) contains (5)", "s1"),
              ("lpM:s1:elements", "72", "C, a, e, I", "s1"), (BS, "72", "B occurs in (6)", "s1"),
              ("lpM:s1:chamber#chamber", "79", "I(t) ∈ Q", "s1")],
        note="spatial MAIN theorem; its frozen statement is LP2 (packet LP-athm-w3). 'Lemmas 1-6, 9-14, 16-18' is read "
             "with N7 (Lemmas 12, 13 are alternative routes inside Lemma 14). AMENDED: N7, N8, N10."),
    "lpM:T19#align": dict(
        kind="step", title="Lemma 18 aligns the frame, gives the ball (47) and the collar; Lemma 17 symplectic chart; (1), (4) exact",
        stmt="T19:601-601", proof="T19:603-603", H=T19H, Q=T19Q,
        C="after the fixed rotation of Lemma 18, the entire ball (47) and a uniform complex collar are available; the chart "
          "is symplectic (Lemma 17) and the Kepler energy and exact perturbation are (1), (4)", S="none",
        deps=[("lpM:L18", "603", "the aligned frame and the domain"),
              ("lpM:L18#alignment", "603", "one fixed rotation per solution"),
              ("lpM:L17", "603", "the symplectic chart"),
              ("lpM:s1:fast", "603", "the Kepler energy h of (4)")]),
    "lpM:T19#apply-L14": dict(
        kind="step", title="n fast angles, 2n slow pairs; |z(t)|^2/2 = C(t) by conservation; Lemma 14 proves (7)-(9)",
        stmt="T19:601-601", proof="T19:603-603", H=T19H, Q=T19Q,
        C="with n fast angles and m = 2n slow pairs, the drift suppliers apply with only dimension constants changed (small "
          "divisors k·ω(I^0), k ∈ ℤ^n, no secular divisors); conservation of the vector angular momentum gives ¦z(t)¦^2/2 = "
          "C(t) in the physical chart; these discharge every condition of Lemma 14, which proves the exponential interval, "
          "the action and AMD bounds, moving-threshold safety, separation and continuation", S="none",
        deps=[("lpM:L14", "603", "Lemma 14"), ("lpM:T19#align", "603", "the chart and domain premises"),
              ("lpM:L17#deficit-identity", "603", "C_{e_3} = ¦z¦^2/2"),
              ("lpM:L3#dynamic", "603", "conservation of L keeps C_{e_3} = C")]),
    "lpM:T19#osculating": dict(
        kind="step", title="Lemma 16 in dimension three: the osculating conclusion",
        stmt="T19:601-601", proof="T19:603-603", H=T19H, Q=T19Q + "; t ∈ [-T_μ, T_μ]",
        C="as lpM:T15#osculating, in d = 3", S="A, A_osc depend only on Lemma 5's compact set and the masses",
        deps=[("lpM:L16", "603", "Lemma 16 (d = 3)"), ("lpM:L16#mu0-choice", "528", "N10", "L16"),
              ("lpM:L16#half-gaps", "529", "the osculating half gaps", "L16"),
              ("lpM:L14#separation", "603", "the orbit stays in Lemma 5's compact set (m = δ/2)", "T19"),
              ("lpM:T19#apply-L14", "603", "the solution on [-T_μ, T_μ]")],
        note="AMENDED: N10 (AMENDMENTS.md L19)"),
    "lpM:T19#reconstruction": dict(
        kind="step", title="Lemma 1 reconstructs the exact Newtonian solution (d = 3)",
        stmt="T19:601-601", proof="T19:603-603", H=T19H, Q=T19Q,
        C="the solution reconstructs a Newtonian (1+n)-body solution with masses (1, μν_i); star and pair distances are "
          "¦q_i¦, ¦q_i - q_j¦", S="none",
        deps=[("lpM:L1", "603", "Lemma 1"), ("lpM:T19#apply-L14", "603", "the collision-free solution")]),
    "lpM:T19#unrotate": dict(
        kind="step", title="the inverse fixed rotation returns to the original frame without changing any inequality",
        stmt="T19:601-601", proof="T19:603-603", H=T19H, Q=T19Q,
        C="all the inequalities of the conclusion are invariant under the inverse fixed rotation", S="none",
        deps=[("lpM:L18#rotation-invariance", "603", "rotation invariance of lengths, H and C"),
              ("lpM:T19#apply-L14", "603", "the inequalities in the aligned frame"),
              ("lpM:T19#osculating", "603", "the osculating inequalities in the aligned frame")]),
}
COV = {
    "lpM:eq44": ("NODE lpM:L17", "display (44), the domain of the chart"),
    "lpM:eq45": ("NODE lpM:L17", "display (45)"),
    "lpM:eq46": ("NODE lpM:L17#rotation", "display (46)"),
    "lpM:eq47": ("NODE lpM:L18", "display (47)"),
}
