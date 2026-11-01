# Track LP, slice LP-m2a, wave 1: MAIN L94-L160, Lemmas 1-4.
# Q3 (ruling root-b8): Lemma 3 splits into a static part lpM:L3#static (consumed by Lemma 5, hence LP0) and a dynamic
# part lpM:L3#dynamic (consumed by Lemma 6 and the dynamic anchors); lpM:L3 is their conjunction with the planar
# orientation clause. Q4: Lemma 4's statement is recorded without its unconsumed clauses (radial contact and the
# Laskar-Petit identification at L143, sharpness at L147); their items are EXCLUDED.
# MAIN nodes are d-generic; dimension-specific frozen carriers attach at the anchors (SPEC §5, dimension rule).

L1H = "context of the proof of lpM:L1: d ∈ {2,3}; ν_i > 0; μ > 0"
L2H = "context of the proof of lpM:L2: ν > 0, q ≠ 0, v = p/ν, E = ¦v¦^2/2 - 1/¦q¦ < 0"
L3H = ("context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state "
       "(E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence")
L4H = "context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j"
L4Q = "for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)"
ALPHA = "local data: α = a_i(I)/a_j(I) ∈ (0,1)"

NODES = {
    # ---------------- Lemma 1
    "lpM:L1": dict(
        kind="lemma", title="Lemma 1: normalization and Newtonian reconstruction", stmt="L1:99-99", proof="L1:101-108",
        H="d ∈ {2,3}; ν_i > 0; μ > 0", Q="for every d ∈ {2,3}, ν > 0 and μ > 0",
        C="the Hamiltonian (1) is the zero-total-momentum translation reduction of the Newtonian (1+n)-body "
          "Hamiltonian, divided by μ, in unchanged time; its solutions reconstruct Newtonian solutions with masses "
          "(1, μν_1, ..., μν_n)", S="none",
        deps=[("lpM:L1#reduction", "101-102", "the reduction and the division by μ give (1)"),
              ("lpM:L1#reconstruction", "104-108", "the explicit inverse reconstructs Newtonian solutions"),
              ("lpM:s1:model", "99", "the statement concerns Hamiltonian (1) and the masses μν_i")]),
    "lpM:L1#reduction": dict(
        kind="step", title="translation reduction with P_i = mu p_i, cancelling mu gives (1)",
        stmt="L1:101-102", proof="L1:101-102", H=L1H, Q="for every d, ν, μ (inherited from lpM:L1)",
        C="in barycentric coordinates with P_i = μ p_i and P_0 = -Σ_i P_i, the translation reduction has relative "
          "positions q_i = x_i - x_0 and momenta P_i (Σ_{i=0}^n P_i·dx_i = Σ_{i≥1} P_i·dq_i), kinetic energy "
          "Σ_i ¦P_i¦^2/(2μν_i) + ¦Σ_i P_i¦^2/2 and potential -Σ_i μν_i/¦q_i¦ - Σ_{i<j} μ^2 ν_iν_j/¦q_i - q_j¦; the "
          "symplectic form and the Hamiltonian both acquire the factor μ, and cancelling it gives (1) with the same "
          "time", S="none",
        deps=[("lpM:s1:model", "102", "the result is compared with the Hamiltonian (1) and its symplectic form")]),
    "lpM:L1#velocity": dict(
        kind="display", title="(10): Hamilton's equation for q_i, the actual velocity", stmt="L1:105-107",
        proof="L1:104-107", H=L1H + "; a solution of (1)", Q="along every solution of (1) and for every i",
        C="q̇_i = p_i/ν_i + μ Σ_j p_j, (10)", S="none",
        deps=[("lpM:s1:model", "106", "Hamilton's equation q̇_i = ∂H_μ/∂p_i for the Hamiltonian (1)")],
        note="display (10), refined into its own node because Lemma 3 (recoil term) and Lemma 16 (V_i) consume it "
             "independently of the reconstruction (SPEC §5, displays)"),
    "lpM:L1#reconstruction": dict(
        kind="step", title="explicit inverse: barycentric positions and velocities, Newton's equations",
        stmt="L1:104-108", proof="L1:104-108", H=L1H + "; a solution of (1)",
        Q="for every solution of (1) (inherited from lpM:L1)",
        C="with M = 1 + μΣ_i ν_i, x_0 = -μ Σ_i ν_i q_i/M, x_i = x_0 + q_i, ẋ_0 = -μ Σ_i p_i and ẋ_i = p_i/ν_i, the "
          "displayed velocities differentiate the displayed positions, and the equations for ṗ_i are Newton's "
          "equations after multiplying the planet momenta by μ; pair differences are q_i - q_j and star differences "
          "q_i", S="none",
        deps=[("lpM:L1#velocity", "105-108", "Hamilton's equation (10) shows that the displayed velocities "
               "differentiate the displayed positions"),
              ("lpM:L1#reduction", "108", "the planet momenta are multiplied by μ (P_i = μ p_i) as in the reduction"),
              ("lpM:s1:model", "108", "the equations for ṗ_i come from differentiating the potentials in (1)")]),
    # ---------------- Lemma 2
    "lpM:L2": dict(
        kind="lemma", title="Lemma 2: elementary orbital identities (11)-(12)", stmt="L2:112-122", proof="L2:124-128",
        H="ν > 0; q ≠ 0; v = p/ν; E = ¦v¦^2/2 - 1/¦q¦ < 0 (one planet, any dimension)",
        Q="for every ν > 0, q ≠ 0 and p with E < 0",
        C="e^2 = 1 + 2E¦q × v¦^2 = 1 - ¦q × v¦^2/a ≤ 1 and ¦q × p¦ = I √(1 - e^2) (11); a(1 - e) ≤ ¦q¦ ≤ a(1 + e) and "
          "¦p¦^2 = ν^2(2/¦q¦ - 1/a) (12); including the radial case e = 1", S="none",
        deps=[("lpM:L2#ecc-identity", "124", "the first identity of (11) and its substitutions"),
              ("lpM:L2#radial-bounds", "124-128", "the bounds and the momentum identity (12)"),
              ("lpM:s1:elements", "112", "definitions (2) of a, e, I")]),
    "lpM:L2#ecc-identity": dict(
        kind="step", title="(11): e^2 = 1 + 2E|q x v|^2 = 1 - |q x v|^2/a and |q x p| = I sqrt(1 - e^2)",
        stmt="L2:113-115", proof="L2:124-124", H=L2H, Q="for every such q, p (inherited from lpM:L2)",
        C="expanding the square of (¦v¦^2 - 1/¦q¦) q - (q·v) v with ¦q × v¦^2 = ¦q¦^2¦v¦^2 - (q·v)^2 gives "
          "e^2 = 1 + 2E¦q × v¦^2; substituting 2E = -1/a gives e^2 = 1 - ¦q × v¦^2/a ≤ 1 and ¦q × p¦ = I √(1 - e^2)",
        S="none", deps=[("lpM:s1:elements", "124", "the eccentricity vector, E, a and I of (2)")]),
    "lpM:L2#radial-bounds": dict(
        kind="step", title="(12): a(1-e) <= |q| <= a(1+e) and |p|^2 = nu^2(2/|q| - 1/a)",
        stmt="L2:118-121", proof="L2:124-128", H=L2H + "; local data: r = ¦q¦, ℓ = q × v",
        Q="for every such q, p (inherited from lpM:L2)",
        C="the energy identity and the radial/tangential decomposition give (q·v)^2 = 2r - r^2/a - ¦ℓ¦^2 ≥ 0; with "
          "¦ℓ¦^2 = a(1 - e^2), completing the square gives (r - a)^2 ≤ a^2 e^2, i.e. a(1 - e) ≤ r ≤ a(1 + e); "
          "¦p¦^2 = ν^2(2/¦q¦ - 1/a) is the energy definition", S="none",
        deps=[("lpM:L2#ecc-identity", "128", "uses ¦ℓ¦^2 = a(1 - e^2) from (11)"),
              ("lpM:s1:elements", "124", "the energy definition E = ¦v¦^2/2 - 1/¦q¦ = -1/(2a)")]),
    # ---------------- Lemma 3 (Q3 split)
    "lpM:L3": dict(
        kind="lemma", title="Lemma 3: exact angular momentum and the AMD identity (static and dynamic parts)",
        stmt="L3:132-137", proof="L3:139-139",
        H="the model (1) with its data (n, ν, d, μ > 0); m > 0 in the last clause",
        Q="for every solution of (1) on a connected interval of existence, every negative-energy state, and m > 0",
        C="L is constant on every connected interval of existence of (1); C ≥ 0 in the negative-energy region; if "
          "C < B_⋆(I) then L ≠ 0 and all H_i = L_i·L̂ are positive, and on such an orbit C(t) - C(0) = Σ_i(I_i(t) - "
          "I_i(0)) and C = Σ_i(I_i - H_i) ≥ Σ_i I_i D(e_i) (13); if C ≤ B_⋆(I) - m then H_i ≥ m for every i; in the "
          "planar case, orienting the plane so that L > 0 makes all individual scalar angular momenta positive",
        S="none",
        deps=[("lpM:L3#static", "139", "the static clauses: C ≥ 0, L ≠ 0, H_i > 0, H_i ≥ m and the inequality of (13)"),
              ("lpM:L3#dynamic", "139", "the dynamic clauses: conservation of L and the identity of (13)"),
              ("lpM:L3#planar-orientation", "137", "the planar orientation clause")],
        note="Q3 split (ruling root-b8): the conjunction of lpM:L3#static (consumed by Lemma 5, hence LP0, which thus "
             "does not reach Lemma 1) and lpM:L3#dynamic (consumed by Lemma 6 and the dynamic anchors)"),
    "lpM:L3#static": dict(
        kind="lemma", title="Lemma 3, static part: C >= 0, L != 0, positive projections, H_i >= m, inequality of (13)",
        stmt="L3:132-137", proof="L3:139-139",
        H="a negative-energy state of the model (E_i < 0, q_i ≠ 0 for every i; ν > 0); m > 0 in the last clause",
        Q="for every negative-energy state and every m > 0",
        C="C ≥ 0; if C < B_⋆(I) = min_i I_i then L ≠ 0, every H_i = L_i·L̂ is positive, and C = Σ_i(I_i - H_i) ≥ "
          "Σ_i I_i D(e_i) (the inequality of (13)); if C ≤ B_⋆(I) - m then H_i ≥ m for every i", S="none",
        deps=[("lpM:L3#amd-nonneg", "139", "C ≥ 0"),
              ("lpM:L3#L-nonzero", "139", "L ≠ 0 when C < B_⋆"),
              ("lpM:L3#projections", "139", "H_i ≥ I_i - C, hence H_i > 0 and H_i ≥ m"),
              ("lpM:L3#deficit", "139", "the inequality of (13)"),
              ("lpM:s1:thresholds#eccDeficit", "135", "D occurs in (13)", "L3")],
        note="Q3 split: no dynamics is used; this is the part of Lemma 3 that Lemma 5 (and LP0) consumes"),
    "lpM:L3#dynamic": dict(
        kind="lemma", title="Lemma 3, dynamic part: L is conserved and C(t) - C(0) = sum(I_i(t) - I_i(0))",
        stmt="L3:132-135", proof="L3:139-139",
        H="a solution of (1) on a connected interval of existence; for the identity, negative energies along it "
          "(MAIN: 'on such an orbit', C < B_⋆)",
        Q="for every such solution and all times t in its interval",
        C="L(t) is constant; C(t) - C(0) = Σ_i(I_i(t) - I_i(0)), the identity of (13)", S="none",
        deps=[("lpM:L3#conservation", "139", "L̇ = 0 and constancy"),
              ("lpM:s1:elements", "139", "C = Σ I_i - ¦L¦ with constant ¦L¦ gives the identity")],
        note="Q3 split: the dynamic clauses of Lemma 3 (consumed by Lemma 6 and the dynamic anchors)"),
    "lpM:L3#conservation": dict(
        kind="step", title="dL/dt = 0: recoil term, central forces and pair torques vanish; constancy by FTC",
        stmt="L3:132-132", proof="L3:139-139", H=L3H + " (a solution on a connected interval)",
        Q="along every solution of (1) on a connected interval of existence",
        C="differentiating Σ_i q_i × p_i: the recoil contribution from q̇_i is μ(Σ_j p_j) × (Σ_i p_i) = 0, the other "
          "kinetic terms vanish individually, central forces have zero torque, and the two forces of each planet "
          "pair contribute a multiple of (q_i - q_j) × (q_i - q_j) = 0; thus L̇ = 0 and L is constant", S="none",
        deps=[("lpM:L1#velocity", "139", "the recoil term comes from q̇_i = p_i/ν_i + μΣ_j p_j of (10)"),
              ("lpM:s1:model", "139", "the forces are those of the Hamiltonian (1)"),
              ("lpM:s1:elements", "139", "L = Σ_i q_i × p_i"),
              ("lpM:ext-ftc", "139", "the fundamental theorem of calculus gives constancy")]),
    "lpM:L3#amd-nonneg": dict(
        kind="step", title="|L| <= sum |L_i| <= sum I_i, so C >= 0", stmt="L3:132-132", proof="L3:139-139",
        H=L3H + " (a negative-energy state)", Q="for every negative-energy state",
        C="¦L¦ ≤ Σ_i ¦L_i¦ ≤ Σ_i I_i, hence C = Σ_i I_i - ¦L¦ ≥ 0", S="none",
        deps=[("lpM:L2", "139", "by (11), ¦L_i¦ = ¦q_i × p_i¦ = I_i √(1 - e_i^2) ≤ I_i"),
              ("lpM:s1:elements", "139", "C = Σ I_i - ¦L¦")]),
    "lpM:L3#L-nonzero": dict(
        kind="step", title="C < B_star forces L != 0", stmt="L3:132-132", proof="L3:139-139",
        H=L3H + " (a negative-energy state with C < B_⋆(I))", Q="for every such state",
        C="if L = 0 then C = Σ_i I_i ≥ min_i I_i = B_⋆(I), contradicting C < B_⋆(I); so L ≠ 0", S="none",
        deps=[("lpM:s1:elements", "139", "C = Σ I_i - ¦L¦ and the actions I_i > 0")]),
    "lpM:L3#projections": dict(
        kind="step", title="0 <= I_i - H_i, sum = C, so H_i >= I_i - C (> 0, >= m)", stmt="L3:132-137",
        proof="L3:139-139", H=L3H + " (a negative-energy state with L ≠ 0); local data: L̂ = L/¦L¦, H_i = L_i·L̂",
        Q="for every such state and every m > 0",
        C="H_i ≤ ¦L_i¦ ≤ I_i, so every I_i - H_i ≥ 0, and Σ_i (I_i - H_i) = C; hence H_i ≥ I_i - C ≥ B_⋆(I) - C, so "
          "H_i > 0 when C < B_⋆(I) and H_i ≥ m when C ≤ B_⋆(I) - m", S="none",
        deps=[("lpM:L3#L-nonzero", "139", "L ≠ 0 (when C < B_⋆) makes L̂ and H_i defined"),
              ("lpM:L2", "139", "¦L_i¦ ≤ I_i by (11)"),
              ("lpM:s1:elements", "139", "Σ_i H_i = ¦L¦ and C = Σ I_i - ¦L¦")]),
    "lpM:L3#deficit": dict(
        kind="step", title="H_i <= I_i sqrt(1 - e_i^2) gives C >= sum I_i D(e_i) (inequality of (13))",
        stmt="L3:133-135", proof="L3:139-139",
        H=L3H + " (a negative-energy state with L ≠ 0, as on an orbit with C < B_⋆); local data: L̂, H_i",
        Q="for every such state",
        C="H_i ≤ ¦L_i¦ = I_i √(1 - e_i^2), hence C = Σ_i(I_i - H_i) ≥ Σ_i I_i(1 - √(1 - e_i^2)) = Σ_i I_i D(e_i)",
        S="none",
        deps=[("lpM:L3#projections", "139", "C = Σ_i (I_i - H_i)"),
              ("lpM:L2", "139", "¦L_i¦ = I_i √(1 - e_i^2) by (11)"),
              ("lpM:s1:thresholds#eccDeficit", "139", "D(e) = 1 - √(1 - e^2)")],
        note="the argument uses only L ≠ 0 (to define L̂); MAIN applies it on orbits with C < B_⋆"),
    "lpM:L3#deficit-zero-L": dict(
        kind="step", title="the deficit bound when L = 0: C = sum I_i >= sum I_i D(e_i)",
        stmt="L3:133-135", proof="L3:139-139", H=L3H + " (a negative-energy state with L = 0)",
        Q="for every such state", C="C = Σ_i I_i ≥ Σ_i I_i D(e_i), since 0 ≤ e_i ≤ 1 and D(e) ≤ 1 on [0,1]", S="none",
        deps=[("lpM:L2", "139", "e_i ≤ 1 by (11)"),
              ("lpM:s1:thresholds#eccDeficit", "139", "D(e) ≤ 1 for e ∈ [0,1]"),
              ("lpM:s1:elements", "139", "C = Σ I_i - ¦L¦ = Σ I_i when L = 0")],
        note="SOURCE_GAP: MAIN states and proves the inequality of (13) only on orbits with C < B_⋆ (hence L ≠ 0, via "
             "H_i); the frozen characterization sum_action_mul_eccDeficit_le_sourceStrongAMD asserts it on every source "
             "canonical phase, and the case L = 0 is not argued in MAIN (it is immediate from D ≤ 1 on [0,1])"),
    "lpM:L3#planar-orientation": dict(
        kind="claim", title="planar case: orient so that L > 0; all scalar L_i are then positive",
        stmt="L3:137-137", proof="L3:137-137",
        H="d = 2; a negative-energy state with C < B_⋆(I)", Q="for every such planar state",
        C="choosing the plane's orientation so that L > 0, every individual scalar angular momentum L_i is positive",
        S="none",
        deps=[("lpM:L3#projections", "137", "in the plane H_i = L_i·sign(L) > 0")],
        note="consumed by Theorem 15's orientation step (wave 2; N8, OD-1)"),
    # ---------------- Lemma 4 (Q4 split)
    "lpM:L4": dict(
        kind="lemma", title="Lemma 4: attained, positive, continuous thresholds and (14)", stmt="L4:143-146",
        proof="L4:149-156", H="ν_i > 0 for every i ('all positive masses'); I ∈ Q",
        Q="for every ν > 0 and I ∈ Q (each pair i < j)",
        C="every minimum in (3) is attained and positive; each B_ij and B is continuous on Q; B_ij(I) < I_j and "
          "B(I) = min(B_cross(I), I_1) (14)", S="none",
        deps=[("lpM:L4#feasible-compact", "149", "the pair minima are attained"),
              ("lpM:L4#continuity", "154-156", "continuity of B_ij and B"),
              ("lpM:L4#positivity", "156", "positivity of the minima"),
              ("lpM:L4#competitor", "156", "the competitor proves (14)"),
              ("lpM:s1:chamber#chamber", "143", "I ∈ Q", "L4"),
              ("lpM:s1:thresholds#orderedPairThreshold", "143", "B_ij occurs", "L4"),
              ("lpM:s1:thresholds#orderedCrossThreshold", "145", "B_cross occurs in (14)", "L4"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "143", "B occurs", "L4")],
        note="Q4 split (ruling root-b8): the statement clauses on radial contact and the Laskar-Petit identification "
             "(L143) and on geometric sharpness (L147) are not part of this record; no proof consumes them (N9). Their "
             "items lpM:L4#stmt-contact-lp and lpM:L4#stmt-sharpness and the supporting prose L158 and L160 are "
             "EXCLUDED"),
    "lpM:L4#feasible-compact": dict(
        kind="step", title="the feasible set is closed and nonempty and the objective continuous: minimum attained",
        stmt="L4:143-143", proof="L4:149-149", H=L4H + "; " + ALPHA, Q=L4Q,
        C="the feasible subset of [0,1]^2 is closed and nonempty, since (0, 1 - α) is feasible, and the objective "
          "I_i D(u) + I_j D(v) is continuous, so the pair minimum is attained", S="none",
        deps=[("lpM:s1:thresholds#pairFeasible", "149", "the feasible set"),
              ("lpM:s1:thresholds#pairObjective", "149", "the objective"),
              ("lpM:s1:thresholds#eccDeficit", "149", "continuity of D on [0,1]"),
              ("lpM:s1:thresholds#actionAxis", "149", "α = a_i(I)/a_j(I)"),
              ("lpM:s1:chamber#chamber", "149", "I ∈ Q gives α < 1"),
              ("lpM:ext-compact-min", "149", "a continuous function on a nonempty compact set attains its minimum")]),
    "lpM:L4#contact-reduction": dict(
        kind="step", title="scaling a feasible point to contact does not increase the objective",
        stmt="L4:143-143", proof="L4:149-149", H=L4H + "; " + ALPHA, Q=L4Q + "; for every feasible (u,v)",
        C="replacing (u,v) by t(u,v) with t = (1 - α)/(αu + v) ≤ 1 gives contact a_i(1 + tu) = a_j(1 - tv) and does "
          "not increase the objective", S="none",
        deps=[("lpM:s1:thresholds#pairFeasible", "149", "feasibility and contact"),
              ("lpM:s1:thresholds#pairObjective", "149", "the objective"),
              ("lpM:s1:thresholds#eccDeficit", "149", "D is nondecreasing on [0,1]")]),
    "lpM:L4#contact-param": dict(
        kind="step", title="(15): contact parameterized over t in [0,1]", stmt="L4:150-153", proof="L4:149-153",
        H=L4H + "; " + ALPHA, Q=L4Q + "; t ∈ [0,1]",
        C="with m(α) = min(1, (1 - α)/α), u = m(α)t, v = 1 - α - αm(α)t (15) parameterizes the contact set over the "
          "fixed interval [0,1], so B_ij(I) = min_{t ∈ [0,1]} F(I,t) with F the objective along (15)", S="none",
        deps=[("lpM:L4#contact-reduction", "149", "the minimum is attained on the contact set"),
              ("lpM:s1:thresholds#pairObjective", "151", "F is the objective along (15)")]),
    "lpM:L4#continuity": dict(
        kind="step", title="continuity of B_ij and B on Q via uniform continuity on compact neighborhoods",
        stmt="L4:143-143", proof="L4:154-156", H=L4H, Q="for every ν > 0 and every I, J ∈ Q",
        C="the objective in (15) is jointly continuous in (I,t), hence uniformly continuous on K × [0,1] for every "
          "compact neighborhood K ⊂ Q; ¦min_t F(I,t) - min_t F(J,t)¦ ≤ sup_t ¦F(I,t) - F(J,t)¦ proves continuity of "
          "B_ij on Q; finite minima preserve continuity, so B_cross and B are continuous", S="none",
        deps=[("lpM:L4#contact-param", "154", "B_ij is the minimum over t of the objective in (15)"),
              ("lpM:ext-heine-cantor", "154", "uniform continuity on compact sets"),
              ("lpM:ext-compact-min", "155", "the minima over t ∈ [0,1] are attained"),
              ("lpM:s1:chamber#chamber", "154", "compact neighborhoods inside the open chamber Q"),
              ("lpM:s1:thresholds#orderedPairThreshold", "155", "continuity of B_ij"),
              ("lpM:s1:thresholds#orderedCrossThreshold", "156", "finite minimum B_cross"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "156", "finite minimum B")]),
    "lpM:L4#positivity": dict(
        kind="step", title="a zero minimum cannot give contact; finite minima stay positive", stmt="L4:143-143",
        proof="L4:156-156", H=L4H + "; " + ALPHA, Q=L4Q,
        C="a zero minimum would require u = v = 0, which is not feasible because α < 1; so B_ij(I) > 0, and the finite "
          "minima B_cross(I), B(I) are positive (I_i > 0)", S="none",
        deps=[("lpM:L4#feasible-compact", "156", "the minimum is attained at a feasible point"),
              ("lpM:s1:thresholds#eccDeficit", "156", "D(u) = 0 only at u = 0"),
              ("lpM:s1:thresholds#pairFeasible", "156", "(0,0) is not feasible when α < 1"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "156", "B is a finite minimum of positive numbers")]),
    "lpM:L4#competitor": dict(
        kind="step", title="competitor (0, 1 - alpha): B_ij <= I_j D(1 - alpha) < I_j, proving (14)",
        stmt="L4:144-146", proof="L4:156-156", H=L4H + "; " + ALPHA, Q=L4Q,
        C="the feasible competitor (0, 1 - α) gives B_ij(I) ≤ I_j D(1 - α) < I_j; since B_{i,i+1}(I) < I_{i+1}, "
          "B(I) = min(B_cross(I), I_1) (14)", S="none",
        deps=[("lpM:L4#feasible-compact", "156", "(0, 1 - α) is feasible"),
              ("lpM:s1:thresholds#pairObjective", "156", "the objective at the competitor is I_j D(1 - α)"),
              ("lpM:s1:thresholds#eccDeficit", "156", "D(1 - α) < 1 for 0 < α"),
              ("lpM:s1:thresholds#orderedPairThreshold", "156", "B_ij"),
              ("lpM:s1:thresholds#orderedCrossThreshold", "156", "B_cross in (14)"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "156", "B in (14)")]),
}
COV = {
    "lpM:eq10": ("NODE lpM:L1#velocity", "display (10) is its own node: Lemma 3 (recoil) and Lemma 16 (V_i) consume it"),
    "lpM:L3": ("NODE lpM:L3, lpM:L3#static, lpM:L3#dynamic",
               "Q3 split (ruling root-b8): the full lemma and its static and dynamic parts"),
    "lpM:eq13": ("NODE lpM:L3#static, lpM:L3#dynamic",
                 "Q3 split: the inequality of (13) is static (LP0), the identity dynamic"),
    "lpM:L4": ("NODE lpM:L4", "attained, positive, continuous thresholds and (14); Q4 split: the radial-contact, "
               "Laskar-Petit and sharpness clauses are separate EXCLUDED items (lpM:L4#stmt-contact-lp, "
               "lpM:L4#stmt-sharpness)"),
    "lpM:L4#sharpness": ("EXCLUDED", "Q4 split and amendment N9: the interior-minimizer and geometric-realization "
                         "paragraph is not used downstream; it supports only the excluded statement clauses"),
}
NEWCOV = [
    ("lpM:L4#stmt-contact-lp", "claim", "L4:143-143", "EXCLUDED",
     "Q4 split (ruling root-b8): the statement clauses 'The pair minimum occurs at radial contact. It agrees, after "
     "division by I_j, with the Laskar-Petit relative critical AMD' have no consumer (N9); the proof's contact "
     "reduction itself is the step lpM:L4#contact-reduction"),
    ("lpM:L4#stmt-sharpness", "claim", "L4:147-147", "EXCLUDED",
     "Q4 split: the exact-least-AMD (sharpness) sentence has no consumer (N9); it is not in lpM:L4's source fields"),
    ("lpM:L3#deficit-zero-L", "proof-region", "L3:133-135", "NODE lpM:L3#deficit-zero-L",
     "the case L = 0 of the frozen deficit characterization, not argued in MAIN (SOURCE_GAP step)"),
]
