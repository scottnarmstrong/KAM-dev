# Track LP, slice LP-m5, wave 2: MAIN L465-L529, Lemma 14 (first exit), Theorem 15 (planar theorem), Lemma 16
# (osculating ellipses).
# Routes (SPEC §6, N7): the stopped drift is consumed in Lemma 14's improvement step (L487; alternative at L500). The
# route nodes lpM:L14#route-L12 (Lemma 12: r = √μ, improvement r/4) and lpM:L14#route-L13 (Lemma 13, the Lean route:
# r = D_0√μ, improvement r/2, N6) are owned by lpM:L14#improvement, the step that consumes the drift supplier (a
# refinement of the SPEC proposal 'lpM:L14 owns them': the other steps of Lemma 14 are route-independent up to the
# radius r). Lemma 14 is d-generic and conditional on the chart premises; Theorem 15 discharges them in the plane
# (lpM:T15#apply-L14), Theorem 19 in space (wave 3). The headline anchors LP1/LP1-H are in packet LP-athm-w2.

L14H = ("context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and "
        "(6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic "
        "symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along "
        "the physical orbit in a fixed reference frame")
L14Q = "for 0 < μ ≤ μ_0 (constants fixed first) and every such initial state (inherited from lpM:L14)"
L16H = ("context of the proof of lpM:L16: a fixed safe compact physical set K of Lemma 5 (for a compact U ⊂ Q and "
        "m > 0) with ¦p_i¦ ≤ P, ¦q_i¦ ≥ d_⋆, E_i ≤ -1/(2a_max) on K; the elements (42); μ > 0 small")
L16Q = "for every state of K and every i (inherited from lpM:L16)"
T15H = ("context of the proof of lpM:T15: the data of §1 with d = 2; 0 < μ ≤ μ_0; a planar initial state with q_i ≠ 0, "
        "E_i < 0 and (6)")
T15Q = "for every such μ and initial state (inherited from lpM:T15)"
BS = ("lpM:s1:thresholds#orderedStrongThreshold", "B occurs")
CH = ("lpM:s1:chamber#chamber", "the chamber Q occurs")


def sym(line, unit, pairs):
    return [(t, line, why, unit) for t, why in pairs]


NODES = {
    # ---------------- Lemma 14
    "lpM:L14": dict(
        kind="lemma", title="Lemma 14: first exit on the entire allowed secular ball (assembly, conditional on the chart)",
        stmt="L14:470-470", proof="L14:472-500",
        H="the data of §1 (n ≥ 2, ν, 𝒜, δ, γ, τ, d); the uniform chart/domain construction (21)-(22) with m slow pairs; "
          "the exact real chart is an analytic symplectic diffeomorphism of the entire prograde negative-energy region "
          "modulo the fast angle lattice, satisfies H_μ = h + μf, and along the physical orbit in a fixed reference frame "
          "has ¦z(t)¦_2^2/2 = C(t)",
        Q="there are μ_0, c, T_0, A_I, A_a, d_⋆, d_pair > 0 (fixed first); then for every 0 < μ ≤ μ_0 and every initial "
          "state with q_i ≠ 0, E_i < 0 and (6)",
        C="existence, uniqueness and (8)-(9) on (7): the unique maximal solution of (1) exists on [-T_μ, T_μ], T_μ = "
          "T_0 exp(cμ^{-a}); on it the state is elliptic, I(t) ∈ Q, ‖I(t) - I^0‖_∞ ≤ A_I√μ, ‖a(t) - a(0)‖_∞ ≤ A_a√μ, "
          "¦C(t) - C(0)¦ ≤ nA_I√μ, C(t) ≤ B(I(t)) - δ/2, a_i(1 - e_i) ≥ d_⋆, a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair, "
          "and all star and planet-pair distances are at least d_⋆, d_pair",
        S="the constants depend only on (d, n, ν, 𝒜, δ, γ, τ) (and D_0 on route L13) and precede μ and the initial state",
        deps=[("lpM:L14#centers", "472", "admissible centers lie in 𝓛_δ"),
              ("lpM:L14#choices", "472-476", "U, μ_0 and (39)"),
              ("lpM:L14#maximal-solution", "478", "the maximal local Newtonian solution"),
              ("lpM:L14#stopped-membership", "478-487", "(40) and the whole-ball membership"),
              ("lpM:L14#improvement", "487", "the improved action and AMD bounds"),
              ("lpM:L14#no-exit", "489", "no finite forward end before T_μ"),
              ("lpM:L14#backward", "489", "the backward direction"),
              ("lpM:L14#separation", "491-495", "d_⋆ (41), d_pair and all pair distances"),
              ("lpM:L14#axis-drift", "495-500", "A_I, A_a, T_0"),
              ("lpM:L3#dynamic", "470", "(8)'s AMD drift ¦C(t) - C(0)¦ = ¦Σ_i(I_i(t) - I_i^0)¦ ≤ n‖I(t) - I^0‖_∞ by the "
               "identity of (13)", "L14"),
              ("lpM:s1:dioph", "470", "the initial premises (6) include (5)", "L14")]
        + sym("470", "L14", [BS, CH]),
        note="d-generic internal assembly lemma; its chart premises are discharged in the headline theorems "
             "(lpM:T15#apply-L14; Theorem 19 in wave 3). Its proof lists Lemmas 3-6 and 12; under N7 the drift supplier "
             "is Lemma 12 or Lemma 13 (routes at lpM:L14#improvement). AMENDED: N2, N6, N7 (AMENDMENTS.md L11, L15, L16)."),
    "lpM:L14#centers": dict(
        kind="step", title="by C >= 0, every admissible center I^0 lies in L_delta",
        stmt="L14:470-470", proof="L14:472-472", H=L14H, Q=L14Q,
        C="C(0) ≥ 0 and C(0) ≤ B(I^0) - δ give B(I^0) ≥ δ, so I^0 ∈ 𝓛_δ; no assumption B > δ on all of 𝒜 is needed",
        S="none",
        deps=[("lpM:L3#static", "472", "the nonnegativity of AMD"), BS[:1] + ("472", BS[1])]),
    "lpM:L14#choices": dict(
        kind="step", title="shared compact neighborhood U of L_delta; mu_0 so that the radius r has its tube in U and (39)",
        stmt="L14:472-476", proof="L14:472-476", H=L14H + "; local data: the stopped radius r of the drift supplier "
        "(r = √μ on route L12, r = D_0√μ on route L13)", Q="fixed before the initial point and μ",
        C="choose once and for all a compact neighborhood U ⊂ Q of 𝓛_δ; decrease μ_0 (to at most the supplier's "
          "threshold) so that the action tube of radius r lies in U and nr + Ω_B(r) ≤ δ/4, Ω_B(r) ≤ δ/16 (39); all these "
          "choices precede the initial point and μ, and the modulus is uniform on U",
        S="U and μ_0 depend only on the fixed data (and the supplier's constants)",
        deps=[("lpM:L6#shared-U", "472", "the shared compact U and its modulus Ω_B(r) → 0 (N2)"),
              ("lpM:L14#centers", "472", "the centers lie in 𝓛_δ"),
              BS[:1] + ("474", BS[1]), CH[:1] + ("472", CH[1])],
        note="AMENDED: N2 (AMENDMENTS.md L11): U is the one shared compact set of Lemmas 6 and 8, r ≤ r_g; AMENDED: N6 "
             "(AMENDMENTS.md L15): on route L13 the radius is r = D_0√μ"),
    "lpM:L14#maximal-solution": dict(
        kind="step", title="the initial state is collision-free (Lemma 5, m = delta); the unique maximal solution exists",
        stmt="L14:470-470", proof="L14:478-478", H=L14H, Q=L14Q,
        C="the initial state lies in the open physical domain (by Lemma 5 with U and m = δ, ¦q_i¦ ≥ d_⋆ and ¦q_i - q_j¦ ≥ "
          "d_pair > 0: initial pair collisions are excluded by (6)); the solution of (1) from it is locally unique and has "
          "a unique maximal interval of existence, on which it agrees with every local solution",
        S="none",
        deps=[("lpM:L5", "478", "Lemma 5 with m = δ: the initial state lies in a compact nonsingular set (premise "
               "C(0) ≤ B(I^0) - δ, I^0 ∈ 𝓛_δ ⊂ U)"),
              ("lpM:L5#pair-distances", "478", "¦q_i - q_j¦ ≥ d_pair > 0 at the initial state (§1 L78)"),
              ("lpM:L14#choices", "478", "the compact U containing 𝓛_δ"),
              ("lpM:L6#local-existence", "478", "local existence and uniqueness of solutions of (1)")],
        note="SOURCE_GAP: MAIN takes 'the maximal local Newtonian solution' (L478) and uniqueness (L470, §1 L74) for "
             "granted; the passage from Lemma 6's local existence and uniqueness to a unique maximal solution agreeing "
             "with every local solution on its overlap is not argued (standard ODE continuation). §1 L78 'initial pair "
             "collisions are excluded by (6), as proved below' is supplied here by Lemma 5 with m = δ"),
    "lpM:L14#stopped-membership": dict(
        kind="step", title="(40) on the stopped interval gives |z|^2/2 = C < B(I^0) - 7 delta/16: every point lies in D_1",
        stmt="L14:478-481", proof="L14:478-487", H=L14H + "; the connected interval containing 0 on which the solution is "
        "elliptic, its chart is defined and (40) ‖I(t) - I^0‖_∞ < r, C(t) < B(I(t)) - δ/2 hold", Q=L14Q,
        C="on that interval ¦z(t)¦_2^2/2 = C(t) < B(I^0) - δ/2 + Ω_B(r) ≤ B(I^0) - 7δ/16, so every physical point lies in "
          "D_1 (using the whole ball (21)); this uses only the stopped conditions (40)",
        S="none",
        deps=[("lpM:L14#choices", "484", "Ω_B(r) ≤ δ/16 of (39) and the tube in U"),
              ("lpM:L6#shared-U", "484", "B(I(t)) ≤ B(I^0) + Ω_B(r) on the tube"),
              ("lpM:L14#maximal-solution", "478", "the maximal local solution whose stopped interval is taken"),
              BS[:1] + ("484", BS[1])]),
    "lpM:L14#improvement": dict(
        kind="step", title="the drift supplier improves the action bound (r/4 or r/2); (13), (17), (39) give AMD margin >= 3 delta/4",
        stmt="L14:487-487", proof="L14:487-487", H=L14H + "; the stopped interval of lpM:L14#stopped-membership, up to "
        "T_μ", Q=L14Q + "; on every finite subinterval up to T_μ",
        C="on every finite subinterval of the stopped interval up to T_μ the action bound improves to r' (r' = r/4 on "
          "route L12, r' = r/2 on route L13), and C(t) ≤ B(I(t)) - δ + nr' + Ω_B(r') ≤ B(I(t)) - 3δ/4",
        S="none",
        deps=[("lpM:L14#stopped-membership", "487", "the orbit lies in D_1 (the drift supplier's stopped premise)"),
              ("lpM:L3#dynamic", "487", "the identity of (13)"),
              ("lpM:L6#moving-threshold", "487", "(17) with the improved radius"),
              ("lpM:L14#choices", "487", "(39)")],
        routes=[("lpM:L14#route-L12", "487", "Lemma 12 is valid on the stopped interval and improves the bound to r/4"),
                ("lpM:L14#route-L13", "500", "using Lemma 13 instead: its stopped slow-membership premise is the "
                 "membership proved before the improvement")],
        note="AMENDED: N6, N7 (AMENDMENTS.md L15, L16): the two drift suppliers are alternatives (route nodes)"),
    "lpM:L14#route-L12": dict(
        kind="route", title="drift supplier Lemma 12: r = sqrt(mu), improvement to r/4 up to T_mu = exp(c mu^{-a})",
        stmt="L14:487-487", proof="L14:487-487", H="as in lpM:L14#improvement", Q="as in lpM:L14#improvement",
        C="with r = √μ and μ_0 ≤ μ_1, on every finite subinterval of the stopped interval up to T_μ = exp(cμ^{-a}), "
          "‖I(t) - I^0‖_∞ ≤ r/4 (34)",
        S="μ_1, c and M_1 are those of Lemma 12", route_for="lpM:L14#improvement",
        deps=[("lpM:L12", "487", "Lemma 12 (its premises: the chart-domain statement of Lemma 14's hypothesis and (5))")],
        note="AMENDED: N7 (AMENDMENTS.md L16): the paper route; A_I = 1, T_0 = 1 (L500)"),
    "lpM:L14#route-L13": dict(
        kind="route", title="drift supplier Lemma 13 (Lean route): r = D_0 sqrt(mu), improvement to r/2 up to exp(c_1 mu^{-a})",
        stmt="L14:500-500", proof="L14:500-500", H="as in lpM:L14#improvement", Q="as in lpM:L14#improvement",
        C="with r = D_0√μ, on every finite subinterval of the stopped interval up to exp(c_1μ^{-a}), ‖I(t) - I^0‖_∞ ≤ r/2; "
          "the stopped slow-membership premise of Lemma 13 is the membership proved before the improvement; A_I becomes a "
          "fixed multiple of D_0",
        S="κ_1, c_1 and the μ threshold are those of Lemma 13 for the fixed D_0", route_for="lpM:L14#improvement",
        deps=[("lpM:L13", "500", "Lemma 13 with the stopped interval J of Lemma 14 (its premises: the chart-domain "
               "statement of Lemma 14's hypothesis and (5))")],
        note="AMENDED: N6, N7 (AMENDMENTS.md L15, L16): the Lean route; (39) still gives C ≤ B(I(t)) - δ + nr/2 + "
             "Ω_B(r/2) ≤ B(I(t)) - 3δ/4"),
    "lpM:L14#no-exit": dict(
        kind="step", title="a forward end t_* <= T_mu is impossible: Lemma 5 compact set, Lemma 6 continuation, persisting improved bounds",
        stmt="L14:470-470", proof="L14:489-489", H=L14H, Q=L14Q,
        C="if the forward end of the stopped interval were t_* ≤ T_μ: Lemma 5 with margin δ/2 bounds the preceding orbit in "
          "a compact nonsingular physical set (energies uniformly negative, individual angular-momentum projections "
          "bounded away from zero); Lemma 6 extends the physical solution through a finite maximal endpoint (continuity "
          "at any other endpoint); the chart stays valid at the limit (it covers the entire prograde region); the "
          "improved bounds r' < r and 3δ/4 > δ/2 persist near t_*, a contradiction; hence the solution and (40) hold "
          "through T_μ, elliptic with I(t) ∈ U ⊂ Q",
        S="none",
        deps=[("lpM:L5", "489", "Lemma 5 with m = δ/2 (its premise C ≤ B(I) - δ/2 is (40))"),
              ("lpM:L6", "489", "Lemma 6 continues the solution through a finite maximal endpoint"),
              ("lpM:L14#improvement", "489", "the improved bounds r' and 3δ/4"),
              ("lpM:L14#stopped-membership", "489", "the stopped interval and its chart")]),
    "lpM:L14#backward": dict(
        kind="step", title="the backward direction by the same normal-form estimate with |t| and backward continuation",
        stmt="L14:470-470", proof="L14:489-489", H=L14H, Q=L14Q + "; t ≤ 0",
        C="the solution exists back to -T_μ with the same bounds; all inequalities hold at both endpoints of (7) by "
          "continuity",
        S="none",
        deps=[("lpM:L14#no-exit", "489", "the forward argument with ¦t¦"),
              ("lpM:L6#backward", "489", "the backward continuation of Lemma 6")]),
    "lpM:L14#separation": dict(
        kind="step", title="separation constants of Lemma 5 with m = delta/2, d_star = a_min delta^2/(8 I_max^2) (41); all pairs separated",
        stmt="L14:491-495", proof="L14:491-495", H=L14H, Q=L14Q + "; every t ∈ [-T_μ, T_μ]",
        C="the final separation constants are those of Lemma 5 with m = δ/2, including d_⋆ = a_min δ^2/(8 I_max^2) (41); "
          "(9) holds on [-T_μ, T_μ], and all adjacent and nonadjacent physical pairs, and the star distances, are "
          "separated by d_pair, d_⋆",
        S="d_⋆, d_pair depend only on (n, ν, U, δ)",
        deps=[("lpM:L5", "491", "Lemma 5 with U and m = δ/2: perihelia and adjacent gaps"),
              ("lpM:L5#perihelion", "493", "(16) with m = δ/2 is (41)"),
              ("lpM:L5#pair-distances", "495", "star and nonadjacent pair distances"),
              ("lpM:L14#no-exit", "491", "C(t) ≤ B(I(t)) - δ/2 and I(t) ∈ U on the forward interval"),
              ("lpM:L14#backward", "491", "the same on the backward interval")]),
    "lpM:L14#axis-drift": dict(
        kind="step", title="|a_i(I) - a_i(I^0)| <= (2 I_max/min nu_i^2) ||I - I^0||: A_I = 1, A_a, T_0 = 1",
        stmt="L14:495-500", proof="L14:495-500", H=L14H, Q=L14Q + "; every t ∈ [-T_μ, T_μ]",
        C="¦a_i(I) - a_i(I^0)¦ = ¦I_i - I_i^0¦ ¦I_i + I_i^0¦/ν_i^2 ≤ (2I_max/min_i ν_i^2)‖I - I^0‖_∞; one can take A_I = 1, "
          "A_a = 2I_max/min_i ν_i^2 and T_0 = 1 (on route L13, A_I a fixed multiple of D_0); enlarging constants is "
          "harmless",
        S="A_I, A_a, T_0 depend only on the fixed data (and D_0 on route L13)",
        deps=[("lpM:s1:thresholds#actionAxis", "497", "a_i(I) = (I_i/ν_i)^2"),
              ("lpM:L14#no-exit", "500", "‖I(t) - I^0‖_∞ ≤ r' ≤ r on the forward interval"),
              ("lpM:L14#backward", "500", "the same backward"),
              ("lpM:L5#perihelion", "498", "I_max is the extremum over U of Lemma 5")]),
    # ---------------- Theorem 15
    "lpM:T15": dict(
        kind="theorem", title="Theorem 15: planar nonresonant exponential safety (the §1 conclusion for d = 2)",
        stmt="T15:504-504", proof="T15:506-506",
        H="d = 2; n ≥ 2; ν_i > 0 with max_i ν_i = 1; 𝒜 ⊂ {0 < a_1 < ... < a_n} compact; δ, γ > 0; τ > n - 1",
        Q="there exist μ_0, c, T_0, A_I, A_a, d_⋆, d_pair, A_osc > 0; then for every 0 < μ ≤ μ_0 and every planar initial "
          "state with q_i ≠ 0, E_i < 0 and (6): a(0) ∈ 𝒜, (5) at ω(I^0), C(0) ≤ B(I^0) - δ",
        C="the unique maximal solution of (1) exists on [-T_μ, T_μ], T_μ = T_0 exp(cμ^{-a}), a = 1/(2(τ+1)) (7); on it the "
          "state is elliptic, I(t) ∈ Q, ‖I(t) - I^0‖_∞ ≤ A_I√μ, ‖a(t) - a(0)‖_∞ ≤ A_a√μ, ¦C(t) - C(0)¦ ≤ nA_I√μ, C(t) ≤ "
          "B(I(t)) - δ/2 (8), a_i(1 - e_i) ≥ d_⋆, a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair (9); actual star distances "
          "and all planet-pair distances are at least d_⋆, d_pair; the velocity-osculating perihelion and aphelion radii "
          "are within A_osc μ of the canonical ones and their star and adjacent-annulus gaps are at least d_⋆/2, d_pair/2 "
          "(no orbit crossing, L93)",
        S="μ_0, c, T_0, A_I, A_a, d_⋆, d_pair, A_osc depend only on (n, ν, 𝒜, δ, γ, τ) (d = 2) and are chosen before μ and "
          "the initial state; A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2 (N10)",
        deps=[("lpM:T15#orientation", "506", "orientation reversal so that L > 0"),
              ("lpM:T15#chart-cover", "506", "the Lemma 7 charts cover and C = ¦z¦^2/2"),
              ("lpM:T15#apply-L14", "506", "Lemma 14 closes the first exit and proves (7)-(9)"),
              ("lpM:T15#reconstruction", "506", "Lemma 1: actual star and pair distances are those of q"),
              ("lpM:T15#osculating", "506", "Lemma 16: the osculating conclusion"),
              ("lpM:s1:data", "70", "the fixed data (n, ν with max ν = 1, 𝒜, δ, γ, τ)", "s1"),
              ("lpM:s1:dioph", "72", "(6) contains (5)", "s1"),
              ("lpM:s1:elements", "72", "C, a, e, I of the initial state and along the orbit", "s1")]
        + sym("72", "s1", [BS, CH]),
        note="planar MAIN theorem; its frozen statement is the anchor LP1 lpM:T15#planar_strongAMD_exponentialSafety "
             "(packet LP-athm-w2). The source dependency list 'Lemmas 1-14 and 16' is read with N7: Lemmas 12 and 13 "
             "are alternatives (routes inside Lemma 14). AMENDED: N7, N8, N10 (AMENDMENTS.md L16, L17, L19)."),
    "lpM:T15#orientation": dict(
        kind="step", title="Lemma 3: L != 0, all L_i of its sign; reverse the plane so that the sign is positive (H, constants invariant)",
        stmt="T15:504-504", proof="T15:506-506", H=T15H, Q=T15Q,
        C="C(0) ≤ B(I^0) - δ < B_⋆(I^0), so Lemma 3 gives L ≠ 0 and individual scalar angular momenta of its sign; "
          "reversing the planar orientation (simultaneously on positions and momenta) makes the sign positive, and the "
          "Hamiltonian (1), the orientation-free C and all constants are invariant",
        S="none",
        deps=[("lpM:L3#static", "506", "L ≠ 0 and H_i > 0 under C < B_⋆ (supplied by (6))"),
              ("lpM:L3#planar-orientation", "506", "in the plane all L_i share the sign of L"),
              ("lpM:s1:model", "506", "(1) is invariant under the orthogonal change"),
              ("lpM:s1:elements", "506", "C = ΣI - ¦L¦ is orientation-free (N8)"), BS[:1] + ("506", BS[1])],
        note="AMENDED: N8 (AMENDMENTS.md L17): this reflection reduction is the bridge between the frozen orientation-free "
             "C (OD-1) and the prograde chart"),
    "lpM:T15#chart-cover": dict(
        kind="step", title="the product of the Lemma 7 charts covers every initial state; C = sum Gamma_i = |z|^2/2 in the prograde region",
        stmt="T15:504-504", proof="T15:506-506", H=T15H + "; orientation with L > 0", Q=T15Q,
        C="the product of the charts of Lemma 7 covers every (oriented) initial state and gives C = Σ_i Γ_i = ¦z¦_2^2/2 "
          "wherever the physical orbit remains in the prograde region; exact conservation of L keeps the reference "
          "orientation fixed",
        S="none",
        deps=[("lpM:L7", "506", "the chart of each planet, with G_i = I_i - Γ_i"),
              ("lpM:T15#orientation", "506", "all L_i > 0 at the initial state"),
              ("lpM:L3#dynamic", "506", "conservation of L"),
              ("lpM:s1:elements", "506", "C = Σ I_i - ¦L¦ = Σ(I_i - G_i) when every L_i > 0")]),
    "lpM:T15#apply-L14": dict(
        kind="step", title="Lemma 14 with the Lemma 7 product chart and Lemma 8 (m = n): (7)-(9) in the plane",
        stmt="T15:504-504", proof="T15:506-506", H=T15H, Q=T15Q,
        C="the premises of Lemma 14 hold in the plane (chart of the entire prograde negative-energy region with H_μ = h + "
          "μf by Lemmas 7-8, the uniform domain (21)-(22) by Lemma 8 with m = n, the identity ¦z(t)¦^2/2 = C(t)), so the "
          "unique maximal solution exists on (7) with (8)-(9) and the distance bounds",
        S="the constants of Lemma 14, for d = 2",
        deps=[("lpM:L14", "506", "Lemma 14 closes the first exit"),
              ("lpM:L7", "506", "the chart of the entire prograde negative-energy region"),
              ("lpM:L8", "506", "the analytic domain, perturbation bounds and exact split (m = n slow pairs)"),
              ("lpM:T15#chart-cover", "506", "the identity ¦z(t)¦^2/2 = C(t) along the orbit")]),
    "lpM:T15#reconstruction": dict(
        kind="step", title="Lemma 1 reconstructs the exact Newtonian motion (masses 1, mu nu_i)",
        stmt="T15:504-504", proof="T15:506-506", H=T15H, Q=T15Q + "; t ∈ [-T_μ, T_μ]",
        C="the solution of (1) on [-T_μ, T_μ] reconstructs a Newtonian (1+n)-body solution with masses (1, μν_1, ..., "
          "μν_n) (barycentric positions and velocities of Lemma 1); its star and pair distances are ¦q_i¦ and ¦q_i - q_j¦",
        S="none",
        deps=[("lpM:L1", "506", "Lemma 1 reconstructs the Newtonian motion"),
              ("lpM:T15#apply-L14", "506", "the collision-free solution on [-T_μ, T_μ]")]),
    "lpM:T15#osculating": dict(
        kind="step", title="Lemma 16 on the Lemma 5 compact set (m = delta/2) gives the osculating conclusion",
        stmt="T15:504-504", proof="T15:506-506", H=T15H, Q=T15Q + "; t ∈ [-T_μ, T_μ]",
        C="along the solution the velocity-osculating elements are nondegenerate elliptic (E^osc < 0, a^osc > 0, "
          "e^osc < 1), the osculating ellipse passes through q_i (a^osc(1 - e^osc) ≤ ¦q_i¦ ≤ a^osc(1 + e^osc)), "
          "¦a^osc - a¦ + ¦e^osc - e¦ ≤ Aμ, the perihelion and aphelion radii are within A_osc μ of the canonical ones, and "
          "with A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 the osculating star and adjacent gaps are at least d_⋆/2, d_pair/2",
        S="A and A_osc depend only on the compact set of Lemma 5 (m = δ/2) and the fixed masses",
        deps=[("lpM:L16", "506", "Lemma 16 on the compact set of Lemma 5"),
              ("lpM:L16#mu0-choice", "528", "the final μ_0 of N10", "L16"),
              ("lpM:L16#half-gaps", "529", "the osculating half gaps", "L16"),
              ("lpM:L14#separation", "506", "the orbit stays in Lemma 5's compact set with m = δ/2", "T15"),
              ("lpM:T15#apply-L14", "506", "the solution on [-T_μ, T_μ]")],
        note="AMENDED: N10 (AMENDMENTS.md L19)"),
    # ---------------- Lemma 16
    "lpM:L16:defs": dict(
        kind="definition", title="actual-velocity osculating elements (42), any dimension d", stmt="L16:510-519",
        proof="-", H="the data of lpM:s1:data; μ > 0; a state (q, p) of the model", Q="for every state and every i",
        C="V_i = q̇_i = p_i/ν_i + μΣ_j p_j, k_i = 1 + μν_i, E_i^osc = ¦V_i¦^2/2 - k_i/¦q_i¦, a_i^osc = -k_i/(2E_i^osc), "
          "e_i^osc = ((¦V_i¦^2 - k_i/¦q_i¦)q_i - (q_i·V_i)V_i)/k_i, e_i^osc = ¦e_i^osc¦ (42)",
        S="none",
        deps=[("lpM:L1#velocity", "512", "V_i is the actual velocity q̇_i of (10)"),
              ("lpM:s1:model", "512", "the masses ν_i, μ and the variables q, p"),
              ("lpM:s1:data", "515", "the Euclidean length and the dimension d")],
        note="d-generic source definition (d ∈ {2,3}); the planar frozen realizations are the anchors lpM:L16:defs#* "
             "(LP-adef-pl), the spatial ones come in wave 3 (SPEC §5)"),
    "lpM:L16": dict(
        kind="lemma", title="Lemma 16: actual-velocity osculating ellipses (43), any dimension d", stmt="L16:510-525",
        proof="L16:527-529",
        H="a fixed safe compact physical set K of Lemma 5 (for some compact U ⊂ Q and m > 0); the elements (42); d ∈ {2,3}",
        Q="there are A, A_osc > 0 and a threshold μ_0 > 0; then for every 0 < μ ≤ μ_0, uniformly on K, and every i",
        C="the elements (42) are nondegenerate elliptic (E_i^osc < 0, e_i^osc < 1) and ¦a_i^osc - a_i¦ + ¦e_i^osc - e_i¦ "
          "≤ Aμ, ¦a_i^osc(1 ± e_i^osc) - a_i(1 ± e_i)¦ ≤ A_osc μ (43); these ellipses pass through the current positions and "
          "are tangent to the actual heliocentric velocities",
        S="A, A_osc and μ_0 depend only on K and the fixed masses",
        deps=[("lpM:L16#element-error", "527", "¦E^osc - E¦ + ¦e^osc - e¦ ≤ A_0μ"),
              ("lpM:L16#elliptic", "527", "E^osc ≤ -1/(4a_max), the axis estimate, e^osc < 1"),
              ("lpM:L16#endpoint-estimate", "527", "the second estimate of (43)"),
              ("lpM:L16#tangent-ellipse", "527", "the ellipse through q_i tangent to V_i"),
              ("lpM:L16:defs", "510", "the elements (42)", "L16"),
              ("lpM:L5", "510", "the safe compact physical sets of Lemma 5", "L16"),
              ("lpM:L1#velocity", "525", "V_i = q̇_i: tangency to the actual velocity", "L16")],
        note="the closing remark on the gravitational-parameter-one convention (L529) is EXCLUDED"),
    "lpM:L16#element-error": dict(
        kind="step", title="|V_i - v_i| <= n P mu, |k_i - 1| <= mu; expansion: |E^osc - E| + |e^osc - e| <= A_0 mu",
        stmt="L16:521-524", proof="L16:527-527", H=L16H, Q=L16Q,
        C="¦V_i - v_i¦ ≤ nPμ and ¦k_i - 1¦ ≤ μ; direct expansion of (42) with bounded positions and momenta and ¦q_i¦ ≥ "
          "d_⋆ gives ¦E_i^osc - E_i¦ + ¦e_i^osc - e_i¦ ≤ A_0μ",
        S="A_0 depends only on K and the masses",
        deps=[("lpM:L16:defs", "527", "the elements (42)"),
              ("lpM:L1#velocity", "527", "V_i - v_i = μΣ_j p_j by (10)"),
              ("lpM:L5#compact-physical", "527", "positions and momenta bounded (¦p_i¦ ≤ P) on K"),
              ("lpM:L5#pair-distances", "527", "¦q_i¦ ≥ d_⋆ on K"),
              ("lpM:s1:data", "527", "ν_i ≤ max ν = 1 gives ¦k_i - 1¦ ≤ μ", "L16"),
              ("lpM:s1:elements", "527", "E_i and e_i of (2)")]),
    "lpM:L16#elliptic": dict(
        kind="step", title="E^osc <= -1/(4 a_max) for small mu_0; reciprocal identity: axis estimate; |e^osc - e| <= |e^osc vec - e vec|; e^osc < 1",
        stmt="L16:520-523", proof="L16:527-527", H=L16H, Q=L16Q,
        C="since E_i ≤ -1/(2a_max), μ_0 can be chosen with E_i^osc ≤ -1/(4a_max); the identity for the difference of two "
          "reciprocals gives ¦a_i^osc - a_i¦ ≤ Aμ; the triangle inequality gives ¦e_i^osc - e_i¦ ≤ ¦e_i^osc - e_i¦ "
          "(vectors), including at circular orbits; since e_i ≤ e_* < 1, decreasing μ_0 gives e_i^osc < 1",
        S="A and μ_0 depend only on K and the masses",
        deps=[("lpM:L16#element-error", "527", "the energy and eccentricity-vector errors"),
              ("lpM:L5#compact-physical", "527", "E_i ≤ -1/(2a_max) on K"),
              ("lpM:L5#perihelion", "527", "√(1 - e_i^2) ≥ m/I_max: e_i ≤ e_* < 1 on K"),
              ("lpM:L16:defs", "527", "a^osc = -k/(2E^osc)")]),
    "lpM:L16#endpoint-estimate": dict(
        kind="step", title="expansion of the products: |a^osc(1 +- e^osc) - a(1 +- e)| <= A_osc mu",
        stmt="L16:521-524", proof="L16:527-527", H=L16H, Q=L16Q,
        C="expanding the products gives the second estimate of (43): ¦a_i^osc(1 ± e_i^osc) - a_i(1 ± e_i)¦ ≤ A_osc μ",
        S="A_osc depends only on K and the masses",
        deps=[("lpM:L16#elliptic", "527", "the axis and eccentricity errors")]),
    "lpM:L16#tangent-ellipse": dict(
        kind="step", title="the two-body ellipse with position q_i, velocity V_i, parameter k_i; Lemma 2 with parameter k_i: it contains q_i",
        stmt="L16:525-525", proof="L16:527-527",
        H="one planet: q ≠ 0, a velocity V, a parameter k > 0 with E^osc = ¦V¦^2/2 - k/¦q¦ < 0; the elements (42)",
        Q="for every such (q, V, k)",
        C="the two-body initial-value problem with position q, velocity V and gravitational parameter k defines the "
          "tangent ellipse with invariants a^osc, e^osc; Lemma 2 with parameter k gives a^osc(1 - e^osc) ≤ ¦q¦ ≤ "
          "a^osc(1 + e^osc) and e^osc ≤ 1, so the ellipse contains the position",
        S="none",
        deps=[("lpM:L2", "527", "the orbital identities (11)-(12), with parameter k (rescale V by 1/√k)"),
              ("lpM:L16:defs", "527", "the elements (42)")],
        note="Lemma 2 is stated with parameter one; applying it with parameter k_i is the rescaling w = V/√k, which maps "
             "(42) to the elements of (2) with ν = 1 (routine)"),
    "lpM:L16#mu0-choice": dict(
        kind="step", title="final mu_0: A_osc mu_0 <= d_star/2 and 2 A_osc mu_0 <= d_pair/2 (N10)",
        stmt="L16:528-528", proof="L16:528-528", H=L16H, Q="fixed before μ",
        C="μ_0 also satisfies A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2", S="μ_0 depends only on the fixed data",
        deps=[("lpM:L16#endpoint-estimate", "528", "the constant A_osc"),
              ("lpM:L5", "528", "d_⋆ and d_pair of Lemma 5")],
        note="AMENDED: N10 (AMENDMENTS.md L19): the headline constant list records this"),
    "lpM:L16#half-gaps": dict(
        kind="step", title="subtracting the endpoint errors: osculating star gap >= d_star/2, adjacent gaps >= d_pair/2",
        stmt="L16:529-529", proof="L16:529-529", H=L16H + "; μ ≤ μ_0 of N10", Q=L16Q,
        C="a_i^osc(1 - e_i^osc) ≥ d_⋆ - A_osc μ ≥ d_⋆/2 and a_{i+1}^osc(1 - e_{i+1}^osc) - a_i^osc(1 + e_i^osc) ≥ d_pair - "
          "2A_osc μ ≥ d_pair/2",
        S="none",
        deps=[("lpM:L16#endpoint-estimate", "529", "the endpoint errors ≤ A_osc μ"),
              ("lpM:L16#mu0-choice", "529", "A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2"),
              ("lpM:L5", "529", "the canonical perihelia ≥ d_⋆ and gaps ≥ d_pair on K")]),
}
COV = {
    "lpM:eq39": ("NODE lpM:L14#choices", "display (39)"),
    "lpM:eq40": ("NODE lpM:L14#stopped-membership", "display (40)"),
    "lpM:eq41": ("NODE lpM:L14#separation", "display (41)"),
    "lpM:L14#route-L12": ("NODE lpM:L14#route-L12", "route node owned by lpM:L14#improvement (N7)"),
    "lpM:L14#route-L13": ("NODE lpM:L14#route-L13", "route node owned by lpM:L14#improvement (N6, N7)"),
    "lpM:L14#stopped-membership": ("NODE lpM:L14#maximal-solution, lpM:L14#stopped-membership",
                                   "L478 'take the maximal local Newtonian solution' (SOURCE_GAP step) and (40)"),
    "lpM:eq42": ("NODE lpM:L16:defs", "display (42)"),
    "lpM:eq43": ("NODE lpM:L16", "display (43)"),
    "lpM:L16#convention-remark": ("EXCLUDED", "the gravitational-parameter-one convention is a separately named "
                                  "variant that no proof uses"),
}
