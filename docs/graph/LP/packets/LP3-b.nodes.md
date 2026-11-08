NODE: lp3:s2.4
KIND: lemma
TITLE: the LP3 drift supplier in the exact hstop shape (planar): drift <= r/2 on stopped orbits
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L261-L265
PROOF_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L267-L303
CONTRACT_ID: lp3:s2.4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data n ≥ 2, ν_i > 0 with max ν = 1, 𝒜 compact and ordered, δ > 0 (no γ, τ, no (5)); planar; 0 < μ ≤ μ_0; r = r(μ) = (B_0μ)^{b_n}
SOURCE_QUANTIFIERS: for every 0 < μ ≤ μ_0, every stopped orbit (a moving solution z on an order-connected J ∋ 0 with z(0) = z_0, stopped on [0, t]) and every t ∈ J with ¦t¦ ≤ T(μ)
SOURCE_CONCLUSION: ‖Λ(z(t)) - Λ(z_0)‖ ≤ r/2 (the stopped-drift premise of the first exit), forward and backward in time
CONSTANT_SCOPE: μ_0, T(μ) and the cover depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lp3:s2.3, N:bpN:p0:partial, lpM:L7, lpM:L14#stopped-membership, lpM:L6#shared-U
ROUTES: -
ROUTE_FOR: -
EDGE: lp3:s2.3 | docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L275-L275 | the cell of I^0 and the discharged premises
EDGE: N:bpN:p0:partial | docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L294-L294 | the imported theorem gives the fast drift ≤ μ^{b_n}/2 = r/2
EDGE: lpM:L7 | docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L269-L269 | the chart lift of the stopped orbit (Lemma 7's chart)
EDGE: lpM:L14#stopped-membership | docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L278-L278 | stopped states satisfy C < B(c_j) - 3δ/8 (the sharp sublevel, §3)
EDGE: lpM:L6#shared-U | docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L278-L278 | within a cell B varies by at most Ω_B(4r_g) ≤ δ/16
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: LP3-PLAN §2.4 with §3 'how the whole sharp sublevel enters' (L333-L351); uniformity L302-L303

NODE: lp3:s2.5
KIND: step
TITLE: spatial version of the drift supplier (k = 2n slow pairs, Lemma 17 chart)
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.5@L305-L328
PROOF_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.5@L305-L328
CONTRACT_ID: lp3:s2.5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data n ≥ 2, ν_i > 0 with max ν = 1, 𝒜 compact and ordered, δ > 0 (no γ, τ, no (5)); spatial; 0 < μ ≤ μ_0; r = (B_0μ)^{b_n}
SOURCE_QUANTIFIERS: as in lp3:s2.4
SOURCE_CONCLUSION: the conclusion of lp3:s2.4 for the spatial chart: ‖Λ(z(t)) - Λ(z_0)‖ ≤ r/2 on stopped spatial orbits
CONSTANT_SCOPE: as in lp3:s2.4
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lp3:s2.4, N:bpN:p0:partial, lpM:L17, lpM:L18
ROUTES: -
ROUTE_FOR: -
EDGE: lp3:s2.4 | docs/tracks/LP/lp3/LP3-PLAN.md#s2.5@L305-L305 | the planar argument with k = 2n
EDGE: N:bpN:p0:partial | docs/tracks/LP/lp3/LP3-PLAN.md#s2.5@L305-L305 | the imported theorem with k = 2n slow pairs
EDGE: lpM:L17 | docs/tracks/LP/lp3/LP3-PLAN.md#s2.5@L305-L305 | the spatial chart
EDGE: lpM:L18 | docs/tracks/LP/lp3/LP3-PLAN.md#s2.5@L305-L305 | the spatial whole-sublevel domain
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lp3:s3#first-exit
KIND: step
TITLE: the stopped first exit (Lemma 14's argument) with r = (B_0 mu)^{b_n}, T = T(mu) and the LP3 drift supplier
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s3@L352-L362
PROOF_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s3@L352-L362
CONTRACT_ID: lp3:s3#first-exit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data n ≥ 2, ν_i > 0 with max ν = 1, 𝒜 compact and ordered, δ > 0 (no γ, τ, no (5)); the chart premises of Lemma 14 (any dimension); a stopped-drift supplier in the hstop shape (premise, supplied by lp3:s2.4 in the plane and lp3:s2.5 in space)
SOURCE_QUANTIFIERS: for every 0 < μ ≤ μ_0 and every initial state with q_i ≠ 0, E_i < 0, a(0) ∈ 𝒜, C(0) ≤ B(I^0) - δ
SOURCE_CONCLUSION: with U the shared tube, r = (B_0μ)^{b_n}, T = T(μ), the budget nr + Ω_B(r) ≤ δ/4 and hstop the supplier, the unique maximal solution exists on [-T, T]; the action bound improves from < r to ≤ r/2 and the AMD margin to 3δ/4; on [-T, T] the state is elliptic, I(t) ∈ Q, C(t) ≤ B(I(t)) - δ/2, the drifts are ≤ A_Λ μ^{b_n}, A_a μ^{b_n}, nA_Λ μ^{b_n}, and (9) and the star and pair distances hold with Lemma 5's constants (m = δ/2)
CONSTANT_SCOPE: the constants depend only on (n, ν, 𝒜, δ) and precede μ and the state
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L14#centers, lpM:L14#choices, lpM:L14#maximal-solution, lpM:L14#stopped-membership, lpM:L3#dynamic, lpM:L6#moving-threshold, lpM:L6, lpM:L5, lpM:L5#perihelion, lpM:L5#pair-distances, lpM:s1:thresholds#actionAxis, lp3:s2.3
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L14#centers | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L352-L352 | the admissible centres lie in 𝓛_δ
EDGE: lpM:L14#choices | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L357-L357 | U and the budget (39) with r = (B_0μ)^{b_n}
EDGE: lpM:L14#maximal-solution | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L352-L352 | the unique maximal solution
EDGE: lpM:L14#stopped-membership | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L359-L359 | the stopped interval in the whole ball
EDGE: lpM:L3#dynamic | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L362-L362 | the identity of (13)
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L362-L362 | (17) with the improved radius r/2
EDGE: lpM:L6 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L352-L352 | continuation through a finite maximal endpoint
EDGE: lpM:L5 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L352-L352 | Lemma 5 with m = δ/2: the compact safe set and (9)
EDGE: lpM:L5#perihelion | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L352-L352 | d_⋆ (41)
EDGE: lpM:L5#pair-distances | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L352-L352 | star and pair distances
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L364-L364 | the action-to-axis estimate
EDGE: lp3:s2.3 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L355-L355 | r(μ), T(μ) and the budget radius
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: LP3 drops (5), so this is not lpM:L14 (whose source hypotheses include (5) and whose improvement step owns the L12/L13 routes): Lemma 14's route-independent steps are reused with the LP3 drift supplier
