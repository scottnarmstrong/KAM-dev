NODE: lpM:L14
KIND: lemma
TITLE: Lemma 14: first exit on the entire allowed secular ball (assembly, conditional on the chart)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L470-L470
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L472-L500
CONTRACT_ID: lpM:L14
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of §1 (n ≥ 2, ν, 𝒜, δ, γ, τ, d); the uniform chart/domain construction (21)-(22) with m slow pairs; the exact real chart is an analytic symplectic diffeomorphism of the entire prograde negative-energy region modulo the fast angle lattice, satisfies H_μ = h + μf, and along the physical orbit in a fixed reference frame has ¦z(t)¦_2^2/2 = C(t)
SOURCE_QUANTIFIERS: there are μ_0, c, T_0, A_I, A_a, d_⋆, d_pair > 0 (fixed first); then for every 0 < μ ≤ μ_0 and every initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_CONCLUSION: existence, uniqueness and (8)-(9) on (7): the unique maximal solution of (1) exists on [-T_μ, T_μ], T_μ = T_0 exp(cμ^{-a}); on it the state is elliptic, I(t) ∈ Q, ‖I(t) - I^0‖_∞ ≤ A_I√μ, ‖a(t) - a(0)‖_∞ ≤ A_a√μ, ¦C(t) - C(0)¦ ≤ nA_I√μ, C(t) ≤ B(I(t)) - δ/2, a_i(1 - e_i) ≥ d_⋆, a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair, and all star and planet-pair distances are at least d_⋆, d_pair
CONSTANT_SCOPE: the constants depend only on (d, n, ν, 𝒜, δ, γ, τ) (and D_0 on route L13) and precede μ and the initial state
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L14#centers, lpM:L14#choices, lpM:L14#maximal-solution, lpM:L14#stopped-membership, lpM:L14#improvement, lpM:L14#no-exit, lpM:L14#backward, lpM:L14#separation, lpM:L14#axis-drift, lpM:L3#dynamic, lpM:s1:dioph, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:chamber#chamber
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L14#centers | docs/tracks/LP/source/MAIN.md#L14@L472-L472 | admissible centers lie in 𝓛_δ
EDGE: lpM:L14#choices | docs/tracks/LP/source/MAIN.md#L14@L472-L476 | U, μ_0 and (39)
EDGE: lpM:L14#maximal-solution | docs/tracks/LP/source/MAIN.md#L14@L478-L478 | the maximal local Newtonian solution
EDGE: lpM:L14#stopped-membership | docs/tracks/LP/source/MAIN.md#L14@L478-L487 | (40) and the whole-ball membership
EDGE: lpM:L14#improvement | docs/tracks/LP/source/MAIN.md#L14@L487-L487 | the improved action and AMD bounds
EDGE: lpM:L14#no-exit | docs/tracks/LP/source/MAIN.md#L14@L489-L489 | no finite forward end before T_μ
EDGE: lpM:L14#backward | docs/tracks/LP/source/MAIN.md#L14@L489-L489 | the backward direction
EDGE: lpM:L14#separation | docs/tracks/LP/source/MAIN.md#L14@L491-L495 | d_⋆ (41), d_pair and all pair distances
EDGE: lpM:L14#axis-drift | docs/tracks/LP/source/MAIN.md#L14@L495-L500 | A_I, A_a, T_0
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#L14@L470-L470 | (8)'s AMD drift ¦C(t) - C(0)¦ = ¦Σ_i(I_i(t) - I_i^0)¦ ≤ n‖I(t) - I^0‖_∞ by the identity of (13)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L14@L470-L470 | the initial premises (6) include (5)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L14@L470-L470 | B occurs
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L14@L470-L470 | the chamber Q occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: d-generic internal assembly lemma; its chart premises are discharged in the headline theorems (lpM:T15#apply-L14; Theorem 19 in wave 3). Its proof lists Lemmas 3-6 and 12; under N7 the drift supplier is Lemma 12 or Lemma 13 (routes at lpM:L14#improvement). AMENDED: N2, N6, N7 (AMENDMENTS.md L11, L15, L16).

NODE: lpM:L14#centers
KIND: step
TITLE: by C >= 0, every admissible center I^0 lies in L_delta
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L470-L470
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L472-L472
CONTRACT_ID: lpM:L14#centers
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and (6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along the physical orbit in a fixed reference frame
SOURCE_QUANTIFIERS: for 0 < μ ≤ μ_0 (constants fixed first) and every such initial state (inherited from lpM:L14)
SOURCE_CONCLUSION: C(0) ≥ 0 and C(0) ≤ B(I^0) - δ give B(I^0) ≥ δ, so I^0 ∈ 𝓛_δ; no assumption B > δ on all of 𝒜 is needed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#static, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L14@L472-L472 | the nonnegativity of AMD
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L14@L472-L472 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L14#choices
KIND: step
TITLE: shared compact neighborhood U of L_delta; mu_0 so that the radius r has its tube in U and (39)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L472-L476
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L472-L476
CONTRACT_ID: lpM:L14#choices
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and (6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along the physical orbit in a fixed reference frame; local data: the stopped radius r of the drift supplier (r = √μ on route L12, r = D_0√μ on route L13)
SOURCE_QUANTIFIERS: fixed before the initial point and μ
SOURCE_CONCLUSION: choose once and for all a compact neighborhood U ⊂ Q of 𝓛_δ; decrease μ_0 (to at most the supplier's threshold) so that the action tube of radius r lies in U and nr + Ω_B(r) ≤ δ/4, Ω_B(r) ≤ δ/16 (39); all these choices precede the initial point and μ, and the modulus is uniform on U
CONSTANT_SCOPE: U and μ_0 depend only on the fixed data (and the supplier's constants)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#shared-U, lpM:L14#centers, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:chamber#chamber
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/MAIN.md#L14@L472-L472 | the shared compact U and its modulus Ω_B(r) → 0 (N2)
EDGE: lpM:L14#centers | docs/tracks/LP/source/MAIN.md#L14@L472-L472 | the centers lie in 𝓛_δ
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L14@L474-L474 | B occurs
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L14@L472-L472 | the chamber Q occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): U is the one shared compact set of Lemmas 6 and 8, r ≤ r_g; AMENDED: N6 (AMENDMENTS.md L15): on route L13 the radius is r = D_0√μ

NODE: lpM:L14#maximal-solution
KIND: step
TITLE: the initial state is collision-free (Lemma 5, m = delta); the unique maximal solution exists
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L470-L470
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L478-L478
CONTRACT_ID: lpM:L14#maximal-solution
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and (6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along the physical orbit in a fixed reference frame
SOURCE_QUANTIFIERS: for 0 < μ ≤ μ_0 (constants fixed first) and every such initial state (inherited from lpM:L14)
SOURCE_CONCLUSION: the initial state lies in the open physical domain (by Lemma 5 with U and m = δ, ¦q_i¦ ≥ d_⋆ and ¦q_i - q_j¦ ≥ d_pair > 0: initial pair collisions are excluded by (6)); the solution of (1) from it is locally unique and has a unique maximal interval of existence, on which it agrees with every local solution
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5, lpM:L5#pair-distances, lpM:L14#choices, lpM:L6#local-existence
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L14@L478-L478 | Lemma 5 with m = δ: the initial state lies in a compact nonsingular set (premise C(0) ≤ B(I^0) - δ, I^0 ∈ 𝓛_δ ⊂ U)
EDGE: lpM:L5#pair-distances | docs/tracks/LP/source/MAIN.md#L14@L478-L478 | ¦q_i - q_j¦ ≥ d_pair > 0 at the initial state (§1 L78)
EDGE: lpM:L14#choices | docs/tracks/LP/source/MAIN.md#L14@L478-L478 | the compact U containing 𝓛_δ
EDGE: lpM:L6#local-existence | docs/tracks/LP/source/MAIN.md#L14@L478-L478 | local existence and uniqueness of solutions of (1)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: MAIN takes 'the maximal local Newtonian solution' (L478) and uniqueness (L470, §1 L74) for granted; the passage from Lemma 6's local existence and uniqueness to a unique maximal solution agreeing with every local solution on its overlap is not argued (standard ODE continuation). §1 L78 'initial pair collisions are excluded by (6), as proved below' is supplied here by Lemma 5 with m = δ

NODE: lpM:L14#stopped-membership
KIND: step
TITLE: (40) on the stopped interval gives ¦z¦^2/2 = C < B(I^0) - 7 delta/16: every point lies in D_1
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L478-L481
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L478-L487
CONTRACT_ID: lpM:L14#stopped-membership
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and (6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along the physical orbit in a fixed reference frame; the connected interval containing 0 on which the solution is elliptic, its chart is defined and (40) ‖I(t) - I^0‖_∞ < r, C(t) < B(I(t)) - δ/2 hold
SOURCE_QUANTIFIERS: for 0 < μ ≤ μ_0 (constants fixed first) and every such initial state (inherited from lpM:L14)
SOURCE_CONCLUSION: on that interval ¦z(t)¦_2^2/2 = C(t) < B(I^0) - δ/2 + Ω_B(r) ≤ B(I^0) - 7δ/16, so every physical point lies in D_1 (using the whole ball (21)); this uses only the stopped conditions (40)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L14#choices, lpM:L6#shared-U, lpM:L14#maximal-solution, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L14#choices | docs/tracks/LP/source/MAIN.md#L14@L484-L484 | Ω_B(r) ≤ δ/16 of (39) and the tube in U
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/MAIN.md#L14@L484-L484 | B(I(t)) ≤ B(I^0) + Ω_B(r) on the tube
EDGE: lpM:L14#maximal-solution | docs/tracks/LP/source/MAIN.md#L14@L478-L478 | the maximal local solution whose stopped interval is taken
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L14@L484-L484 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L14#improvement
KIND: step
TITLE: the drift supplier improves the action bound (r/4 or r/2); (13), (17), (39) give AMD margin >= 3 delta/4
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L487-L487
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L487-L487
CONTRACT_ID: lpM:L14#improvement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and (6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along the physical orbit in a fixed reference frame; the stopped interval of lpM:L14#stopped-membership, up to T_μ
SOURCE_QUANTIFIERS: for 0 < μ ≤ μ_0 (constants fixed first) and every such initial state (inherited from lpM:L14); on every finite subinterval up to T_μ
SOURCE_CONCLUSION: on every finite subinterval of the stopped interval up to T_μ the action bound improves to r' (r' = r/4 on route L12, r' = r/2 on route L13), and C(t) ≤ B(I(t)) - δ + nr' + Ω_B(r') ≤ B(I(t)) - 3δ/4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L14#stopped-membership, lpM:L3#dynamic, lpM:L6#moving-threshold, lpM:L14#choices
ROUTES: lpM:L14#route-L12, lpM:L14#route-L13
ROUTE_FOR: -
EDGE: lpM:L14#stopped-membership | docs/tracks/LP/source/MAIN.md#L14@L487-L487 | the orbit lies in D_1 (the drift supplier's stopped premise)
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#L14@L487-L487 | the identity of (13)
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L14@L487-L487 | (17) with the improved radius
EDGE: lpM:L14#choices | docs/tracks/LP/source/MAIN.md#L14@L487-L487 | (39)
EDGE: lpM:L14#route-L12 | docs/tracks/LP/source/MAIN.md#L14@L487-L487 | Lemma 12 is valid on the stopped interval and improves the bound to r/4
EDGE: lpM:L14#route-L13 | docs/tracks/LP/source/MAIN.md#L14@L500-L500 | using Lemma 13 instead: its stopped slow-membership premise is the membership proved before the improvement
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N6, N7 (AMENDMENTS.md L15, L16): the two drift suppliers are alternatives (route nodes)

NODE: lpM:L14#route-L12
KIND: route
TITLE: drift supplier Lemma 12: r = sqrt(mu), improvement to r/4 up to T_mu = exp(c mu^{-a})
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L487-L487
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L487-L487
CONTRACT_ID: lpM:L14#route-L12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as in lpM:L14#improvement
SOURCE_QUANTIFIERS: as in lpM:L14#improvement
SOURCE_CONCLUSION: with r = √μ and μ_0 ≤ μ_1, on every finite subinterval of the stopped interval up to T_μ = exp(cμ^{-a}), ‖I(t) - I^0‖_∞ ≤ r/4 (34)
CONSTANT_SCOPE: μ_1, c and M_1 are those of Lemma 12
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L12
ROUTES: -
ROUTE_FOR: lpM:L14#improvement
EDGE: lpM:L12 | docs/tracks/LP/source/MAIN.md#L14@L487-L487 | Lemma 12 (its premises: the chart-domain statement of Lemma 14's hypothesis and (5))
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N7 (AMENDMENTS.md L16): the paper route; A_I = 1, T_0 = 1 (L500)

NODE: lpM:L14#route-L13
KIND: route
TITLE: drift supplier Lemma 13 (Lean route): r = D_0 sqrt(mu), improvement to r/2 up to exp(c_1 mu^{-a})
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L500-L500
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L500-L500
CONTRACT_ID: lpM:L14#route-L13
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as in lpM:L14#improvement
SOURCE_QUANTIFIERS: as in lpM:L14#improvement
SOURCE_CONCLUSION: with r = D_0√μ, on every finite subinterval of the stopped interval up to exp(c_1μ^{-a}), ‖I(t) - I^0‖_∞ ≤ r/2; the stopped slow-membership premise of Lemma 13 is the membership proved before the improvement; A_I becomes a fixed multiple of D_0
CONSTANT_SCOPE: κ_1, c_1 and the μ threshold are those of Lemma 13 for the fixed D_0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L13
ROUTES: -
ROUTE_FOR: lpM:L14#improvement
EDGE: lpM:L13 | docs/tracks/LP/source/MAIN.md#L14@L500-L500 | Lemma 13 with the stopped interval J of Lemma 14 (its premises: the chart-domain statement of Lemma 14's hypothesis and (5))
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N6, N7 (AMENDMENTS.md L15, L16): the Lean route; (39) still gives C ≤ B(I(t)) - δ + nr/2 + Ω_B(r/2) ≤ B(I(t)) - 3δ/4

NODE: lpM:L14#no-exit
KIND: step
TITLE: a forward end t_* <= T_mu is impossible: Lemma 5 compact set, Lemma 6 continuation, persisting improved bounds
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L470-L470
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L489-L489
CONTRACT_ID: lpM:L14#no-exit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and (6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along the physical orbit in a fixed reference frame
SOURCE_QUANTIFIERS: for 0 < μ ≤ μ_0 (constants fixed first) and every such initial state (inherited from lpM:L14)
SOURCE_CONCLUSION: if the forward end of the stopped interval were t_* ≤ T_μ: Lemma 5 with margin δ/2 bounds the preceding orbit in a compact nonsingular physical set (energies uniformly negative, individual angular-momentum projections bounded away from zero); Lemma 6 extends the physical solution through a finite maximal endpoint (continuity at any other endpoint); the chart stays valid at the limit (it covers the entire prograde region); the improved bounds r' < r and 3δ/4 > δ/2 persist near t_*, a contradiction; hence the solution and (40) hold through T_μ, elliptic with I(t) ∈ U ⊂ Q
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5, lpM:L6, lpM:L14#improvement, lpM:L14#stopped-membership
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L14@L489-L489 | Lemma 5 with m = δ/2 (its premise C ≤ B(I) - δ/2 is (40))
EDGE: lpM:L6 | docs/tracks/LP/source/MAIN.md#L14@L489-L489 | Lemma 6 continues the solution through a finite maximal endpoint
EDGE: lpM:L14#improvement | docs/tracks/LP/source/MAIN.md#L14@L489-L489 | the improved bounds r' and 3δ/4
EDGE: lpM:L14#stopped-membership | docs/tracks/LP/source/MAIN.md#L14@L489-L489 | the stopped interval and its chart
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L14#backward
KIND: step
TITLE: the backward direction by the same normal-form estimate with ¦t¦ and backward continuation
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L470-L470
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L489-L489
CONTRACT_ID: lpM:L14#backward
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and (6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along the physical orbit in a fixed reference frame
SOURCE_QUANTIFIERS: for 0 < μ ≤ μ_0 (constants fixed first) and every such initial state (inherited from lpM:L14); t ≤ 0
SOURCE_CONCLUSION: the solution exists back to -T_μ with the same bounds; all inequalities hold at both endpoints of (7) by continuity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L14#no-exit, lpM:L6#backward
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L14#no-exit | docs/tracks/LP/source/MAIN.md#L14@L489-L489 | the forward argument with ¦t¦
EDGE: lpM:L6#backward | docs/tracks/LP/source/MAIN.md#L14@L489-L489 | the backward continuation of Lemma 6
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L14#separation
KIND: step
TITLE: separation constants of Lemma 5 with m = delta/2, d_star = a_min delta^2/(8 I_max^2) (41); all pairs separated
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L491-L495
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L491-L495
CONTRACT_ID: lpM:L14#separation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and (6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along the physical orbit in a fixed reference frame
SOURCE_QUANTIFIERS: for 0 < μ ≤ μ_0 (constants fixed first) and every such initial state (inherited from lpM:L14); every t ∈ [-T_μ, T_μ]
SOURCE_CONCLUSION: the final separation constants are those of Lemma 5 with m = δ/2, including d_⋆ = a_min δ^2/(8 I_max^2) (41); (9) holds on [-T_μ, T_μ], and all adjacent and nonadjacent physical pairs, and the star distances, are separated by d_pair, d_⋆
CONSTANT_SCOPE: d_⋆, d_pair depend only on (n, ν, U, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5, lpM:L5#perihelion, lpM:L5#pair-distances, lpM:L14#no-exit, lpM:L14#backward
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L14@L491-L491 | Lemma 5 with U and m = δ/2: perihelia and adjacent gaps
EDGE: lpM:L5#perihelion | docs/tracks/LP/source/MAIN.md#L14@L493-L493 | (16) with m = δ/2 is (41)
EDGE: lpM:L5#pair-distances | docs/tracks/LP/source/MAIN.md#L14@L495-L495 | star and nonadjacent pair distances
EDGE: lpM:L14#no-exit | docs/tracks/LP/source/MAIN.md#L14@L491-L491 | C(t) ≤ B(I(t)) - δ/2 and I(t) ∈ U on the forward interval
EDGE: lpM:L14#backward | docs/tracks/LP/source/MAIN.md#L14@L491-L491 | the same on the backward interval
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L14#axis-drift
KIND: step
TITLE: ¦a_i(I) - a_i(I^0)¦ <= (2 I_max/min nu_i^2) ¦¦I - I^0¦¦: A_I = 1, A_a, T_0 = 1
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L495-L500
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L14@L495-L500
CONTRACT_ID: lpM:L14#axis-drift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L14: the data of §1 (lpM:s1:data) and an initial state with q_i ≠ 0, E_i < 0 and (6); the uniform chart/domain construction (21)-(22) (Lemma 8 type, m slow pairs); an exact real analytic symplectic chart of the entire prograde negative-energy region with H_μ = h + μf and ¦z(t)¦_2^2/2 = C(t) along the physical orbit in a fixed reference frame
SOURCE_QUANTIFIERS: for 0 < μ ≤ μ_0 (constants fixed first) and every such initial state (inherited from lpM:L14); every t ∈ [-T_μ, T_μ]
SOURCE_CONCLUSION: ¦a_i(I) - a_i(I^0)¦ = ¦I_i - I_i^0¦ ¦I_i + I_i^0¦/ν_i^2 ≤ (2I_max/min_i ν_i^2)‖I - I^0‖_∞; one can take A_I = 1, A_a = 2I_max/min_i ν_i^2 and T_0 = 1 (on route L13, A_I a fixed multiple of D_0); enlarging constants is harmless
CONSTANT_SCOPE: A_I, A_a, T_0 depend only on the fixed data (and D_0 on route L13)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:thresholds#actionAxis, lpM:L14#no-exit, lpM:L14#backward, lpM:L5#perihelion
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L14@L497-L497 | a_i(I) = (I_i/ν_i)^2
EDGE: lpM:L14#no-exit | docs/tracks/LP/source/MAIN.md#L14@L500-L500 | ‖I(t) - I^0‖_∞ ≤ r' ≤ r on the forward interval
EDGE: lpM:L14#backward | docs/tracks/LP/source/MAIN.md#L14@L500-L500 | the same backward
EDGE: lpM:L5#perihelion | docs/tracks/LP/source/MAIN.md#L14@L498-L498 | I_max is the extremum over U of Lemma 5
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:T15
KIND: theorem
TITLE: Theorem 15: planar nonresonant exponential safety (the §1 conclusion for d = 2)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L504-L504
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
CONTRACT_ID: lpM:T15
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 2; n ≥ 2; ν_i > 0 with max_i ν_i = 1; 𝒜 ⊂ {0 < a_1 < ... < a_n} compact; δ, γ > 0; τ > n - 1
SOURCE_QUANTIFIERS: there exist μ_0, c, T_0, A_I, A_a, d_⋆, d_pair, A_osc > 0; then for every 0 < μ ≤ μ_0 and every planar initial state with q_i ≠ 0, E_i < 0 and (6): a(0) ∈ 𝒜, (5) at ω(I^0), C(0) ≤ B(I^0) - δ
SOURCE_CONCLUSION: the unique maximal solution of (1) exists on [-T_μ, T_μ], T_μ = T_0 exp(cμ^{-a}), a = 1/(2(τ+1)) (7); on it the state is elliptic, I(t) ∈ Q, ‖I(t) - I^0‖_∞ ≤ A_I√μ, ‖a(t) - a(0)‖_∞ ≤ A_a√μ, ¦C(t) - C(0)¦ ≤ nA_I√μ, C(t) ≤ B(I(t)) - δ/2 (8), a_i(1 - e_i) ≥ d_⋆, a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair (9); actual star distances and all planet-pair distances are at least d_⋆, d_pair; the velocity-osculating perihelion and aphelion radii are within A_osc μ of the canonical ones and their star and adjacent-annulus gaps are at least d_⋆/2, d_pair/2 (no orbit crossing, L93)
CONSTANT_SCOPE: μ_0, c, T_0, A_I, A_a, d_⋆, d_pair, A_osc depend only on (n, ν, 𝒜, δ, γ, τ) (d = 2) and are chosen before μ and the initial state; A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2 (N10)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:T15#orientation, lpM:T15#chart-cover, lpM:T15#apply-L14, lpM:T15#reconstruction, lpM:T15#osculating, lpM:s1:data, lpM:s1:dioph, lpM:s1:elements, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:chamber#chamber
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T15#orientation | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | orientation reversal so that L > 0
EDGE: lpM:T15#chart-cover | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the Lemma 7 charts cover and C = ¦z¦^2/2
EDGE: lpM:T15#apply-L14 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | Lemma 14 closes the first exit and proves (7)-(9)
EDGE: lpM:T15#reconstruction | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | Lemma 1: actual star and pair distances are those of q
EDGE: lpM:T15#osculating | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | Lemma 16: the osculating conclusion
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L70-L70 | the fixed data (n, ν with max ν = 1, 𝒜, δ, γ, τ)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | (6) contains (5)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | C, a, e, I of the initial state and along the orbit
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | B occurs
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | the chamber Q occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: planar MAIN theorem; its frozen statement is the anchor LP1 lpM:T15#planar_strongAMD_exponentialSafety (packet LP-athm-w2). The source dependency list 'Lemmas 1-14 and 16' is read with N7: Lemmas 12 and 13 are alternatives (routes inside Lemma 14). AMENDED: N7, N8, N10 (AMENDMENTS.md L16, L17, L19).

NODE: lpM:T15#orientation
KIND: step
TITLE: Lemma 3: L != 0, all L_i of its sign; reverse the plane so that the sign is positive (H, constants invariant)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L504-L504
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
CONTRACT_ID: lpM:T15#orientation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T15: the data of §1 with d = 2; 0 < μ ≤ μ_0; a planar initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T15)
SOURCE_CONCLUSION: C(0) ≤ B(I^0) - δ < B_⋆(I^0), so Lemma 3 gives L ≠ 0 and individual scalar angular momenta of its sign; reversing the planar orientation (simultaneously on positions and momenta) makes the sign positive, and the Hamiltonian (1), the orientation-free C and all constants are invariant
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#static, lpM:L3#planar-orientation, lpM:s1:model, lpM:s1:elements, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | L ≠ 0 and H_i > 0 under C < B_⋆ (supplied by (6))
EDGE: lpM:L3#planar-orientation | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | in the plane all L_i share the sign of L
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | (1) is invariant under the orthogonal change
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | C = ΣI - ¦L¦ is orientation-free (N8)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N8 (AMENDMENTS.md L17): this reflection reduction is the bridge between the frozen orientation-free C (OD-1) and the prograde chart

NODE: lpM:T15#chart-cover
KIND: step
TITLE: the product of the Lemma 7 charts covers every initial state; C = sum Gamma_i = ¦z¦^2/2 in the prograde region
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L504-L504
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
CONTRACT_ID: lpM:T15#chart-cover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T15: the data of §1 with d = 2; 0 < μ ≤ μ_0; a planar initial state with q_i ≠ 0, E_i < 0 and (6); orientation with L > 0
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T15)
SOURCE_CONCLUSION: the product of the charts of Lemma 7 covers every (oriented) initial state and gives C = Σ_i Γ_i = ¦z¦_2^2/2 wherever the physical orbit remains in the prograde region; exact conservation of L keeps the reference orientation fixed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7, lpM:T15#orientation, lpM:L3#dynamic, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the chart of each planet, with G_i = I_i - Γ_i
EDGE: lpM:T15#orientation | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | all L_i > 0 at the initial state
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | conservation of L
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | C = Σ I_i - ¦L¦ = Σ(I_i - G_i) when every L_i > 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:T15#apply-L14
KIND: step
TITLE: Lemma 14 with the Lemma 7 product chart and Lemma 8 (m = n): (7)-(9) in the plane
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L504-L504
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
CONTRACT_ID: lpM:T15#apply-L14
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T15: the data of §1 with d = 2; 0 < μ ≤ μ_0; a planar initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T15)
SOURCE_CONCLUSION: the premises of Lemma 14 hold in the plane (chart of the entire prograde negative-energy region with H_μ = h + μf by Lemmas 7-8, the uniform domain (21)-(22) by Lemma 8 with m = n, the identity ¦z(t)¦^2/2 = C(t)), so the unique maximal solution exists on (7) with (8)-(9) and the distance bounds
CONSTANT_SCOPE: the constants of Lemma 14, for d = 2
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L14, lpM:L7, lpM:L8, lpM:T15#chart-cover
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L14 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | Lemma 14 closes the first exit
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the chart of the entire prograde negative-energy region
EDGE: lpM:L8 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the analytic domain, perturbation bounds and exact split (m = n slow pairs)
EDGE: lpM:T15#chart-cover | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the identity ¦z(t)¦^2/2 = C(t) along the orbit
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:T15#reconstruction
KIND: step
TITLE: Lemma 1 reconstructs the exact Newtonian motion (masses 1, mu nu_i)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L504-L504
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
CONTRACT_ID: lpM:T15#reconstruction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T15: the data of §1 with d = 2; 0 < μ ≤ μ_0; a planar initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T15); t ∈ [-T_μ, T_μ]
SOURCE_CONCLUSION: the solution of (1) on [-T_μ, T_μ] reconstructs a Newtonian (1+n)-body solution with masses (1, μν_1, ..., μν_n) (barycentric positions and velocities of Lemma 1); its star and pair distances are ¦q_i¦ and ¦q_i - q_j¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1, lpM:T15#apply-L14
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | Lemma 1 reconstructs the Newtonian motion
EDGE: lpM:T15#apply-L14 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the collision-free solution on [-T_μ, T_μ]
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:T15#osculating
KIND: step
TITLE: Lemma 16 on the Lemma 5 compact set (m = delta/2) gives the osculating conclusion
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L504-L504
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
CONTRACT_ID: lpM:T15#osculating
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T15: the data of §1 with d = 2; 0 < μ ≤ μ_0; a planar initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T15); t ∈ [-T_μ, T_μ]
SOURCE_CONCLUSION: along the solution the velocity-osculating elements are nondegenerate elliptic (E^osc < 0, a^osc > 0, e^osc < 1), the osculating ellipse passes through q_i (a^osc(1 - e^osc) ≤ ¦q_i¦ ≤ a^osc(1 + e^osc)), ¦a^osc - a¦ + ¦e^osc - e¦ ≤ Aμ, the perihelion and aphelion radii are within A_osc μ of the canonical ones, and with A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 the osculating star and adjacent gaps are at least d_⋆/2, d_pair/2
CONSTANT_SCOPE: A and A_osc depend only on the compact set of Lemma 5 (m = δ/2) and the fixed masses
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L16, lpM:L16#mu0-choice, lpM:L16#half-gaps, lpM:L14#separation, lpM:T15#apply-L14
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | Lemma 16 on the compact set of Lemma 5
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/source/MAIN.md#L16@L528-L528 | the final μ_0 of N10
EDGE: lpM:L16#half-gaps | docs/tracks/LP/source/MAIN.md#L16@L529-L529 | the osculating half gaps
EDGE: lpM:L14#separation | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the orbit stays in Lemma 5's compact set with m = δ/2
EDGE: lpM:T15#apply-L14 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the solution on [-T_μ, T_μ]
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N10 (AMENDMENTS.md L19)

NODE: lpM:L16:defs
KIND: definition
TITLE: actual-velocity osculating elements (42), any dimension d
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L519
PROOF_SOURCE: -
CONTRACT_ID: lpM:L16:defs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of lpM:s1:data; μ > 0; a state (q, p) of the model
SOURCE_QUANTIFIERS: for every state and every i
SOURCE_CONCLUSION: V_i = q̇_i = p_i/ν_i + μΣ_j p_j, k_i = 1 + μν_i, E_i^osc = ¦V_i¦^2/2 - k_i/¦q_i¦, a_i^osc = -k_i/(2E_i^osc), e_i^osc = ((¦V_i¦^2 - k_i/¦q_i¦)q_i - (q_i·V_i)V_i)/k_i, e_i^osc = ¦e_i^osc¦ (42)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1#velocity, lpM:s1:model, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#velocity | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | V_i is the actual velocity q̇_i of (10)
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the masses ν_i, μ and the variables q, p
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | the Euclidean length and the dimension d
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: d-generic source definition (d ∈ {2,3}); the planar frozen realizations are the anchors lpM:L16:defs#* (LP-adef-pl), the spatial ones come in wave 3 (SPEC §5)

NODE: lpM:L16
KIND: lemma
TITLE: Lemma 16: actual-velocity osculating ellipses (43), any dimension d
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L529
CONTRACT_ID: lpM:L16
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a fixed safe compact physical set K of Lemma 5 (for some compact U ⊂ Q and m > 0); the elements (42); d ∈ {2,3}
SOURCE_QUANTIFIERS: there are A, A_osc > 0 and a threshold μ_0 > 0; then for every 0 < μ ≤ μ_0, uniformly on K, and every i
SOURCE_CONCLUSION: the elements (42) are nondegenerate elliptic (E_i^osc < 0, e_i^osc < 1) and ¦a_i^osc - a_i¦ + ¦e_i^osc - e_i¦ ≤ Aμ, ¦a_i^osc(1 ± e_i^osc) - a_i(1 ± e_i)¦ ≤ A_osc μ (43); these ellipses pass through the current positions and are tangent to the actual heliocentric velocities
CONSTANT_SCOPE: A, A_osc and μ_0 depend only on K and the fixed masses
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L16#element-error, lpM:L16#elliptic, lpM:L16#endpoint-estimate, lpM:L16#tangent-ellipse, lpM:L16:defs, lpM:L5, lpM:L1#velocity
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#element-error | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | ¦E^osc - E¦ + ¦e^osc - e¦ ≤ A_0μ
EDGE: lpM:L16#elliptic | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | E^osc ≤ -1/(4a_max), the axis estimate, e^osc < 1
EDGE: lpM:L16#endpoint-estimate | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | the second estimate of (43)
EDGE: lpM:L16#tangent-ellipse | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | the ellipse through q_i tangent to V_i
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the elements (42)
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the safe compact physical sets of Lemma 5
EDGE: lpM:L1#velocity | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | V_i = q̇_i: tangency to the actual velocity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the closing remark on the gravitational-parameter-one convention (L529) is EXCLUDED

NODE: lpM:L16#element-error
KIND: step
TITLE: ¦V_i - v_i¦ <= n P mu, ¦k_i - 1¦ <= mu; expansion: ¦E^osc - E¦ + ¦e^osc - e¦ <= A_0 mu
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L524
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: lpM:L16#element-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L16: a fixed safe compact physical set K of Lemma 5 (for a compact U ⊂ Q and m > 0) with ¦p_i¦ ≤ P, ¦q_i¦ ≥ d_⋆, E_i ≤ -1/(2a_max) on K; the elements (42); μ > 0 small
SOURCE_QUANTIFIERS: for every state of K and every i (inherited from lpM:L16)
SOURCE_CONCLUSION: ¦V_i - v_i¦ ≤ nPμ and ¦k_i - 1¦ ≤ μ; direct expansion of (42) with bounded positions and momenta and ¦q_i¦ ≥ d_⋆ gives ¦E_i^osc - E_i¦ + ¦e_i^osc - e_i¦ ≤ A_0μ
CONSTANT_SCOPE: A_0 depends only on K and the masses
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L16:defs, lpM:L1#velocity, lpM:L5#compact-physical, lpM:L5#pair-distances, lpM:s1:data, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | the elements (42)
EDGE: lpM:L1#velocity | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | V_i - v_i = μΣ_j p_j by (10)
EDGE: lpM:L5#compact-physical | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | positions and momenta bounded (¦p_i¦ ≤ P) on K
EDGE: lpM:L5#pair-distances | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | ¦q_i¦ ≥ d_⋆ on K
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | ν_i ≤ max ν = 1 gives ¦k_i - 1¦ ≤ μ
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | E_i and e_i of (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L16#elliptic
KIND: step
TITLE: E^osc <= -1/(4 a_max) for small mu_0; reciprocal identity: axis estimate; ¦e^osc - e¦ <= ¦e^osc vec - e vec¦; e^osc < 1
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L523
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: lpM:L16#elliptic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L16: a fixed safe compact physical set K of Lemma 5 (for a compact U ⊂ Q and m > 0) with ¦p_i¦ ≤ P, ¦q_i¦ ≥ d_⋆, E_i ≤ -1/(2a_max) on K; the elements (42); μ > 0 small
SOURCE_QUANTIFIERS: for every state of K and every i (inherited from lpM:L16)
SOURCE_CONCLUSION: since E_i ≤ -1/(2a_max), μ_0 can be chosen with E_i^osc ≤ -1/(4a_max); the identity for the difference of two reciprocals gives ¦a_i^osc - a_i¦ ≤ Aμ; the triangle inequality gives ¦e_i^osc - e_i¦ ≤ ¦e_i^osc - e_i¦ (vectors), including at circular orbits; since e_i ≤ e_* < 1, decreasing μ_0 gives e_i^osc < 1
CONSTANT_SCOPE: A and μ_0 depend only on K and the masses
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L16#element-error, lpM:L5#compact-physical, lpM:L5#perihelion, lpM:L16:defs
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#element-error | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | the energy and eccentricity-vector errors
EDGE: lpM:L5#compact-physical | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | E_i ≤ -1/(2a_max) on K
EDGE: lpM:L5#perihelion | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | √(1 - e_i^2) ≥ m/I_max: e_i ≤ e_* < 1 on K
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | a^osc = -k/(2E^osc)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L16#endpoint-estimate
KIND: step
TITLE: expansion of the products: ¦a^osc(1 +- e^osc) - a(1 +- e)¦ <= A_osc mu
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L524
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: lpM:L16#endpoint-estimate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L16: a fixed safe compact physical set K of Lemma 5 (for a compact U ⊂ Q and m > 0) with ¦p_i¦ ≤ P, ¦q_i¦ ≥ d_⋆, E_i ≤ -1/(2a_max) on K; the elements (42); μ > 0 small
SOURCE_QUANTIFIERS: for every state of K and every i (inherited from lpM:L16)
SOURCE_CONCLUSION: expanding the products gives the second estimate of (43): ¦a_i^osc(1 ± e_i^osc) - a_i(1 ± e_i)¦ ≤ A_osc μ
CONSTANT_SCOPE: A_osc depends only on K and the masses
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L16#elliptic
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#elliptic | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | the axis and eccentricity errors
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L16#tangent-ellipse
KIND: step
TITLE: the two-body ellipse with position q_i, velocity V_i, parameter k_i; Lemma 2 with parameter k_i: it contains q_i
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L525-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: lpM:L16#tangent-ellipse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: one planet: q ≠ 0, a velocity V, a parameter k > 0 with E^osc = ¦V¦^2/2 - k/¦q¦ < 0; the elements (42)
SOURCE_QUANTIFIERS: for every such (q, V, k)
SOURCE_CONCLUSION: the two-body initial-value problem with position q, velocity V and gravitational parameter k defines the tangent ellipse with invariants a^osc, e^osc; Lemma 2 with parameter k gives a^osc(1 - e^osc) ≤ ¦q¦ ≤ a^osc(1 + e^osc) and e^osc ≤ 1, so the ellipse contains the position
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:L16:defs
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | the orbital identities (11)-(12), with parameter k (rescale V by 1/√k)
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | the elements (42)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Lemma 2 is stated with parameter one; applying it with parameter k_i is the rescaling w = V/√k, which maps (42) to the elements of (2) with ν = 1 (routine)

NODE: lpM:L16#mu0-choice
KIND: step
TITLE: final mu_0: A_osc mu_0 <= d_star/2 and 2 A_osc mu_0 <= d_pair/2 (N10)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L528-L528
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L528-L528
CONTRACT_ID: lpM:L16#mu0-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L16: a fixed safe compact physical set K of Lemma 5 (for a compact U ⊂ Q and m > 0) with ¦p_i¦ ≤ P, ¦q_i¦ ≥ d_⋆, E_i ≤ -1/(2a_max) on K; the elements (42); μ > 0 small
SOURCE_QUANTIFIERS: fixed before μ
SOURCE_CONCLUSION: μ_0 also satisfies A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2
CONSTANT_SCOPE: μ_0 depends only on the fixed data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L16#endpoint-estimate, lpM:L5
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#endpoint-estimate | docs/tracks/LP/source/MAIN.md#L16@L528-L528 | the constant A_osc
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L16@L528-L528 | d_⋆ and d_pair of Lemma 5
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N10 (AMENDMENTS.md L19): the headline constant list records this

NODE: lpM:L16#half-gaps
KIND: step
TITLE: subtracting the endpoint errors: osculating star gap >= d_star/2, adjacent gaps >= d_pair/2
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L529-L529
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L529-L529
CONTRACT_ID: lpM:L16#half-gaps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L16: a fixed safe compact physical set K of Lemma 5 (for a compact U ⊂ Q and m > 0) with ¦p_i¦ ≤ P, ¦q_i¦ ≥ d_⋆, E_i ≤ -1/(2a_max) on K; the elements (42); μ > 0 small; μ ≤ μ_0 of N10
SOURCE_QUANTIFIERS: for every state of K and every i (inherited from lpM:L16)
SOURCE_CONCLUSION: a_i^osc(1 - e_i^osc) ≥ d_⋆ - A_osc μ ≥ d_⋆/2 and a_{i+1}^osc(1 - e_{i+1}^osc) - a_i^osc(1 + e_i^osc) ≥ d_pair - 2A_osc μ ≥ d_pair/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L16#endpoint-estimate, lpM:L16#mu0-choice, lpM:L5
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#endpoint-estimate | docs/tracks/LP/source/MAIN.md#L16@L529-L529 | the endpoint errors ≤ A_osc μ
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/source/MAIN.md#L16@L529-L529 | A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L16@L529-L529 | the canonical perihelia ≥ d_⋆ and gaps ≥ d_pair on K
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
