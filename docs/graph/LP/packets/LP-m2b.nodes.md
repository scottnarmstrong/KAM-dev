NODE: lpM:L5
KIND: lemma
TITLE: Lemma 5: the uniform strong barrier (any dimension d)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L175
CONTRACT_ID: lpM:L5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 and ν_i > 0 (lpM:s1:data); U ⊂ Q compact; m > 0
SOURCE_QUANTIFIERS: for every n ≥ 2, positive ν, d ∈ {2,3}, compact U ⊂ Q and m > 0: there exist d_⋆ > 0 and d_pair > 0 before all states and lists; for every negative-energy state with I ∈ U and C ≤ B(I) - m the state clauses hold; independently, for every I ∈ U and e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m the same perihelion and gap bounds hold with a_i = a_i(I)
SOURCE_CONCLUSION: perihelia a_i(1 - e_i) ≥ d_⋆ and adjacent-annulus gaps a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair, for these states and for these lists; all these states belong to a compact subset of the nonsingular physical region and satisfy H_i ≥ m in their invariable frame
CONSTANT_SCOPE: d_⋆ and d_pair are uniform: they depend only on (n, ν, U, m)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5#gap-positive, lpM:L5#Km-compact, lpM:L5#empty-case, lpM:L5#perihelion, lpM:L5#compact-physical, lpM:L5#projection, lpM:s1:data, lpM:s1:elements, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5#gap-positive | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | every adjacent gap is positive
EDGE: lpM:L5#Km-compact | docs/tracks/LP/source/MAIN.md#L5@L166-L170 | the compact set K_m and d_pair
EDGE: lpM:L5#empty-case | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | the empty case
EDGE: lpM:L5#perihelion | docs/tracks/LP/source/MAIN.md#L5@L170-L175 | the perihelion bound d_⋆ (16)
EDGE: lpM:L5#compact-physical | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | the compact nonsingular physical set
EDGE: lpM:L5#projection | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | H_i ≥ m
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | n ≥ 2 and the masses ν are fixed data
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | C, the elements a_i, e_i and H_i of (2)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | U ⊂ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | B(I) occurs
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | Σ I_i D(e_i) occurs
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the independent list clause uses a_i(I) = (I_i/ν_i)^2, rather than an axis extracted from a physical state
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2b
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.barrier_osc_data ; KAM.Planetary.Spatial.spatialBarrier_osc_data
LEAN_NOTE: d-generic: planar and spatial realizations (mechanical docstring match, D65)
NOTE: d-generic source lemma (d ∈ {2,3}); its planar instance is the anchor LP0 (lpM:L5#planar_strongAMD_barrier); the spatial consumers (Lemma 6, Lemma 16, wave 3) use this node. AMENDED: N11 (AMENDMENTS.md L20).

NODE: lpM:L5#gap-positive
KIND: step
TITLE: a nonpositive adjacent gap would be feasible, so C >= B_{i,i+1} >= B: contradiction
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L166
CONTRACT_ID: lpM:L5#gap-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited)
SOURCE_CONCLUSION: every adjacent gap a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) is positive: otherwise (e_i, e_{i+1}) is feasible for B_{i,i+1}(I), and Σ_k I_k D(e_k) ≥ B_{i,i+1}(I) ≥ B(I) (for states via C ≥ Σ_k I_k D(e_k)) contradicts ≤ B(I) - m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#static, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#actionAxis, lpM:s1:elements, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the inequality of (13), C ≥ Σ I_k D(e_k); its premise C < B_⋆ holds because C ≤ B(I) - m < B(I) ≤ B_⋆(I)
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | a nonpositive gap makes the pair feasible
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the feasible pair costs at least B_{i,i+1}(I)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | B_{i,i+1}(I) ≥ B(I)
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the constraint uses a_i(I) = (I_i/ν_i)^2
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the Kepler axis of a state equals a_i(I) since I_i = ν_i √a_i
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the deficit sum uses D and its nonnegativity on [0,1]
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the feasible pair objective I_i D(e_i) + I_{i+1} D(e_{i+1}) is bounded by the total deficit and below by the pair minimum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2b
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L5#Km-compact
KIND: step
TITLE: K_m is compact by Lemma 4; d_pair is the minimum of the gaps over K_m
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L167-L169
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L170
CONTRACT_ID: lpM:L5#Km-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m; local data: K_m = {(I,e) ∈ U × [0,1]^n : Σ_i I_i D(e_i) ≤ B(I) - m}
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited)
SOURCE_CONCLUSION: K_m is compact; every state of the hypothesis gives (I, e) ∈ K_m; every adjacent gap is positive on K_m; if K_m ≠ ∅, d_pair(U,m) := the minimum over K_m of the finitely many adjacent gaps is positive
CONSTANT_SCOPE: d_pair depends only on (n, ν, U, m)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4, lpM:L5#gap-positive, lpM:L3#static, lpM:ext-compact-min, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4 | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | K_m is compact by the continuity of B (Lemma 4)
EDGE: lpM:L5#gap-positive | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | every adjacent gap is positive on K_m
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | states satisfy Σ I_i D(e_i) ≤ C ≤ B(I) - m, so (I, e) ∈ K_m
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | the continuous gaps attain their minimum on the compact K_m
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L5@L168-L168 | K_m is defined with D
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L5@L168-L168 | K_m is defined with B
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | the gaps a_{i+1}(I)(1 - e_{i+1}) - a_i(I)(1 + e_i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L5#empty-case
KIND: step
TITLE: K_m empty: any positive constants, the assertions are vacuous
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L170-L170
CONTRACT_ID: lpM:L5#empty-case
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m; K_m = ∅
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited)
SOURCE_CONCLUSION: if K_m is empty, any positive constants d_⋆, d_pair work and all assertions are vacuous
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5#Km-compact
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5#Km-compact | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | the case split is on K_m, which contains every state and list of the hypothesis
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L5#perihelion
KIND: step
TITLE: (16): sqrt(1 - e_i^2) >= m/I_max and a_i(1 - e_i) >= a_min m^2/(2 I_max^2) =: d_star
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L171-L174
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L170-L175
CONTRACT_ID: lpM:L5#perihelion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m; K_m ≠ ∅; local data: I_max = max_{I∈U,i} I_i, a_min = min_{I∈U,i} a_i(I) > 0, a_max = max_{I∈U,i} a_i(I)
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited)
SOURCE_CONCLUSION: the deficit bound I_i D(e_i) ≤ B(I) - m ≤ I_i - m gives √(1 - e_i^2) ≥ m/I_i ≥ m/I_max, and with 1 - e ≥ (1 - e^2)/2, a_i(1 - e_i) ≥ a_min m^2/(2 I_max^2) =: d_⋆ (16); in the nonempty case m ≤ I_max
CONSTANT_SCOPE: d_⋆ depends only on (n, ν, U, m) and is defined before the momentum bound (N11)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5#Km-compact, lpM:ext-compact-min, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#actionAxis, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:chamber#chamber
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5#Km-compact | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | every state and list gives a point of K_m
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | I_max, a_min, a_max are extrema over the compact U
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L5@L172-L172 | D(e) = 1 - √(1 - e^2)
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | a_i(I) on U
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L5@L172-L172 | B(I) ≤ B_⋆(I) ≤ I_i
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | a_min > 0 because U ⊂ Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N11 (AMENDMENTS.md L20): define d_⋆ := a_min m^2/(2 I_max^2) first, then bound ¦p_i¦

NODE: lpM:L5#bounds
KIND: step
TITLE: ¦q_i¦ <= 2 a_max and ¦p_i¦ <= nu_i sqrt(2/d_star) by (12)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
CONTRACT_ID: lpM:L5#bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m; K_m ≠ ∅
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited) (states)
SOURCE_CONCLUSION: for every state of the hypothesis, ¦q_i¦ ≤ a_i(1 + e_i) ≤ 2 a_max and ¦p_i¦ ≤ ν_i √(2/d_⋆)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:L5#perihelion
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | (12): ¦q¦ ≤ a(1 + e) and ¦p¦^2 = ν^2(2/¦q¦ - 1/a)
EDGE: lpM:L5#perihelion | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | ¦q_i¦ ≥ a_i(1 - e_i) ≥ d_⋆ and the extrema a_max
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N11 (AMENDMENTS.md L20)

NODE: lpM:L5#pair-distances
KIND: step
TITLE: ¦q_i¦ >= d_star and ordered radial intervals give ¦q_j - q_i¦ >= d_pair
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
CONTRACT_ID: lpM:L5#pair-distances
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m; K_m ≠ ∅
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited) (states); for all i < j
SOURCE_CONCLUSION: for every state of the hypothesis, ¦q_i¦ ≥ a_i(1 - e_i) ≥ d_⋆, and ¦q_j - q_i¦ ≥ d_pair for all i < j, by summing intervening gaps of the ordered radial intervals [a_i(1 - e_i), a_i(1 + e_i)] or by ordering the endpoints
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:L5#perihelion, lpM:L5#Km-compact
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | (12): ¦q_i¦ lies in its radial interval [a_i(1 - e_i), a_i(1 + e_i)]
EDGE: lpM:L5#perihelion | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | a_i(1 - e_i) ≥ d_⋆
EDGE: lpM:L5#Km-compact | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | every adjacent gap is at least d_pair
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: the star-distance and pair-distance bounds are proved here and restated at §1 L91; LP0 states them

NODE: lpM:L5#compact-physical
KIND: step
TITLE: energies <= -1/(2 a_max): a compact nonsingular physical set
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
CONTRACT_ID: lpM:L5#compact-physical
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m; K_m ≠ ∅
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited) (states)
SOURCE_CONCLUSION: every state of the hypothesis has energies E_i = -1/(2a_i) ≤ -1/(2a_max); closing the bounded inequalities (¦q_i¦ ≤ 2a_max, ¦q_i¦ ≥ d_⋆, ¦q_j - q_i¦ ≥ d_pair, ¦p_i¦ ≤ ν_i √(2/d_⋆), E_i ≤ -1/(2a_max)) gives a compact physical set with no zero denominator and no zero energy that contains all these states
CONSTANT_SCOPE: the compact set depends only on (n, ν, U, m)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5#bounds, lpM:L5#pair-distances, lpM:s1:model, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5#bounds | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | the position and momentum bounds
EDGE: lpM:L5#pair-distances | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | the star and pair distance bounds
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | the nonsingular physical region excludes q_i = 0 and q_i = q_j
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | E_i = -1/(2a_i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L5#projection
KIND: step
TITLE: H_i >= m by Lemma 3
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
CONTRACT_ID: lpM:L5#projection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited) (states)
SOURCE_CONCLUSION: every state of the hypothesis satisfies H_i ≥ m in its invariable frame
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#static, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | Lemma 3: C ≤ B_⋆(I) - m gives H_i ≥ m
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | C ≤ B(I) - m ≤ B_⋆(I) - m
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L6
KIND: lemma
TITLE: Lemma 6: the moving threshold (17) and continuation
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L179-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0: there exist one compact neighborhood U ⊂ Q of 𝓛, r_g > 0 and its modulus Ω_B, before r and the solution; then for every 0 < r ≤ r_g and every solution starting at I^0 ∈ 𝓛 with C_0 ≤ B(I^0) - δ, while its negative-energy actions stay within r of I^0 with that tube in U, and every time t
SOURCE_CONCLUSION: the closed 4r_g sup-norm tube about 𝓛 is contained in U; Ω_B(s) = sup{¦B(I) - B(J)¦ : I,J ∈ U, ‖I-J‖_∞ ≤ s} tends to zero as s ↓ 0 and Ω_B(4r_g) ≤ δ/16; the same U and Ω_B are used in Lemmas 8 and 14 when 𝓛 = 𝓛_δ; C(t) ≤ B(I(t)) - δ + nr + Ω_B(r) (17); if nr + Ω_B(r) ≤ δ/2, there is no finite-time termination while the action and ellipticity conditions hold, in either time direction
CONSTANT_SCOPE: U, r_g and Ω_B depend only on (n, ν, 𝓛, δ), before r and the solution; they are shared across the later applications with 𝓛 = 𝓛_δ
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#shared-U, lpM:L6#moving-threshold, lpM:L6#continuation, lpM:L6#backward, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/AMENDMENTS.md#N2@L11-L11 | one shared U contains the closed 4r_g tube, supplies the common modulus, and r ≤ r_g (MAIN L179-L189 supplies the construction and modulus claim)
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | (17)
EDGE: lpM:L6#continuation | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | no finite-time termination
EDGE: lpM:L6#backward | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the backward assertion
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L6@L179-L179 | 𝓛, U ⊂ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L181-L181 | B and Ω_B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2b
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.

NODE: lpM:L6#shared-U
KIND: step
TITLE: compact neighborhood U of the compact set inside the chamber; modulus Omega_B -> 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L179-L182
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#shared-U
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, there exist a compact neighborhood U ⊂ Q, r_g > 0 and Ω_B, chosen before any radius r or solution; Ω_B is defined for all s ≥ 0
SOURCE_CONCLUSION: choose one compact neighborhood U of 𝓛 inside Q; uniform continuity of B on U gives Ω_B(s) = sup{¦B(I)-B(J)¦ : I,J ∈ U, ‖I-J‖_∞ ≤ s} → 0 as s ↓ 0; choose r_g > 0 small enough that the closed 4r_g sup-norm tube about 𝓛 is in U and Ω_B(4r_g) ≤ δ/16; when 𝓛 = 𝓛_δ this U and its modulus are the same in (17), Lemma 8 and (39), with subsequent r ≤ r_g
CONSTANT_SCOPE: U, r_g and Ω_B depend only on (n, ν, 𝓛, δ), before r and the solution
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4, lpM:ext-heine-cantor, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4 | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | B is continuous on Q
EDGE: lpM:ext-heine-cantor | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | uniform continuity on the compact U
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | U lies in the open chamber Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the modulus of B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2b
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.

NODE: lpM:L6#moving-threshold
KIND: step
TITLE: (17) from the identity of (13) and B(I^0) <= B(I(t)) + Omega_B(r)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L183-L186
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#moving-threshold
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0; local notation: U, r_g, Ω_B are the witnesses constructed by lpM:L6#shared-U before r and the solution; 0 < r ≤ r_g; a solution in the negative-energy region on the connected interval under consideration, with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ and ‖I(t) - I^0‖_∞ ≤ r, with that tube in U
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, first choose the shared U, r_g > 0 and Ω_B; then for every 0 < r ≤ r_g and every solution as specified, and all times in the interval
SOURCE_CONCLUSION: C(t) = C_0 + Σ_i(I_i(t) - I_i^0) ≤ C_0 + nr and B(I^0) ≤ B(I(t)) + Ω_B(r), hence C(t) ≤ B(I(t)) - δ + nr + Ω_B(r) (17)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#dynamic, lpM:L6#shared-U, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the action identity of (13)
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | I^0 and I(t) lie in U within r, so the modulus applies
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2b
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.

NODE: lpM:L6#local-existence
KIND: step
TITLE: Lemma 5 compact set, bounded field and derivative, Picard contraction, uniqueness
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L187-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#local-existence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0; local notation: U, r_g, Ω_B are the witnesses constructed by lpM:L6#shared-U before r and the solution; 0 < r ≤ r_g; a solution in the negative-energy region on the connected interval under consideration, with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ and ‖I(t) - I^0‖_∞ ≤ r, with that tube in U; nr + Ω_B(r) ≤ δ/2 for the continuation assertion
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, first choose the shared U, r_g > 0 and Ω_B; then for every 0 < r ≤ r_g and every solution as specified, and all times in the interval
SOURCE_CONCLUSION: by (17), C ≤ B(I) - δ/2 along the solution, so Lemma 5 (with U and m = δ/2) supplies a compact nonsingular physical set with bounded momenta and energies separated from zero; the vector field of (1) and its derivative are bounded on a neighborhood of it; at every point of that set a local solution exists and is unique: on a small closed ball, z(t) = z_* + ∫_0^t X_H(z(u)) du is a contraction for times below the ball radius divided by the field bound and the inverse derivative bound (Picard iteration), and the same Lipschitz bound gives uniqueness by iterating the integral inequality
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5, lpM:L6#moving-threshold, lpM:s1:model, lpM:ext-picard, lpM:ext-gronwall, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | Lemma 5 supplies the compact nonsingular physical set (its premise C ≤ B(I) - δ/2 comes from (17))
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | (17) gives C ≤ B(I) - δ/2 along the solution
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the vector field X_H of (1)
EDGE: lpM:ext-picard | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | contraction mapping and Picard iteration
EDGE: lpM:ext-gronwall | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | uniqueness by iterating the integral inequality
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the direct application of Lemma 5 uses the moving bound C ≤ B(I) - δ/2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2b
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.

NODE: lpM:L6#continuation
KIND: step
TITLE: limit at a finite endpoint, local solution there and gluing; ellipticity is not lost
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L187-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#continuation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0; local notation: U, r_g, Ω_B are the witnesses constructed by lpM:L6#shared-U before r and the solution; 0 < r ≤ r_g; a solution in the negative-energy region on the connected interval under consideration, with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ and ‖I(t) - I^0‖_∞ ≤ r, with that tube in U; nr + Ω_B(r) ≤ δ/2 for the continuation assertion
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, first choose the shared U, r_g > 0 and Ω_B; then for every 0 < r ≤ r_g and every solution as specified, and all times in the interval
SOURCE_CONCLUSION: the field bound makes the trajectory Lipschitz in time, so at a finite endpoint it has a limit in the compact set; the local solution there glues to extend the solution; bounded actions keep the energies a fixed distance below zero, so ellipticity cannot be lost unnoticed; hence the solution cannot terminate at a finite time while the action and ellipticity conditions hold
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#local-existence, lpM:L5
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#local-existence | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | local existence and uniqueness at the limit point
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | use U and m = δ/2: (17) and nr + Ω_B(r) ≤ δ/2 supply C ≤ B(I) - m, as delivered by local-existence; the endpoint limit stays in that compact set
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2b
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.

NODE: lpM:L6#backward
KIND: step
TITLE: replacing the vector field by its negative gives the backward assertion
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L187-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#backward
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0; local notation: U, r_g, Ω_B are the witnesses constructed by lpM:L6#shared-U before r and the solution; 0 < r ≤ r_g; a solution in the negative-energy region on the connected interval under consideration, with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ and ‖I(t) - I^0‖_∞ ≤ r, with that tube in U
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, first choose the shared U, r_g > 0 and Ω_B; then for every 0 < r ≤ r_g and every solution as specified, and all times in the interval; t ≤ 0 for the reversed-time assertion
SOURCE_CONCLUSION: the moving-threshold estimate (17) holds backwards in time; if nr + Ω_B(r) ≤ δ/2, the solution also cannot terminate at a finite backward endpoint while the action and ellipticity conditions hold, by applying the continuation argument to the negated field
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#continuation, lpM:L6#moving-threshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#continuation | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the forward argument applied to the negated field
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | (17) holds for negative times as well
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2b
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.
