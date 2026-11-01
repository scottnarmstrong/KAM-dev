NODE: lpM:L5#planar_strongAMD_barrier
KIND: lemma
TITLE: LP0: the planar sharp strong barrier (planar case of Lemma 5)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L175
CONTRACT_ID: planetary.d59.planar_strongAMD_barrier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0 for every i; U ⊂ Q compact; m > 0; planar (d = 2)
SOURCE_QUANTIFIERS: for every n ≥ 2, ν > 0, compact U ⊂ Q and m > 0: there exist d_⋆ > 0 and d_pair > 0, then (a) for every I ∈ U and every e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m, and (b) there exists a compact set K of planar phases such that for every planar phase z with ¦q_i¦ > 0, E_i < 0, Λ(z) ∈ U and C(z) ≤ B(Λ(z)) - m
SOURCE_CONCLUSION: (a) a_i(I)(1 - e_i) ≥ d_⋆ for every i and a_{i+1}(I)(1 - e_{i+1}) - a_i(I)(1 + e_i) ≥ d_pair for every adjacent pair; (b) K is compact and every point of K is collision-free with all Kepler energies negative; every such z satisfies a_i(1 - e_i) ≥ d_⋆, a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair, ¦q_i¦ ≥ d_⋆ for every i, ¦q_i - q_j¦ ≥ d_pair for i ≠ j, z ∈ K, and ¦L_i¦ ≥ m with L_i L > 0 for every i (H_i ≥ m in the invariable frame)
CONSTANT_SCOPE: d_⋆, d_pair and K depend only on (n, ν, U, m) and are chosen before I, e and z (N11 order: d_⋆ is fixed before the momentum bound)
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planar_strongAMD_barrier
FROZEN_ANCHOR_ID: planetary.d59.planar_strongAMD_barrier.v1
FROZEN_ABI_SHA256: 4816775b095a255429f67a3b8521c9cb64a8bd3fecdd99496d070ee7352497f7
DEPS: lpM:L5, lpM:L5#pair-distances, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#actionAxis, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceStrongAMD, lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerEnergy, lpM:s1:model#bodyVector, lpM:s1:data#planeLength, lpM:s1:elements#planeCross, lpM:s1:elements#totalMomentum, lpM:s1:model#NoCollision, lpM:s1:model#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L5@L166-L175 | LP0 is the planar case d = 2 of Lemma 5; its proof is that of Lemma 5
EDGE: lpM:L5#pair-distances | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | the star and pair distance bounds ¦q_i¦ ≥ d_⋆, ¦q_j - q_i¦ ≥ d_pair are proved in the proof of Lemma 5 (also restated at §1 L91)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | U ⊂ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | B(I) occurs
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the deficit Σ I_i D(e_i) occurs
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the element-list clause uses a_i(I)
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the adjacent pairs (i, i+1) index the gaps
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the gap of the pair (i, i+1) uses the index i + 1
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the statement quantifies over source canonical phases
EDGE: lpM:s1:elements#sourceStrongAMD | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | C occurs on source canonical phases
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the perihelia and gaps use a_i
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the perihelia and gaps use e_i = ¦e_i¦
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the actions Λ(z) ∈ U occur
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | negative-energy states
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the position q_i occurs in the statement
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | Euclidean lengths ¦·¦ occur in the statement
EDGE: lpM:s1:elements#planeCross | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | H_i ≥ m is stated through L_i = q_i × p_i
EDGE: lpM:s1:elements#totalMomentum | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the invariable frame is that of L
EDGE: lpM:s1:model#NoCollision | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the compact set lies in the nonsingular physical region
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | states are planar phases
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-athm
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planar_strongAMD_barrier (KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDBarrier.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_barrier
NOTE: Anchor LP0. Planar instance (d = 2) of the d-generic MAIN Lemma 5 (node lpM:L5), bound as its own anchor node so that the spatial consumers of Lemma 5 do not depend on a planar declaration (SPEC §1). The distance clauses are proved at L175 and restated at §1 L91. Q3: Lemma 5 consumes only the static part of Lemma 3. AMENDED: N11 (AMENDMENTS.md L20).

NODE: lpM:L4#orderedPairThreshold_isLeast
KIND: lemma
TITLE: B_ij(I) is the attained minimum of the pair objective over the feasible set
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L47-L55
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
CONTRACT_ID: planetary.d59.orderedPairThreshold_isLeast
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I ∈ Q (OrderedActions ν); i < j
SOURCE_QUANTIFIERS: for every n, ν, I ∈ Q and i < j
SOURCE_CONCLUSION: B_ij(I) is the least element of {I_i D(u) + I_j D(v) : (u,v) feasible}: an attained minimum
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdIsLeast.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast
FROZEN_ANCHOR_ID: planetary.d59.orderedPairThreshold_isLeast.v1
FROZEN_ABI_SHA256: 8a4a9ca0b3a8ed72192667f31315ee47a6a945981fb6759f349269d14a9eef70
DEPS: lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#actionAxis, lpM:s1:thresholds#eccDeficit, lpM:ext-compact-min
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the statement is on the chamber carrier I ∈ Q
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | B_ij occurs
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the feasible set occurs
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the objective occurs
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the feasible competitor uses alpha = a_i(I)/a_j(I); on OrderedActions with i < j, 0 <= alpha < 1
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the objective I_i D(u) + I_j D(v) is continuous on [0,1]^2
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | directly apply extreme value to the closed nonempty feasible subset of [0,1]^2 and its continuous objective; the witness (0, 1 - alpha) is valid also for alpha = 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-athm
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.orderedPairThreshold_isLeast (KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdIsLeast.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_isLeast
NOTE: Carrier-level use of MAIN L149 only: no positive-mass premise is added. The original supplier lpM:L4#feasible-compact is recorded for positive masses with alpha in (0,1), so it is not applied here. L149 itself needs only the carrier consequences I_i > 0 and 0 <= a_i(I) < a_j(I), giving 0 <= alpha < 1; its closedness, feasible competitor and continuous-objective argument apply on this carrier. No contact parameterization (15), positivity of B_ij, or L151 division by alpha is used. The unique value is not a unique optimizer.

NODE: lpM:L4#orderedPairThreshold_existsUnique_value
KIND: lemma
TITLE: the pair minimum value is the unique least value
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L47-L55
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
CONTRACT_ID: planetary.d59.orderedPairThreshold_existsUnique_value
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I ∈ Q (OrderedActions ν); i < j
SOURCE_QUANTIFIERS: for every n, ν, I ∈ Q and i < j; there exists a unique b
SOURCE_CONCLUSION: there is exactly one b that is the least element of {I_i D(u) + I_j D(v) : (u,v) feasible}
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdExistsUniqueValue.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value
FROZEN_ANCHOR_ID: planetary.d59.orderedPairThreshold_existsUnique_value.v1
FROZEN_ABI_SHA256: c6d8eb9bce1d8bad0dda3f050fbd47464f6ca6045e4aecd1555d8a56614e7cb0
DEPS: lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#actionAxis, lpM:s1:thresholds#eccDeficit, lpM:ext-compact-min
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the statement is on the chamber carrier I ∈ Q
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the feasible set occurs
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the objective occurs
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the feasible competitor uses alpha = a_i(I)/a_j(I); on OrderedActions with i < j, 0 <= alpha < 1
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the objective I_i D(u) + I_j D(v) is continuous on [0,1]^2
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | directly apply extreme value to the closed nonempty feasible subset of [0,1]^2 and its continuous objective; the witness (0, 1 - alpha) is valid also for alpha = 0; uniqueness of the least value is elementary order reasoning
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-athm
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value (KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedPairThresholdExistsUniqueValue.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.orderedPairThreshold_existsUnique_value
NOTE: Carrier-level use of MAIN L149 only: no positive-mass premise is added. The original supplier lpM:L4#feasible-compact is recorded for positive masses with alpha in (0,1), so it is not applied here. L149 itself needs only the carrier consequences I_i > 0 and 0 <= a_i(I) < a_j(I), giving 0 <= alpha < 1; its closedness, feasible competitor and continuous-objective argument apply on this carrier. No contact parameterization (15), positivity of B_ij, or L151 division by alpha is used. The unique value is not a unique optimizer.

NODE: lpM:L4#orderedCrossThreshold_isLeast
KIND: lemma
TITLE: B_cross(I) is the attained minimum of the adjacent pair thresholds
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L52-L55
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
CONTRACT_ID: planetary.d59.orderedCrossThreshold_isLeast
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; I ∈ Q (OrderedActions ν)
SOURCE_QUANTIFIERS: for every n ≥ 2, ν and I ∈ Q
SOURCE_CONCLUSION: B_cross(I) is the least element of {B_{i,i+1}(I) : i + 1 < n}
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedCrossThresholdIsLeast.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast
FROZEN_ANCHOR_ID: planetary.d59.orderedCrossThreshold_isLeast.v1
FROZEN_ABI_SHA256: 960caadb1ee1979d1eb596770b57f164b0868885d328250141f799c83ecd0a4f
DEPS: lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedPairThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the statement is on the chamber carrier I ∈ Q
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | B_cross occurs
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the pair thresholds B_{i,i+1} occur
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-athm
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.orderedCrossThreshold_isLeast (KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedCrossThresholdIsLeast.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.orderedCrossThreshold_isLeast
NOTE: MAIN L55 asserts attainment; L4 L156 says 'Finite minima preserve continuity and positivity'. The local binder n >= 2 supplies nonemptiness of the finite adjacent family at this consumer (MAIN L52, L156); it does not import the full lpM:s1:data package, including positive normalized masses, delta, gamma, tau and A. No pair-minimum attainment or positivity premise is needed to take the minimum of the finite nonempty family of real pair-threshold values.

NODE: lpM:L4#orderedStrongThreshold_isLeast
KIND: lemma
TITLE: B(I) is the attained minimum of the adjacent thresholds and the actions
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L52-L55
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
CONTRACT_ID: planetary.d59.orderedStrongThreshold_isLeast
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; I ∈ Q (OrderedActions ν)
SOURCE_QUANTIFIERS: for every n ≥ 2, ν and I ∈ Q
SOURCE_CONCLUSION: B(I) = min(B_cross(I), min_i I_i) is the least element of {B_{i,i+1}(I) : i + 1 < n} ∪ {I_i}
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedStrongThresholdIsLeast.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast
FROZEN_ANCHOR_ID: planetary.d59.orderedStrongThreshold_isLeast.v1
FROZEN_ABI_SHA256: 1dd51f606407a4de87aca3abfe2c61e14660ecc796ed2289ff3ec904e07eff41
DEPS: lpM:L4#orderedCrossThreshold_isLeast, lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#orderedCrossThreshold_isLeast | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_cross(I) is attained among the adjacent thresholds
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the statement is on the chamber carrier I ∈ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | B occurs
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the pair thresholds B_{i,i+1} occur
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L53 | B = min(B_cross, min_i I_i) uses B_cross directly; combine its attained minimum with the finite nonempty action family
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-athm
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.orderedStrongThreshold_isLeast (KAM/Frozen/Planetary/StrongAMD/Theorems/OrderedStrongThresholdIsLeast.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.orderedStrongThreshold_isLeast
NOTE: -

NODE: lpM:L3#sourceStrongAMD_nonneg
KIND: lemma
TITLE: C >= 0 on source canonical phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L132
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: planetary.d59.sourceStrongAMD_nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν and source canonical phase z
SOURCE_CONCLUSION: 0 ≤ C(z)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceStrongAMDNonneg.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg
FROZEN_ANCHOR_ID: planetary.d59.sourceStrongAMD_nonneg.v1
FROZEN_ABI_SHA256: d9af681d12072e83d8f9f986a13815ef93e6397132728dc72f32e916ef3df3ad
DEPS: lpM:L3#amd-nonneg, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#amd-nonneg | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | ¦L¦ ≤ Σ¦L_i¦ ≤ Σ I_i, so C ≥ 0
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L3@L132-L132 | the statement quantifies over source canonical phases
EDGE: lpM:s1:elements#sourceStrongAMD | docs/tracks/LP/source/MAIN.md#L3@L132-L132 | C occurs
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-athm
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceStrongAMD_nonneg (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceStrongAMDNonneg.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceStrongAMD_nonneg
NOTE: -

NODE: lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD
KIND: lemma
TITLE: the deficit bound sum Lambda_i D(e_i) <= C on source canonical phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L135
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: planetary.d59.sum_action_mul_eccDeficit_le_sourceStrongAMD
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν and source canonical phase z
SOURCE_CONCLUSION: Σ_i Λ_i D(e_i) ≤ C(z), with e_i = ¦e_i¦
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SumActionMulEccDeficitLeSourceStrongAMD.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD
FROZEN_ANCHOR_ID: planetary.d59.sum_action_mul_eccDeficit_le_sourceStrongAMD.v1
FROZEN_ABI_SHA256: 62bf6dccb8d42f5cf06341752baa424e5e0b7fd00ee59a66ef4d867e34577b38
DEPS: lpM:L3#deficit, lpM:L3#deficit-zero-L, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceStrongAMD, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerEccVector, lpM:s1:data#planeLength, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#deficit | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | for L ≠ 0: H_i ≤ I_i √(1 - e_i^2) and C = Σ(I_i - H_i) give the inequality of (13)
EDGE: lpM:L3#deficit-zero-L | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the case L = 0, which the frozen statement includes
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L3@L134-L134 | the statement quantifies over source canonical phases
EDGE: lpM:s1:elements#sourceStrongAMD | docs/tracks/LP/source/MAIN.md#L3@L134-L134 | C occurs
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/source/MAIN.md#L3@L134-L134 | Λ_i = I_i occurs
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#L3@L134-L134 | e_i = ¦e_i¦ occurs
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L3@L134-L134 | Euclidean lengths ¦·¦ occur in the statement
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L3@L134-L134 | D occurs
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-athm
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD (KAM/Frozen/Planetary/StrongAMD/Theorems/SumActionMulEccDeficitLeSourceStrongAMD.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sum_action_mul_eccDeficit_le_sourceStrongAMD
NOTE: MAIN states the inequality of (13) on orbits with C < B_⋆; the frozen characterization states it on every source canonical phase, so it also depends on the gap step lpM:L3#deficit-zero-L

NODE: lpM:L2#sourceKepler_axis_pos
KIND: lemma
TITLE: a_i > 0 on source canonical phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
CONTRACT_ID: planetary.d59.sourceKepler_axis_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, source canonical phase z and i
SOURCE_CONCLUSION: 0 < a_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerAxisPos.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceKepler_axis_pos
FROZEN_ANCHOR_ID: planetary.d59.sourceKepler_axis_pos.v1
FROZEN_ABI_SHA256: 7731886247386b82082b66054cd1af471037b5eb5a3aa17365e4d098032b4174
DEPS: lpM:s1:elements, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#keplerAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | when E_i < 0, a_i = -1/(2E_i) > 0 by (2)
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement quantifies over source canonical phases
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | a_i occurs
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-athm
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceKepler_axis_pos (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerAxisPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceKepler_axis_pos
NOTE: -

NODE: lpM:L2#sourceKepler_ecc_le_one
KIND: lemma
TITLE: e_i <= 1 on source canonical phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: planetary.d59.sourceKepler_ecc_le_one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, source canonical phase z and i
SOURCE_CONCLUSION: e_i = ¦e_i¦ ≤ 1
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerEccLeOne.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceKepler_ecc_le_one
FROZEN_ANCHOR_ID: planetary.d59.sourceKepler_ecc_le_one.v1
FROZEN_ABI_SHA256: 2ede1e6266422e98b0ba3d414f6b7e2417c45d2f436166e975ee776e48fe8b3f
DEPS: lpM:L2, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#keplerEccVector, lpM:s1:data#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | (11) gives e^2 = 1 - ¦q × v¦^2/a ≤ 1
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L114-L114 | the statement quantifies over source canonical phases
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#L2@L114-L114 | the eccentricity vector occurs
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L2@L114-L114 | Euclidean lengths ¦·¦ occur in the statement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-athm
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceKepler_ecc_le_one (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerEccLeOne.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceKepler_ecc_le_one
NOTE: -

NODE: lpM:L2#sourceKeplerPeri_le_planeLength
KIND: lemma
TITLE: a_i(1 - e_i) <= ¦q_i¦ on source canonical phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L122
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: planetary.d59.sourceKeplerPeri_le_planeLength
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, source canonical phase z and i
SOURCE_CONCLUSION: a_i(1 - e_i) ≤ ¦q_i¦
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerPeriLePlaneLength.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength
FROZEN_ANCHOR_ID: planetary.d59.sourceKeplerPeri_le_planeLength.v1
FROZEN_ABI_SHA256: 79bcc85c4a9986ce41a1c5048ae42d81d204f3a14dbb942750f5e224be142111
DEPS: lpM:L2, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceKeplerPeri, lpM:s1:data#planeLength, lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L128-L128 | (12): a(1 - e) ≤ ¦q¦
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L119-L119 | the statement quantifies over source canonical phases
EDGE: lpM:s1:elements#sourceKeplerPeri | docs/tracks/LP/source/MAIN.md#L2@L119-L119 | the canonical perihelion occurs
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L2@L119-L119 | Euclidean lengths ¦·¦ occur in the statement
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L2@L119-L119 | the position q_i occurs in the statement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-athm
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceKeplerPeriLePlaneLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceKeplerPeri_le_planeLength
NOTE: -

NODE: lpM:L2#planeLength_le_sourceKeplerApo
KIND: lemma
TITLE: ¦q_i¦ <= a_i(1 + e_i) on source canonical phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L122
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: planetary.d59.planeLength_le_sourceKeplerApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, source canonical phase z and i
SOURCE_CONCLUSION: ¦q_i¦ ≤ a_i(1 + e_i)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceKeplerApo.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planeLength_le_sourceKeplerApo
FROZEN_ANCHOR_ID: planetary.d59.planeLength_le_sourceKeplerApo.v1
FROZEN_ABI_SHA256: bc651b06061a57764696ecf57cb3e675ed1c4b578f682984948d8cee15d4d6ae
DEPS: lpM:L2, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceKeplerApo, lpM:s1:data#planeLength, lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L128-L128 | (12): ¦q¦ ≤ a(1 + e)
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L119-L119 | the statement quantifies over source canonical phases
EDGE: lpM:s1:elements#sourceKeplerApo | docs/tracks/LP/source/MAIN.md#L2@L119-L119 | the canonical aphelion occurs
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L2@L119-L119 | Euclidean lengths ¦·¦ occur in the statement
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L2@L119-L119 | the position q_i occurs in the statement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-athm
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planeLength_le_sourceKeplerApo (KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceKeplerApo.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceKeplerApo
NOTE: -
