# Proof dependency database - track LP

GRAPH_VERSION: 4
ROOTS: lpM:L4#orderedPairThreshold_isLeast, lpM:L4#orderedPairThreshold_existsUnique_value, lpM:L4#orderedCrossThreshold_isLeast, lpM:L4#orderedStrongThreshold_isLeast, lpM:L3#sourceStrongAMD_nonneg, lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD, lpM:L2#sourceKepler_axis_pos, lpM:L2#sourceKepler_ecc_le_one, lpM:L2#sourceKeplerPeri_le_planeLength, lpM:L2#planeLength_le_sourceKeplerApo, lpM:L16#sourceOscAxis_pos, lpM:L16#sourceOscPeri_pos, lpM:L16#sourceOscPeri_le_planeLength, lpM:L16#planeLength_le_sourceOscApo, lpM:L2#spatialSourceKeplerAxis_pos, lpM:L2#spatialSourceKeplerAction_pos, lpM:L2#spatialSourceKeplerAction_sq, lpM:L2#spatialSourceKeplerEcc_sq, lpM:L2#spatialSourceKeplerEcc_nonneg, lpM:L2#spatialSourceKeplerEcc_le_one, lpM:L2#spatialSourcePlanetAngularMomentum_length, lpM:L2#spatialSourcePlanetAngularMomentum_length_le, lpM:L2#spatialSourceKeplerPeri_le_length, lpM:L2#spatialSourceKeplerApo_ge_length, lpM:L3#spatialSourceStrongAMD_nonneg, lpM:L3#spatialSourceAction_mul_eccDeficit_le, lpM:L16#spatialSourceOscParam_pos, lpM:L16#spatialSourceOscEnergy_neg, lpM:L16#spatialSourceOscEcc_lt_one, lpM:L16#spatialSourceOscEcc_nonneg, lpM:L16#spatialSourceOscAxis_pos, lpM:L16#spatialSourceOscPeri_pos, lpM:L16#spatialSourceOscPeri_le_length, lpM:L16#spatialSourceOscApo_ge_length, lpM:L5#planar_strongAMD_barrier, lpM:T15#planar_strongAMD_exponentialSafety, lpM:T15#planar_strongAMD_exponentialSafety_halfInteger, lpM:T19#spatial_strongAMD_exponentialSafety, lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger, lpM:T15#planar_strongAMD_exponentialSafety_noArith, lpM:T19#spatial_strongAMD_exponentialSafety_noArith
CORPUS: docs/tracks/LP/source/{MAIN,AMENDMENTS}.md pinned by SHA-256 in docs/graph/LP/CORPUS.sha256 (MAIN 68e9167f...48c1b, 679 lines; AMENDMENTS c887d1e2...51881, 26 lines; N1 fixed in place, N2-N12 override the MAIN lines they cite); wave 4: docs/tracks/LP/lp3/LP3-PLAN.md (1b58b704...ba06ba, 506 lines), the LP3 source under D65 (no separate LP3 source note); branch inp-lp-graph off inp after the D62 freeze (main f46b94fb); waves 1-4; streamlined review (D65): one global review, no per-slice reviews; LEAN_STATUS set mechanically from LEAN_REFs that resolve on main
CONVENTIONS: docs/graph/LP/SPEC.md §4: Euclidean ¦·¦ (planeLength, spaceLength) vs max norm on actions; period 2π angles (L13 converts to period one); G = 1, star mass 1, masses μν_i, max ν = 1, physical AMD μC; C = ΣI - ¦L¦ orientation-free (N8, OD-1); thresholds on the chamber carrier OrderedActions (n ≥ 2) with attained-minimum characterizations; C(0) ≤ B(I^0) - δ, conclusion C(t) ≤ B(I(t)) - δ/2; frozen keplerEnergy is ν_i E_i; MAIN lemmas are d-generic (d ∈ {2,3}) and dimension-specific frozen carriers attach at the anchors (SPEC §5 dimension rule); constants depend only on (d, n, ν, 𝒜, δ, γ, τ), L5's d_⋆, d_pair only on (n, ν, U, m), chosen before μ and the state
STANDING_ASSUMPTIONS: -
EXTERNAL_POLICY: a closed list of Mathlib-level externals lpM:ext-* fixed in SPEC §3 (KIND external, LEAN_STATUS EXTERNAL, located at the first appeal in MAIN); cross-track results that a proof uses are IMPORTED nodes N:<node> / P:<node> (KIND external, source fields copied from that track's graph, NOTE IMPORTED), never read through implementation files; any other unproved fact is a step node with NOTE SOURCE_GAP
FROZEN_ANCHORS: lpM:s1:thresholds#actionAxis, lpM:s1:chamber#chamber, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#pairThreshold, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:elements#strongAMD, lpM:s1:elements#keplerPeri, lpM:s1:elements#keplerApo, lpM:L16:defs#oscVelocity, lpM:L16:defs#oscParam, lpM:L16:defs#oscEnergy, lpM:L16:defs#oscAxis, lpM:L16:defs#oscEccVector, lpM:L16:defs#oscEcc, lpM:L16:defs#oscPeri, lpM:L16:defs#oscApo, lpM:s1:elements#SourceCanonicalPhase, lpM:L16:defs#SourceOsculatingPhase, lpM:s1:elements#sourceStrongAMD, lpM:s1:elements#sourceKeplerPeri, lpM:s1:elements#sourceKeplerApo, lpM:L16:defs#sourceOscEnergy, lpM:L16:defs#sourceOscAxis, lpM:L16:defs#sourceOscEccVector, lpM:L16:defs#sourceOscEcc, lpM:L16:defs#sourceOscPeri, lpM:L16:defs#sourceOscApo, lpM:s1:data#spaceDot, lpM:s1:data#spaceSq, lpM:s1:data#spaceLength, lpM:s1:elements#spaceCross, lpM:s1:model#bodyVector3, lpM:s1:elements#planetAngularMomentum3, lpM:s1:elements#angularMomentum3, lpM:s1:model#spatialHamiltonian, lpM:s1:model#SpatialNoCollision, lpM:s1:model#IsSpatialMovingSolutionOn, lpM:s1:model#SpatialMovingUniqueOn, lpM:L1#spatialBarycentricPositions, lpM:L1#spatialBarycentricVelocities, lpM:s1:model#spatialMasses, lpM:L1#IsSpatialNewtonSolutionOn, lpM:s1:elements#spatialKeplerEnergy, lpM:s1:elements#spatialKeplerAxis, lpM:s1:elements#spatialKeplerAction, lpM:s1:elements#spatialKeplerEccVector, lpM:s1:elements#SpatialNegativeEnergy, lpM:s1:elements#SpatialElliptic, lpM:s1:elements#spatialKeplerPeri, lpM:s1:elements#spatialKeplerApo, lpM:L16:defs#spatialOscVelocity, lpM:L16:defs#spatialOscParam, lpM:L16:defs#spatialOscEnergy, lpM:L16:defs#spatialOscAxis, lpM:L16:defs#spatialOscEccVector, lpM:L16:defs#spatialOscEcc, lpM:L16:defs#spatialOscPeri, lpM:L16:defs#spatialOscApo, lpM:L16:defs#SpatialOscPhase, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:L16:defs#SpatialSourceOsculatingPhase, lpM:s1:elements#spatialSourceKeplerAxis, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerEccVector, lpM:s1:elements#spatialSourceKeplerEcc, lpM:s1:elements#spatialSourcePlanetAngularMomentum, lpM:s1:elements#spatialSourceAngularMomentum, lpM:s1:elements#spatialSourceStrongAMD, lpM:s1:elements#spatialSourceKeplerPeri, lpM:s1:elements#spatialSourceKeplerApo, lpM:L16:defs#spatialSourceOscParam, lpM:L16:defs#spatialSourceOscEnergy, lpM:L16:defs#spatialSourceOscAxis, lpM:L16:defs#spatialSourceOscEccVector, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#spatialSourceOscApo, lpM:L1#spatialSourceBarycentricPositions, lpM:L1#spatialSourceBarycentricVelocities, lpM:L4#orderedPairThreshold_isLeast, lpM:L4#orderedPairThreshold_existsUnique_value, lpM:L4#orderedCrossThreshold_isLeast, lpM:L4#orderedStrongThreshold_isLeast, lpM:L3#sourceStrongAMD_nonneg, lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD, lpM:L2#sourceKepler_axis_pos, lpM:L2#sourceKepler_ecc_le_one, lpM:L2#sourceKeplerPeri_le_planeLength, lpM:L2#planeLength_le_sourceKeplerApo, lpM:L16#sourceOscAxis_pos, lpM:L16#sourceOscPeri_pos, lpM:L16#sourceOscPeri_le_planeLength, lpM:L16#planeLength_le_sourceOscApo, lpM:L2#spatialSourceKeplerAxis_pos, lpM:L2#spatialSourceKeplerAction_pos, lpM:L2#spatialSourceKeplerAction_sq, lpM:L2#spatialSourceKeplerEcc_sq, lpM:L2#spatialSourceKeplerEcc_nonneg, lpM:L2#spatialSourceKeplerEcc_le_one, lpM:L2#spatialSourcePlanetAngularMomentum_length, lpM:L2#spatialSourcePlanetAngularMomentum_length_le, lpM:L2#spatialSourceKeplerPeri_le_length, lpM:L2#spatialSourceKeplerApo_ge_length, lpM:L3#spatialSourceStrongAMD_nonneg, lpM:L3#spatialSourceAction_mul_eccDeficit_le, lpM:L16#spatialSourceOscParam_pos, lpM:L16#spatialSourceOscEnergy_neg, lpM:L16#spatialSourceOscEcc_lt_one, lpM:L16#spatialSourceOscEcc_nonneg, lpM:L16#spatialSourceOscAxis_pos, lpM:L16#spatialSourceOscPeri_pos, lpM:L16#spatialSourceOscPeri_le_length, lpM:L16#spatialSourceOscApo_ge_length, lpM:L5#planar_strongAMD_barrier, lpM:T15#planar_strongAMD_exponentialSafety, lpM:T15#planar_strongAMD_exponentialSafety_halfInteger, lpM:T19#spatial_strongAMD_exponentialSafety, lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger, lpM:s1:model#IsHamiltonianSolutionOn, lpM:s1:dioph#IsDiophantine, lpM:s1:model#NoCollision, lpM:s1:model#Phase, lpM:s1:model#actualMasses, lpM:L1#barycentricPositions, lpM:L1#barycentricVelocities, lpM:s1:model#bodyVector, lpM:s1:model#IsMovingSolutionOn, lpM:L1#IsNewtonSolutionOn, lpM:s1:model#MovingUniqueOn, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:elements#keplerEnergy, lpM:s1:elements#planeCross, lpM:s1:elements#totalMomentum, lpM:s1:data#planeDot, lpM:s1:data#planeLength, lpM:s1:data#planeSq, lpM:T15#planar_strongAMD_exponentialSafety_noArith, lpM:T19#spatial_strongAMD_exponentialSafety_noArith, lp3:s1.1#planetaryTimeExponent, lp3:s1.1#planetaryDriftExponent
FROZEN_MANIFEST: manifest/frozen-anchors.json | sha256:e518662231ee06f71209863433e49b20b957c4ba2a9dcc7120c4824095a48375
WRITER: kam-lp
GLOBAL_REVIEWER: -
GLOBAL_REVIEW_REF: -

The dependency direction is `NODE -> prerequisite`. Node blocks are assembled from `docs/graph/LP/packets/<slice>.nodes.md`; edit those, then re-run `inp_depgraph_assemble.py` (orchestrator-tools).

## Nodes

NODE: lpM:s1:thresholds#actionAxis
KIND: definition
TITLE: action axis a_i(I) = (I_i/nu_i)^2
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L45-L45
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.actionAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν, I : Fin n → ℝ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, I, i
SOURCE_CONCLUSION: a_i(I) = (I_i/ν_i)^2 (MAIN §1 L45), a total formula; MAIN uses it for I in the chamber Q
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/ActionAxis.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.actionAxis
FROZEN_ANCHOR_ID: planetary.d59.actionAxis.v1
FROZEN_ABI_SHA256: d5ad8dc786c2a14554e8b89eccde6e39a603a7940c907e614204e6c5dc95a4dd
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.actionAxis (KAM/Frozen/Planetary/StrongAMD/Defs/ActionAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:chamber#chamber
KIND: definition
TITLE: the action chamber Q
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L41-L44
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.chamber
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, ν
SOURCE_CONCLUSION: Q = {I : I_i > 0 for every i, and (I_1/ν_1)^2 < ... < (I_n/ν_n)^2}, written as a_i(I) < a_j(I) for i < j
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/Chamber.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.chamber
FROZEN_ANCHOR_ID: planetary.d59.chamber.v1
FROZEN_ABI_SHA256: 9cc5ec65df5dfe2ee99959839aaf121fe0f58cc2d4b429a8925f1829a1e2eaab
DEPS: lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#s1@L43-L43 | the ordering (I_i/ν_i)^2 is a_i(I)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.chamber (KAM/Frozen/Planetary/StrongAMD/Defs/Chamber.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:thresholds#eccDeficit
KIND: definition
TITLE: eccentricity deficit D(u) = 1 - sqrt(1 - u^2)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L45-L45
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.eccDeficit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u : ℝ (typing data)
SOURCE_QUANTIFIERS: for every u
SOURCE_CONCLUSION: D(u) = 1 - √(1 - u^2) (MAIN §1 L45), used on u ∈ [0,1]
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/EccDeficit.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.eccDeficit
FROZEN_ANCHOR_ID: planetary.d59.eccDeficit.v1
FROZEN_ABI_SHA256: 8e801ff76c90860eaf3a26128931dd910e823ec8f547c6113357245ceb6f6803
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.eccDeficit (KAM/Frozen/Planetary/StrongAMD/Defs/EccDeficit.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:thresholds#pairFeasible
KIND: definition
TITLE: pair feasible set {(u,v) in [0,1]^2 : a_i(1+u) >= a_j(1-v)}
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L47-L48
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.pairFeasible
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν, I : Fin n → ℝ; i, j : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, I, i, j
SOURCE_CONCLUSION: the feasible set {(u,v) : 0 ≤ u, v ≤ 1, a_i(I)(1+u) ≥ a_j(I)(1-v)} of the minimum B_ij in (3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/PairFeasible.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.pairFeasible
FROZEN_ANCHOR_ID: planetary.d59.pairFeasible.v1
FROZEN_ABI_SHA256: 6d14a6a1abecfcb4a34314f3f30bf0c70cf69b47d42ec1c16db1a849b6e46c13
DEPS: lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#s1@L48-L48 | the constraint is written with a_i(I), a_j(I)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.pairFeasible (KAM/Frozen/Planetary/StrongAMD/Defs/PairFeasible.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:thresholds#pairObjective
KIND: definition
TITLE: pair objective I_i D(u) + I_j D(v)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L49-L49
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.pairObjective
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; I : Fin n → ℝ; i, j : Fin n; (u,v) : ℝ × ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, I, i, j, (u,v)
SOURCE_CONCLUSION: the objective I_i D(u) + I_j D(v) of the minimum B_ij in (3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/PairObjective.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.pairObjective
FROZEN_ANCHOR_ID: planetary.d59.pairObjective.v1
FROZEN_ABI_SHA256: 024b20f3a47742f053ef4842fe6ec5003382d90645687d560e2fef18668f9852
DEPS: lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#s1@L49-L49 | the objective is built from D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.pairObjective (KAM/Frozen/Planetary/StrongAMD/Defs/PairObjective.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:thresholds#pairThreshold
KIND: definition
TITLE: pair threshold helper: sInf of the objective over the feasible set
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L47-L50
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.pairThreshold
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν, I : Fin n → ℝ; i, j : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, I, i, j
SOURCE_CONCLUSION: internal helper: the literal infimum of I_i D(u) + I_j D(v) over the feasible set (total in I); its source meaning is B_ij(I) of (3) only on its carrier I ∈ Q, i < j, where Lemma 4 shows the infimum is attained
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/PairThreshold.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.pairThreshold
FROZEN_ANCHOR_ID: planetary.d59.pairThreshold.v1
FROZEN_ABI_SHA256: 293566de81d28fcd969f94618cf2952a3c801b57dfe816185f24d4683c5ca9ab
DEPS: lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#s1@L47-L48 | the infimum runs over the feasible set
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#s1@L49-L49 | the infimum is of the pair objective
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.pairThreshold (KAM/Frozen/Planetary/StrongAMD/Defs/PairThreshold.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: internal helper (FREEZE-PROPOSAL draft 7 role 'internal'); source meaning only on its carrier

NODE: lpM:s1:thresholds#AdjIdx
KIND: definition
TITLE: index type of adjacent pairs (i, i+1)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L52-L52
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.AdjIdx
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ (typing data)
SOURCE_QUANTIFIERS: for every n
SOURCE_CONCLUSION: the indices i with i + 1 < n, indexing the adjacent pairs (i, i+1) of B_cross = min_{i<n} B_{i,i+1}
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdx.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.AdjIdx
FROZEN_ANCHOR_ID: planetary.d59.AdjIdx.v1
FROZEN_ABI_SHA256: b5f634e0a44da0960607f622f84d116b7dd00f4f67d0b6a33981693330d37301
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.AdjIdx (KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdx.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: internal helper (typing of the adjacent-pair family); source meaning only through B_cross

NODE: lpM:s1:thresholds#AdjIdx.upperIdx
KIND: definition
TITLE: upper index i+1 of an adjacent pair
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L52-L52
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.AdjIdx.upperIdx
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a : AdjIdx n (typing data)
SOURCE_QUANTIFIERS: for every n and adjacent index a
SOURCE_CONCLUSION: the upper index i + 1 of the adjacent pair (i, i+1)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdxUpperIdx.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.AdjIdx.upperIdx
FROZEN_ANCHOR_ID: planetary.d59.AdjIdx.upperIdx.v1
FROZEN_ABI_SHA256: d0e461d2d5c54b8bff9e3430b24cc47d88ccc2b58a3900301eca01219b00e531
DEPS: lpM:s1:thresholds#AdjIdx
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | defined on the adjacent index type
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.AdjIdx.upperIdx (KAM/Frozen/Planetary/StrongAMD/Defs/AdjIdxUpperIdx.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: internal helper; source meaning only through B_cross and the gaps of (9)

NODE: lpM:s1:chamber#OrderedActions
KIND: definition
TITLE: the carrier of action vectors in the chamber Q
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L41-L44
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.OrderedActions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, ν
SOURCE_CONCLUSION: the subtype of action vectors I ∈ Q, the carrier on which the thresholds (3) are defined (MAIN L55: 'on their indicated carriers, without arbitrary values outside the action chamber')
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OrderedActions.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.OrderedActions
FROZEN_ANCHOR_ID: planetary.d59.OrderedActions.v1
FROZEN_ABI_SHA256: 562bb6e2ed2dba05140b630c2dc06f46b4b857fff09c6d433396b40577b47162
DEPS: lpM:s1:chamber#chamber
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L41-L41 | the carrier is the chamber Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.OrderedActions (KAM/Frozen/Planetary/StrongAMD/Defs/OrderedActions.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:thresholds#orderedPairThreshold
KIND: definition
TITLE: pair threshold B_ij(I) on the chamber carrier
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L47-L50
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.orderedPairThreshold
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; I ∈ Q (OrderedActions); i, j : Fin n with i < j (the ordering proof is typing data)
SOURCE_QUANTIFIERS: for every n, ν, I ∈ Q, i < j
SOURCE_CONCLUSION: B_ij(I) = min over the feasible set of I_i D(u) + I_j D(v), (3), on the carrier I ∈ Q, i < j (the helper value)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OrderedPairThreshold.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.orderedPairThreshold
FROZEN_ANCHOR_ID: planetary.d59.orderedPairThreshold.v1
FROZEN_ABI_SHA256: 4ec867fd80f0445d0f0b348cb82b625a2f111fe869b7cc48e292f5b0c0740c48
DEPS: lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#pairThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the carrier: action vectors in the chamber Q
EDGE: lpM:s1:thresholds#pairThreshold | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the value is the pair-threshold helper at I
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.orderedPairThreshold (KAM/Frozen/Planetary/StrongAMD/Defs/OrderedPairThreshold.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:thresholds#orderedCrossThreshold
KIND: definition
TITLE: cross threshold B_cross(I) = min_{i<n} B_{i,i+1}(I)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L52-L52
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.orderedCrossThreshold
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (typing data); ν : Fin n → ℝ; I ∈ Q (OrderedActions)
SOURCE_QUANTIFIERS: for every n ≥ 2, ν, I ∈ Q
SOURCE_CONCLUSION: B_cross(I) = min_{i<n} B_{i,i+1}(I), (3), as the infimum over the adjacent pairs
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OrderedCrossThreshold.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.orderedCrossThreshold
FROZEN_ANCHOR_ID: planetary.d59.orderedCrossThreshold.v1
FROZEN_ABI_SHA256: 86b2da3d81eda68ba8bb775b7dc712dc3d0a90147c26c7c031f97ed9087d8183
DEPS: lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedPairThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the minimum runs over the adjacent pairs (i, i+1)
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the second index of each adjacent pair is i + 1
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the carrier: action vectors in the chamber Q
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the minimum is of the pair thresholds B_{i,i+1}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.orderedCrossThreshold (KAM/Frozen/Planetary/StrongAMD/Defs/OrderedCrossThreshold.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:thresholds#orderedStrongThreshold
KIND: definition
TITLE: strong threshold B(I) = min(B_cross(I), B_star(I))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L52-L53
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.orderedStrongThreshold
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (typing data); ν : Fin n → ℝ; I ∈ Q (OrderedActions)
SOURCE_QUANTIFIERS: for every n ≥ 2, ν, I ∈ Q
SOURCE_CONCLUSION: B(I) = min(B_cross(I), B_⋆(I)) with B_⋆(I) = min_i I_i, (3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OrderedStrongThreshold.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.orderedStrongThreshold
FROZEN_ANCHOR_ID: planetary.d59.orderedStrongThreshold.v1
FROZEN_ABI_SHA256: 04abc34ad0f0932d9db56255430732564b704f27505f05989c65917a8b1d453a
DEPS: lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedCrossThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L53-L53 | the carrier: action vectors in the chamber Q
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#s1@L53-L53 | B is the minimum of B_cross and B_star
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.orderedStrongThreshold (KAM/Frozen/Planetary/StrongAMD/Defs/OrderedStrongThreshold.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:elements#strongAMD
KIND: definition
TITLE: strong AMD C = sum Lambda_i - ¦L¦
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L32-L36
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.strongAMD
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; z : Phase (n*2) (typing data; total formula, source meaning on negative-energy states)
SOURCE_QUANTIFIERS: for every n, ν, z
SOURCE_CONCLUSION: C = Σ_i Λ_i - ¦L¦, (2), with Λ_i the Kepler action and ¦L¦ the absolute value of the total (scalar planar) angular momentum; orientation-free (amendment N8, ruling OD-1/D59)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/StrongAMD.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.strongAMD
FROZEN_ANCHOR_ID: planetary.d59.strongAMD.v1
FROZEN_ABI_SHA256: 302f70fe20850c0973d1ef0d3af71b6405869abf58fce9ff70e41ea440313c00
DEPS: lpM:s1:elements#keplerAction, lpM:s1:elements#totalMomentum, lpM:s1:model#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/source/MAIN.md#s1@L33-L35 | Λ_i = I_i is the Kepler action
EDGE: lpM:s1:elements#totalMomentum | docs/tracks/LP/source/MAIN.md#s1@L33-L35 | L is the total angular momentum
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L33-L35 | the phase type Phase (n*2) of planar positions and momenta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.strongAMD (KAM/Frozen/Planetary/StrongAMD/Defs/StrongAMD.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: AMENDED: N8 (AMENDMENTS.md L17): the orientation-free convention C = ΣΛ - ¦L¦ is the frozen one (OD-1)

NODE: lpM:s1:elements#keplerPeri
KIND: definition
TITLE: canonical perihelion radius a_i(1 - e_i)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L88-L89
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.keplerPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, z, i
SOURCE_CONCLUSION: the canonical perihelion radius a_i(1 - e_i) of (9), with a_i the Kepler axis and e_i = ¦e_i¦ the length of the eccentricity vector
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/KeplerPeri.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.keplerPeri
FROZEN_ANCHOR_ID: planetary.d59.keplerPeri.v1
FROZEN_ABI_SHA256: e3e8ad61d7eee3e71d1b06a9d2c03eee76068f5808fdb35bf0e1990d94fb3d9d
DEPS: lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:model#Phase, lpM:s1:data#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | a_i is the Kepler axis
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | e_i is the length of the eccentricity vector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | the Euclidean length ¦·¦ of a planar vector
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.keplerPeri (KAM/Frozen/Planetary/StrongAMD/Defs/KeplerPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:elements#keplerApo
KIND: definition
TITLE: canonical aphelion radius a_i(1 + e_i)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L88-L89
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.keplerApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, z, i
SOURCE_CONCLUSION: the canonical aphelion radius a_i(1 + e_i) of (9)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/KeplerApo.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.keplerApo
FROZEN_ANCHOR_ID: planetary.d59.keplerApo.v1
FROZEN_ABI_SHA256: 43024b250cebf92740dcc172da23740ac0cd9b049b3e4611c09f94c72eb22fa3
DEPS: lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:model#Phase, lpM:s1:data#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | a_i is the Kepler axis
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | e_i is the length of the eccentricity vector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the Euclidean length ¦·¦ of a planar vector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.keplerApo (KAM/Frozen/Planetary/StrongAMD/Defs/KeplerApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:elements#SourceCanonicalPhase
KIND: definition
TITLE: source canonical phases (nu > 0, q_i != 0, E_i < 0)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SourceCanonicalPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, ν
SOURCE_CONCLUSION: the planar phases z with ν_i > 0 for every i and, for every planet, ¦q_i¦ > 0 and negative Kepler energy (E_i < 0): the region where (2) is defined
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceCanonicalPhase.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.SourceCanonicalPhase
FROZEN_ANCHOR_ID: planetary.d59.SourceCanonicalPhase.v1
FROZEN_ABI_SHA256: 2b1d4f563d8a7e7e1be25be909f06c3e8463e515ca822939290e47557f8b183e
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector, lpM:s1:data#planeLength, lpM:s1:elements#keplerEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L28-L31 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L28-L31 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L28-L31 | the Euclidean length ¦·¦ of a planar vector
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L28-L31 | the carrier requires negative Kepler energy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.SourceCanonicalPhase (KAM/Frozen/Planetary/StrongAMD/Defs/SourceCanonicalPhase.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:elements#sourceStrongAMD
KIND: definition
TITLE: strong AMD C on source canonical phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L32-L36
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceStrongAMD
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceCanonicalPhase n ν (typing data)
SOURCE_QUANTIFIERS: for every n, ν, z
SOURCE_CONCLUSION: C(z) = strongAMD ν z on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceStrongAMD.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceStrongAMD
FROZEN_ANCHOR_ID: planetary.d59.sourceStrongAMD.v1
FROZEN_ABI_SHA256: f3f9ec60c7a6fa9c1692e70e8b59bd59a0a8de8937d6a7d024de2939c388a940
DEPS: lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#strongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L35-L35 | the carrier of source canonical phases
EDGE: lpM:s1:elements#strongAMD | docs/tracks/LP/source/MAIN.md#s1@L35-L35 | the value is the strong AMD
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceStrongAMD (KAM/Frozen/Planetary/StrongAMD/Defs/SourceStrongAMD.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:elements#sourceKeplerPeri
KIND: definition
TITLE: canonical perihelion on source canonical phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L88-L89
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceKeplerPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceCanonicalPhase n ν; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, z, i
SOURCE_CONCLUSION: a_i(1 - e_i) on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerPeri.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceKeplerPeri
FROZEN_ANCHOR_ID: planetary.d59.sourceKeplerPeri.v1
FROZEN_ABI_SHA256: 0ec040b0e5ac579dcf6f87c8133828c620b4e9267a4b01393332f1d6c4532537
DEPS: lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#keplerPeri
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | the carrier of source canonical phases
EDGE: lpM:s1:elements#keplerPeri | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | the value is the canonical perihelion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceKeplerPeri (KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:elements#sourceKeplerApo
KIND: definition
TITLE: canonical aphelion on source canonical phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L88-L89
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceKeplerApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceCanonicalPhase n ν; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, z, i
SOURCE_CONCLUSION: a_i(1 + e_i) on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerApo.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceKeplerApo
FROZEN_ANCHOR_ID: planetary.d59.sourceKeplerApo.v1
FROZEN_ABI_SHA256: 0c8b3de0105c5c7a55c38b9a7090f961ac41ceb6fb90e12f140ca905c694680b
DEPS: lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#keplerApo
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the carrier of source canonical phases
EDGE: lpM:s1:elements#keplerApo | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the value is the canonical aphelion
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceKeplerApo (KAM/Frozen/Planetary/StrongAMD/Defs/SourceKeplerApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#oscVelocity
KIND: definition
TITLE: actual heliocentric velocity V_i = p_i/nu_i + mu sum_j p_j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L512-L512
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.oscVelocity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; μ : ℝ; z : Phase (n*2); i : Fin n (typing data; total formula, source meaning on the source osculating phases)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: V_i = p_i/ν_i + μ Σ_j p_j, the actual velocity q̇_i of (10)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OscVelocity.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.oscVelocity
FROZEN_ANCHOR_ID: planetary.d59.oscVelocity.v1
FROZEN_ABI_SHA256: f4c4af24e85b0746619d6c176a830284c2ae2a197fa78f649f3dfaaab612d07a
DEPS: lpM:s1:model#bodyVector, lpM:s1:model#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the phase type Phase (n*2) of planar positions and momenta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.oscVelocity (KAM/Frozen/Planetary/StrongAMD/Defs/OscVelocity.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#oscParam
KIND: definition
TITLE: gravitational parameter k_i = 1 + mu nu_i
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L512-L512
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.oscParam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; μ : ℝ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ, i
SOURCE_CONCLUSION: k_i = 1 + μ ν_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OscParam.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.oscParam
FROZEN_ANCHOR_ID: planetary.d59.oscParam.v1
FROZEN_ABI_SHA256: 83c4392908734d61f8fbd748fc137b446a86b7bcc30ee7789f27a1497c40a8f4
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.oscParam (KAM/Frozen/Planetary/StrongAMD/Defs/OscParam.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#oscEnergy
KIND: definition
TITLE: osculating energy E_i^osc = ¦V_i¦^2/2 - k_i/¦q_i¦
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L515-L515
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.oscEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; μ : ℝ; z : Phase (n*2); i : Fin n (typing data; total formula, source meaning on the source osculating phases)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: E_i^osc = ¦V_i¦^2/2 - k_i/¦q_i¦, (42)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OscEnergy.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.oscEnergy
FROZEN_ANCHOR_ID: planetary.d59.oscEnergy.v1
FROZEN_ABI_SHA256: e574ac411b3164af465f8009be12e45aadba8c85e2e11c49fa9a4cac4d72e80d
DEPS: lpM:s1:model#bodyVector, lpM:s1:model#Phase, lpM:s1:data#planeLength, lpM:s1:data#planeSq, lpM:L16:defs#oscParam, lpM:L16:defs#oscVelocity
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | the Euclidean length ¦·¦ of a planar vector
EDGE: lpM:s1:data#planeSq | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | the squared Euclidean length ¦·¦^2
EDGE: lpM:L16:defs#oscParam | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | k_i occurs in the energy
EDGE: lpM:L16:defs#oscVelocity | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | V_i occurs in the energy
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.oscEnergy (KAM/Frozen/Planetary/StrongAMD/Defs/OscEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#oscAxis
KIND: definition
TITLE: osculating axis a_i^osc = -k_i/(2 E_i^osc)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L516-L516
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.oscAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; μ : ℝ; z : Phase (n*2); i : Fin n (typing data; total formula, source meaning on the source osculating phases)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: a_i^osc = -k_i/(2 E_i^osc), (42)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OscAxis.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.oscAxis
FROZEN_ANCHOR_ID: planetary.d59.oscAxis.v1
FROZEN_ABI_SHA256: c199a483d7944c4f262ce5f1e072bdf5a71fb7fba240a12dd34dd562a108d3e3
DEPS: lpM:s1:model#Phase, lpM:L16:defs#oscEnergy, lpM:L16:defs#oscParam
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L516-L516 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/source/MAIN.md#L16@L516-L516 | the axis is built from E_i^osc
EDGE: lpM:L16:defs#oscParam | docs/tracks/LP/source/MAIN.md#L16@L516-L516 | k_i occurs in the axis
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.oscAxis (KAM/Frozen/Planetary/StrongAMD/Defs/OscAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#oscEccVector
KIND: definition
TITLE: osculating eccentricity vector
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L517-L517
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.oscEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; μ : ℝ; z : Phase (n*2); i : Fin n (typing data; total formula, source meaning on the source osculating phases)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: e_i^osc = ((¦V_i¦^2 - k_i/¦q_i¦) q_i - (q_i·V_i) V_i)/k_i, (42)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OscEccVector.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.oscEccVector
FROZEN_ANCHOR_ID: planetary.d59.oscEccVector.v1
FROZEN_ABI_SHA256: 2de2060de127f5bfd0a729634c68176364d2766abac76391d70ecf413c106b8d
DEPS: lpM:s1:model#bodyVector, lpM:s1:model#Phase, lpM:s1:data#planeDot, lpM:s1:data#planeLength, lpM:s1:data#planeSq, lpM:L16:defs#oscParam, lpM:L16:defs#oscVelocity
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L16@L517-L517 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L517-L517 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeDot | docs/tracks/LP/source/MAIN.md#L16@L517-L517 | the Euclidean scalar product of planar vectors
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L16@L517-L517 | the Euclidean length ¦·¦ of a planar vector
EDGE: lpM:s1:data#planeSq | docs/tracks/LP/source/MAIN.md#L16@L517-L517 | the squared Euclidean length ¦·¦^2
EDGE: lpM:L16:defs#oscParam | docs/tracks/LP/source/MAIN.md#L16@L517-L517 | k_i occurs in the vector
EDGE: lpM:L16:defs#oscVelocity | docs/tracks/LP/source/MAIN.md#L16@L517-L517 | V_i occurs in the vector
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.oscEccVector (KAM/Frozen/Planetary/StrongAMD/Defs/OscEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#oscEcc
KIND: definition
TITLE: osculating eccentricity e_i^osc = ¦e_i^osc¦
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L518-L518
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.oscEcc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; μ : ℝ; z : Phase (n*2); i : Fin n (typing data; total formula, source meaning on the source osculating phases)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: e_i^osc = ¦e_i^osc vector¦, (42)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OscEcc.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.oscEcc
FROZEN_ANCHOR_ID: planetary.d59.oscEcc.v1
FROZEN_ABI_SHA256: 3a1f4067cf962b0b97d5e16f2f1c8238a81dafe48934ae548b647fe414d67b97
DEPS: lpM:s1:model#Phase, lpM:s1:data#planeLength, lpM:L16:defs#oscEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | the Euclidean length ¦·¦ of a planar vector
EDGE: lpM:L16:defs#oscEccVector | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | the eccentricity is the length of the vector
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.oscEcc (KAM/Frozen/Planetary/StrongAMD/Defs/OscEcc.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#oscPeri
KIND: definition
TITLE: osculating perihelion a_i^osc(1 - e_i^osc)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L523-L523
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.oscPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; μ : ℝ; z : Phase (n*2); i : Fin n (typing data; total formula, source meaning on the source osculating phases)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the osculating perihelion radius a_i^osc(1 - e_i^osc) of (43)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OscPeri.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.oscPeri
FROZEN_ANCHOR_ID: planetary.d59.oscPeri.v1
FROZEN_ABI_SHA256: a9c308e0c85c730b9da744665e3b162b42f981c8922590c1800b280789684eb3
DEPS: lpM:s1:model#Phase, lpM:L16:defs#oscAxis, lpM:L16:defs#oscEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:L16:defs#oscAxis | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | a_i^osc occurs
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | e_i^osc occurs
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.oscPeri (KAM/Frozen/Planetary/StrongAMD/Defs/OscPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#oscApo
KIND: definition
TITLE: osculating aphelion a_i^osc(1 + e_i^osc)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L523-L523
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.oscApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; μ : ℝ; z : Phase (n*2); i : Fin n (typing data; total formula, source meaning on the source osculating phases)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the osculating aphelion radius a_i^osc(1 + e_i^osc) of (43)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/OscApo.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.oscApo
FROZEN_ANCHOR_ID: planetary.d59.oscApo.v1
FROZEN_ABI_SHA256: 3b761db8cb87d3381bb119ebb1f48a9f7a887a94b384efe432416d006b1c808e
DEPS: lpM:s1:model#Phase, lpM:L16:defs#oscAxis, lpM:L16:defs#oscEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:L16:defs#oscAxis | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | a_i^osc occurs
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | e_i^osc occurs
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.oscApo (KAM/Frozen/Planetary/StrongAMD/Defs/OscApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#SourceOsculatingPhase
KIND: definition
TITLE: source osculating phases (nu > 0, mu > 0, q_i != 0, E^osc < 0, e^osc < 1)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SourceOsculatingPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; μ : ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ
SOURCE_CONCLUSION: the planar phases with ν_i > 0, μ > 0 and, for every planet, ¦q_i¦ > 0, E_i^osc < 0 and e_i^osc < 1: the nondegenerate elliptic actual-velocity elements of Lemma 16
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceOsculatingPhase.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.SourceOsculatingPhase
FROZEN_ANCHOR_ID: planetary.d59.SourceOsculatingPhase.v1
FROZEN_ABI_SHA256: a95826fff22c5725fbc68ed4ad44927739fe644b9276f988f80e7c5d258983a1
DEPS: lpM:s1:model#bodyVector, lpM:s1:model#Phase, lpM:s1:data#planeLength, lpM:L16:defs#oscEcc, lpM:L16:defs#oscEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L16@L510-L520 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L520 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L16@L510-L520 | the Euclidean length ¦·¦ of a planar vector
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/source/MAIN.md#L16@L510-L520 | the carrier requires e_i^osc < 1
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/source/MAIN.md#L16@L510-L520 | the carrier requires E_i^osc < 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.SourceOsculatingPhase (KAM/Frozen/Planetary/StrongAMD/Defs/SourceOsculatingPhase.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#sourceOscEnergy
KIND: definition
TITLE: osculating energy on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L515-L515
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceOscEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceOsculatingPhase n ν μ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the osculating energy of Lemma 16 on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEnergy.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscEnergy
FROZEN_ANCHOR_ID: planetary.d59.sourceOscEnergy.v1
FROZEN_ABI_SHA256: 5823351c9783e599ebbc32d4c6ea8142d0585020866fb25b967d8d80cf197061
DEPS: lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#oscEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | the carrier of source osculating phases
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | the value is the osculating energy
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscEnergy (KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#sourceOscAxis
KIND: definition
TITLE: osculating axis on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L516-L516
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceOscAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceOsculatingPhase n ν μ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the osculating axis of Lemma 16 on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscAxis.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscAxis
FROZEN_ANCHOR_ID: planetary.d59.sourceOscAxis.v1
FROZEN_ABI_SHA256: 382df895c542e5710ba0718ab5d364fbeb642b5fdb33884337e2d19f4c364cfa
DEPS: lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#oscAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L516-L516 | the carrier of source osculating phases
EDGE: lpM:L16:defs#oscAxis | docs/tracks/LP/source/MAIN.md#L16@L516-L516 | the value is the osculating axis
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscAxis (KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#sourceOscEccVector
KIND: definition
TITLE: osculating eccentricity vector on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L517-L517
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceOscEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceOsculatingPhase n ν μ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the osculating eccentricity vector of Lemma 16 on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEccVector.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscEccVector
FROZEN_ANCHOR_ID: planetary.d59.sourceOscEccVector.v1
FROZEN_ABI_SHA256: 265d073f6f1a73cbf3eaf8d7eceb4166ca791fb3d486b1c5571c28a5f2706e96
DEPS: lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#oscEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L517-L517 | the carrier of source osculating phases
EDGE: lpM:L16:defs#oscEccVector | docs/tracks/LP/source/MAIN.md#L16@L517-L517 | the value is the osculating eccentricity vector
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscEccVector (KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#sourceOscEcc
KIND: definition
TITLE: osculating eccentricity on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L518-L518
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceOscEcc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceOsculatingPhase n ν μ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the osculating eccentricity of Lemma 16 on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEcc.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscEcc
FROZEN_ANCHOR_ID: planetary.d59.sourceOscEcc.v1
FROZEN_ABI_SHA256: 8854f8abb708a7cdf33c58cec2421335bc9bf496eeb25c9b548550faa39aa60b
DEPS: lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#oscEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | the carrier of source osculating phases
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | the value is the osculating eccentricity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscEcc (KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscEcc.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#sourceOscPeri
KIND: definition
TITLE: osculating perihelion on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L523-L523
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceOscPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceOsculatingPhase n ν μ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the osculating perihelion of Lemma 16 on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscPeri.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscPeri
FROZEN_ANCHOR_ID: planetary.d59.sourceOscPeri.v1
FROZEN_ABI_SHA256: 71b54296120eb7553308212e58a570d934543caee092b70f4c01e47769713126
DEPS: lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#oscPeri
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | the carrier of source osculating phases
EDGE: lpM:L16:defs#oscPeri | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | the value is the osculating perihelion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscPeri (KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:L16:defs#sourceOscApo
KIND: definition
TITLE: osculating aphelion on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L523-L523
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceOscApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceOsculatingPhase n ν μ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the osculating aphelion of Lemma 16 on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscApo.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscApo
FROZEN_ANCHOR_ID: planetary.d59.sourceOscApo.v1
FROZEN_ABI_SHA256: 5c37f6767d386c77834ead460c3160898a39eaac536ccb2f1561b0ceee223fa3
DEPS: lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#oscApo
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | the carrier of source osculating phases
EDGE: lpM:L16:defs#oscApo | docs/tracks/LP/source/MAIN.md#L16@L523-L523 | the value is the osculating aphelion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscApo (KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: lpM:s1:model#Phase
KIND: definition
TITLE: phase type: positions and scaled momenta
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L17
PROOF_SOURCE: -
CONTRACT_ID: planetary.Phase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d : ℕ (typing data)
SOURCE_QUANTIFIERS: for every d
SOURCE_CONCLUSION: canonical coordinates (q, p) ∈ (Fin d → ℝ) × (Fin d → ℝ); the planar LP phases are Phase (n*2): heliocentric positions q_i and scaled canonical momenta p_i of MAIN §1 L17
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/Phase.lean
FROZEN_DECL: KAM.Planetary.Phase
FROZEN_ANCHOR_ID: planetary.Phase.v1
FROZEN_ABI_SHA256: 0b8db62a1a83c34b9c3562bd1bb6043b1db7174c9222df403355844422056af8
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Phase (KAM/Frozen/Planetary/Defs/Phase.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.Phase.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:model#bodyVector
KIND: definition
TITLE: planet i's planar coordinate vector
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L17
PROOF_SOURCE: -
CONTRACT_ID: planetary.bodyVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; q : Fin (n*2) → ℝ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, q, i
SOURCE_CONCLUSION: the two Cartesian coordinates of planet i in a stacked planar vector (q_i or p_i)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/BodyVector.lean
FROZEN_DECL: KAM.Planetary.bodyVector
FROZEN_ANCHOR_ID: planetary.bodyVector.v1
FROZEN_ABI_SHA256: 09f09ead30448301bb78763192f9a9c6ca3edcf4d3d2a771d616c548347661b4
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.bodyVector (KAM/Frozen/Planetary/Defs/BodyVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.bodyVector.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:model#NoCollision
KIND: definition
TITLE: collision-free configurations: q_i != 0, q_i != q_j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L24-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.NoCollision
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; q : Fin (n*2) → ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, q
SOURCE_CONCLUSION: ¦q_i¦ > 0 for every i and ¦q_i - q_j¦ > 0 for i ≠ j: the open physical domain of (1) excludes q_i = 0 and q_i = q_j
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/NoCollision.lean
FROZEN_DECL: KAM.Planetary.NoCollision
FROZEN_ANCHOR_ID: planetary.NoCollision.v1
FROZEN_ABI_SHA256: 31e597095beb23bba20a6793288094acda1208d7d884eb456886c2787f7d244b
DEPS: lpM:s1:model#bodyVector, lpM:s1:data#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | the Euclidean length ¦·¦ of a planar vector
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.NoCollision (KAM/Frozen/Planetary/Defs/NoCollision.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.NoCollision.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:elements#keplerEnergy
KIND: definition
TITLE: Kepler term nu_i E_i = ¦p_i¦^2/(2 nu_i) - nu_i/¦q_i¦
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L28-L28
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.keplerEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, z, i
SOURCE_CONCLUSION: ¦p_i¦^2/(2ν_i) - ν_i/¦q_i¦, the Kepler term of (1), equal to ν_i E_i with E_i = ¦v_i¦^2/2 - 1/¦q_i¦, v_i = p_i/ν_i (MAIN L28); for ν_i > 0 it has the sign of E_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/KeplerEnergy.lean
FROZEN_DECL: KAM.Planetary.keplerEnergy
FROZEN_ANCHOR_ID: planetary.d25.keplerEnergy.v1
FROZEN_ABI_SHA256: 16c4abfa143974cfab2700e7d6d8677f17282610a4442788226f49d67dc35bc7
DEPS: lpM:s1:model#bodyVector, lpM:s1:model#Phase, lpM:s1:data#planeLength, lpM:s1:data#planeSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L28-L28 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L28-L28 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L28-L28 | the Euclidean length ¦·¦ of a planar vector
EDGE: lpM:s1:data#planeSq | docs/tracks/LP/source/MAIN.md#s1@L28-L28 | the squared Euclidean length ¦·¦^2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.keplerEnergy (KAM/Frozen/Planetary/Defs/KeplerEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.keplerEnergy.v1 (track P), bound as an LP anchor node (Q6); convention watch: the frozen value is ν_i E_i, not the specific energy E_i

NODE: lpM:s1:elements#keplerAxis
KIND: definition
TITLE: Kepler axis a_i = -1/(2 E_i)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.keplerAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, z, i
SOURCE_CONCLUSION: a_i = -ν_i/(2 ν_i E_i) = -1/(2E_i), (2); meaningful when E_i < 0 and ν_i > 0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/KeplerAxis.lean
FROZEN_DECL: KAM.Planetary.keplerAxis
FROZEN_ANCHOR_ID: planetary.d25.keplerAxis.v1
FROZEN_ABI_SHA256: 8b55c0149ea62631a5254e243408a8d995b7e8f4808a16a0a580ed961a24913f
DEPS: lpM:s1:model#Phase, lpM:s1:elements#keplerEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | a_i is built from the Kepler term ν_i E_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.keplerAxis (KAM/Frozen/Planetary/Defs/KeplerAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.keplerAxis.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:elements#keplerAction
KIND: definition
TITLE: Kepler action I_i = Lambda_i = nu_i sqrt(a_i)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.keplerAction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, z, i
SOURCE_CONCLUSION: I_i = Λ_i = ν_i √a_i, (2)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/KeplerAction.lean
FROZEN_DECL: KAM.Planetary.keplerAction
FROZEN_ANCHOR_ID: planetary.d25.keplerAction.v1
FROZEN_ABI_SHA256: bb4ff50c2f5da52bcb864343bc951d280ef83bd68edbe387811453a1e42f10da
DEPS: lpM:s1:model#Phase, lpM:s1:elements#keplerAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | Λ_i is built from a_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.keplerAction (KAM/Frozen/Planetary/Defs/KeplerAction.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.keplerAction.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:elements#keplerEccVector
KIND: definition
TITLE: eccentricity vector e_i
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L29-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.keplerEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; ν : Fin n → ℝ; z : Phase (n*2); i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, z, i
SOURCE_CONCLUSION: e_i = (¦v_i¦^2 - 1/¦q_i¦) q_i - (q_i·v_i) v_i with v_i = p_i/ν_i (MAIN L29), written with p_i and ν_i^2
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/KeplerEccVector.lean
FROZEN_DECL: KAM.Planetary.keplerEccVector
FROZEN_ANCHOR_ID: planetary.d25.keplerEccVector.v1
FROZEN_ABI_SHA256: 754654458593f4c80d7e127afc0bd14f866161831a7400aeec7e374efcb4d7a3
DEPS: lpM:s1:model#bodyVector, lpM:s1:model#Phase, lpM:s1:data#planeDot, lpM:s1:data#planeLength, lpM:s1:data#planeSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L29-L29 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L29-L29 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeDot | docs/tracks/LP/source/MAIN.md#s1@L29-L29 | the Euclidean scalar product of planar vectors
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L29-L29 | the Euclidean length ¦·¦ of a planar vector
EDGE: lpM:s1:data#planeSq | docs/tracks/LP/source/MAIN.md#s1@L29-L29 | the squared Euclidean length ¦·¦^2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.keplerEccVector (KAM/Frozen/Planetary/Defs/KeplerEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.keplerEccVector.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:elements#planeCross
KIND: definition
TITLE: planar angular momentum q x p (oriented scalar determinant)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L34-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.planeCross
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q, p : Fin 2 → ℝ (typing data)
SOURCE_QUANTIFIERS: for every q, p
SOURCE_CONCLUSION: q × p = q_0 p_1 - q_1 p_0, the oriented scalar determinant of MAIN L37 (L_i = q_i × p_i)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlaneCross.lean
FROZEN_DECL: KAM.Planetary.planeCross
FROZEN_ANCHOR_ID: planetary.d25.planeCross.v1
FROZEN_ABI_SHA256: 27b7e3e428e60b15c01126bb9108975bef6f4c08bdd2bcd42149bf2229dab898
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planeCross (KAM/Frozen/Planetary/Defs/PlaneCross.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.planeCross.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:elements#totalMomentum
KIND: definition
TITLE: total planar angular momentum L = sum_i q_i x p_i
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L34-L35
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.totalMomentum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; z : Phase (n*2) (typing data)
SOURCE_QUANTIFIERS: for every n, z
SOURCE_CONCLUSION: L = Σ_i L_i = Σ_i q_i × p_i (scalar, signed), (2)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/TotalMomentum.lean
FROZEN_DECL: KAM.Planetary.totalMomentum
FROZEN_ANCHOR_ID: planetary.d25.totalMomentum.v1
FROZEN_ABI_SHA256: 176b9c28336577a54e1e706d18da24caf3646966e591da4333bfde457dcd66ee
DEPS: lpM:s1:model#bodyVector, lpM:s1:model#Phase, lpM:s1:elements#planeCross
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L34-L35 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L34-L35 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:elements#planeCross | docs/tracks/LP/source/MAIN.md#s1@L34-L35 | L_i = q_i × p_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-adef-pl
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.totalMomentum (KAM/Frozen/Planetary/Defs/TotalMomentum.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.totalMomentum.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:data#planeSq
KIND: definition
TITLE: squared Euclidean length ¦v¦^2
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L15-L15
PROOF_SOURCE: -
CONTRACT_ID: planetary.planeSq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v : Fin 2 → ℝ (typing data)
SOURCE_QUANTIFIERS: for every v
SOURCE_CONCLUSION: ¦v¦^2 = Σ_k v_k^2, the physical Euclidean square of MAIN L15
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlaneSq.lean
FROZEN_DECL: KAM.Planetary.planeSq
FROZEN_ANCHOR_ID: planetary.planeSq.v1
FROZEN_ABI_SHA256: b0de2d3150c6c723a7af40b0f9ef8d6849b211bf81ab6685ebd870b7aa618d5e
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planeSq (KAM/Frozen/Planetary/Defs/PlaneSq.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.planeSq.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:data#planeLength
KIND: definition
TITLE: Euclidean length ¦v¦
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L15-L15
PROOF_SOURCE: -
CONTRACT_ID: planetary.planeLength
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v : Fin 2 → ℝ (typing data)
SOURCE_QUANTIFIERS: for every v
SOURCE_CONCLUSION: ¦v¦ = √(¦v¦^2), the physical Euclidean length of MAIN L15 (distinct from the max norm on action vectors)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlaneLength.lean
FROZEN_DECL: KAM.Planetary.planeLength
FROZEN_ANCHOR_ID: planetary.planeLength.v1
FROZEN_ABI_SHA256: 385b5a3f2a85cef8e532266e97df0d7f79ac00c08d2c9b635dafa0f3c3ccc6f9
DEPS: lpM:s1:data#planeSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#planeSq | docs/tracks/LP/source/MAIN.md#s1@L15-L15 | the squared Euclidean length ¦·¦^2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planeLength (KAM/Frozen/Planetary/Defs/PlaneLength.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.planeLength.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:data#planeDot
KIND: definition
TITLE: Euclidean scalar product q . v
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L29-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.planeDot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v, w : Fin 2 → ℝ (typing data)
SOURCE_QUANTIFIERS: for every v, w
SOURCE_CONCLUSION: v·w = Σ_k v_k w_k, the scalar product q_i·v_i of MAIN L29
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlaneDot.lean
FROZEN_DECL: KAM.Planetary.planeDot
FROZEN_ANCHOR_ID: planetary.planeDot.v1
FROZEN_ABI_SHA256: 8cf08c43a712bf1c8d3e6fd5426b13d34d07a93597447a35b7b671e1126ae661
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-adef-pl
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planeDot (KAM/Frozen/Planetary/Defs/PlaneDot.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.planeDot.v1 (track P), bound as an LP anchor node (Q6)

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

NODE: lpM:ext-ftc
KIND: external
TITLE: fundamental theorem of calculus (zero derivative on an interval)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-ftc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J a real interval; f : J → V continuous on J and differentiable on its interior, with derivative zero there; V is a finite-dimensional real normed vector space (including ℝ)
SOURCE_QUANTIFIERS: for every such J, V and f, and every s, t ∈ J
SOURCE_CONCLUSION: f(t) = f(s); thus f is constant on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-R1-small
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-compact-min
KIND: external
TITLE: extreme values of a continuous function on a nonempty compact set
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-compact-min
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K a nonempty compact set; f : K → ℝ continuous
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: f attains its minimum and its maximum on K (for finitely many functions, the minimum of their minima)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-R1-small
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-heine-cantor
KIND: external
TITLE: Heine-Cantor: continuity on a compact set is uniform
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L154-L154
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-heine-cantor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K a compact metric space; f continuous on K
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: f is uniformly continuous on K
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-R1-small
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-picard
KIND: external
TITLE: contraction mapping principle / Picard iteration for the integral equation
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-picard
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X bounded with bounded derivative (locally Lipschitz) on a closed ball B(z_*, ρ); a time T below ρ/sup¦X¦ and the inverse Lipschitz bound
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: the map z ↦ z_* + ∫_0^t X(z(u)) du is a contraction of C([0,T], B(z_*, ρ)) and its fixed point is a solution of ż = X(z), z(0) = z_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-R1-small
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-gronwall
KIND: external
TITLE: uniqueness of ODE solutions by iterating the integral inequality
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-gronwall
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X Lipschitz on a set containing two solutions with the same initial value
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: the two solutions coincide (iterating ¦z_1 - z_2¦(t) ≤ L ∫_0^t ¦z_1 - z_2¦ gives zero)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-R1-small
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:s1:data
KIND: definition
TITLE: fixed data of track LP (n, nu, A, delta, gamma, tau, d; the two norms)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L11-L15
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: fixed once: n, ν, 𝒜, δ, γ, τ, d
SOURCE_CONCLUSION: an integer n ≥ 2; ν_i > 0 with max_i ν_i = 1; a compact set 𝒜 ⊂ {a ∈ ℝ^n : 0 < a_1 < ... < a_n} (possibly empty, giving a vacuous assertion); δ, γ > 0; τ > n - 1; space dimension d ∈ {2, 3}; physical Euclidean lengths ¦·¦ are distinguished from the max norm ‖·‖_∞ on action and complex coordinate vectors
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: hypothesis package (SPEC §3): not a global standing assumption; a result that assumes part of it names that part in SOURCE_HYPOTHESES and depends on this node

NODE: lpM:s1:model
KIND: definition
TITLE: the exact model: units, masses, symplectic form, Hamiltonian (1), domain, time
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L39
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:model
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of lpM:s1:data (n, ν, d); μ > 0
SOURCE_QUANTIFIERS: for every μ > 0
SOURCE_CONCLUSION: G = 1 and stellar mass 1; planet masses m_i = μν_i; heliocentric positions q_i and scaled canonical momenta p_i with symplectic form Σ_i dp_i ∧ dq_i and ι_{X_H}Ω = -dH; the exact Hamiltonian (1) H_μ = Σ_i(¦p_i¦^2/(2ν_i) - ν_i/¦q_i¦) + μ f, f = ¦Σ_i p_i¦^2/2 - Σ_{i<j} ν_iν_j/¦q_i - q_j¦, on the open domain q_i ≠ 0, q_i ≠ q_j; solutions use physical time; physical angular momentum and AMD are μL and μC, so δ is a normalized margin; the splitting (1) uses central Kepler parameter one (L39)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the data ν, n, d and the Euclidean length ¦·¦ enter (1)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m1
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:s1:elements
KIND: definition
TITLE: canonical Kepler elements and the strong AMD (2), in dimension d
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L37
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:elements
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of lpM:s1:data; a state (q, p) of the model
SOURCE_QUANTIFIERS: for every state and every i
SOURCE_CONCLUSION: v_i = p_i/ν_i, E_i = ¦v_i¦^2/2 - 1/¦q_i¦, e_i = (¦v_i¦^2 - 1/¦q_i¦) q_i - (q_i·v_i) v_i; when E_i < 0: a_i = -1/(2E_i), I_i = Λ_i = ν_i √a_i, e_i = ¦e_i¦, L_i = q_i × p_i, L = Σ_i L_i, C = Σ_i I_i - ¦L¦ (2); in the plane × is the oriented scalar determinant and ¦L¦ its absolute value; a nondegenerate elliptic canonical state has E_i < 0 and e_i < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#s1@L28-L28 | q_i, p_i and ν_i are the variables of the model
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L28-L28 | the Euclidean length ¦·¦ and the dimension d
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: d-generic source definition (d ∈ {2,3}); the planar frozen realizations are the anchors lpM:s1:elements#* (LP-adef-pl), the spatial ones come in wave 3 (SPEC §5, dimension rule). AMENDED: N8 (AMENDMENTS.md L17): C = ΣI - ¦L¦ is the frozen convention (OD-1).

NODE: lpM:s1:fast
KIND: definition
TITLE: fast Hamiltonian h(I) and radian frequencies omega(I) (4)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L57-L61
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:fast
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of lpM:s1:data (n, ν)
SOURCE_QUANTIFIERS: for every action vector I with I_i > 0
SOURCE_CONCLUSION: h(I) = -Σ_i ν_i^3/(2 I_i^2) and ω_i(I) = ν_i^3/I_i^3 = a_i(I)^{-3/2}, (4)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:data, lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L59-L59 | the masses ν_i enter h and ω
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#s1@L60-L60 | ω_i(I) = a_i(I)^{-3/2} uses the action axis
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:s1:dioph
KIND: definition
TITLE: the Diophantine condition (5) at omega(I^0); angles of period 2 pi
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L62-L67
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:dioph
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of lpM:s1:data (γ > 0, τ > n - 1); an initial action vector I^0
SOURCE_QUANTIFIERS: for every I^0 and every 0 ≠ k ∈ ℤ^n
SOURCE_CONCLUSION: ¦k·ω(I^0)¦ ≥ γ ¦k¦_1^{-τ} for every 0 ≠ k ∈ ℤ^n (5); all angles of the proof have period 2π (Lemma 13 records the conversion to period one)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:fast, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#s1@L64-L64 | the frequencies ω(I^0) of (4)
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L64-L64 | γ and τ are fixed data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:s1:half-integer
KIND: claim
TITLE: tau = n - 1/2 is admissible and gives exponent 1/(2n+1)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
CONTRACT_ID: lpM:s1:half-integer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (lpM:s1:data)
SOURCE_QUANTIFIERS: for every n ≥ 2
SOURCE_CONCLUSION: τ = n - 1/2 satisfies τ > n - 1, and a = 1/(2(τ + 1)) = 1/(2n + 1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | admissibility is the condition τ > n - 1 of the data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: arithmetic step of the half-integer corollary anchors LP1-H and LP2-H (waves 2 and 3); the exponent a = 1/(2(τ+1)) is defined in (7)

NODE: lpM:L1
KIND: lemma
TITLE: Lemma 1: normalization and Newtonian reconstruction
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L99-L99
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L101-L108
CONTRACT_ID: lpM:L1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d ∈ {2,3}; ν_i > 0; μ > 0
SOURCE_QUANTIFIERS: for every d ∈ {2,3}, ν > 0 and μ > 0
SOURCE_CONCLUSION: the Hamiltonian (1) is the zero-total-momentum translation reduction of the Newtonian (1+n)-body Hamiltonian, divided by μ, in unchanged time; its solutions reconstruct Newtonian solutions with masses (1, μν_1, ..., μν_n)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1#reduction, lpM:L1#reconstruction, lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#reduction | docs/tracks/LP/source/MAIN.md#L1@L101-L102 | the reduction and the division by μ give (1)
EDGE: lpM:L1#reconstruction | docs/tracks/LP/source/MAIN.md#L1@L104-L108 | the explicit inverse reconstructs Newtonian solutions
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L1@L99-L99 | the statement concerns Hamiltonian (1) and the masses μν_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L1#reduction
KIND: step
TITLE: translation reduction with P_i = mu p_i, cancelling mu gives (1)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L101-L102
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L101-L102
CONTRACT_ID: lpM:L1#reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L1: d ∈ {2,3}; ν_i > 0; μ > 0
SOURCE_QUANTIFIERS: for every d, ν, μ (inherited from lpM:L1)
SOURCE_CONCLUSION: in barycentric coordinates with P_i = μ p_i and P_0 = -Σ_i P_i, the translation reduction has relative positions q_i = x_i - x_0 and momenta P_i (Σ_{i=0}^n P_i·dx_i = Σ_{i≥1} P_i·dq_i), kinetic energy Σ_i ¦P_i¦^2/(2μν_i) + ¦Σ_i P_i¦^2/2 and potential -Σ_i μν_i/¦q_i¦ - Σ_{i<j} μ^2 ν_iν_j/¦q_i - q_j¦; the symplectic form and the Hamiltonian both acquire the factor μ, and cancelling it gives (1) with the same time
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L1@L102-L102 | the result is compared with the Hamiltonian (1) and its symplectic form
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L1#velocity
KIND: display
TITLE: (10): Hamilton's equation for q_i, the actual velocity
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L105-L107
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L107
CONTRACT_ID: lpM:L1#velocity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L1: d ∈ {2,3}; ν_i > 0; μ > 0; a solution of (1)
SOURCE_QUANTIFIERS: along every solution of (1) and for every i
SOURCE_CONCLUSION: q̇_i = p_i/ν_i + μ Σ_j p_j, (10)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L1@L106-L106 | Hamilton's equation q̇_i = ∂H_μ/∂p_i for the Hamiltonian (1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.oscVelocity_eq_movingField ; KAM.Planetary.Spatial.spatialOscVelocity_eq_hamiltonianVectorField
LEAN_NOTE: d-generic: planar and spatial realizations (mechanical docstring match, D65)
NOTE: display (10), refined into its own node because Lemma 3 (recoil term) and Lemma 16 (V_i) consume it independently of the reconstruction (SPEC §5, displays)

NODE: lpM:L1#reconstruction
KIND: step
TITLE: explicit inverse: barycentric positions and velocities, Newton's equations
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L108
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L108
CONTRACT_ID: lpM:L1#reconstruction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L1: d ∈ {2,3}; ν_i > 0; μ > 0; a solution of (1)
SOURCE_QUANTIFIERS: for every solution of (1) (inherited from lpM:L1)
SOURCE_CONCLUSION: with M = 1 + μΣ_i ν_i, x_0 = -μ Σ_i ν_i q_i/M, x_i = x_0 + q_i, ẋ_0 = -μ Σ_i p_i and ẋ_i = p_i/ν_i, the displayed velocities differentiate the displayed positions, and the equations for ṗ_i are Newton's equations after multiplying the planet momenta by μ; pair differences are q_i - q_j and star differences q_i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1#velocity, lpM:L1#reduction, lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#velocity | docs/tracks/LP/source/MAIN.md#L1@L105-L108 | Hamilton's equation (10) shows that the displayed velocities differentiate the displayed positions
EDGE: lpM:L1#reduction | docs/tracks/LP/source/MAIN.md#L1@L108-L108 | the planet momenta are multiplied by μ (P_i = μ p_i) as in the reduction
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L1@L108-L108 | the equations for ṗ_i come from differentiating the potentials in (1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L2
KIND: lemma
TITLE: Lemma 2: elementary orbital identities (11)-(12)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L122
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: lpM:L2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν > 0; q ≠ 0; v = p/ν; E = ¦v¦^2/2 - 1/¦q¦ < 0 (one planet, any dimension)
SOURCE_QUANTIFIERS: for every ν > 0, q ≠ 0 and p with E < 0
SOURCE_CONCLUSION: e^2 = 1 + 2E¦q × v¦^2 = 1 - ¦q × v¦^2/a ≤ 1 and ¦q × p¦ = I √(1 - e^2) (11); a(1 - e) ≤ ¦q¦ ≤ a(1 + e) and ¦p¦^2 = ν^2(2/¦q¦ - 1/a) (12); including the radial case e = 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2#ecc-identity, lpM:L2#radial-bounds, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2#ecc-identity | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | the first identity of (11) and its substitutions
EDGE: lpM:L2#radial-bounds | docs/tracks/LP/source/MAIN.md#L2@L124-L128 | the bounds and the momentum identity (12)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | definitions (2) of a, e, I
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.orbital_identities ; KAM.Planetary.Spatial.spatial_orbital_identities
LEAN_NOTE: d-generic: planar and spatial realizations (mechanical docstring match, D65)
NOTE: -

NODE: lpM:L2#ecc-identity
KIND: step
TITLE: (11): e^2 = 1 + 2E¦q x v¦^2 = 1 - ¦q x v¦^2/a and ¦q x p¦ = I sqrt(1 - e^2)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L113-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: lpM:L2#ecc-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L2: ν > 0, q ≠ 0, v = p/ν, E = ¦v¦^2/2 - 1/¦q¦ < 0
SOURCE_QUANTIFIERS: for every such q, p (inherited from lpM:L2)
SOURCE_CONCLUSION: expanding the square of (¦v¦^2 - 1/¦q¦) q - (q·v) v with ¦q × v¦^2 = ¦q¦^2¦v¦^2 - (q·v)^2 gives e^2 = 1 + 2E¦q × v¦^2; substituting 2E = -1/a gives e^2 = 1 - ¦q × v¦^2/a ≤ 1 and ¦q × p¦ = I √(1 - e^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | the eccentricity vector, E, a and I of (2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L2#radial-bounds
KIND: step
TITLE: (12): a(1-e) <= ¦q¦ <= a(1+e) and ¦p¦^2 = nu^2(2/¦q¦ - 1/a)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L121
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: lpM:L2#radial-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L2: ν > 0, q ≠ 0, v = p/ν, E = ¦v¦^2/2 - 1/¦q¦ < 0; local data: r = ¦q¦, ℓ = q × v
SOURCE_QUANTIFIERS: for every such q, p (inherited from lpM:L2)
SOURCE_CONCLUSION: the energy identity and the radial/tangential decomposition give (q·v)^2 = 2r - r^2/a - ¦ℓ¦^2 ≥ 0; with ¦ℓ¦^2 = a(1 - e^2), completing the square gives (r - a)^2 ≤ a^2 e^2, i.e. a(1 - e) ≤ r ≤ a(1 + e); ¦p¦^2 = ν^2(2/¦q¦ - 1/a) is the energy definition
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2#ecc-identity, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2#ecc-identity | docs/tracks/LP/source/MAIN.md#L2@L128-L128 | uses ¦ℓ¦^2 = a(1 - e^2) from (11)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | the energy definition E = ¦v¦^2/2 - 1/¦q¦ = -1/(2a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L3
KIND: lemma
TITLE: Lemma 3: exact angular momentum and the AMD identity (static and dynamic parts)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L137
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model (1) with its data (n, ν, d, μ > 0); m > 0 in the last clause
SOURCE_QUANTIFIERS: for every solution of (1) on a connected interval of existence, every negative-energy state, and m > 0
SOURCE_CONCLUSION: L is constant on every connected interval of existence of (1); C ≥ 0 in the negative-energy region; if C < B_⋆(I) then L ≠ 0 and all H_i = L_i·L̂ are positive, and on such an orbit C(t) - C(0) = Σ_i(I_i(t) - I_i(0)) and C = Σ_i(I_i - H_i) ≥ Σ_i I_i D(e_i) (13); if C ≤ B_⋆(I) - m then H_i ≥ m for every i; in the planar case, orienting the plane so that L > 0 makes all individual scalar angular momenta positive
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#static, lpM:L3#dynamic, lpM:L3#planar-orientation, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the static clauses: C ≥ 0, L ≠ 0, H_i > 0, H_i ≥ m and the inequality of (13)
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the dynamic clauses: conservation of L and the identity of (13)
EDGE: lpM:L3#planar-orientation | docs/tracks/LP/source/MAIN.md#L3@L137-L137 | the planar orientation clause
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L3@L135-L135 | D occurs directly in the full statement of (13), independently of the conjunction edges
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: Q3 split (ruling root-b8): the conjunction of lpM:L3#static (consumed by Lemma 5, hence LP0, which thus does not reach Lemma 1) and lpM:L3#dynamic (consumed by Lemma 6 and the dynamic anchors)

NODE: lpM:L3#static
KIND: lemma
TITLE: Lemma 3, static part: C >= 0, L != 0, positive projections, H_i >= m, inequality of (13)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L137
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#static
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a negative-energy state of the model (E_i < 0, q_i ≠ 0 for every i; ν > 0); m > 0 in the last clause
SOURCE_QUANTIFIERS: for every negative-energy state and every m > 0
SOURCE_CONCLUSION: C ≥ 0; if C < B_⋆(I) = min_i I_i then L ≠ 0, every H_i = L_i·L̂ is positive, and C = Σ_i(I_i - H_i) ≥ Σ_i I_i D(e_i) (the inequality of (13)); if C ≤ B_⋆(I) - m then H_i ≥ m for every i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#amd-nonneg, lpM:L3#L-nonzero, lpM:L3#projections, lpM:L3#deficit, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#amd-nonneg | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C ≥ 0
EDGE: lpM:L3#L-nonzero | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | L ≠ 0 when C < B_⋆
EDGE: lpM:L3#projections | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | H_i ≥ I_i - C, hence H_i > 0 and H_i ≥ m
EDGE: lpM:L3#deficit | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the inequality of (13)
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L3@L135-L135 | D occurs in (13)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: Q3 split: no dynamics is used; this is the part of Lemma 3 that Lemma 5 (and LP0) consumes

NODE: lpM:L3#dynamic
KIND: lemma
TITLE: Lemma 3, dynamic part: L is conserved and C(t) - C(0) = sum(I_i(t) - I_i(0))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L135
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#dynamic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a solution of (1) on a connected interval of existence; for the identity, negative energies along it (MAIN: 'on such an orbit', C < B_⋆)
SOURCE_QUANTIFIERS: for every such solution and all times t in its interval
SOURCE_CONCLUSION: L(t) is constant; C(t) - C(0) = Σ_i(I_i(t) - I_i(0)), the identity of (13)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#conservation, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#conservation | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | L̇ = 0 and constancy
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ I_i - ¦L¦ with constant ¦L¦ gives the identity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: Q3 split: the dynamic clauses of Lemma 3 (consumed by Lemma 6 and the dynamic anchors)

NODE: lpM:L3#conservation
KIND: step
TITLE: dL/dt = 0: recoil term, central forces and pair torques vanish; constancy by FTC
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L132
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#conservation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a solution on a connected interval)
SOURCE_QUANTIFIERS: along every solution of (1) on a connected interval of existence
SOURCE_CONCLUSION: differentiating Σ_i q_i × p_i: the recoil contribution from q̇_i is μ(Σ_j p_j) × (Σ_i p_i) = 0, the other kinetic terms vanish individually, central forces have zero torque, and the two forces of each planet pair contribute a multiple of (q_i - q_j) × (q_i - q_j) = 0; thus L̇ = 0 and L is constant
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1#velocity, lpM:s1:model, lpM:s1:elements, lpM:ext-ftc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#velocity | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the recoil term comes from q̇_i = p_i/ν_i + μΣ_j p_j of (10)
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the forces are those of the Hamiltonian (1)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | L = Σ_i q_i × p_i
EDGE: lpM:ext-ftc | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the fundamental theorem of calculus gives constancy
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L3#amd-nonneg
KIND: step
TITLE: ¦L¦ <= sum ¦L_i¦ <= sum I_i, so C >= 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L132
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#amd-nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a negative-energy state)
SOURCE_QUANTIFIERS: for every negative-energy state
SOURCE_CONCLUSION: ¦L¦ ≤ Σ_i ¦L_i¦ ≤ Σ_i I_i, hence C = Σ_i I_i - ¦L¦ ≥ 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | by (11), ¦L_i¦ = ¦q_i × p_i¦ = I_i √(1 - e_i^2) ≤ I_i
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ I_i - ¦L¦
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L3#L-nonzero
KIND: step
TITLE: C < B_star forces L != 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L132
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#L-nonzero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a negative-energy state with C < B_⋆(I))
SOURCE_QUANTIFIERS: for every such state
SOURCE_CONCLUSION: if L = 0 then C = Σ_i I_i ≥ min_i I_i = B_⋆(I), contradicting C < B_⋆(I); so L ≠ 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ I_i - ¦L¦ and the actions I_i > 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L3#projections
KIND: step
TITLE: 0 <= I_i - H_i, sum = C, so H_i >= I_i - C (> 0, >= m)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L137
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#projections
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: negative-energy state: ν_i > 0, q_i ≠ 0 and E_i < 0 for every i, d ∈ {2,3}; local nonzero-L case: L ≠ 0; local definitions L̂ = L/¦L¦ and H_i = L_i·L̂; m > 0 for the margin implication
SOURCE_QUANTIFIERS: for every such negative-energy state with L ≠ 0 and every m > 0
SOURCE_CONCLUSION: H_i ≤ ¦L_i¦ ≤ I_i, so every I_i - H_i ≥ 0, and Σ_i (I_i - H_i) = C; hence H_i ≥ I_i - C ≥ B_⋆(I) - C, so H_i > 0 when C < B_⋆(I) and H_i ≥ m when C ≤ B_⋆(I) - m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | ¦L_i¦ ≤ I_i by (11)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | Σ_i H_i = ¦L¦ and C = Σ I_i - ¦L¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: The local L ≠ 0 case is explicit, as needed by the nonzero-L deficit argument. The C < B_⋆ and C ≤ B_⋆ - m clauses are conditional conclusions. Do not apply lpM:L3#L-nonzero here: its premise C < B_⋆ is absent in the general nonzero-L case; lpM:L3#static obtains L ≠ 0 separately before using this step.

NODE: lpM:L3#deficit
KIND: step
TITLE: H_i <= I_i sqrt(1 - e_i^2) gives C >= sum I_i D(e_i) (inequality of (13))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L135
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#deficit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a negative-energy state with L ≠ 0, as on an orbit with C < B_⋆); local data: L̂, H_i
SOURCE_QUANTIFIERS: for every such state
SOURCE_CONCLUSION: H_i ≤ ¦L_i¦ = I_i √(1 - e_i^2), hence C = Σ_i(I_i - H_i) ≥ Σ_i I_i(1 - √(1 - e_i^2)) = Σ_i I_i D(e_i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#projections, lpM:L2, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#projections | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ_i (I_i - H_i)
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | ¦L_i¦ = I_i √(1 - e_i^2) by (11)
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | D(e) = 1 - √(1 - e^2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: the argument uses only L ≠ 0 (to define L̂); MAIN applies it on orbits with C < B_⋆

NODE: lpM:L3#deficit-zero-L
KIND: step
TITLE: the deficit bound when L = 0: C = sum I_i >= sum I_i D(e_i)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L135
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#deficit-zero-L
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a negative-energy state with L = 0)
SOURCE_QUANTIFIERS: for every such state
SOURCE_CONCLUSION: C = Σ_i I_i ≥ Σ_i I_i D(e_i), since 0 ≤ e_i ≤ 1 and D(e) ≤ 1 on [0,1]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:s1:thresholds#eccDeficit, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | e_i ≤ 1 by (11)
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | D(e) ≤ 1 for e ∈ [0,1]
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ I_i - ¦L¦ = Σ I_i when L = 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: SOURCE_GAP: MAIN states and proves the inequality of (13) only on orbits with C < B_⋆ (hence L ≠ 0, via H_i); the frozen characterization sum_action_mul_eccDeficit_le_sourceStrongAMD asserts it on every source canonical phase, and the case L = 0 is not argued in MAIN (it is immediate from D ≤ 1 on [0,1])

NODE: lpM:L3#planar-orientation
KIND: claim
TITLE: planar case: orient so that L > 0; all scalar L_i are then positive
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L137-L137
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L137-L137
CONTRACT_ID: lpM:L3#planar-orientation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 2; a negative-energy state with C < B_⋆(I)
SOURCE_QUANTIFIERS: for every such planar state
SOURCE_CONCLUSION: choosing the plane's orientation so that L > 0, every individual scalar angular momentum L_i is positive
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#projections, lpM:L3#L-nonzero
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#projections | docs/tracks/LP/source/MAIN.md#L3@L137-L137 | in the plane H_i = L_i·sign(L) > 0
EDGE: lpM:L3#L-nonzero | docs/tracks/LP/source/MAIN.md#L3@L137-L137 | C < B_⋆ supplies L ≠ 0 before applying the projection step and choosing an orientation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: consumed by Theorem 15's orientation step (wave 2; N8, OD-1)

NODE: lpM:L4
KIND: lemma
TITLE: Lemma 4: attained, positive, continuous thresholds and (14)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L146
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L156
CONTRACT_ID: lpM:L4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); ν_i > 0 for every i ('all positive masses'); I ∈ Q
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0 and I ∈ Q (each pair i < j)
SOURCE_CONCLUSION: every minimum in (3) is attained and positive; each B_ij and B is continuous on Q; B_ij(I) < I_j and B(I) = min(B_cross(I), I_1) (14)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#feasible-compact, lpM:L4#continuity, lpM:L4#positivity, lpM:L4#competitor, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the pair minima are attained
EDGE: lpM:L4#continuity | docs/tracks/LP/source/MAIN.md#L4@L154-L156 | continuity of B_ij and B
EDGE: lpM:L4#positivity | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | positivity of the minima
EDGE: lpM:L4#competitor | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | the competitor proves (14)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L143-L143 | I ∈ Q
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L143-L143 | B_ij occurs
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L145-L145 | B_cross occurs in (14)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L143-L143 | B occurs
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L143-L143 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: Q4 split (ruling root-b8): the statement clauses on radial contact and the Laskar-Petit identification (L143) and on geometric sharpness (L147) are not part of this record; no proof consumes them (N9). Their items lpM:L4#stmt-contact-lp and lpM:L4#stmt-sharpness and the supporting prose L158 and L160 are EXCLUDED

NODE: lpM:L4#feasible-compact
KIND: step
TITLE: the feasible set is closed and nonempty and the objective continuous: minimum attained
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
CONTRACT_ID: lpM:L4#feasible-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)
SOURCE_CONCLUSION: the feasible subset of [0,1]^2 is closed and nonempty, since (0, 1 - α) is feasible, and the objective I_i D(u) + I_j D(v) is continuous, so the pair minimum is attained
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#actionAxis, lpM:s1:chamber#chamber, lpM:ext-compact-min, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the feasible set
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the objective
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | continuity of D on [0,1]
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | α = a_i(I)/a_j(I)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | I ∈ Q gives α < 1
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | a continuous function on a nonempty compact set attains its minimum
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L4#contact-reduction
KIND: step
TITLE: scaling a feasible point to contact does not increase the objective
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
CONTRACT_ID: lpM:L4#contact-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4); for every feasible (u,v)
SOURCE_CONCLUSION: replacing (u,v) by t(u,v) with t = (1 - α)/(αu + v) ≤ 1 gives contact a_i(1 + tu) = a_j(1 - tv) and does not increase the objective
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#eccDeficit, lpM:s1:data, lpM:s1:chamber#chamber, lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | feasibility and contact
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the objective
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | D is nondecreasing on [0,1]
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | I ∈ Q is a direct carrier premise
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the local ratio α = a_i(I)/a_j(I) directly uses the action-axis formula
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L4#contact-param
KIND: step
TITLE: (15): contact parameterized over t in [0,1]
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L150-L153
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L153
CONTRACT_ID: lpM:L4#contact-param
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4); t ∈ [0,1]
SOURCE_CONCLUSION: with m(α) = min(1, (1 - α)/α), u = m(α)t, v = 1 - α - αm(α)t (15) parameterizes the contact set over the fixed interval [0,1], so B_ij(I) = min_{t ∈ [0,1]} F(I,t) with F the objective along (15)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#contact-reduction, lpM:s1:thresholds#pairObjective, lpM:s1:data, lpM:s1:chamber#chamber, lpM:s1:thresholds#actionAxis, lpM:s1:thresholds#orderedPairThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#contact-reduction | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the minimum is attained on the contact set
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L151-L151 | F is the objective along (15)
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | I ∈ Q is a direct carrier premise
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the local ratio α = a_i(I)/a_j(I) directly uses the action-axis formula
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the conclusion directly identifies or bounds B_ij(I)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L4#continuity
KIND: step
TITLE: continuity of B_ij and B on Q via uniform continuity on compact neighborhoods
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L154-L156
CONTRACT_ID: lpM:L4#continuity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0 and every I, J ∈ Q
SOURCE_CONCLUSION: the objective in (15) is jointly continuous in (I,t), hence uniformly continuous on K × [0,1] for every compact neighborhood K ⊂ Q; ¦min_t F(I,t) - min_t F(J,t)¦ ≤ sup_t ¦F(I,t) - F(J,t)¦ proves continuity of B_ij on Q; finite minima preserve continuity, so B_cross and B are continuous
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#contact-param, lpM:ext-heine-cantor, lpM:ext-compact-min, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:data, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#contact-param | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | B_ij is the minimum over t of the objective in (15)
EDGE: lpM:ext-heine-cantor | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | uniform continuity on compact sets
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L4@L155-L155 | the minima over t ∈ [0,1] are attained
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | compact neighborhoods inside the open chamber Q
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L155-L155 | continuity of B_ij
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | finite minimum B_cross
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | finite minimum B
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L154-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | joint continuity is asserted directly for the objective composed with (15)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L4#positivity
KIND: step
TITLE: a zero minimum cannot give contact; finite minima stay positive
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
CONTRACT_ID: lpM:L4#positivity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)
SOURCE_CONCLUSION: a zero minimum would require u = v = 0, which is not feasible because α < 1; so B_ij(I) > 0, and the finite minima B_cross(I), B(I) are positive (I_i > 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#feasible-compact, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:data, lpM:s1:chamber#chamber, lpM:s1:thresholds#actionAxis, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | the minimum is attained at a feasible point
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | D(u) = 0 only at u = 0
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | (0,0) is not feasible when α < 1
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B is a finite minimum of positive numbers
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | I ∈ Q is a direct carrier premise
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the local ratio α = a_i(I)/a_j(I) directly uses the action-axis formula
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the conclusion directly identifies or bounds B_ij(I)
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_cross(I) is directly asserted positive as a finite minimum
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | a zero value of I_i D(u) + I_j D(v) forces u = v = 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L4#competitor
KIND: step
TITLE: competitor (0, 1 - alpha): B_ij <= I_j D(1 - alpha) < I_j, proving (14)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L144-L146
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
CONTRACT_ID: lpM:L4#competitor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)
SOURCE_CONCLUSION: the feasible competitor (0, 1 - α) gives B_ij(I) ≤ I_j D(1 - α) < I_j; since B_{i,i+1}(I) < I_{i+1}, B(I) = min(B_cross(I), I_1) (14)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#feasible-compact, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:data, lpM:s1:chamber#chamber, lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | (0, 1 - α) is feasible
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | the objective at the competitor is I_j D(1 - α)
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | D(1 - α) < 1 for 0 < α
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_ij
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_cross in (14)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B in (14)
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | I ∈ Q is a direct carrier premise
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the local ratio α = a_i(I)/a_j(I) directly uses the action-axis formula
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

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





NODE: lpM:L7
KIND: lemma
TITLE: Lemma 7: a regular planar canonical chart
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L195-L200
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L202-L242
CONTRACT_ID: lpM:L7
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν > 0 (one planet, d = 2)
SOURCE_QUANTIFIERS: for every ν > 0
SOURCE_CONCLUSION: the map (19), with angle read modulo 2π, is a real analytic symplectic diffeomorphism from {I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I} onto the positive-angular-momentum negative-energy planar region; its form is dI ∧ dλ + dx ∧ dy, its energy is -ν^3/(2I^2), its angular momentum is G = I - Γ; it is regular at circular orbits
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#kepler-equation, lpM:L7#chart-formula, lpM:L7#rotated-form, lpM:L7#symplectic, lpM:L7#inverse, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L7@L207-L211 | the eccentric longitude F of (18) and its analytic dependence
EDGE: lpM:L7#chart-formula | docs/tracks/LP/source/MAIN.md#L7@L213-L220 | the chart (19)
EDGE: lpM:L7#rotated-form | docs/tracks/LP/source/MAIN.md#L7@L221-L226 | the energy, angular momentum and eccentricity vector of the image
EDGE: lpM:L7#symplectic | docs/tracks/LP/source/MAIN.md#L7@L228-L238 | the chart is symplectic
EDGE: lpM:L7#inverse | docs/tracks/LP/source/MAIN.md#L7@L240-L242 | the analytic inverse onto the region: a diffeomorphism modulo the angle lattice
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L7@L200-L200 | energy, angular momentum and the negative-energy region are those of (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L7#kepler-equation
KIND: step
TITLE: (18): unique eccentric longitude F, analytic in the data, F(lambda + 2 pi) = F(lambda) + 2 pi
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L202-L210
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L207-L211
CONTRACT_ID: lpM:L7#kepler-equation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: k^2 + l^2 = 1 - s^2 < 1; F - k sin F + l cos F = λ (18) has a unique solution F modulo 2π, since D_F = 1 - k cos F - l sin F ≥ 1 - √(k^2 + l^2) > 0 and the lift increases by 2π per period; the solution is analytic in (I, λ, x, y): the Newton-type fixed-point map is a contraction on small complex disks, its holomorphic iterates converge uniformly; uniqueness patches the branches and gives F(λ + 2π) = F(λ) + 2π
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:ext-holomorphic-limit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:ext-holomorphic-limit | docs/tracks/LP/source/MAIN.md#L7@L211-L211 | uniform limits of the holomorphic iterates are holomorphic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: the convergence of the iterates of a contraction is elementary (geometric series); only the holomorphy of the limit is an external input

NODE: lpM:L7#chart-formula
KIND: display
TITLE: (19): the chart q = a(A c(F) - (k,l)), p = nu A c'(F)/(sqrt(a) D_F)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L213-L220
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L213-L220
CONTRACT_ID: lpM:L7#chart-formula
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: with A = [[1 - l^2/(1+s), kl/(1+s)], [kl/(1+s), 1 - k^2/(1+s)]], c(F) = (cos F, sin F), c'(F) = (-sin F, cos F): q = a(A c(F) - (k,l)), p = (ν/√a) A c'(F)/D_F (19); no perihelion angle is used at zero eccentricity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#kepler-equation
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L7@L219-L219 | F solves (18) and D_F > 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L7#rotated-form
KIND: step
TITLE: (20) for e > 0; energy -nu^3/(2I^2), angular momentum G = I - Gamma, eccentricity vector (k,l); e = 0 by continuity
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L221-L226
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L221-L226
CONTRACT_ID: lpM:L7#rotated-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: for e = √(k^2 + l^2) > 0, (k, l) = e(cos ϖ, sin ϖ), F = E + ϖ, (19) is the rotation of (20) q = a(cos E - e, s sin E), p = ν(-sin E, s cos E)/(√a(1 - e cos E)); multiplication gives energy -ν^3/(2I^2), angular momentum G = I - Γ and eccentricity vector (k, l); the identities extend to e = 0 by continuity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#chart-formula, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#chart-formula | docs/tracks/LP/source/MAIN.md#L7@L221-L224 | (20) is (19) in rotated coordinates
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L7@L226-L226 | energy, angular momentum and eccentricity vector are those of (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L7#symplectic
KIND: step
TITLE: p.dq = I dlambda + Gamma d(-varpi) + d(2Ie sin E): the chart is symplectic
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L228-L238
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L228-L238
CONTRACT_ID: lpM:L7#symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: in the coordinates (20), p·dq = 2e sin E dI + I(1 + e cos E) dE + I sin E de; a varying perihelion rotation adds G dϖ; with ℓ = E - e sin E, p·dq = I dλ + Γ d(-ϖ) + d(2Ie sin E), and (x, y) = √(2Γ)(cos ϖ, -sin ϖ) gives Γ d(-ϖ) = (x dy - y dx)/2; exterior differentiation proves symplecticity on e > 0, and analyticity extends it across e = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#rotated-form, lpM:L7#kepler-equation, lpM:ext-identity-theorem
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#rotated-form | docs/tracks/LP/source/MAIN.md#L7@L229-L232 | the computation is done in the rotated coordinates (20)
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L7@L232-L235 | λ = ℓ + ϖ through (18) with F = E + ϖ
EDGE: lpM:ext-identity-theorem | docs/tracks/LP/source/MAIN.md#L7@L238-L238 | the analytic identity of the two forms extends from e > 0 across e = 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N1 (AMENDMENTS.md L10), fixed in place at MAIN L238: Γ d(-ϖ) = (x dy - y dx)/2

NODE: lpM:L7#inverse
KIND: step
TITLE: analytic inverse: a, I, G from energy and momentum, (k,l) from the eccentricity vector, lambda from (18)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L240-L242
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L240-L242
CONTRACT_ID: lpM:L7#inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: on the positive-angular-momentum negative-energy region: a, I, G from energy and angular momentum; (k, l) as the eccentricity vector, x = k/b_e, y = -l/b_e; A has eigenvalues 1, s > 0 and A^{-1}(q/a + (k,l)) = c(F) (length one by e·q = a(1 - e^2) - ¦q¦); λ from (18) modulo 2π via e^{iλ} = e^{iF} exp[-i(k sin F - l cos F)]; the momentum is recovered uniquely from the positive angular momentum and e = v × (q × v) - q/¦q¦; all inverse formulas are analytic, so the chart is a diffeomorphism onto the region modulo the angle lattice
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:L7#rotated-form, lpM:L7#kepler-equation, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L7@L240-L240 | (11): ¦q × p¦ = I √(1 - e^2), so s = G/I = √(1 - e^2) and k^2 + l^2 = 1 - s^2 recover the eccentricity data
EDGE: lpM:L7#rotated-form | docs/tracks/LP/source/MAIN.md#L7@L240-L240 | the image has energy -ν^3/(2I^2), angular momentum I - Γ and eccentricity vector (k, l), which the inverse inverts
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L7@L240-L241 | λ is recovered from F through (18)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L7@L242-L242 | the eccentricity vector of (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L8
KIND: lemma
TITLE: Lemma 8: a whole-sublevel planar analytic neighborhood (21)-(22)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L246-L255
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L271
CONTRACT_ID: lpM:L8
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data (n, ν, 𝒜, δ) of lpM:s1:data, planar (d = 2); 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}
SOURCE_QUANTIFIERS: there exist r_*, s, b, M > 0 (fixed first); then for every I^0 ∈ 𝓛_δ, with Z_0 = {z = (x_i, y_i)_i : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21)
SOURCE_CONCLUSION: the product chart of Lemma 7 and the exact pulled-back perturbation f are holomorphic on ‖I - I^0‖_∞ < r_*, ¦Im λ¦_∞ < 4s, dist_∞(z, Z_0) < 4b (22); on a slightly smaller domain the chart, momenta, f and all their first derivatives are bounded by M; every Newtonian denominator there has a single holomorphic branch with modulus bounded away from zero; in physical coordinates the chart Hamiltonian equals h(I) + μ f(I, λ, z) without truncation; the ball (21) contains every secular state allowed by the initial margin, with a fixed collar
CONSTANT_SCOPE: r_*, s, b, M depend only on (n, ν, 𝒜, δ) and are chosen before I^0 (and before μ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#empty-case, lpM:L8#shared-tube, lpM:L8#real-margin, lpM:L8#compact-real-set, lpM:L8#newton-extension, lpM:L8#gluing, lpM:L8#denominators, lpM:L8#widths, lpM:L8#exact-split, lpM:L7, lpM:s1:model, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#empty-case | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | the empty case
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | U and r_g
EDGE: lpM:L8#real-margin | docs/tracks/LP/source/MAIN.md#L8@L258-L261 | the real margin, safety and e_*
EDGE: lpM:L8#compact-real-set | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | the compact real set and analyticity of the chart near it
EDGE: lpM:L8#newton-extension | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | the uniform complex extension of the Kepler-equation solution
EDGE: lpM:L8#gluing | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | single-valued uniform complex neighborhood
EDGE: lpM:L8#denominators | docs/tracks/LP/source/MAIN.md#L8@L267-L271 | the Newtonian denominators
EDGE: lpM:L8#widths | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the widths r_*, s, b and the bound M
EDGE: lpM:L8#exact-split | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the exact split h + μ f
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L8@L255-L255 | the product chart of Lemma 7 gives ΣΓ_i = Σ(I_i - G_i) = C on prograde states, so the ball (21) contains every secular state with C ≤ B(I^0) - δ, with collar 3δ/4
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L8@L250-L250 | the perturbation f of (1)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L8@L246-L246 | 𝓛_δ lies in the chamber Q (𝒜 is ordered)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L8@L246-L246 | B occurs in 𝓛_δ and in (21)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.lemma8_complete (KAM/Planetary/StrongAMD/AnalyticDomain/Bounds.lean)
LEAN_NOTE: mechanical docstring match on main (D65; tools/lp_depgraph_lean_refmap.py, reports/lean-ref-map.txt): unique LP:MAIN citation; #print axioms [propext, Classical.choice, Quot.sound]
NOTE: planar (d = 2) lemma; the spatial analogue is Lemma 18 (wave 3). Lemmas 12-14 take its conclusion (with m = n slow pairs here) as a premise; Theorem 15 discharges it (lpM:T15#apply-L14). AMENDED: N2, N3 (AMENDMENTS.md L11, L12).

NODE: lpM:L8#empty-case
KIND: step
TITLE: L_delta empty: no initial state satisfies (6); otherwise L_delta is compact
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L246-L246
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L257
CONTRACT_ID: lpM:L8#empty-case
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21)
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: if 𝓛_δ is empty there is no initial state satisfying (6) (C(0) ≥ 0 and C(0) ≤ B(I^0) - δ force B(I^0) ≥ δ); otherwise 𝓛_δ is compact (a closed subset of the compact 𝓛, B being continuous)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#static, lpM:L4, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | C ≥ 0, so an initial state with (6) has B(I^0) ≥ δ
EDGE: lpM:L4 | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | B is continuous, so 𝓛_δ is closed in the compact 𝓛
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L8#shared-tube
KIND: step
TITLE: compact chamber neighborhood U and width r_g: 4r_g tube in U, Omega_B(4 r_g) <= delta/16
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L257
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L257
CONTRACT_ID: lpM:L8#shared-tube
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: there are a compact chamber neighborhood U of 𝓛_δ and a fixed real action width r_g > 0 such that every 4r_g-tube about 𝓛_δ (sup norm) lies in U and Ω_B(4r_g) ≤ δ/16
CONSTANT_SCOPE: U and r_g depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#shared-U, lpM:L8#empty-case, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | the compact neighborhood U of the compact 𝓛_δ and the modulus Ω_B(r) → 0
EDGE: lpM:L8#empty-case | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | 𝓛_δ is compact
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | U lies in the chamber Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N2 (AMENDMENTS.md L11): this U is the one compact set shared with Lemmas 6 and 14; it contains the closed 4r_g-tube about 𝓛_δ

NODE: lpM:L8#real-margin
KIND: step
TITLE: real tube: sum Gamma_i <= B(I) - 3 delta/16, Gamma_i < I_i, phases safe by Lemma 5, e <= e_* < 1
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L261
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L261
CONTRACT_ID: lpM:L8#real-margin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅; real I with ‖I - I^0‖_∞ ≤ 4r_g and z ∈ Z_0
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (inherited from lpM:L8; the widths are fixed before I^0); for every such real (I, z) and λ
SOURCE_CONCLUSION: Σ_i Γ_i ≤ B(I^0) - δ/4 ≤ B(I) - 3δ/16; consequently Γ_i < I_i with a fixed margin, the corresponding planar phases are safe (a compact nonsingular set of Lemma 5) and the eccentricities are bounded by one fixed e_* < 1
CONSTANT_SCOPE: the margin and e_* depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#shared-tube, lpM:L7, lpM:L5, lpM:L5#perihelion, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/MAIN.md#L8@L258-L259 | Ω_B(4r_g) ≤ δ/16 gives B(I^0) - δ/4 ≤ B(I) - 3δ/16
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | G_i = I_i - Γ_i, so these points are prograde states with C = ΣΓ_i
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | Lemma 5 with U and m = 3δ/16: the phases form a compact nonsingular set (its premise C ≤ B(I) - 3δ/16 is the display)
EDGE: lpM:L5#perihelion | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | √(1 - e_i^2) ≥ m/I_max bounds the eccentricities by e_* < 1
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L8@L259-L259 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L8#compact-real-set
KIND: step
TITLE: the set of (I^0, I, z, lambda) with one closed angle cell is compact; the chart is analytic near it
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L261-L261
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L261-L261
CONTRACT_ID: lpM:L8#compact-real-set
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: the set of (I^0, I, z, λ) with I^0 ∈ 𝓛_δ, real ‖I - I^0‖_∞ ≤ 4r_g, z ∈ Z_0 and λ in one closed period cell is compact, and the chart of Lemma 7 is analytic on an open neighborhood of it; every point of (22) lies within sup distance max(r_*, 4s, 4b) of the compact projection K' of this set
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#real-margin, lpM:L8#shared-tube, lpM:L7
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#real-margin | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | the points lie in the chart's region with a fixed margin
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | the tube is closed and bounded inside U
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | the chart is real analytic on its region
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N3 (AMENDMENTS.md L12): the projection K' over I^0 ∈ 𝓛_δ of this closed set, with r_* ≤ 4r_g

NODE: lpM:L8#newton-extension
KIND: step
TITLE: uniform complex extension of the solution of (18): radii rho, eta, contraction by 1/2
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L263-L263
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L263-L263
CONTRACT_ID: lpM:L8#newton-extension
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: at every point of the compact real set
SOURCE_CONCLUSION: at each real point the derivative of (18) is at least 1 - e_*; fixed radii ρ, η > 0 make the Newton fixed-point map preserve the ρ-disk and contract by 1/2, so its holomorphic iterates converge uniformly to a bounded holomorphic local branch; the positive radicands and 1 + s in (19) stay a fixed distance from zero; complexified real squares are bilinear (w·w), never Hermitian
CONSTANT_SCOPE: ρ and η are fixed (depend only on (n, ν, 𝒜, δ))
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#real-margin, lpM:L7#kepler-equation, lpM:L8#compact-real-set, lpM:ext-holomorphic-limit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#real-margin | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | the derivative bound 1 - e_*
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | the fixed-point map of (18)
EDGE: lpM:L8#compact-real-set | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | uniformity over the compact real set
EDGE: lpM:ext-holomorphic-limit | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | the uniform limit of the holomorphic iterates is holomorphic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L8#gluing
KIND: step
TITLE: glue local extensions on complex balls (identity theorem, finite subcover): single-valued on the angle torus
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L265-L265
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L265-L265
CONTRACT_ID: lpM:L8#gluing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: local extensions on complex balls centered at real points agree on intersections (convex, with a nonempty real part where both equal the real analytic map; power series and the identity theorem); translates of the angle cell patch the same way; a finite subcover of the compact real set with half-sized balls leaves a uniform complex neighborhood; the periodic chart and disturbing function are single-valued on the angle torus, independently of I^0 and μ
CONSTANT_SCOPE: the complex neighborhood is fixed (independent of I^0 and μ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#newton-extension, lpM:L8#compact-real-set, lpM:ext-identity-theorem, lpM:ext-compact-cover
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#newton-extension | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | the local holomorphic extensions
EDGE: lpM:L8#compact-real-set | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | the compact real set covered by finitely many balls
EDGE: lpM:ext-identity-theorem | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | equality on the connected intersection
EDGE: lpM:ext-compact-cover | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | a finite subcover of the compact real set
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L8#denominators
KIND: step
TITLE: Re(w.w) >= d^2/2 for every star and pair denominator; holomorphic square root, reciprocal <= sqrt 2/d
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L255-L255
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L267-L271
CONTRACT_ID: lpM:L8#denominators
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅; local data: d a common real lower bound of ¦q_i¦ and ¦q_i - q_j¦, Q a real upper bound
SOURCE_QUANTIFIERS: for every complex w within η_q of a real w_0
SOURCE_CONCLUSION: ¦w·w - ¦w_0¦^2¦ ≤ 2Qη_q + η_q^2 ≤ d^2/2 after reducing the neighborhood, so Re(w·w) ≥ d^2/2; the square root with positive real part and its reciprocal are holomorphic, the reciprocal bounded by √2/d; this applies to every star and pair denominator
CONSTANT_SCOPE: d, Q and η_q depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5#pair-distances, lpM:L8#real-margin, lpM:L8#gluing, lpM:ext-cauchy-estimates
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5#pair-distances | docs/tracks/LP/source/MAIN.md#L8@L267-L267 | the safe real phases have ¦q_i¦ ≥ d_⋆ and ¦q_i - q_j¦ ≥ d_pair: a common real lower bound d
EDGE: lpM:L8#real-margin | docs/tracks/LP/source/MAIN.md#L8@L267-L267 | the real phases are those of Lemma 5's compact set (bounded lengths Q)
EDGE: lpM:L8#gluing | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the neighborhood being reduced
EDGE: lpM:ext-cauchy-estimates | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the holomorphic square root with positive real part
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L8#widths
KIND: step
TITLE: Cauchy bounds on a smaller compact complex neighborhood; choice of r_*, s, b (r_* <= 4 r_g) and M
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L246-L255
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L271-L271
CONTRACT_ID: lpM:L8#widths
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: the chart and its derivatives are bounded on a smaller compact complex neighborhood (displayed formulas and Cauchy's one-variable estimates); f and its first derivatives have a uniform bound M; r_*, s, b are chosen so that (22) and a small enlargement lie inside this neighborhood
CONSTANT_SCOPE: r_*, s, b, M depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#gluing, lpM:L8#denominators, lpM:ext-cauchy-estimates, lpM:L8#shared-tube
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#gluing | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the uniform complex neighborhood
EDGE: lpM:L8#denominators | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | f's denominators are holomorphic and bounded away from zero
EDGE: lpM:ext-cauchy-estimates | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | Cauchy's one-variable estimates for the derivatives
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/AMENDMENTS.md#N3@L12-L12 | N3: r_* ≤ 4r_g, so (22) lies within the 4r_g-tube data
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N3 (AMENDMENTS.md L12): r_* ≤ 4r_g is stated explicitly

NODE: lpM:L8#exact-split
KIND: step
TITLE: the product chart gives (4): chart Hamiltonian h(I) + mu f, no truncation
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L255-L255
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L271-L271
CONTRACT_ID: lpM:L8#exact-split
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21)
SOURCE_QUANTIFIERS: for every μ > 0 and every point of (22)
SOURCE_CONCLUSION: the product of the Lemma 7 charts turns the Kepler part of (1) into h(I) = -Σ_i ν_i^3/(2I_i^2) of (4), so the chart Hamiltonian is exactly h(I) + μ f(I, λ, z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7, lpM:s1:fast, lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | each planet's Kepler term has energy -ν_i^3/(2I_i^2) in the chart
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | h of (4)
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the splitting (1) H_μ = Σ Kepler terms + μ f
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L9
KIND: lemma
TITLE: Lemma 9: Fourier, Cauchy and commutator estimates in the norm (24)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L279-L296
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L298-L304
CONTRACT_ID: lpM:L9
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; the domains D_ρ (23) and the norm (24) with D = 2n + 2m
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, every loss 0 < σ < ρ - 1, all periodic holomorphic vector fields V, W and every K
SOURCE_CONCLUSION: norms are monotone under restriction; the mean and complementary Fourier projections have norm at most one; ‖[V,W]‖_{ρ-σ} ≤ (2D/σ)‖V‖_ρ‖W‖_ρ (25); the Fourier tail with ¦k¦_1 > K on a strip narrowed by σs has norm at most e^{-σsK}‖V‖_ρ; a uniform supremum bound for V̂ on D_4 gives a finite bound on ‖V‖_3 depending only on that bound, n and s
CONSTANT_SCOPE: the bound on ‖V‖_3 depends only on the supremum bound, n and s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#domains, lpM:L9#norm, lpM:L9#sup-to-fourier, lpM:L9#commutator, lpM:L9#projections-tail
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#domains | docs/tracks/LP/source/MAIN.md#L9@L279-L284 | the domains (23)
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L285-L291 | the norm (24)
EDGE: lpM:L9#sup-to-fourier | docs/tracks/LP/source/MAIN.md#L9@L298-L299 | the supremum-to-Fourier bound
EDGE: lpM:L9#commutator | docs/tracks/LP/source/MAIN.md#L9@L302-L304 | (25)
EDGE: lpM:L9#projections-tail | docs/tracks/LP/source/MAIN.md#L9@L304-L304 | monotonicity, projections and the tail
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L9#domains
KIND: definition
TITLE: the complex domains D_rho (23): action, angle-strip and slow max-norm tube
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L279-L285
PROOF_SOURCE: -
CONTRACT_ID: lpM:L9#domains
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; I^0
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4
SOURCE_CONCLUSION: D_ρ = {‖I - I^0‖_∞ < ρr, ¦Im θ¦_∞ < ρs, dist_∞(z, Z) < ρb} (23); the slow tube uses the maximum norm and Z need not be a polydisk; Hamiltonian fields use the standard constant symplectic form in (I, θ, z), with blocks rs and b^2 after scaling
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L9#norm
KIND: definition
TITLE: scaled components and the weighted Fourier norm (24)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L285-L291
PROOF_SOURCE: -
CONTRACT_ID: lpM:L9#norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the domains D_ρ (lpM:L9#domains); D = 2n + 2m
SOURCE_QUANTIFIERS: for every periodic holomorphic vector field V and 1 ≤ ρ ≤ 4
SOURCE_CONCLUSION: V̂ = (V_I/r, V_θ/s, V_z/b) and ‖V‖_ρ = Σ_{k ∈ ℤ^n} sup_{‖I - I^0‖ < ρr, dist(z,Z) < ρb} ¦V̂_k(I,z)¦_∞ e^{ρs¦k¦_1} (24)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#domains
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#domains | docs/tracks/LP/source/MAIN.md#L9@L289-L289 | the supremum runs over the action and slow parts of D_ρ
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L9#sup-to-fourier
KIND: step
TITLE: contour shift: a sup bound M on width 4s gives ¦V_k¦ <= M e^{-4s¦k¦_1}, hence ¦¦V¦¦_3 <= M((1+e^{-s})/(1-e^{-s}))^n
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L296-L296
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L298-L299
CONTRACT_ID: lpM:L9#sup-to-fourier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: a supremum bound M for V̂ on D_4 gives coefficient bound M e^{-4s¦k¦_1} on the parameter domain of D_3 (limits from narrower contours), and summing at width 3s gives ‖V‖_3 ≤ M Σ_k e^{-s¦k¦_1} = M((1 + e^{-s})/(1 - e^{-s}))^n
CONSTANT_SCOPE: the bound depends only on M, n and s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:ext-fourier-contour, lpM:L9#norm, lpM:L9#domains
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:ext-fourier-contour | docs/tracks/LP/source/MAIN.md#L9@L298-L298 | Fourier coefficients as torus integrals and the contour shift
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L299-L299 | summing the coefficients in the norm (24)
EDGE: lpM:L9#domains | docs/tracks/LP/source/MAIN.md#L9@L298-L298 | the strip of width 4s of D_4
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L9#banach-algebra
KIND: step
TITLE: products have convolution coefficients: the Banach-algebra estimate
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L300-L300
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L300-L300
CONTRACT_ID: lpM:L9#banach-algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: products of Fourier series have convolution coefficients and ¦k + l¦_1 ≤ ¦k¦_1 + ¦l¦_1, so the weighted norm is submultiplicative; absolute convergence on smaller domains justifies multiplication and differentiation
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#norm
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L300-L300 | the weights e^{ρs¦k¦_1} of (24)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L9#cauchy-derivative
KIND: step
TITLE: Cauchy: derivative bound 1/sigma in scaled action and slow coordinates; angle factor 1/(e sigma)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L302-L303
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L302-L303
CONTRACT_ID: lpM:L9#cauchy-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: a complex disk of radius σr or σb about a point of D_{ρ-σ} lies in D_ρ (triangle inequality for dist to Z), so Cauchy's formula gives derivative bound 1/σ in scaled coordinates; for angles s¦k_j¦e^{-σs¦k¦_1} ≤ 1/(eσ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:ext-cauchy-estimates, lpM:L9#domains, lpM:L9#norm
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:ext-cauchy-estimates | docs/tracks/LP/source/MAIN.md#L9@L302-L302 | Cauchy's formula on the disks
EDGE: lpM:L9#domains | docs/tracks/LP/source/MAIN.md#L9@L302-L302 | the disks lie in the larger tube
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L303-L303 | the angle derivative acts on the weights of (24)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L9#commutator
KIND: display
TITLE: (25): ¦¦[V,W]¦¦_{rho-sigma} <= (2D/sigma) ¦¦V¦¦_rho ¦¦W¦¦_rho
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L292-L295
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L302-L304
CONTRACT_ID: lpM:L9#commutator
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: each of the D terms in a component of DV W - DW V is bounded by the product of the norms divided by σ, giving ‖[V,W]‖_{ρ-σ} ≤ (2D/σ)‖V‖_ρ‖W‖_ρ (25)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#cauchy-derivative, lpM:L9#banach-algebra
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#cauchy-derivative | docs/tracks/LP/source/MAIN.md#L9@L304-L304 | the derivative bounds 1/σ and 1/(eσ)
EDGE: lpM:L9#banach-algebra | docs/tracks/LP/source/MAIN.md#L9@L304-L304 | products of the derivative and the field
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L9#projections-tail
KIND: step
TITLE: monotonicity; mean and complementary projections have norm <= 1; tail bound e^{-sigma s K}
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L292-L296
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L304-L304
CONTRACT_ID: lpM:L9#projections-tail
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: norms are monotone under restriction; removing the zero coefficient proves that the mean and complementary Fourier projections have norm at most one; extracting e^{-σsK} bounds the tail with ¦k¦_1 > K on the strip narrowed by σs by e^{-σsK}‖V‖_ρ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#norm
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L304-L304 | the norm (24) is a weighted sum over k
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L10
KIND: lemma
TITLE: Lemma 10: cohomological equation (26) and a controlled Lie step (27)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L308-L321
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L323-L349
CONTRACT_ID: lpM:L10
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of lpM:L9 (n, m, Z, r, b, s); ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ
SOURCE_QUANTIFIERS: for every such H and every loss 0 < σ < ρ - 1; constants c_D, B_D > 0 depending only on D are fixed first
SOURCE_CONCLUSION: there is a Hamiltonian generator χ, real on real points, with ω·∂_θχ = f - ⟨f⟩ and ‖X_χ‖_{ρ-σ/2} ≤ Aσ^{-τ}E =: u, A = γ^{-1} max{1, (2τ/(es))^τ} (26); if u/σ ≤ c_D its time-one map φ is holomorphic, real, symplectic and periodic-equivariant on D_{ρ-σ}, with H∘φ = h_0 + g + ⟨f⟩ + f_+ and ‖X_{f_+}‖_{ρ-σ} ≤ B_D (u/σ)(G + E) (27); the map and the negative-time map move points by at most u in scaled coordinates where the collar is available, their derivatives differ from the identity by at most a dimension constant times u/σ on a further half-collar, and they are mutual inverses on their common inner domain
CONSTANT_SCOPE: c_D, B_D depend only on D; the constants do not depend on r, b, Z, I^0 or the coefficients of the scaled symplectic form
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10#homological, lpM:L10#flow-existence, lpM:L10#remainder, lpM:L9#norm, lpM:s1:dioph
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10#homological | docs/tracks/LP/source/MAIN.md#L10@L323-L328 | the generator χ and (26)
EDGE: lpM:L10#flow-existence | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | the time-one map, its displacement, inverse and symplecticity
EDGE: lpM:L10#remainder | docs/tracks/LP/source/MAIN.md#L10@L342-L349 | the exact remainder (29) and (27)
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L10@L308-L308 | the norms ‖X_f‖_ρ of (24)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L10@L308-L308 | ω satisfies the Diophantine condition (5)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L10#homological
KIND: step
TITLE: chi_k = f_k/(i k.omega): (26), the scalar series and reality
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L309-L314
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L323-L328
CONTRACT_ID: lpM:L10#homological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10)
SOURCE_CONCLUSION: χ_0 = 0 and χ_k = f_k/(ik·ω) for k ≠ 0; the Fourier coefficients of X_χ are those of X_f divided by ik·ω; with ¦k¦_1^τ e^{-σs¦k¦_1/2} ≤ (2τ/(eσs))^τ this gives (26); the scalar series exists (a fast action component of X_f equals -ik_j f_k); f_{-k} = conj(f_k) gives the same relation for χ (reality)
CONSTANT_SCOPE: A = γ^{-1} max{1, (2τ/(es))^τ}
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:dioph, lpM:L9#norm
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L10@L323-L323 | (5): ¦ik·ω¦ ≥ γ¦k¦_1^{-τ} for k ≠ 0
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L10@L325-L325 | the coefficients are weighted as in (24) on the narrowed strip
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L10#lie-series-bound
KIND: display
TITLE: (28): (1/j!)¦¦ad_Y^j V¦¦_{rho-eta} <= (2eDu/eta)^j ¦¦V¦¦_rho
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L330-L336
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L330-L336
CONTRACT_ID: lpM:L10#lie-series-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1; a holomorphic field Y of norm u on a larger domain; a collar η
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10); for every j ≥ 1
SOURCE_CONCLUSION: repeated application of (25), dividing the collar η into j equal parts, gives (1/j!)‖ad_Y^j V‖_{ρ-η} ≤ (j^j/j!)(2Du/η)^j‖V‖_ρ ≤ (2eDu/η)^j‖V‖_ρ (28), using j! ≥ (j/e)^j; the Lie series converges when 2eDu/η < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#commutator
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#commutator | docs/tracks/LP/source/MAIN.md#L10@L331-L331 | (25) applied j times with loss η/j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L10#lie-flow-identification
KIND: step
TITLE: the Lie series represents the pullback by the flow; exact scalar identity
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L315-L321
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L336-L338
CONTRACT_ID: lpM:L10#lie-flow-identification
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1; 4eDu/σ ≤ 1/4
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10)
SOURCE_CONCLUSION: the Lie series of the pullback converges and equals the pullback by the actual flow (the flow solves the integral equation, its derivative the variational equation, and differentiating the pullback gives the commutator equation); the scalar series converges after its first bracket (a scalar bracket is bounded by D max(rs, b^2)‖X_F‖‖X_χ‖); trajectories from D_{ρ-σ} stay in D_{ρ-3σ/4}, and the Taylor remainders have geometric ratio ≤ 8eDu/σ ≤ 1/2, proving the exact scalar identity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10#lie-series-bound, lpM:L10#flow-existence
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10#lie-series-bound | docs/tracks/LP/source/MAIN.md#L10@L336-L338 | (28) bounds the iterated brackets and the remainders
EDGE: lpM:L10#flow-existence | docs/tracks/LP/source/MAIN.md#L10@L336-L338 | the actual flow exists and moves points by at most u
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: SOURCE_GAP: AMENDED N5 (AMENDMENTS.md L14): MAIN only sketches the flow existence, the Lie-series identification and the choice of c_D; they matter only for the optional packages 9-11 (route lpM:L14#route-L12), not for the Lean route through Lemma 13

NODE: lpM:L10#flow-existence
KIND: step
TITLE: the flow exists for ¦t¦ <= 1: contraction on paths, holomorphy, inverse, reality, displacement, symplecticity
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L315-L321
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L340-L340
CONTRACT_ID: lpM:L10#flow-existence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1; u a sufficiently small multiple of the collar
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10); both signs of time up to one
SOURCE_CONCLUSION: in a scaled ball about any starting point of the inner domain, Cauchy bounds DY by a dimension constant times u/η; the integral map on continuous paths stays in the ball and contracts, its iterates converge uniformly (holomorphic dependence, also for complex initial values); uniqueness gives the inverse, reality and lattice equivariance; displacement ≤ u and ‖Dφ - 1‖ ≤ e^{C_D u/η} - 1 ≤ 2C_D u/η; (DY)^T Ω + Ω DY = 0 gives symplecticity, for any constant nondegenerate Ω; c_D is decreased so that these estimates hold
CONSTANT_SCOPE: C_D and c_D depend only on D
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10#homological, lpM:ext-cauchy-estimates, lpM:ext-picard, lpM:ext-holomorphic-limit, lpM:ext-gronwall
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10#homological | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | the generator χ with ‖X_χ‖ ≤ u
EDGE: lpM:ext-cauchy-estimates | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | Cauchy's estimate for DY
EDGE: lpM:ext-picard | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | the integral map on continuous paths is a contraction (Picard iteration)
EDGE: lpM:ext-holomorphic-limit | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | uniform limits of the holomorphic iterates are holomorphic
EDGE: lpM:ext-gronwall | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | uniqueness of the flow gives the inverse, reality and equivariance
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: SOURCE_GAP: AMENDED N5 (AMENDMENTS.md L14): MAIN only sketches the flow existence, the Lie-series identification and the choice of c_D; they matter only for the optional packages 9-11 (route lpM:L14#route-L12), not for the Lean route through Lemma 13

NODE: lpM:L10#remainder
KIND: step
TITLE: L_chi h_0 = -f^osc and the exact remainder (29); (27) with B_D = 16eD
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L316-L320
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L342-L349
CONTRACT_ID: lpM:L10#remainder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1; v = 4eDu/σ ≤ 1/4
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10)
SOURCE_CONCLUSION: with L_χF = {F, χ}, L_χ h_0 = -(f - ⟨f⟩); the exact remainder is f_+ = Σ_{j≥1} L_χ^j(g + f)/j! - Σ_{j≥1} L_χ^j f^osc/(j+1)! (29); each bracket is a vector-field commutator, so (28) with η = σ/2 bounds the two sums by v(1 - v)^{-1}(G + 2E) ≤ 4v(G + E), proving (27) with B_D = 16eD; the field X_{h_0} disappears through the homological identity
CONSTANT_SCOPE: B_D = 16eD
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10#homological, lpM:L10#lie-series-bound, lpM:L10#lie-flow-identification
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10#homological | docs/tracks/LP/source/MAIN.md#L10@L342-L342 | ω·∂_θχ = f - ⟨f⟩ gives L_χ h_0 = -f^osc
EDGE: lpM:L10#lie-series-bound | docs/tracks/LP/source/MAIN.md#L10@L347-L347 | (28) with η = σ/2
EDGE: lpM:L10#lie-flow-identification | docs/tracks/LP/source/MAIN.md#L10@L349-L349 | H∘φ equals the Lie series (exact scalar identity)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N5 (AMENDMENTS.md L14): c_D is only implicit ('decreased to satisfy the flow estimates')

NODE: lpM:L11
KIND: lemma
TITLE: Lemma 11: exponential normal form on the full slow set (30)-(31)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L353-L363
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L365-L379
CONTRACT_ID: lpM:L11
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1
SOURCE_QUANTIFIERS: a number q_D > 0 depending only on D is fixed first; then for every such H, ε, N with A ε N^{τ+1} ≤ q_D (30)
SOURCE_CONCLUSION: there is a real holomorphic symplectic map Φ : D_2 → D_3 with H∘Φ = h_0 + Z + R, ∂_θZ = 0, ‖X_R‖_2 ≤ ε2^{-N}, ‖X_Z‖_2 ≤ 2ε (31); its scaled displacement is at most 1/16; its inverse exists on D_{3/2}, takes values in D_2 and has the same displacement bound, so the two action-coordinate errors are at most r/16; this holds on the entire tube around Z, with no restriction on the slow dynamics
CONSTANT_SCOPE: q_D depends only on D
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#qD-choice, lpM:L11#induction, lpM:L11#composition, lpM:L11#inverse
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#qD-choice | docs/tracks/LP/source/MAIN.md#L11@L371-L375 | q_D and the validity of each step under (30)
EDGE: lpM:L11#induction | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the estimates E_j ≤ ε2^{-j}, ‖X_{g_j}‖ ≤ 2ε
EDGE: lpM:L11#composition | docs/tracks/LP/source/MAIN.md#L11@L375-L379 | Φ, (31) and the displacement 1/32 < 1/16
EDGE: lpM:L11#inverse | docs/tracks/LP/source/MAIN.md#L11@L379-L379 | the inverse on D_{3/2}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L11#step-estimate
KIND: step
TITLE: one Lie step with loss 1/N: u_j <= A N^tau eps 2^{-j}, E_{j+1} <= 3 B_D A eps N^{tau+1} E_j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L365-L370
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L365-L370
CONTRACT_ID: lpM:L11#step-estimate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F; E_j ≤ ε2^{-j}, G_j ≤ 2ε at step j
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11); every j < N
SOURCE_CONCLUSION: Lemma 10 with σ = 1/N on ρ_j gives u_j ≤ A N^τ ε 2^{-j} and E_{j+1} ≤ 3B_D A ε N^{τ+1} E_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L11@L365-L370 | Lemma 10 with loss σ = 1/N on D_{ρ_j}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L11#qD-choice
KIND: step
TITLE: q_D = min(c_D, 1/(6 B_D), 1/64): (30) validates every step and halves E_j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L371-L374
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L371-L375
CONTRACT_ID: lpM:L11#qD-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11)
SOURCE_CONCLUSION: with q_D = min(c_D, 1/(6B_D), 1/64), condition (30) gives u_j/σ ≤ c_D (the step is valid) and E_{j+1} ≤ E_j/2
CONSTANT_SCOPE: q_D depends only on D
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#step-estimate, lpM:L10
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#step-estimate | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the step estimates
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L11@L373-L373 | the constants c_D and B_D of Lemma 10
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L11#induction
KIND: step
TITLE: g_{j+1} = g_j + <f_j>: ¦X_g¦ <= 2 eps, angle independent; induction on j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L375-L375
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L375-L375
CONTRACT_ID: lpM:L11#induction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11); every j ≤ N
SOURCE_CONCLUSION: g_{j+1} = g_j + ⟨f_j⟩ has norm at most Σ_{l<j+1} E_l ≤ 2ε and stays angle independent; induction proves E_j ≤ ε2^{-j}, G_j ≤ 2ε for all j ≤ N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#qD-choice, lpM:L9#projections-tail, lpM:L11#step-estimate
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#qD-choice | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | E_{j+1} ≤ E_j/2 under (30)
EDGE: lpM:L9#projections-tail | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the mean projection has norm at most one: ‖⟨f_l⟩‖ ≤ E_l
EDGE: lpM:L11#step-estimate | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the estimates at each step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L11#composition
KIND: step
TITLE: Phi = phi_0 o ... o phi_{N-1}: (31) with Z = g_N, R = f_N; displacement <= 2 q_D/N <= 1/32
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L358-L363
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L375-L379
CONTRACT_ID: lpM:L11#composition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11)
SOURCE_CONCLUSION: composing the actual flow maps gives Φ = φ_0∘...∘φ_{N-1} and the exact identity (31) with Z = g_N, R = f_N; the telescoped displacement is Σ_{j<N} u_j ≤ 2AεN^τ ≤ 2q_D/N ≤ 1/32 < 1/16; each factor maps its smaller domain into its larger one, so Φ : D_2 → D_3 is defined, injective and symplectic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#induction, lpM:L10
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#induction | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the estimates of every step
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | each φ_j is a holomorphic real symplectic time-one map with displacement u_j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L11#inverse
KIND: step
TITLE: the inverse on D_{3/2} by negative-time flows in reverse order, values in D_2
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L363-L363
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L379-L379
CONTRACT_ID: lpM:L11#inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11)
SOURCE_CONCLUSION: for an initial point in D_{3/2}, the negative-time flows in reverse composition order keep every intermediate point within scaled distance 1/32 of D_{3/2}, hence in D_2, inside every factor's domain; this constructs the inverse with the same telescoped bound, and the compositions are identities by uniqueness of each flow
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#composition, lpM:L10
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#composition | docs/tracks/LP/source/MAIN.md#L11@L379-L379 | the telescoped displacement 1/32
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L11@L379-L379 | the negative-time maps are inverses of the time-one maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L12
KIND: lemma
TITLE: Lemma 12: planetary scaling, exponential time and the drift (34)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L383-L399
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L405-L427
CONTRACT_ID: lpM:L12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the uniform chart-domain statement of Lemma 8 holds with m canonical slow pairs; I^0 satisfies (5)
SOURCE_QUANTIFIERS: there are M_1, κ, μ_1, c > 0 (uniform in I^0); then for every 0 < μ ≤ μ_1, with r = √μ, a = 1/(2(τ+1)), N = ⌊κμ^{-a}⌋ ≥ 1, ε = M_1√μ, h_0 = h(I^0) + ω(I^0)·(I - I^0) (32), and every portion of an original solution
SOURCE_CONCLUSION: the normal form of Lemma 11 exists on the entire corresponding slow tube and H_μ∘Φ = h(J) + 𝒵(J, z) + R(J, θ, z), ∂_θ𝒵 = 0, ¦J̇¦_∞ ≤ rε2^{-N} along every transformed solution in D_2 (33); with T_μ = exp(cμ^{-a}), any portion of an original solution in D_1 of duration at most T_μ starting at action I^0 has ‖I(t) - I^0‖_∞ ≤ r/4 (34)
CONSTANT_SCOPE: M_1, κ, μ_1, c are uniform in I^0 and depend only on the fixed chart data and (γ, τ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L12#perturbation-size, lpM:L12#kappa-choice, lpM:L12#time-choice, lpM:L12#normal-form, lpM:L12#drift, lpM:s1:dioph, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L12#perturbation-size | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | ‖X_{H_μ - h_0}‖_3 ≤ M_1√μ
EDGE: lpM:L12#kappa-choice | docs/tracks/LP/source/MAIN.md#L12@L407-L412 | κ, (36) implies (30), N and ε
EDGE: lpM:L12#time-choice | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | c and T_μ ≤ 2^{N/2}
EDGE: lpM:L12#normal-form | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | (33)
EDGE: lpM:L12#drift | docs/tracks/LP/source/MAIN.md#L12@L414-L420 | (34)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L12@L383-L383 | I^0 satisfies (5)
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L12@L388-L388 | h and ω of (4) in h_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: Q5 (ruling root-b8) and AMENDED: N4 (AMENDMENTS.md L13): (35) (L400-L403, proof L420-L425) is a remark, not a formal dependency, and is omitted from these source fields; Lemma 8's conclusion is a premise (discharged at the application); alternative supplier of the stopped drift (N7): route lpM:L14#route-L12

NODE: lpM:L12#perturbation-size
KIND: step
TITLE: ¦¦X_{H_mu - h_0}¦¦_3 <= M_1 sqrt(mu): h - h_0 of size r, mu f of size mu/r + mu/s + mu/b
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L383-L389
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L405-L405
CONTRACT_ID: lpM:L12#perturbation-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32)
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12)
SOURCE_CONCLUSION: after decreasing the widths of Lemma 8 (D_4 closures with uniform first-derivative bounds) and restricting μ_1 so that 4r < r_* and r ≤ 1, the scaled field of h - h_0 has only angle components (ω(I) - ω(I^0))/s = O(r), the scaled components of X_{μf} are O(μ/r + μ/s + μ/b), both O(√μ); the supremum-to-Fourier estimate of Lemma 9 (losing the fixed strip between D_4 and D_3) gives ‖X_{H_μ - h_0}‖_3 ≤ M_1√μ
CONSTANT_SCOPE: M_1 depends only on the fixed chart data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9, lpM:s1:fast, lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9 | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | the supremum-to-Fourier estimate of Lemma 9, from D_4 to D_3
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | ω(I) - ω(I^0) is O(r) on the action tube
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | H_μ = h + μ f in the chart (the perturbation f)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L12#kappa-choice
KIND: step
TITLE: (36): A M_1 kappa^{tau+1} <= q_D/2 implies (30); N >= kappa mu^{-a}/2, eps <= 1/8
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L407-L412
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L407-L412
CONTRACT_ID: lpM:L12#kappa-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32)
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12)
SOURCE_CONCLUSION: choose κ > 0 with A M_1 κ^{τ+1} ≤ q_D/2 and 4L_ω κ^{τ+1} ≤ γ/2 (36), L_ω a complex Lipschitz bound of ω on the action neighborhood (∂_{I_i}ω_i = -3ν_i^3/I_i^4); since a(τ+1) = 1/2, (36) implies (30); decreasing μ_1 gives κμ^{-a} ≥ 2, N ≥ κμ^{-a}/2 and ε ≤ 1/8
CONSTANT_SCOPE: κ depends only on M_1, A, q_D, L_ω and γ (hence on the chart data and (γ, τ))
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L12#perturbation-size, lpM:L11, lpM:L10, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L12#perturbation-size | docs/tracks/LP/source/MAIN.md#L12@L408-L408 | M_1
EDGE: lpM:L11 | docs/tracks/LP/source/MAIN.md#L12@L412-L412 | (30) and q_D
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L12@L408-L408 | A of (26)
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L12@L412-L412 | ω and its Lipschitz bound L_ω
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: the second restriction of (36) serves only (35), which Q5/N4 omit

NODE: lpM:L12#time-choice
KIND: step
TITLE: c = (log 2) kappa/4, so T_mu = exp(c mu^{-a}) <= 2^{N/2}
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L396-L396
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L414
CONTRACT_ID: lpM:L12#time-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32)
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12)
SOURCE_CONCLUSION: with c = (log 2)κ/4 and N ≥ κμ^{-a}/2, T_μ = exp(cμ^{-a}) ≤ 2^{N/2}
CONSTANT_SCOPE: c depends only on κ
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L12#kappa-choice
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L12#kappa-choice | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | N ≥ κμ^{-a}/2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L12#normal-form
KIND: step
TITLE: Lemma 11 with eps = M_1 sqrt(mu), N; Z := h_0 - h + Z gives (33) and ¦dJ/dt¦ <= r eps 2^{-N}
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L390-L395
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L414
CONTRACT_ID: lpM:L12#normal-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32)
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12)
SOURCE_CONCLUSION: Lemma 11 applies on the entire slow tube with ε, N of (32); 𝒵 := h_0 - h + Z is independent of θ, so (31) becomes (33), and ‖X_R‖_2 ≤ ε2^{-N} gives ¦J̇¦_∞ ≤ rε2^{-N} along every transformed solution in D_2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11, lpM:L12#kappa-choice, lpM:L12#perturbation-size
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11 | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | the normal form Φ and (31)
EDGE: lpM:L12#kappa-choice | docs/tracks/LP/source/MAIN.md#L12@L412-L412 | (30) holds
EDGE: lpM:L12#perturbation-size | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | ‖X_F‖_3 ≤ ε with F = H_μ - h_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L12#drift
KIND: step
TITLE: (34): transformed solution in D_2, integrate (33), errors r/16 + r/16: ¦¦I(t) - I^0¦¦ <= r/4
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L396-L399
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L420
CONTRACT_ID: lpM:L12#drift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32); a portion of an original solution in D_1 of duration ≤ T_μ starting at I^0
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12); both signs of t
SOURCE_CONCLUSION: the inverse of Lemma 11 maps the original solution to a transformed solution inside D_2, which solves the transformed Hamilton equations by symplecticity; integrating (33) with the forward error at t and the inverse error at 0 gives ‖I(t) - I^0‖_∞ ≤ r/16 + rε¦t¦2^{-N} + r/16 ≤ r/8 + rε2^{-N/2} ≤ r/4, for both signs of t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L12#normal-form, lpM:L11, lpM:L12#time-choice
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L12#normal-form | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | (33) along transformed solutions
EDGE: lpM:L11 | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | the inverse on D_{3/2} and the action errors ≤ r/16
EDGE: lpM:L12#time-choice | docs/tracks/LP/source/MAIN.md#L12@L418-L418 | ¦t¦ ≤ T_μ ≤ 2^{N/2}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L13
KIND: lemma
TITLE: Lemma 13: checked reuse of the repository's finite-cutoff engine (nonresonant)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L431-L431
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L433-L464
CONTRACT_ID: lpM:L13
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfies (5)
SOURCE_QUANTIFIERS: for every fixed D_0 > 0 there are κ_1, c_1 > 0 and a smallness threshold for μ (uniform in I^0); then for every small μ > 0, with r = D_0√μ, K = ⌊κ_1μ^{-a}⌋, and every physical orbit starting at action I^0
SOURCE_CONCLUSION: the data can be fed to KAM.Nekhoroshev.nonresonant with the full center-dependent slow ball S = (21), radius r = D_0√μ, cutoff K ≍ μ^{-a} and a fixed slow collar; its stopped action estimate gives ‖I(t) - I^0‖_∞ ≤ r/2 for ¦t¦ ≤ exp(c_1μ^{-a}) provided the physical slow coordinates belong to S through the queried time (the same exponent a as Lemma 12)
CONSTANT_SCOPE: κ_1, c_1 and the μ threshold depend only on the fixed chart data, (γ, τ) and D_0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L13#interface, lpM:L13#period-one, lpM:L13#numeric-hypotheses, lpM:L13#structural-hypotheses, lpM:L13#conclusion, lpM:s1:dioph
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L13#interface | docs/tracks/LP/source/MAIN.md#L13@L433-L433 | the slow set S of nonresonant is arbitrary: take the ball (21)
EDGE: lpM:L13#period-one | docs/tracks/LP/source/MAIN.md#L13@L435-L440 | the period-one conversion
EDGE: lpM:L13#numeric-hypotheses | docs/tracks/LP/source/MAIN.md#L13@L442-L457 | the numeric hypotheses (37)
EDGE: lpM:L13#structural-hypotheses | docs/tracks/LP/source/MAIN.md#L13@L458-L458 | the structural hypotheses
EDGE: lpM:L13#conclusion | docs/tracks/LP/source/MAIN.md#L13@L460-L464 | the drift ≤ r/2 through (38)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L13@L431-L431 | I^0 satisfies (5) (the nonresonance at I^0)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: Lemma 8's conclusion is a premise (discharged at the application); alternative supplier of the stopped drift (N7): route lpM:L14#route-L13, the Lean route. The repository citation (L433) is consumed only through the IMPORTED node N:bpN:p11:nonresonant. AMENDED: N6 (AMENDMENTS.md L15): widths 2πs_1 < 4s with a convergence margin, w < 4b, D_0√μ < r_*, J the stopped interval of Lemma 14; stopped radius r = D_0√μ and improvement to r/2

NODE: lpM:L13#interface
KIND: step
TITLE: nonresonant's real slow set S is arbitrary: take S = the closed ball (21)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L431-L431
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L433-L433
CONTRACT_ID: lpM:L13#interface
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13)
SOURCE_CONCLUSION: the normal-form input of nonresonant leaves the real slow set S arbitrary; S is taken to be the closed ball (21), not a neighborhood of the starting secular point
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p11:nonresonant
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p11:nonresonant | docs/tracks/LP/source/MAIN.md#L13@L433-L433 | the interface of the imported theorem (arbitrary slow set S)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L13#period-one
KIND: step
TITLE: theta = lambda/(2 pi), slow rescaling ell = w/r, H-hat = H/(2 pi); bracket 2 pi/ell^2; same equations and time
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L435-L440
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L435-L440
CONTRACT_ID: lpM:L13#period-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋; local data θ = λ/(2π), ℓ = w/r, z̃ = z/ℓ
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13)
SOURCE_CONCLUSION: Ĥ(θ, I, z̃) = H(2πθ, I, ℓz̃)/(2π) with the weighted slow bracket coefficient c_s = 2π/ℓ^2 gives θ̇ = H_I/(2π), İ = -H_λ, dz̃/dt = J H_z/ℓ: exactly the original equations, in unchanged time; the unperturbed frequencies are ω/(2π); (ξ, η) = (x, -y) planar and (u, -v) for the spatial node pair give the repository's slow bracket
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L13@L440-L440 | the symplectic form Σ dp ∧ dq and ι_{X_H}Ω = -dH of (1)
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L13@L440-L440 | the frequencies ω of (4)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L13#numeric-hypotheses
KIND: step
TITLE: (37): K L r <= alpha/2, eps <= alpha r/(256 K), 64 pi m s_1 r <= w^2, 2 pi K s_1 >= 6
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L442-L452
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L442-L457
CONTRACT_ID: lpM:L13#numeric-hypotheses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋; fixed period-one strip s_1 > 0 and slow width w > 0; p = q = 2
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13)
SOURCE_CONCLUSION: the scalar Fourier bound ε = M_2μ holds uniformly (the contour estimate of Lemma 9 applied to f/(2π)); with α = γK^{-τ}/(2π), K = ⌊κ_1μ^{-a}⌋, r = D_0√μ, the non-geometric numeric hypotheses of ExtNFHyp and nonresonant are KLr ≤ α/2, ε ≤ αr/(256K), 64πm s_1 r ≤ w^2, 2πKs_1 ≥ 6 (37); the first two follow from LD_0κ_1^{τ+1} ≤ γ/(4π) and M_2κ_1^{τ+1} ≤ γD_0/(512π), the last two by decreasing μ_0
CONSTANT_SCOPE: κ_1 depends only on L, M_2, γ, τ and D_0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9, lpM:L13#period-one, lpM:s1:dioph, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9 | docs/tracks/LP/source/MAIN.md#L13@L442-L442 | the contour estimate of Lemma 9 applied to f/(2π) gives ε = M_2μ
EDGE: lpM:L13#period-one | docs/tracks/LP/source/MAIN.md#L13@L442-L442 | the period-one Hamiltonian f/(2π) and frequencies ω/(2π)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L13@L444-L444 | (5) gives ¦k·ω(I^0)/(2π)¦ ≥ α for 0 < ¦k¦_1 ≤ K
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L13@L442-L442 | L bounds the complex frequency derivative of h/(2π)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N6 (AMENDMENTS.md L15): widths 2πs_1 < 4s with a convergence margin, w < 4b, D_0√μ < r_*, J the stopped interval of Lemma 14; stopped radius r = D_0√μ and improvement to r/2

NODE: lpM:L13#structural-hypotheses
KIND: step
TITLE: holomorphy, reality, periodicity, Fourier norm, widths, module {0}, tube inside (22), orbit-field equality
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L458-L458
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L458-L458
CONTRACT_ID: lpM:L13#structural-hypotheses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13)
SOURCE_CONCLUSION: holomorphy, reality, periodicity, the weighted Fourier norm, positivity of widths and perturbation bound, and the dimension hypotheses follow from Lemma 8's data and n ≥ 2, m ≥ 1; the nonresonance module is {0} (symmetric); the rescaled slow tube has physical width w (ℓr = w), not shrinking with μ; the finite action tube lies in (22) for small μ; the computed equations give the literal orbit-field equality; the initial fast action is the center
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L13#period-one, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L13#period-one | docs/tracks/LP/source/MAIN.md#L13@L458-L458 | the computed equations in the new coordinates
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L13@L458-L458 | n ≥ 2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L13#conclusion
KIND: step
TITLE: (38): drift <= r/2 through (s_1 r/(5 eps)) exp(2 pi K s_1/6) >= exp(c_1 mu^{-a}) under stopped slow membership
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L460-L463
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L460-L464
CONTRACT_ID: lpM:L13#conclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13); every queried time t_1
SOURCE_CONCLUSION: nonresonant gives ‖I(t) - I^0‖_∞ ≤ r/2 through (s_1r/(5ε)) exp(2πKs_1/6) (38), provided the physical slow coordinates belong to S up to the queried time; since K ≥ κ_1μ^{-a}/2 for small μ, (38) exceeds exp(c_1μ^{-a}) for a fixed c_1 > 0; the stopped membership is discharged by Lemma 14
CONSTANT_SCOPE: c_1 depends only on κ_1, s_1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p11:nonresonant, lpM:L13#numeric-hypotheses, lpM:L13#structural-hypotheses, lpM:L13#interface
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p11:nonresonant | docs/tracks/LP/source/MAIN.md#L13@L460-L460 | the conclusion of nonresonant: drift ≤ r/2 through T_nr = (s_1r/(5ε))e^{κ/6}
EDGE: lpM:L13#numeric-hypotheses | docs/tracks/LP/source/MAIN.md#L13@L460-L460 | (37) supplies its numeric hypotheses
EDGE: lpM:L13#structural-hypotheses | docs/tracks/LP/source/MAIN.md#L13@L460-L460 | its structural hypotheses
EDGE: lpM:L13#interface | docs/tracks/LP/source/MAIN.md#L13@L460-L460 | S is the ball (21)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: the closing sentences on nnf_disp_radius (slow displacement ≤ w/2^{10}) and on the independent paper proof are a check, not a premise of the drift conclusion; no edge

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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
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
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: N:bpN:p11:nonresonant
KIND: external
TITLE: [N] Nonresonant stability in the extended phase space (KAM.Nekhoroshev.nonresonant)
STATEMENT_SOURCE: blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L65-L68
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p11:nonresonant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r,s,K_a,alpha>0, L>=0, p>1, q=p/(p-1), kappa=2 pi K_a s>=6; r=r_B; h holomorphic on V_r(I_c), real on real points; ¦k.omega(I_c)¦>=alpha for 0<¦k¦_1<=K_a (cond-nr, Lambda={0}), cond-L with L, K_a L r<=alpha/p; (SL); f in O(r,s)^{e,R}, ¦f¦<=eps with eps>0, eps<=alpha r/(2^7 q K_a); H=h+f; T_nr=(s r/(5 eps))e^{kappa/6}
SOURCE_QUANTIFIERS: r,s,K_a,alpha,L,p; h; f; eps; F; J; y; t_1
SOURCE_CONCLUSION: for every F with F=X^c_{H^R} on W^e_r, J containing 0, y with y'=F(y) on J, y(0)=(theta_0,I_c,x-tilde_0), x-tilde_0 in S-tilde, and t_1 in J with ¦t_1¦<=T_nr and x-tilde(u) in S-tilde between 0 and t_1: ¦I(u)-I_c¦<=r/2 between 0 and t_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-N graph, node bpN:p11:nonresonant (there KIND proposition, contract bpN:p11:nonresonant v1); Lean theorem KAM.Nekhoroshev.nonresonant cited by MAIN L433 (never read here)

NODE: N:bpN:p0:partial
KIND: external
TITLE: [N] N-PARTIAL-CONVEX: partialConvex_nekhoroshev (sealed, root of graph N)
STATEMENT_SOURCE: blueprint-N/parts/p0-conventions.tex#bpN:p0:partial@L319-L335
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p0:partial
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a Lean frozen statement; n ≥ 2, k ≥ 1, G, G' ⊂ ℝⁿ open and convex, D ⊂ Ph_k open, ρ, g, m, M_ℂ ∈ ℝ with ρ > 0, M_ℂ > 0, B̄(I,ρ) ⊂ G' for every I ∈ G (closed max-norm ball); h : ℂⁿ → ℂ complex differentiable and complex C² on G'_ρ, Im h(I) = 0 for real I ∈ G'_ρ, ‖D²h(z)‖ ≤ M_ℂ on G'_ρ, HasDefiniteFastPart G' ρ g m h; then for μ ∈ (0,μ₀), P with IsPartialPerturbation G' D ρ P, C > 0, z : ℝ → Ph_{n+k}: (Z1) IsSolutionOn H_μ {𝖨 : fast(𝖨) ∈ G} [0,C] z with H_μ = Re h(fast 𝖨) + μ Re P(cx(φ,𝖨)) (degenerateHamiltonian (realPart h) (Re P ∘ cx) μ); (Z2) fast(z(0)_2) ∈ core(G, μ^{b_n}); t ∈ [0, min(C, μ^{−1} exp(μ^{−a_n}))] with (slow z(u)_1, slow z(u)_2) ∈ core(D, μ^{b_n}) for all u ∈ [0,t]
SOURCE_QUANTIFIERS: n, k; G, G', D, ρ, g, m, M_ℂ, h (with their hypotheses); then ∃ μ₀ > 0; then ∀ μ ∈ (0,μ₀), P, C > 0, z (with Z1, Z2); then ∀ t ∈ [0, min(C, μ^{−1} exp(μ^{−a_n}))] with slow confinement on [0,t]
SOURCE_CONCLUSION: ¦fast(z(t)_2) − fast(z(0)_2)¦ ≤ ½ μ^{b_n}
CONSTANT_SCOPE: μ₀ > 0 depends only on (n, k, G, G', D, ρ, g, m, M_ℂ, h) and is chosen before μ, P, C, z, t; a_n = 2/(6n² − 3n + 14), b_n = 3/(6n² − 3n + 14); slow confinement is tested only on [0,t]; the initial erosion core(G, μ^{b_n}) is used only as fast(z(0)_2) ∈ G
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-N graph, node bpN:p0:partial (there KIND theorem, the frozen root nekhoroshev.d25.partialConvex_nekhoroshev v1, sealed, D58); consumed by LP3 (wave 4)

NODE: lpM:ext-holomorphic-limit
KIND: external
TITLE: uniform limits of holomorphic maps are holomorphic
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L211-L211
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-holomorphic-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a sequence of holomorphic maps on an open set of ℂ^k converging uniformly (on compact subsets)
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: the limit is holomorphic (in particular a uniformly convergent iteration of holomorphic maps has a holomorphic limit)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-identity-theorem
KIND: external
TITLE: identity theorem for analytic maps on a connected domain
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L238-L238
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-identity-theorem
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: two analytic (holomorphic, or real analytic) maps on a connected open set that agree on a nonempty open subset (or have the same power series at one point)
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: they agree on the whole connected set
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-compact-cover
KIND: external
TITLE: finite subcover of a compact set
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L265-L265
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-compact-cover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K a compact subset of a metric space; an open cover of K (e.g. balls centered at points of K)
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: finitely many members of the cover already cover K (with half-sized balls: a Lebesgue-number neighborhood)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-cauchy-estimates
KIND: external
TITLE: Cauchy's integral formula and estimates; holomorphic square root on a half plane
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L271-L271
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-cauchy-estimates
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic on a neighborhood of a closed polydisk of radius ρ, bounded by M there; w in the half plane Re w > 0
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: Cauchy's formula holds and ¦∂^α f¦ ≤ α! M ρ^{-¦α¦} at the center (one-variable form: ¦f'¦ ≤ M/ρ); the principal square root is holomorphic on Re w > 0 with positive real part
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-fourier-contour
KIND: external
TITLE: Fourier coefficients of periodic holomorphic maps and the contour shift
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L298-L298
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-fourier-contour
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic and 2π-periodic in each angle on the strip ¦Im θ¦_∞ < σ, bounded by M on narrower strips
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: the Fourier coefficients are integrals over the real torus, independent of the contour within the strip, and ¦f_k¦ ≤ M e^{-σ'¦k¦_1} for every σ' < σ (shift each contour with sign opposite to the Fourier index)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:T15#planar_strongAMD_exponentialSafety
KIND: theorem
TITLE: LP1: planar strong-AMD exponential safety (Theorem 15 with Lemma 16)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L502-L506
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
CONTRACT_ID: planetary.d59.planar_strongAMD_exponentialSafety
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; τ > n - 1; planar (d = 2)
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (all positive, with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ planar phase z_0 with ¦q_i¦ > 0, E_i < 0 for every i, a(z_0) ∈ 𝒜, (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i, Λ(z_0) ∈ Q (a typing binder; it follows from a(z_0) ∈ 𝒜) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-1/(2(τ+1))}): ∃ z : ℝ → phases, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: z(0) = z_0; z solves (1) on [-T, T] without collision (IsMovingSolutionOn) and agrees with every local solution (MovingUniqueOn); the barycentric reconstruction solves Newton's equations with masses (1, μν_i) on [-T, T]; for every t: ¦q_i¦ > 0, E_i < 0; Λ(t) ∈ Q and C(t) ≤ B(Λ(t)) - δ/2; ‖Λ(t) - Λ(0)‖ ≤ A_Λ√μ; ‖a(t) - a(0)‖ ≤ A_a√μ; ¦C(t) - C(0)¦ ≤ nA_Λ√μ; a_i(1 - e_i) ≥ d_⋆; a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair; ¦q_i¦ ≥ d_⋆; ¦q_i - q_j¦ ≥ d_pair for i ≠ j; the osculating elements are nondegenerate (E^osc < 0, e^osc < 1, a source osculating phase) with E_i^osc < 0, a_i^osc > 0, e_i^osc < 1, a_i^osc(1 - e_i^osc) ≤ ¦q_i¦ ≤ a_i^osc(1 + e_i^osc), ¦a_i^osc - a_i¦ + ¦e_i^osc - e_i¦ ≤ A_elem μ; ¦a_i^osc(1 ∓ e_i^osc) - a_i(1 ∓ e_i)¦ ≤ A_osc μ; a_i^osc(1 - e_i^osc) ≥ d_⋆/2; adjacent osculating gaps ≥ d_pair/2
CONSTANT_SCOPE: μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ, τ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety
FROZEN_ANCHOR_ID: planetary.d59.planar_strongAMD_exponentialSafety.v1
FROZEN_ABI_SHA256: a70e0b6a009377d9cb3c49a23bcec64e175853c0eb2cb59d5a456d29df729591
DEPS: lpM:T15, lpM:T15#reconstruction, lpM:T15#osculating, lpM:L16#mu0-choice, lpM:L16#sourceOscAxis_pos, lpM:L16#sourceOscPeri_le_planeLength, lpM:L16#planeLength_le_sourceOscApo, lpM:s1:dioph#IsDiophantine, lpM:s1:model#actualMasses, lpM:L1#barycentricPositions, lpM:L1#barycentricVelocities, lpM:s1:model#bodyVector, lpM:s1:model#IsMovingSolutionOn, lpM:L1#IsNewtonSolutionOn, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:elements#keplerEnergy, lpM:s1:model#MovingUniqueOn, lpM:s1:model#Phase, lpM:s1:data#planeLength, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:L16:defs#oscEcc, lpM:L16:defs#oscEnergy, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceKeplerApo, lpM:s1:elements#sourceKeplerPeri, lpM:L16:defs#sourceOscApo, lpM:L16:defs#sourceOscAxis, lpM:L16:defs#sourceOscEcc, lpM:L16:defs#sourceOscEccVector, lpM:L16:defs#sourceOscEnergy, lpM:L16:defs#sourceOscPeri, lpM:L16:defs#SourceOsculatingPhase, lpM:s1:elements#sourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T15 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | LP1 is Theorem 15 (the §1 conclusion in d = 2)
EDGE: lpM:T15#reconstruction | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the Newtonian reconstruction clause (Lemma 1)
EDGE: lpM:T15#osculating | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the osculating clauses, including the first estimate of (43) (A_elem)
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/source/MAIN.md#L16@L528-L528 | the stated constant relations A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)
EDGE: lpM:L16#sourceOscAxis_pos | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | a_i^osc > 0 on the osculating carrier
EDGE: lpM:L16#sourceOscPeri_le_planeLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | a_i^osc(1 - e_i^osc) ≤ ¦q_i¦
EDGE: lpM:L16#planeLength_le_sourceOscApo | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | ¦q_i¦ ≤ a_i^osc(1 + e_i^osc)
EDGE: lpM:s1:dioph#IsDiophantine | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the Diophantine premise (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i
EDGE: lpM:s1:model#actualMasses | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the Newtonian masses (1, μν_i)
EDGE: lpM:L1#barycentricPositions | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the reconstructed barycentric positions
EDGE: lpM:L1#barycentricVelocities | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the reconstructed barycentric velocities
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the positions q_i
EDGE: lpM:s1:model#IsMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | z solves (1) on [-T, T] without collision
EDGE: lpM:L1#IsNewtonSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the reconstructed motion solves Newton's equations
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the actions Λ(z)
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the axes a_i
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the eccentricities e_i = ¦e_i¦
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | negative Kepler energies
EDGE: lpM:s1:model#MovingUniqueOn | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | uniqueness against every local solution
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | planar phases
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | Euclidean lengths
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the adjacent pairs of (9)
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the upper index of an adjacent pair
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | I(t) ∈ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | B(I) in (6) and (8)
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the osculating carrier condition e^osc < 1
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the osculating carrier condition E^osc < 0
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the canonical carrier
EDGE: lpM:s1:elements#sourceKeplerApo | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | canonical aphelia
EDGE: lpM:s1:elements#sourceKeplerPeri | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | canonical perihelia
EDGE: lpM:L16:defs#sourceOscApo | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating aphelia
EDGE: lpM:L16:defs#sourceOscAxis | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating axes
EDGE: lpM:L16:defs#sourceOscEcc | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating eccentricities
EDGE: lpM:L16:defs#sourceOscEccVector | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating eccentricity vectors
EDGE: lpM:L16:defs#sourceOscEnergy | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating energies
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating perihelia
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the osculating carrier
EDGE: lpM:s1:elements#sourceStrongAMD | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | C in (6) and (8)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety (KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety
NOTE: Anchor LP1. Planar instance of the §1 conclusion (Theorem 15), with Lemma 16's elliptic, tangency and (43) clauses and N10's constant relations; A_elem is the constant A of (43) (MAIN's §1 list omits it). The premise Λ(z_0) ∈ Q is a typing binder that the source derives from a(0) ∈ 𝒜. AMENDED: N8, N10.

NODE: lpM:T15#planar_strongAMD_exponentialSafety_halfInteger
KIND: corollary
TITLE: LP1-H: LP1 at tau = n - 1/2 (exponent 1/(2n+1))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
CONTRACT_ID: planetary.d59.planar_strongAMD_exponentialSafety_halfInteger
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; planar (d = 2); τ = n - 1/2 fixed
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (all positive, with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ planar phase z_0 with ¦q_i¦ > 0, E_i < 0 for every i, a(z_0) ∈ 𝒜, (5) with τ = n - 1/2 at ω(I^0) = (ν_i^3/Λ_i^3)_i, Λ(z_0) ∈ Q (a typing binder; it follows from a(z_0) ∈ 𝒜) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-1/(2n+1)}): ∃ z : ℝ → phases, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: z(0) = z_0; z solves (1) on [-T, T] without collision (IsMovingSolutionOn) and agrees with every local solution (MovingUniqueOn); the barycentric reconstruction solves Newton's equations with masses (1, μν_i) on [-T, T]; for every t: ¦q_i¦ > 0, E_i < 0; Λ(t) ∈ Q and C(t) ≤ B(Λ(t)) - δ/2; ‖Λ(t) - Λ(0)‖ ≤ A_Λ√μ; ‖a(t) - a(0)‖ ≤ A_a√μ; ¦C(t) - C(0)¦ ≤ nA_Λ√μ; a_i(1 - e_i) ≥ d_⋆; a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair; ¦q_i¦ ≥ d_⋆; ¦q_i - q_j¦ ≥ d_pair for i ≠ j; the osculating elements are nondegenerate (E^osc < 0, e^osc < 1, a source osculating phase) with E_i^osc < 0, a_i^osc > 0, e_i^osc < 1, a_i^osc(1 - e_i^osc) ≤ ¦q_i¦ ≤ a_i^osc(1 + e_i^osc), ¦a_i^osc - a_i¦ + ¦e_i^osc - e_i¦ ≤ A_elem μ; ¦a_i^osc(1 ∓ e_i^osc) - a_i(1 ∓ e_i)¦ ≤ A_osc μ; a_i^osc(1 - e_i^osc) ≥ d_⋆/2; adjacent osculating gaps ≥ d_pair/2
CONSTANT_SCOPE: μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger
FROZEN_ANCHOR_ID: planetary.d59.planar_strongAMD_exponentialSafety_halfInteger.v1
FROZEN_ABI_SHA256: 50df22c53395dc90c388a4d62811762b288e72721e54c799949456bb67897574
DEPS: lpM:T15#planar_strongAMD_exponentialSafety, lpM:s1:half-integer, lpM:s1:dioph#IsDiophantine, lpM:s1:model#actualMasses, lpM:L1#barycentricPositions, lpM:L1#barycentricVelocities, lpM:s1:model#bodyVector, lpM:s1:model#IsMovingSolutionOn, lpM:L1#IsNewtonSolutionOn, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:elements#keplerEnergy, lpM:s1:model#MovingUniqueOn, lpM:s1:model#Phase, lpM:s1:data#planeLength, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:L16:defs#oscEcc, lpM:L16:defs#oscEnergy, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceKeplerApo, lpM:s1:elements#sourceKeplerPeri, lpM:L16:defs#sourceOscApo, lpM:L16:defs#sourceOscAxis, lpM:L16:defs#sourceOscEcc, lpM:L16:defs#sourceOscEccVector, lpM:L16:defs#sourceOscEnergy, lpM:L16:defs#sourceOscPeri, lpM:L16:defs#SourceOsculatingPhase, lpM:s1:elements#sourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T15#planar_strongAMD_exponentialSafety | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | LP1 with τ = n - 1/2
EDGE: lpM:s1:half-integer | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | τ = n - 1/2 > n - 1 and 1/(2(τ+1)) = 1/(2n+1)
EDGE: lpM:s1:dioph#IsDiophantine | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the Diophantine premise (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i
EDGE: lpM:s1:model#actualMasses | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the Newtonian masses (1, μν_i)
EDGE: lpM:L1#barycentricPositions | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the reconstructed barycentric positions
EDGE: lpM:L1#barycentricVelocities | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the reconstructed barycentric velocities
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the positions q_i
EDGE: lpM:s1:model#IsMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | z solves (1) on [-T, T] without collision
EDGE: lpM:L1#IsNewtonSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the reconstructed motion solves Newton's equations
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the actions Λ(z)
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the axes a_i
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the eccentricities e_i = ¦e_i¦
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | negative Kepler energies
EDGE: lpM:s1:model#MovingUniqueOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | uniqueness against every local solution
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | planar phases
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | Euclidean lengths
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the adjacent pairs of (9)
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the upper index of an adjacent pair
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | I(t) ∈ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | B(I) in (6) and (8)
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the osculating carrier condition e^osc < 1
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the osculating carrier condition E^osc < 0
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the canonical carrier
EDGE: lpM:s1:elements#sourceKeplerApo | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | canonical aphelia
EDGE: lpM:s1:elements#sourceKeplerPeri | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | canonical perihelia
EDGE: lpM:L16:defs#sourceOscApo | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating aphelia
EDGE: lpM:L16:defs#sourceOscAxis | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating axes
EDGE: lpM:L16:defs#sourceOscEcc | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating eccentricities
EDGE: lpM:L16:defs#sourceOscEccVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating eccentricity vectors
EDGE: lpM:L16:defs#sourceOscEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating energies
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating perihelia
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the osculating carrier
EDGE: lpM:s1:elements#sourceStrongAMD | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | C in (6) and (8)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger (KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger
NOTE: Anchor LP1-H: the half-integer corollary (MAIN §1 L93) of LP1

NODE: lpM:L16#sourceOscAxis_pos
KIND: lemma
TITLE: a_i^osc > 0 on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.sourceOscAxis_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, source osculating phase z and i
SOURCE_CONCLUSION: 0 < a_i^osc
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscAxisPos.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscAxis_pos
FROZEN_ANCHOR_ID: planetary.d59.sourceOscAxis_pos.v1
FROZEN_ABI_SHA256: 5d18a64bd0fce6435020af9cb258359eeb057b5be6b9ee9e829ad11a3249b87c
DEPS: lpM:L16:defs, lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#sourceOscAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L516-L516 | a^osc = -k_i/(2E^osc) with k_i = 1 + μν_i > 0 and E^osc < 0
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement quantifies over source osculating phases
EDGE: lpM:L16:defs#sourceOscAxis | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | a^osc occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscAxis_pos (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscAxisPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceOscAxis_pos
NOTE: -

NODE: lpM:L16#sourceOscPeri_pos
KIND: lemma
TITLE: a_i^osc(1 - e_i^osc) > 0 on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.sourceOscPeri_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, source osculating phase z and i
SOURCE_CONCLUSION: 0 < a_i^osc(1 - e_i^osc)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriPos.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscPeri_pos
FROZEN_ANCHOR_ID: planetary.d59.sourceOscPeri_pos.v1
FROZEN_ABI_SHA256: 0c5150d43260c99afa47b998ab7a3e9f499a514e1becaf0f34eb92d66e77bf59
DEPS: lpM:L16#sourceOscAxis_pos, lpM:L16:defs, lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#sourceOscPeri
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#sourceOscAxis_pos | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | a^osc > 0
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | e^osc < 1 on the carrier
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement quantifies over source osculating phases
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the osculating perihelion occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscPeri_pos (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceOscPeri_pos
NOTE: -

NODE: lpM:L16#sourceOscPeri_le_planeLength
KIND: lemma
TITLE: a_i^osc(1 - e_i^osc) <= ¦q_i¦ on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L525-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.sourceOscPeri_le_planeLength
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, source osculating phase z and i
SOURCE_CONCLUSION: a_i^osc(1 - e_i^osc) ≤ ¦q_i¦
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriLePlaneLength.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength
FROZEN_ANCHOR_ID: planetary.d59.sourceOscPeri_le_planeLength.v1
FROZEN_ABI_SHA256: 1ce0a7aed32a3f144a29bed616e0d29c34606699a68fd2123a048048ffc3f040
DEPS: lpM:L16#tangent-ellipse, lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#sourceOscPeri, lpM:s1:data#planeLength, lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#tangent-ellipse | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | Lemma 2 with parameter k_i: the ellipse contains the position
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement quantifies over source osculating phases
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the osculating perihelion occurs
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | Euclidean lengths ¦·¦ occur in the statement
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the position q_i occurs in the statement
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriLePlaneLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceOscPeri_le_planeLength
NOTE: -

NODE: lpM:L16#planeLength_le_sourceOscApo
KIND: lemma
TITLE: ¦q_i¦ <= a_i^osc(1 + e_i^osc) on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L525-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.planeLength_le_sourceOscApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, source osculating phase z and i
SOURCE_CONCLUSION: ¦q_i¦ ≤ a_i^osc(1 + e_i^osc)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceOscApo.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo
FROZEN_ANCHOR_ID: planetary.d59.planeLength_le_sourceOscApo.v1
FROZEN_ABI_SHA256: fffced58bd764c2961e056add565ae5347a7c06a8215969009b92f957225f8f3
DEPS: lpM:L16#tangent-ellipse, lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#sourceOscApo, lpM:s1:data#planeLength, lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#tangent-ellipse | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | Lemma 2 with parameter k_i: the ellipse contains the position
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement quantifies over source osculating phases
EDGE: lpM:L16:defs#sourceOscApo | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the osculating aphelion occurs
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | Euclidean lengths ¦·¦ occur in the statement
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the position q_i occurs in the statement
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo (KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceOscApo.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceOscApo
NOTE: -

NODE: lpM:s1:dioph#IsDiophantine
KIND: definition
TITLE: (gamma, tau)-Diophantine vector: gamma/¦k¦_1^tau <= ¦k.omega¦ for k != 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L64-L65
PROOF_SOURCE: -
CONTRACT_ID: kam.IsDiophantine
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; γ, τ : ℝ; ω : Fin n → ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, γ, τ, ω
SOURCE_CONCLUSION: γ/¦k¦_1^τ ≤ ¦k·ω¦ for every 0 ≠ k ∈ ℤ^n: the condition (5) at ω = ω(I^0)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsDiophantine.lean
FROZEN_DECL: KAM.IsDiophantine
FROZEN_ANCHOR_ID: kam.IsDiophantine.v1
FROZEN_ABI_SHA256: 24a486c6ccc5648791465ec3577c2e37fd464ecaec8f0dab9c74a5588535e717
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.IsDiophantine (KAM/Frozen/Defs/IsDiophantine.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition kam.IsDiophantine.v1 (core), bound as an LP anchor node (Q6)

NODE: lpM:s1:model#actualMasses
KIND: definition
TITLE: actual masses (m_0, mu m_1, ..., mu m_n)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L17
PROOF_SOURCE: -
CONTRACT_ID: planetary.actualMasses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m_0 : ℝ; m : Fin n → ℝ; μ : ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, m_0, m, μ
SOURCE_CONCLUSION: the mass vector (m_0, μm_1, ..., μm_n); with m_0 = 1 and m = ν: star mass one and planet masses μν_i (MAIN L17, L99)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/ActualMasses.lean
FROZEN_DECL: KAM.Planetary.actualMasses
FROZEN_ANCHOR_ID: planetary.actualMasses.v1
FROZEN_ABI_SHA256: 37d0c6b0a92ae0e0c839d24e591536f697c601419b11cc5c864150814a680b60
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.actualMasses (KAM/Frozen/Planetary/Defs/ActualMasses.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.actualMasses.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:L1#barycentricPositions
KIND: definition
TITLE: barycentric positions x_0 = -mu sum nu_i q_i/M, x_i = x_0 + q_i
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L104
PROOF_SOURCE: -
CONTRACT_ID: planetary.barycentricPositions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m_0 : ℝ; m : Fin n → ℝ; μ : ℝ; q (typing data)
SOURCE_QUANTIFIERS: for every n, m_0, m, μ, q
SOURCE_CONCLUSION: x_0 = -μ Σ_i m_i q_i/(m_0 + μΣ_i m_i), x_i = x_0 + q_i (Lemma 1's explicit inverse, L104, with m_0 = 1, m = ν)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/BarycentricPositions.lean
FROZEN_DECL: KAM.Planetary.barycentricPositions
FROZEN_ANCHOR_ID: planetary.barycentricPositions.v1
FROZEN_ABI_SHA256: 222cb379298aba4da485faf152163725857fac2c6578168946b7d79fc09910d1
DEPS: lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L1@L104-L104 | planet i's coordinate vector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.barycentricPositions (KAM/Frozen/Planetary/Defs/BarycentricPositions.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.barycentricPositions.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:L1#barycentricVelocities
KIND: definition
TITLE: barycentric velocities x_0' = -mu sum p_i/m_0, x_i' = p_i/m_i
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L104
PROOF_SOURCE: -
CONTRACT_ID: planetary.barycentricVelocities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m_0 : ℝ; m : Fin n → ℝ; μ : ℝ; p (typing data)
SOURCE_QUANTIFIERS: for every n, m_0, m, μ, p
SOURCE_CONCLUSION: ẋ_0 = -(μ/m_0) Σ_i p_i, ẋ_i = p_i/m_i (Lemma 1's explicit inverse, L104, with m_0 = 1, m = ν)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/BarycentricVelocities.lean
FROZEN_DECL: KAM.Planetary.barycentricVelocities
FROZEN_ANCHOR_ID: planetary.barycentricVelocities.v1
FROZEN_ABI_SHA256: f0bb61447643e18562ffdde5d8ddbd4bc7ed46d52985b4fabaeab4a657a15480
DEPS: lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L1@L104-L104 | planet i's coordinate vector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.barycentricVelocities (KAM/Frozen/Planetary/Defs/BarycentricVelocities.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.barycentricVelocities.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:model#IsMovingSolutionOn
KIND: definition
TITLE: z solves the moving-Sun Hamiltonian (1) on J without collision
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.IsMovingSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m : Fin n → ℝ; μ : ℝ; J : Set ℝ; z : ℝ → Phase (n*2) (typing data)
SOURCE_QUANTIFIERS: for every n, m, μ, J, z
SOURCE_CONCLUSION: z is a solution on J of Hamilton's equations of (1) (frozen movingHamiltonian with star mass and G one; the differentiability-guarded ODE predicate) and every z(t), t ∈ J, is collision-free (the open domain of (1))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsMovingSolutionOn.lean
FROZEN_DECL: KAM.Planetary.IsMovingSolutionOn
FROZEN_ANCHOR_ID: planetary.d25.IsMovingSolutionOn.v1
FROZEN_ABI_SHA256: b09b6a924851b13c3ab5d708da0cd1cbeff1a2088abc7803ffaa956c257b3708
DEPS: lpM:s1:model#Phase, lpM:s1:model#NoCollision, lpM:s1:model#IsHamiltonianSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the phase type
EDGE: lpM:s1:model#NoCollision | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the configurations stay collision-free
EDGE: lpM:s1:model#IsHamiltonianSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the guarded Hamiltonian ODE predicate (bound in wave 3)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.IsMovingSolutionOn (KAM/Frozen/Planetary/Defs/IsMovingSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.IsMovingSolutionOn.v1 (track P), bound as an LP anchor node (Q6); movingHamiltonian is typing data

NODE: lpM:s1:model#MovingUniqueOn
KIND: definition
TITLE: z agrees with every local solution from z(0) on the overlap with J
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L24-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.MovingUniqueOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m : Fin n → ℝ; μ : ℝ; J : Set ℝ; z : ℝ → Phase (n*2) (typing data)
SOURCE_QUANTIFIERS: for every n, m, μ, J, z
SOURCE_CONCLUSION: for every open convex U ∋ 0 and every solution w of (1) on U with w(0) = z(0), w = z on U ∩ J: uniqueness of the solution of (1) ('the unique maximal solution', MAIN L74)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/MovingUniqueOn.lean
FROZEN_DECL: KAM.Planetary.MovingUniqueOn
FROZEN_ANCHOR_ID: planetary.d25.MovingUniqueOn.v1
FROZEN_ABI_SHA256: d7cd7186c2539239b187c02b6e2523a88981cb2e7c3c158ace598e407b45089e
DEPS: lpM:s1:model#Phase, lpM:s1:model#IsMovingSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | the phase type
EDGE: lpM:s1:model#IsMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | the competing local solutions
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.MovingUniqueOn (KAM/Frozen/Planetary/Defs/MovingUniqueOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.MovingUniqueOn.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:L1#IsNewtonSolutionOn
KIND: definition
TITLE: finite-interval Newton equations with masses m_j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L108-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.IsNewtonSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: N : ℕ; masses : Fin N → ℝ; J : Set ℝ; Q, V : ℝ → Fin N → ℝ^2 (typing data)
SOURCE_QUANTIFIERS: for every N, masses, J, Q, V
SOURCE_CONCLUSION: on J: the bodies are pairwise distinct, Q̇_i = V_i and V̇_i = Σ_{j≠i} m_j (Q_j - Q_i)/¦Q_j - Q_i¦^3 (Newton's equations of Lemma 1, L108)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsNewtonSolutionOn.lean
FROZEN_DECL: KAM.Planetary.IsNewtonSolutionOn
FROZEN_ANCHOR_ID: planetary.d25.IsNewtonSolutionOn.v1
FROZEN_ABI_SHA256: a03730db1e938d4da88e154ebbb322ec514de0aa287e030a2de6e8a1625e397f
DEPS: lpM:s1:data#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L1@L108-L108 | the Euclidean distances ¦Q_j - Q_i¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.IsNewtonSolutionOn (KAM/Frozen/Planetary/Defs/IsNewtonSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.IsNewtonSolutionOn.v1 (track P), bound as an LP anchor node (Q6)





NODE: lpM:s1:data#spaceDot
KIND: definition
TITLE: spaceDot (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L29-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spaceDot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Euclidean scalar product on Fin 3 → ℝ. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpaceDot.lean
FROZEN_DECL: KAM.Planetary.Spatial.spaceDot
FROZEN_ANCHOR_ID: planetary.d59.spaceDot.v1
FROZEN_ABI_SHA256: 4551abaaa4755d552dd5bab7eac43b0405360fabfc32ef52b3d98fda3049a324
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spaceDot (KAM/Frozen/Planetary/Spatial/Defs/SpaceDot.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:data#spaceSq
KIND: definition
TITLE: spaceSq (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L15-L15
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spaceSq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Squared Euclidean length on Fin 3 → ℝ. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpaceSq.lean
FROZEN_DECL: KAM.Planetary.Spatial.spaceSq
FROZEN_ANCHOR_ID: planetary.d59.spaceSq.v1
FROZEN_ABI_SHA256: bcae08a71ff40c78513831da5ca7c3ca114dc45666dafcf71956999cc38f1cfd
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spaceSq (KAM/Frozen/Planetary/Spatial/Defs/SpaceSq.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:data#spaceLength
KIND: definition
TITLE: spaceLength (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L15-L15
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spaceLength
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Euclidean length on Fin 3 → ℝ, independent of the ambient Pi sup norm. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpaceLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spaceLength
FROZEN_ANCHOR_ID: planetary.d59.spaceLength.v1
FROZEN_ABI_SHA256: 70ce223ee332d660b3e6917f1766402e3c9336962a2f8c5c59b4dc57511cbe03
DEPS: lpM:s1:data#spaceSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#s1@L15-L15 | the declaration uses spaceSq
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spaceLength (KAM/Frozen/Planetary/Spatial/Defs/SpaceLength.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spaceCross
KIND: definition
TITLE: spaceCross (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spaceCross
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The standard cross product on Fin 3 → ℝ, written out in components. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpaceCross.lean
FROZEN_DECL: KAM.Planetary.Spatial.spaceCross
FROZEN_ANCHOR_ID: planetary.d59.spaceCross.v1
FROZEN_ABI_SHA256: 87bc64bdb88d2ae2e38e01091904aa638633c9f8cb56ebb79f2759351e9f9c89
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spaceCross (KAM/Frozen/Planetary/Spatial/Defs/SpaceCross.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#bodyVector3
KIND: definition
TITLE: bodyVector3 (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L20
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.bodyVector3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Extract the three Cartesian coordinates of body i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/BodyVector3.lean
FROZEN_DECL: KAM.Planetary.Spatial.bodyVector3
FROZEN_ANCHOR_ID: planetary.d59.bodyVector3.v1
FROZEN_ABI_SHA256: b5de44382a31d04a5940a23b52e58abda7a369f2ea78bbea0e5aff75c91a860c
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.bodyVector3 (KAM/Frozen/Planetary/Spatial/Defs/BodyVector3.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#planetAngularMomentum3
KIND: definition
TITLE: planetAngularMomentum3 (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.planetAngularMomentum3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Individual angular momentum L_i = q_i × p_i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/PlanetAngularMomentum3.lean
FROZEN_DECL: KAM.Planetary.Spatial.planetAngularMomentum3
FROZEN_ANCHOR_ID: planetary.d59.planetAngularMomentum3.v1
FROZEN_ABI_SHA256: e03d68e8041e465fb213075e42c6fbbc65755b88d5d79c7da8b41b4130e3d079
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:elements#spaceCross
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses bodyVector3
EDGE: lpM:s1:elements#spaceCross | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceCross
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.planetAngularMomentum3 (KAM/Frozen/Planetary/Spatial/Defs/PlanetAngularMomentum3.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#angularMomentum3
KIND: definition
TITLE: angularMomentum3 (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.angularMomentum3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Total angular momentum L = Σ_i q_i × p_i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/AngularMomentum3.lean
FROZEN_DECL: KAM.Planetary.Spatial.angularMomentum3
FROZEN_ANCHOR_ID: planetary.d59.angularMomentum3.v1
FROZEN_ABI_SHA256: ecc6c04d768f5c59f00a205d5a712118a800b6f0be7c82789cbfdb83d46040b7
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:elements#spaceCross
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses bodyVector3
EDGE: lpM:s1:elements#spaceCross | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceCross
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.angularMomentum3 (KAM/Frozen/Planetary/Spatial/Defs/AngularMomentum3.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#spatialHamiltonian
KIND: definition
TITLE: spatialHamiltonian (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialHamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The exact spatial Hamiltonian H_μ (LP:MAIN §1 (1), d = 3): positions q_i and scaled canonical momenta p_i in Phase (n * 3), masses m_i = μ ν_i, central Kepler parameter one. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialHamiltonian.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialHamiltonian
FROZEN_ANCHOR_ID: planetary.d59.spatialHamiltonian.v1
FROZEN_ABI_SHA256: b4614c6f0dba469b5409ef80174b3d0f5043fbb6fca3f6158fc225da6d76e7e0
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses spaceSq
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialHamiltonian (KAM/Frozen/Planetary/Spatial/Defs/SpatialHamiltonian.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#SpatialNoCollision
KIND: definition
TITLE: SpatialNoCollision (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L24-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialNoCollision
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The open physical domain of H_μ: no planet at the star and no two planets together. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialNoCollision.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialNoCollision
FROZEN_ANCHOR_ID: planetary.d59.SpatialNoCollision.v1
FROZEN_ABI_SHA256: cca4510b4e971c550607d55d4583b5b1dfbcf2c1cd25f20cbee2f803a18a8ba4
DEPS: lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | the declaration uses spaceLength
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialNoCollision (KAM/Frozen/Planetary/Spatial/Defs/SpatialNoCollision.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#IsSpatialMovingSolutionOn
KIND: definition
TITLE: IsSpatialMovingSolutionOn (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.IsSpatialMovingSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: A genuine spatial moving-Sun solution on J: the frozen differentiability-guarded Hamiltonian ODE for H_μ together with collision exclusion (LP:MAIN §1 (1)). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/IsSpatialMovingSolutionOn.lean
FROZEN_DECL: KAM.Planetary.Spatial.IsSpatialMovingSolutionOn
FROZEN_ANCHOR_ID: planetary.d59.IsSpatialMovingSolutionOn.v1
FROZEN_ABI_SHA256: 6499ca1d550e8d07037e70c29dff5e48c33dc6c9f7e978637c8c24b09f8fb5e5
DEPS: lpM:s1:model#IsHamiltonianSolutionOn, lpM:s1:model#Phase, lpM:s1:model#spatialHamiltonian, lpM:s1:model#SpatialNoCollision
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#IsHamiltonianSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses IsHamiltonianSolutionOn
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses Phase
EDGE: lpM:s1:model#spatialHamiltonian | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses spatialHamiltonian
EDGE: lpM:s1:model#SpatialNoCollision | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses SpatialNoCollision
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.IsSpatialMovingSolutionOn (KAM/Frozen/Planetary/Spatial/Defs/IsSpatialMovingSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#SpatialMovingUniqueOn
KIND: definition
TITLE: SpatialMovingUniqueOn (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L69-L72
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialMovingUniqueOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Agreement with every other local spatial solution on its overlap with the certified interval (the pattern of the frozen planar MovingUniqueOn). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialMovingUniqueOn.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialMovingUniqueOn
FROZEN_ANCHOR_ID: planetary.d59.SpatialMovingUniqueOn.v1
FROZEN_ABI_SHA256: ca45020ff13ad89b7ed4e3077306848600850bc604bc4f07eadc4bd043d62d31
DEPS: lpM:s1:model#Phase, lpM:s1:model#IsSpatialMovingSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the declaration uses Phase
EDGE: lpM:s1:model#IsSpatialMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the declaration uses IsSpatialMovingSolutionOn
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialMovingUniqueOn (KAM/Frozen/Planetary/Spatial/Defs/SpatialMovingUniqueOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#spatialBarycentricPositions
KIND: definition
TITLE: spatialBarycentricPositions (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialBarycentricPositions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Barycentric positions (star first, then the planets) from heliocentric q, with m₀ = 1. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricPositions.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialBarycentricPositions
FROZEN_ANCHOR_ID: planetary.d59.spatialBarycentricPositions.v1
FROZEN_ABI_SHA256: b5ef0dbc1e597050da5bb1fcca1a9608e9730cdb090fb893239f686c8d069f61
DEPS: lpM:s1:model#bodyVector3
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses bodyVector3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialBarycentricPositions (KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricPositions.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#spatialBarycentricVelocities
KIND: definition
TITLE: spatialBarycentricVelocities (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialBarycentricVelocities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Barycentric velocities: actual planet momenta are μ p, total momentum zero. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricVelocities.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialBarycentricVelocities
FROZEN_ANCHOR_ID: planetary.d59.spatialBarycentricVelocities.v1
FROZEN_ABI_SHA256: cc092f40cafa08fca2fadf837a911b0cb22cf2dec98cae504beb31b40ea620ab
DEPS: lpM:s1:model#bodyVector3
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses bodyVector3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialBarycentricVelocities (KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricVelocities.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#spatialMasses
KIND: definition
TITLE: spatialMasses (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialMasses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The masses (1, μ ν_1, …, μ ν_n). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialMasses.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialMasses
FROZEN_ANCHOR_ID: planetary.d59.spatialMasses.v1
FROZEN_ABI_SHA256: aca567c2ed9ffb877daf85b2616eaa757cd2274656175e2de1d601f7886ff1ad
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialMasses (KAM/Frozen/Planetary/Spatial/Defs/SpatialMasses.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#IsSpatialNewtonSolutionOn
KIND: definition
TITLE: IsSpatialNewtonSolutionOn (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.IsSpatialNewtonSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Finite-interval Newton equations in dimension three, with Euclidean lengths (G = 1). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/IsSpatialNewtonSolutionOn.lean
FROZEN_DECL: KAM.Planetary.Spatial.IsSpatialNewtonSolutionOn
FROZEN_ANCHOR_ID: planetary.d59.IsSpatialNewtonSolutionOn.v1
FROZEN_ABI_SHA256: e0c5f38f79b55a20c71405151c0cde2c1c4a1cb3aaed11a4f685048977fb282d
DEPS: lpM:s1:data#spaceLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses spaceLength
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.IsSpatialNewtonSolutionOn (KAM/Frozen/Planetary/Spatial/Defs/IsSpatialNewtonSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerEnergy
KIND: definition
TITLE: spatialKeplerEnergy (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Total Kepler energy ν_i E_i of planet i (planar convention). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEnergy.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerEnergy
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerEnergy.v1
FROZEN_ABI_SHA256: c302a0603f146706db847d139cc2d8b2222c86a91adacde2a7325699d8b894a1
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceSq
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerEnergy (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerAxis
KIND: definition
TITLE: spatialKeplerAxis (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Canonical semi-major axis a_i = −ν_i/(2 ν_i E_i) = −1/(2 E_i). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAxis.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerAxis
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerAxis.v1
FROZEN_ABI_SHA256: 54bc0be144da1d819d43ee79ea7ad6aa9988e2b0852aced684e006af8bb9e96c
DEPS: lpM:s1:model#Phase, lpM:s1:elements#spatialKeplerEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerEnergy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerAxis (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerAction
KIND: definition
TITLE: spatialKeplerAction (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerAction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Kepler action Λ_i = ν_i √a_i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAction.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerAction
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerAction.v1
FROZEN_ABI_SHA256: d60e5dfcf1d7572d8fcf00135d5b846dd640a5bbb35057b9db282ef49ee7f2bd
DEPS: lpM:s1:model#Phase, lpM:s1:elements#spatialKeplerAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:elements#spatialKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerAxis
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerAction (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAction.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerEccVector
KIND: definition
TITLE: spatialKeplerEccVector (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Eccentricity vector 𝐞_i = (¦v¦² − 1/¦q¦) q − (q·v) v with v = p/ν. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEccVector.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerEccVector
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerEccVector.v1
FROZEN_ABI_SHA256: 1bb4b8de6655df78aa778f7210f66704c5ced8b411bb6cbc5b5dc96195503017
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceDot, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceDot | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceDot
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceSq
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerEccVector (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#SpatialNegativeEnergy
KIND: definition
TITLE: SpatialNegativeEnergy (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialNegativeEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The source carrier of the Kepler elements: positive masses, no planet at the star, negative energy of every planet. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialNegativeEnergy.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialNegativeEnergy
FROZEN_ANCHOR_ID: planetary.d59.SpatialNegativeEnergy.v1
FROZEN_ABI_SHA256: 28c34d877b59da45e883d96289365dbd2a6ede92b5b660372666e1ae5efc18d7
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerEnergy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialNegativeEnergy (KAM/Frozen/Planetary/Spatial/Defs/SpatialNegativeEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#SpatialElliptic
KIND: definition
TITLE: SpatialElliptic (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialElliptic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Phase points of the carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialElliptic.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialElliptic
FROZEN_ANCHOR_ID: planetary.d59.SpatialElliptic.v1
FROZEN_ABI_SHA256: fec96f298327ab83e94caa4f136616dc8c2a7db23c675039543320c8e120853b
DEPS: lpM:s1:model#Phase, lpM:s1:elements#SpatialNegativeEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:elements#SpatialNegativeEnergy | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialNegativeEnergy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialElliptic (KAM/Frozen/Planetary/Spatial/Defs/SpatialElliptic.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerPeri
KIND: definition
TITLE: spatialKeplerPeri (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L89-L91
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Canonical perihelion a_i (1 - e_i). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerPeri.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerPeri
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerPeri.v1
FROZEN_ABI_SHA256: cea64bbc7890c8a63c7b7c163c3314f979815bd8feece862103919a771ab394c
DEPS: lpM:s1:model#Phase, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerAxis, lpM:s1:elements#spatialKeplerEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses Phase
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerAxis
EDGE: lpM:s1:elements#spatialKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerEccVector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerPeri (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerApo
KIND: definition
TITLE: spatialKeplerApo (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L89-L91
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Canonical aphelion a_i (1 + e_i). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerApo.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerApo
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerApo.v1
FROZEN_ABI_SHA256: 087f10dfe3d4707ae053044dc986422b593ed76bc17ac18922db4faa4a6e5289
DEPS: lpM:s1:model#Phase, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerAxis, lpM:s1:elements#spatialKeplerEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses Phase
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerAxis
EDGE: lpM:s1:elements#spatialKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerEccVector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerApo (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscVelocity
KIND: definition
TITLE: spatialOscVelocity (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscVelocity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The actual heliocentric velocity V_i = p_i/ν_i + μ ∑_j p_j (LP:MAIN (10), L16, d = 3). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscVelocity.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscVelocity
FROZEN_ANCHOR_ID: planetary.d59.spatialOscVelocity.v1
FROZEN_ABI_SHA256: c5c4e1fac529168f8c43646d947206434b2525754db216fb2bafe5766d04ba35
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses bodyVector3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscVelocity (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscVelocity.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscParam
KIND: definition
TITLE: spatialOscParam (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscParam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The gravitational parameter k_i = 1 + μ ν_i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscParam.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscParam
FROZEN_ANCHOR_ID: planetary.d59.spatialOscParam.v1
FROZEN_ABI_SHA256: 874d4be03742a7a5e7a10fbdb31a55a42e93db6be29cf92f5e6df89e9f94b8be
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscParam (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscParam.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscEnergy
KIND: definition
TITLE: spatialOscEnergy (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: E_i^osc = ¦V_i¦²/2 - k_i/¦q_i¦ (LP:MAIN L16 (42)). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEnergy.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscEnergy
FROZEN_ANCHOR_ID: planetary.d59.spatialOscEnergy.v1
FROZEN_ABI_SHA256: 1c3f1059f7aab9156865ebab07de7d8efada5b3ed5d9ea145891ada687adeb61
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq, lpM:L16:defs#spatialOscParam, lpM:L16:defs#spatialOscVelocity
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceSq
EDGE: lpM:L16:defs#spatialOscParam | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscParam
EDGE: lpM:L16:defs#spatialOscVelocity | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscVelocity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscEnergy (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscAxis
KIND: definition
TITLE: spatialOscAxis (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a_i^osc = -k_i/(2 E_i^osc) (LP:MAIN L16 (42)). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscAxis.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscAxis
FROZEN_ANCHOR_ID: planetary.d59.spatialOscAxis.v1
FROZEN_ABI_SHA256: be13a432a32f06eaf7bf8e65c1dc9d063c2d35c806b93a362f96952437312439
DEPS: lpM:s1:model#Phase, lpM:L16:defs#spatialOscEnergy, lpM:L16:defs#spatialOscParam
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses Phase
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEnergy
EDGE: lpM:L16:defs#spatialOscParam | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscParam
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscAxis (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscEccVector
KIND: definition
TITLE: spatialOscEccVector (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: 𝐞_i^osc = ((¦V_i¦² - k_i/¦q_i¦) q_i - (q_i·V_i) V_i)/k_i (LP:MAIN L16 (42)). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEccVector.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscEccVector
FROZEN_ANCHOR_ID: planetary.d59.spatialOscEccVector.v1
FROZEN_ABI_SHA256: 322e50eedad1837dd96e547926abc70730d48c48ac3ae6b98891357042b75e84
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceDot, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq, lpM:L16:defs#spatialOscParam, lpM:L16:defs#spatialOscVelocity
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceDot | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceDot
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceSq
EDGE: lpM:L16:defs#spatialOscParam | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscParam
EDGE: lpM:L16:defs#spatialOscVelocity | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscVelocity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscEccVector (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscEcc
KIND: definition
TITLE: spatialOscEcc (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscEcc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: e_i^osc = ¦𝐞_i^osc¦ (LP:MAIN L16 (42)), Euclidean length. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEcc.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscEcc
FROZEN_ANCHOR_ID: planetary.d59.spatialOscEcc.v1
FROZEN_ABI_SHA256: c01dad3160ba00498e7091749a0dcd3bca75e959f5c61d545518f7497ee54b55
DEPS: lpM:s1:model#Phase, lpM:s1:data#spaceLength, lpM:L16:defs#spatialOscEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses Phase
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceLength
EDGE: lpM:L16:defs#spatialOscEccVector | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEccVector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscEcc (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEcc.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscPeri
KIND: definition
TITLE: spatialOscPeri (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Osculating perihelion a^osc (1 - e^osc). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPeri.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscPeri
FROZEN_ANCHOR_ID: planetary.d59.spatialOscPeri.v1
FROZEN_ABI_SHA256: f607bde6f14125867faf6530601b3735a0ce944d9b8b547a85b040814db5c2d1
DEPS: lpM:s1:model#Phase, lpM:L16:defs#spatialOscAxis, lpM:L16:defs#spatialOscEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses Phase
EDGE: lpM:L16:defs#spatialOscAxis | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscAxis
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscEcc
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscPeri (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscApo
KIND: definition
TITLE: spatialOscApo (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Osculating aphelion a^osc (1 + e^osc). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscApo.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscApo
FROZEN_ANCHOR_ID: planetary.d59.spatialOscApo.v1
FROZEN_ABI_SHA256: 4169a2ca2838fccbe5e583252d933a154f84da08f26d48250d740df2555d87e6
DEPS: lpM:s1:model#Phase, lpM:L16:defs#spatialOscAxis, lpM:L16:defs#spatialOscEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses Phase
EDGE: lpM:L16:defs#spatialOscAxis | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscAxis
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscEcc
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscApo (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#SpatialOscPhase
KIND: definition
TITLE: SpatialOscPhase (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialOscPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Valid actual-velocity osculating states (LP:MAIN L16, nondegenerate ellipses): positive masses, μ > 0, and for every planet ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPhase.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialOscPhase
FROZEN_ANCHOR_ID: planetary.d59.SpatialOscPhase.v1
FROZEN_ABI_SHA256: 55de99be412cc3aa6d71e52e3b46f9157294990b777c1ffa3662c9440a3794c2
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:L16:defs#spatialOscEcc, lpM:L16:defs#spatialOscEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses spaceLength
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses spatialOscEcc
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses spatialOscEnergy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialOscPhase (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPhase.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#SpatialSourceCanonicalPhase
KIND: definition
TITLE: SpatialSourceCanonicalPhase (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialSourceCanonicalPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The canonical source carrier (LP:MAIN §1 (2)): phase points with positive masses, no planet at the star and negative Kepler energy of every planet. This is SP-MODEL's SpatialElliptic ν. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceCanonicalPhase.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialSourceCanonicalPhase
FROZEN_ANCHOR_ID: planetary.d59.SpatialSourceCanonicalPhase.v1
FROZEN_ABI_SHA256: b2abbd09007c6b34051abd4fd40f13363f3f2b72a883d30af4f7c02919a30758
DEPS: lpM:s1:elements#SpatialElliptic
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#SpatialElliptic | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses SpatialElliptic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialSourceCanonicalPhase (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceCanonicalPhase.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#SpatialSourceOsculatingPhase
KIND: definition
TITLE: SpatialSourceOsculatingPhase (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialSourceOsculatingPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The osculating source carrier (LP:MAIN L16): SP-OSC's SpatialOscPhase n ν μ. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOsculatingPhase.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialSourceOsculatingPhase
FROZEN_ANCHOR_ID: planetary.d59.SpatialSourceOsculatingPhase.v1
FROZEN_ABI_SHA256: 9363a6265245b1e5a17f1b1bfa0b9c1185326f524c8baf505f27fe25c1226828
DEPS: lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialSourceOsculatingPhase (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOsculatingPhase.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerAxis
KIND: definition
TITLE: spatialSourceKeplerAxis (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAxis.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAxis
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAxis.v1
FROZEN_ABI_SHA256: 2d8e5041c2666c4ea07cf34d4b57420b868bcb362ef63a95b5b787235082651c
DEPS: lpM:s1:elements#spatialKeplerAxis, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#spatialKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerAxis
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAxis (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerAction
KIND: definition
TITLE: spatialSourceKeplerAction (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerAction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Λ_i = ν_i √a_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAction.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAction
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAction.v1
FROZEN_ABI_SHA256: 5dfa254c39d05876472ccc2036741976e8bcde824b39509d0e78e411d66018d5
DEPS: lpM:s1:elements#spatialKeplerAction, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#spatialKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerAction
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAction (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAction.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerEccVector
KIND: definition
TITLE: spatialSourceKeplerEccVector (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The eccentricity vector 𝐞_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEccVector.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEccVector
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEccVector.v1
FROZEN_ABI_SHA256: 19466c1f4e528379a1f780425e508e4e093bad6bbb8a7a9acfc0ac7beec3c53f
DEPS: lpM:s1:elements#spatialKeplerEccVector, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#spatialKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spatialKeplerEccVector
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEccVector (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerEcc
KIND: definition
TITLE: spatialSourceKeplerEcc (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerEcc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The eccentricity e_i = ¦𝐞_i¦ on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEcc.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEcc
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEcc.v1
FROZEN_ABI_SHA256: b0194453d629f3233d0b241b7bf74a2620c04a7e188a990c81e14757cd15e57d
DEPS: lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialSourceKeplerEccVector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEcc (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEcc.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourcePlanetAngularMomentum
KIND: definition
TITLE: spatialSourcePlanetAngularMomentum (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourcePlanetAngularMomentum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The individual angular momentum L_i = q_i × p_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourcePlanetAngularMomentum.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum
FROZEN_ANCHOR_ID: planetary.d59.spatialSourcePlanetAngularMomentum.v1
FROZEN_ABI_SHA256: c9ae99ca6bc813fa278608faf90c10a9b03650c5643209dd52adb4d6f6639a3f
DEPS: lpM:s1:elements#planetAngularMomentum3, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#planetAngularMomentum3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses planetAngularMomentum3
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourcePlanetAngularMomentum.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceAngularMomentum
KIND: definition
TITLE: spatialSourceAngularMomentum (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceAngularMomentum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The total angular momentum L = Σ_i q_i × p_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceAngularMomentum.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceAngularMomentum
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceAngularMomentum.v1
FROZEN_ABI_SHA256: 7cd0696d5f64ceaaee58528d1ceb008f044ec2bc8034b1c5bb0c77cfa51c1059
DEPS: lpM:s1:elements#angularMomentum3, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#angularMomentum3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses angularMomentum3
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceAngularMomentum (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceAngularMomentum.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceStrongAMD
KIND: definition
TITLE: spatialSourceStrongAMD (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceStrongAMD
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The strong AMD C = Σ_i Λ_i − ¦L¦ on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceStrongAMD.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceStrongAMD
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceStrongAMD.v1
FROZEN_ABI_SHA256: db40ab8154db4af09586f1dbea057be06d210e1746fdf2cc59d5948eb87e50be
DEPS: lpM:s1:data#spaceLength, lpM:s1:elements#spatialSourceAngularMomentum, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceLength
EDGE: lpM:s1:elements#spatialSourceAngularMomentum | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialSourceAngularMomentum
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialSourceKeplerAction
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceStrongAMD (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceStrongAMD.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerPeri
KIND: definition
TITLE: spatialSourceKeplerPeri (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L89-L91
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a (1 - e) on the canonical negative-energy carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerPeri.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerPeri
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerPeri.v1
FROZEN_ABI_SHA256: 0f954b44e61d475642b9b5755a284bd6d892d0f791c1c888ad5bb4d86a38a85e
DEPS: lpM:s1:elements#SpatialElliptic, lpM:s1:elements#spatialKeplerPeri
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#SpatialElliptic | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses SpatialElliptic
EDGE: lpM:s1:elements#spatialKeplerPeri | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerPeri
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerPeri (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerApo
KIND: definition
TITLE: spatialSourceKeplerApo (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L89-L91
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a (1 + e) on the canonical negative-energy carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerApo.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerApo
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerApo.v1
FROZEN_ABI_SHA256: 93cec71a28e2b1385b1e9368c131383f103a8a4938d79fcd7f9d9dd31435e86d
DEPS: lpM:s1:elements#SpatialElliptic, lpM:s1:elements#spatialKeplerApo
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#SpatialElliptic | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses SpatialElliptic
EDGE: lpM:s1:elements#spatialKeplerApo | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerApo
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerApo (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscParam
KIND: definition
TITLE: spatialSourceOscParam (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscParam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: k_i on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscParam.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscParam
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscParam.v1
FROZEN_ABI_SHA256: 7cc4a890e34e51a19e4dcccaae46a2d6a33ddc268c8a7507be53017527f05ff0
DEPS: lpM:L16:defs#spatialOscParam, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscParam | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses spatialOscParam
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscParam (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscParam.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscEnergy
KIND: definition
TITLE: spatialSourceOscEnergy (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: E_i^osc on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEnergy.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEnergy
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEnergy.v1
FROZEN_ABI_SHA256: 78032793e3980fd9a80aa47db770fb1122a90526656d29a4f206ad8711a0b9c6
DEPS: lpM:L16:defs#spatialOscEnergy, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEnergy
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEnergy (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscAxis
KIND: definition
TITLE: spatialSourceOscAxis (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L528
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a_i^osc on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscAxis.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscAxis
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscAxis.v1
FROZEN_ABI_SHA256: 8132682794d8795bbe9d0dccb709f454e4b8339bde4202b30ffbaf93ae44d776
DEPS: lpM:L16:defs#spatialOscAxis, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscAxis | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscAxis
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscAxis (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscEccVector
KIND: definition
TITLE: spatialSourceOscEccVector (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: 𝐞_i^osc on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEccVector.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEccVector
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEccVector.v1
FROZEN_ABI_SHA256: a76d9ddaef222ec0aec2eb470849d8d481a47f3dcac07dad89bd6fd7d16f015a
DEPS: lpM:L16:defs#spatialOscEccVector, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscEccVector | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEccVector
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEccVector (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscEcc
KIND: definition
TITLE: spatialSourceOscEcc (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscEcc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: e_i^osc on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEcc.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEcc
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEcc.v1
FROZEN_ABI_SHA256: 7c2c4107f425ba9a7a8b7590b02f9811ad0ff3d84a8197d5c4ba448d967d77b9
DEPS: lpM:L16:defs#spatialOscEcc, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEcc
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEcc (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEcc.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscPeri
KIND: definition
TITLE: spatialSourceOscPeri (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L528
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a^osc (1 - e^osc) on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscPeri.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscPeri
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscPeri.v1
FROZEN_ABI_SHA256: d0f2beb1b8b01df0732f4f00cd0c0937a69348dc3248329ced5cd939c5bd8f9d
DEPS: lpM:L16:defs#spatialOscPeri, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscPeri | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscPeri
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscPeri (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscApo
KIND: definition
TITLE: spatialSourceOscApo (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L528
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a^osc (1 + e^osc) on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscApo.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscApo
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscApo.v1
FROZEN_ABI_SHA256: d66fd59c0696142631e582a3970f20f5277f01aba2f2db01ea806949b960c8d8
DEPS: lpM:L16:defs#spatialOscApo, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscApo | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscApo
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscApo (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#spatialSourceBarycentricPositions
KIND: definition
TITLE: spatialSourceBarycentricPositions (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceBarycentricPositions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: the barycentric positions of Lemma 1's explicit inverse (L104) on their source domain ν_i > 0, μ > 0 (literal formula, definitionally the total helper spatialBarycentricPositions) (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricPositions.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceBarycentricPositions
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceBarycentricPositions.v1
FROZEN_ABI_SHA256: 7bc0dbad04af66325815929350cf51358ced2ce7cc9394b923cb84e82da21b32
DEPS: lpM:L1#spatialBarycentricPositions
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#spatialBarycentricPositions | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses spatialBarycentricPositions
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceBarycentricPositions (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricPositions.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#spatialSourceBarycentricVelocities
KIND: definition
TITLE: spatialSourceBarycentricVelocities (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceBarycentricVelocities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: the barycentric velocities of Lemma 1's explicit inverse (L104) on their source domain ν_i > 0, μ > 0 (literal formula, definitionally the total helper spatialBarycentricVelocities) (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricVelocities.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceBarycentricVelocities
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceBarycentricVelocities.v1
FROZEN_ABI_SHA256: 625b6a1a24052b3d6c8ff36714206c239543f7b4b3fdb85842d11fdb66ee66ab
DEPS: lpM:L1#spatialBarycentricVelocities
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#spatialBarycentricVelocities | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses spatialBarycentricVelocities
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceBarycentricVelocities (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricVelocities.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#IsHamiltonianSolutionOn
KIND: definition
TITLE: IsHamiltonianSolutionOn (reused)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L17
PROOF_SOURCE: -
CONTRACT_ID: iso.IsHamiltonianSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: A genuine lifted Hamiltonian solution on an open time interval, in an action domain. The domain is part of the solution concept, not an assumed confinement estimate.
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean
FROZEN_DECL: KAM.Iso.IsHamiltonianSolutionOn
FROZEN_ANCHOR_ID: iso.IsHamiltonianSolutionOn.v1
FROZEN_ABI_SHA256: b20065362bfe0068a5eb3cfdf98a886d7ffd591bdef0464cebfbe3e171d56beb
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.IsHamiltonianSolutionOn (KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition iso.IsHamiltonianSolutionOn.v1, bound as an LP anchor node (Q6); typing data of the moving-Sun solution predicates

NODE: lpM:L17
KIND: lemma
TITLE: Lemma 17: regular spatial Poincare coordinates on the prograde region (44)-(45)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L535-L546
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L548-L578
CONTRACT_ID: lpM:L17
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a reference unit vector e_3; ν > 0 (one planet, d = 3)
SOURCE_QUANTIFIERS: for every e_3 and ν > 0
SOURCE_CONCLUSION: the map (46) with (18)-(19) is a real analytic symplectic diffeomorphism from the region (44) onto the negative-energy spatial states with (q × p)·e_3 > 0, with form dI ∧ dλ + dx ∧ dy + du ∧ dv, energy -ν^3/(2I^2), angular-momentum magnitude G = I - Γ and projection H = I - Γ - Z (45); it is regular at circular and coplanar orbits; for n bodies the fixed-plane deficit is C_{e_3} = Σ_i I_i - L·e_3 = ½Σ_i(x_i^2 + y_i^2 + u_i^2 + v_i^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L17#rotation, lpM:L17#symplectic, lpM:L17#inverse, lpM:L17#deficit-identity, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L17#rotation | docs/tracks/LP/source/MAIN.md#L17@L548-L558 | the rotation R of (46) and (45)
EDGE: lpM:L17#symplectic | docs/tracks/LP/source/MAIN.md#L17@L560-L571 | symplecticity
EDGE: lpM:L17#inverse | docs/tracks/LP/source/MAIN.md#L17@L573-L578 | the analytic inverse onto the prograde region
EDGE: lpM:L17#deficit-identity | docs/tracks/LP/source/MAIN.md#L17@L578-L578 | the fixed-plane deficit identity
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L17@L541-L541 | energy and angular momentum of (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L17#rotation
KIND: step
TITLE: (46): R from t = (u,-v,0)/(2 sqrt G); R orthogonal, det 1, q x p = G R e_3 gives (45)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L548-L558
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L548-L558
CONTRACT_ID: lpM:L17#rotation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L17: a reference unit vector e_3; ν > 0; the region (44) I > 0, λ ∈ 𝕋, (x, y, u, v) ∈ ℝ^4, Γ = (x^2 + y^2)/2, Z = (u^2 + v^2)/2, Γ + Z < I
SOURCE_QUANTIFIERS: for every ν > 0 and every point of (44) (inherited from lpM:L17)
SOURCE_CONCLUSION: with Q, P of (19) embedded in the plane, G = I - Γ > 0, t = (u, -v, 0)/(2√G), c = √(1 - ¦t¦^2), R = (1 - 2¦t¦^2)Id + 2tt^T + 2c[t]_×, q = RQ, p = RP (46); ¦t¦^2 = Z/(2G) < 1/2 makes the roots analytic; [t]_×^2 = tt^T - ¦t¦^2 Id gives R^TR = Id, det R = 1, Re_3 = (-cv/√G, -cu/√G, 1 - Z/G), hence q × p = G Re_3 and (45); (46) is the definition also at Γ = 0 or Z = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7, lpM:L7#chart-formula
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L17@L548-L548 | the planar chart (18)-(19) with angular momentum G = I - Γ
EDGE: lpM:L7#chart-formula | docs/tracks/LP/source/MAIN.md#L17@L548-L548 | Q, P are (19)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L17#symplectic
KIND: step
TITLE: p.dq = I dlambda + Gamma d(-varpi) + Z d(-h_n) + d(2Ie sin E); density of e > 0, Z > 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L541-L541
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L560-L571
CONTRACT_ID: lpM:L17#symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L17: a reference unit vector e_3; ν > 0; the region (44) I > 0, λ ∈ 𝕋, (x, y, u, v) ∈ ℝ^4, Γ = (x^2 + y^2)/2, Z = (u^2 + v^2)/2, Γ + Z < I
SOURCE_QUANTIFIERS: for every ν > 0 and every point of (44) (inherited from lpM:L17)
SOURCE_CONCLUSION: where e > 0 and Z > 0, with node longitude h_n, inclination ι and perihelion longitude ϖ, R = R_z(h_n)R_x(ι)R_z(-h_n); the varying rotations contribute G dg and H dh_n (zero about the line of nodes), so with Lemma 7's computation p·dq = I dλ + Γ d(-ϖ) + Z d(-h_n) + d(2Ie sin E); exterior differentiation gives the form; the set e > 0, Z > 0 is dense and both sides are analytic, so equality extends to the circular and coplanar loci
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L17#rotation, lpM:L7#symplectic, lpM:ext-identity-theorem
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L17#rotation | docs/tracks/LP/source/MAIN.md#L17@L566-L566 | the rotation R and q × p = G Re_3
EDGE: lpM:L7#symplectic | docs/tracks/LP/source/MAIN.md#L17@L566-L566 | the unrotated calculation of Lemma 7
EDGE: lpM:ext-identity-theorem | docs/tracks/LP/source/MAIN.md#L17@L571-L571 | analytic equality extends from a dense set
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L17#inverse
KIND: step
TITLE: inverse from w-hat = (q x p)/G: c, u, v reconstruct R; Lemma 7's inverse gives x, y, lambda
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L573-L578
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L573-L578
CONTRACT_ID: lpM:L17#inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L17: a reference unit vector e_3; ν > 0; the region (44) I > 0, λ ∈ 𝕋, (x, y, u, v) ∈ ℝ^4, Γ = (x^2 + y^2)/2, Z = (u^2 + v^2)/2, Γ + Z < I
SOURCE_QUANTIFIERS: for every ν > 0 and every point of (44) (inherited from lpM:L17)
SOURCE_CONCLUSION: for ŵ = (q × p)/G with ŵ_3 > 0: recover I, G from energy and angular momentum, c = √((1 + ŵ_3)/2), u = -√G ŵ_2/c, v = -√G ŵ_1/c reconstruct R; R^{-1}q, R^{-1}p are planar with positive angular momentum and Lemma 7's inverse recovers x, y, λ: onto, unique modulo 2π, analytically invertible, image exactly the prograde negative-energy region
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#inverse, lpM:L17#rotation
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#inverse | docs/tracks/LP/source/MAIN.md#L17@L578-L578 | Lemma 7's explicit inverse
EDGE: lpM:L17#rotation | docs/tracks/LP/source/MAIN.md#L17@L576-L576 | R and q × p = G Re_3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L17#deficit-identity
KIND: claim
TITLE: fixed-plane deficit C_{e_3} = sum I_i - L.e_3 = ¦z¦^2/2 (summing (45))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L545-L546
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L578-L578
CONTRACT_ID: lpM:L17#deficit-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L17: a reference unit vector e_3; ν > 0; the region (44) I > 0, λ ∈ 𝕋, (x, y, u, v) ∈ ℝ^4, Γ = (x^2 + y^2)/2, Z = (u^2 + v^2)/2, Γ + Z < I; n bodies
SOURCE_QUANTIFIERS: for every point of the n-fold product chart
SOURCE_CONCLUSION: C_{e_3} = Σ_i I_i - L·e_3 = Σ_i(Γ_i + Z_i) = ½Σ_i(x_i^2 + y_i^2 + u_i^2 + v_i^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L17#rotation
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L17#rotation | docs/tracks/LP/source/MAIN.md#L17@L578-L578 | (45): H_i = I_i - Γ_i - Z_i is the e_3-projection of L_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18
KIND: lemma
TITLE: Lemma 18: spatial whole-sublevel complex domain (47), m = 2n
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L582-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L588-L597
CONTRACT_ID: lpM:L18
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data (n, ν, 𝒜, δ) of lpM:s1:data, spatial (d = 3); 𝓛_δ as in Lemma 8
SOURCE_QUANTIFIERS: there exist r_*, s, b, M > 0 (fixed first, independent of the reference direction); then for every I^0 ∈ 𝓛_δ, with Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)
SOURCE_CONCLUSION: the conclusions of Lemma 8 hold spatially with m = 2n slow pairs and the product chart of Lemma 17; the domain includes all states allowed by (6) after aligning e_3 with the initial total angular momentum
CONSTANT_SCOPE: r_*, s, b, M depend only on (n, ν, 𝒜, δ), not on the reference direction
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L18#margins, lpM:L18#whole-ball-safe, lpM:L18#extension, lpM:L18#rotation-invariance, lpM:L18#alignment, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L18#margins | docs/tracks/LP/source/MAIN.md#L18@L588-L593 | the fixed positive margins
EDGE: lpM:L18#whole-ball-safe | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | Lemma 5 on the whole ball
EDGE: lpM:L18#extension | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the complex extension (Lemma 8's argument in 6n coordinates)
EDGE: lpM:L18#rotation-invariance | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | independence of the reference direction
EDGE: lpM:L18#alignment | docs/tracks/LP/source/MAIN.md#L18@L597-L597 | the alignment of e_3 with L
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L18@L584-L584 | B occurs in (47)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N2, N3 (via Lemma 8's construction), N12 (AMENDMENTS.md L21: the spatial tube typing is engineering only, no graph obligation)

NODE: lpM:L18#margins
KIND: step
TITLE: Gamma_i + Z_i <= I_i - 3 delta/16: G_i, H_i >= 3 delta/16, c_i^2 > 1/2
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L582-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L588-L593
CONTRACT_ID: lpM:L18#margins
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47); real ‖I - I^0‖_∞ ≤ 4r_g and z ∈ (47)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: Γ_i + Z_i ≤ B(I^0) - δ/4 ≤ B(I) - 3δ/16 ≤ I_i - 3δ/16, hence G_i ≥ 3δ/16, H_i ≥ 3δ/16, c_i^2 = 1 - Z_i/(2G_i) > 1/2: all new radicands and denominators in (46) have a fixed positive margin
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#shared-tube, lpM:L17, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/MAIN.md#L18@L590-L590 | the real action neighborhood of Lemma 8 with Ω_B(4r_g) ≤ δ/16
EDGE: lpM:L17 | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | (45): G = I - Γ, H = I - Γ - Z
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L18@L590-L590 | B(I) ≤ B_⋆(I) ≤ I_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18#whole-ball-safe
KIND: step
TITLE: fixed-plane deficit = ¦z¦^2/2 >= sum I_i D(e_i): Lemma 5 applies on the whole ball
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L586-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L593-L593
CONTRACT_ID: lpM:L18#whole-ball-safe
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: the fixed-plane deficit equals ¦z¦_2^2/2 and each I_i - H_i ≥ I_i - ¦L_i¦ = I_i D(e_i); hence Lemma 5 applies to every point of the ball, including points whose total angular momentum is not parallel to e_3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L17#deficit-identity, lpM:L2, lpM:L5, lpM:L18#margins, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L17#deficit-identity | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | C_{e_3} = ¦z¦^2/2
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | ¦L_i¦ = I_i √(1 - e_i^2) by (11)
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | Lemma 5 in its list form Σ I_i D(e_i) ≤ B(I) - m
EDGE: lpM:L18#margins | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | Σ(Γ_i + Z_i) ≤ B(I) - 3δ/16
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | D(e) = 1 - √(1 - e^2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18#extension
KIND: step
TITLE: Lemma 8's gluing, uniform widths and complex denominators verbatim in 6n coordinates
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L582-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L595-L595
CONTRACT_ID: lpM:L18#extension
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: the family over compact 𝓛_δ, the real action neighborhood and a full angle cell is compact; (18)-(19) and (46) with the margins give holomorphic local extensions; the gluing, uniform-width and complex-denominator arguments of Lemma 8 apply verbatim in 6n coordinates; every (q_i - q_j)·(q_i - q_j) has positive real part on the chosen complex tube
CONSTANT_SCOPE: the widths depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L18#margins, lpM:L18#whole-ball-safe, lpM:L8#newton-extension, lpM:L8#gluing, lpM:L8#denominators, lpM:L8#widths, lpM:L8#exact-split, lpM:L17
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L18#margins | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the positive margins of (46)
EDGE: lpM:L18#whole-ball-safe | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the real phases are safe (Lemma 5)
EDGE: lpM:L8#newton-extension | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the local extension argument
EDGE: lpM:L8#gluing | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the gluing and finite-subcover argument
EDGE: lpM:L8#denominators | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the complex-denominator estimate
EDGE: lpM:L8#widths | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the uniform widths and bounds
EDGE: lpM:L8#exact-split | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the product chart gives the exact split h + μf
EDGE: lpM:L17 | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the chart (46) is analytic on its region
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18#rotation-invariance
KIND: step
TITLE: scalar products and potentials are invariant under a simultaneous rotation: bounds independent of the frame
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L584-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L595-L595
CONTRACT_ID: lpM:L18#rotation-invariance
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: the exact scalar products and Newtonian potentials are invariant under a simultaneous real orthogonal rotation of positions and momenta, so the domain bounds can be chosen for an abstract orthonormal frame, independently of its orientation
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model, lpM:L18#extension
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | (1) is rotation invariant
EDGE: lpM:L18#extension | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the bounds being made frame-independent
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18#alignment
KIND: step
TITLE: one fixed rotation per solution takes L/¦L¦ to e_3; C_{e_3} = C along it; Lemma 17 covers it
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L586-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L597-L597
CONTRACT_ID: lpM:L18#alignment
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47); an actual initial state with (6)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: Lemma 3 gives L ≠ 0; a fixed orientation-preserving orthogonal map taking L/¦L¦ to e_3, applied to q and p, is symplectic (one per solution, constants rotation invariant); conservation of L gives C_{e_3} = C along the solution; positive individual projections let Lemma 17 cover it until the stopped boundary
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3, lpM:L18#rotation-invariance, lpM:L17
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3 | docs/tracks/LP/source/MAIN.md#L18@L597-L597 | Lemma 3: L ≠ 0 and positive projections H_i under C < B_⋆ (supplied by (6)), and conservation of L
EDGE: lpM:L18#rotation-invariance | docs/tracks/LP/source/MAIN.md#L18@L597-L597 | constants are rotation invariant
EDGE: lpM:L17 | docs/tracks/LP/source/MAIN.md#L18@L597-L597 | the chart covers the prograde states
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:T19
KIND: theorem
TITLE: Theorem 19: spatial nonresonant exponential safety (the §1 conclusion for d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 3; n ≥ 2; ν_i > 0 with max_i ν_i = 1; 𝒜 ⊂ {0 < a_1 < ... < a_n} compact; δ, γ > 0; τ > n - 1
SOURCE_QUANTIFIERS: there exist μ_0, c, T_0, A_I, A_a, d_⋆, d_pair, A_osc > 0; then for every 0 < μ ≤ μ_0 and every spatial initial state with q_i ≠ 0, E_i < 0 and (6), including circular or coplanar initial orbits
SOURCE_CONCLUSION: the conclusion of §1 in d = 3: the unique maximal solution exists on [-T_μ, T_μ] (7), with ellipticity, I(t) ∈ Q, (8), (9), the star and all pair distances, and the osculating radii and half gaps
CONSTANT_SCOPE: the constants depend only on (n, ν, 𝒜, δ, γ, τ) (d = 3) and precede μ and the initial state; N10
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:T19#align, lpM:T19#apply-L14, lpM:T19#osculating, lpM:T19#reconstruction, lpM:T19#unrotate, lpM:s1:data, lpM:s1:dioph, lpM:s1:elements, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:chamber#chamber
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T19#align | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | alignment, the ball (47), the symplectic chart
EDGE: lpM:T19#apply-L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 14 with m = 2n
EDGE: lpM:T19#osculating | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 16 in dimension three
EDGE: lpM:T19#reconstruction | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 1
EDGE: lpM:T19#unrotate | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | back to the original frame
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L70-L70 | the fixed data
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | (6) contains (5)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | C, a, e, I
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | B occurs in (6)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L79-L79 | I(t) ∈ Q
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: spatial MAIN theorem; its frozen statement is LP2 (packet LP-athm-w3). 'Lemmas 1-6, 9-14, 16-18' is read with N7 (Lemmas 12, 13 are alternative routes inside Lemma 14). AMENDED: N7, N8, N10.

NODE: lpM:T19#align
KIND: step
TITLE: Lemma 18 aligns the frame, gives the ball (47) and the collar; Lemma 17 symplectic chart; (1), (4) exact
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#align
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19)
SOURCE_CONCLUSION: after the fixed rotation of Lemma 18, the entire ball (47) and a uniform complex collar are available; the chart is symplectic (Lemma 17) and the Kepler energy and exact perturbation are (1), (4)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L18, lpM:L18#alignment, lpM:L17, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L18 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the aligned frame and the domain
EDGE: lpM:L18#alignment | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | one fixed rotation per solution
EDGE: lpM:L17 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the symplectic chart
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the Kepler energy h of (4)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:T19#apply-L14
KIND: step
TITLE: n fast angles, 2n slow pairs; ¦z(t)¦^2/2 = C(t) by conservation; Lemma 14 proves (7)-(9)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#apply-L14
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19)
SOURCE_CONCLUSION: with n fast angles and m = 2n slow pairs, the drift suppliers apply with only dimension constants changed (small divisors k·ω(I^0), k ∈ ℤ^n, no secular divisors); conservation of the vector angular momentum gives ¦z(t)¦^2/2 = C(t) in the physical chart; these discharge every condition of Lemma 14, which proves the exponential interval, the action and AMD bounds, moving-threshold safety, separation and continuation
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L14, lpM:T19#align, lpM:L17#deficit-identity, lpM:L3#dynamic
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 14
EDGE: lpM:T19#align | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the chart and domain premises
EDGE: lpM:L17#deficit-identity | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | C_{e_3} = ¦z¦^2/2
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | conservation of L keeps C_{e_3} = C
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:T19#osculating
KIND: step
TITLE: Lemma 16 in dimension three: the osculating conclusion
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#osculating
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19); t ∈ [-T_μ, T_μ]
SOURCE_CONCLUSION: as lpM:T15#osculating, in d = 3
CONSTANT_SCOPE: A, A_osc depend only on Lemma 5's compact set and the masses
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L16, lpM:L16#mu0-choice, lpM:L16#half-gaps, lpM:L14#separation, lpM:T19#apply-L14
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 16 (d = 3)
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/source/MAIN.md#L16@L528-L528 | N10
EDGE: lpM:L16#half-gaps | docs/tracks/LP/source/MAIN.md#L16@L529-L529 | the osculating half gaps
EDGE: lpM:L14#separation | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the orbit stays in Lemma 5's compact set (m = δ/2)
EDGE: lpM:T19#apply-L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the solution on [-T_μ, T_μ]
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N10 (AMENDMENTS.md L19)

NODE: lpM:T19#reconstruction
KIND: step
TITLE: Lemma 1 reconstructs the exact Newtonian solution (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#reconstruction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19)
SOURCE_CONCLUSION: the solution reconstructs a Newtonian (1+n)-body solution with masses (1, μν_i); star and pair distances are ¦q_i¦, ¦q_i - q_j¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1, lpM:T19#apply-L14
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 1
EDGE: lpM:T19#apply-L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the collision-free solution
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:T19#unrotate
KIND: step
TITLE: the inverse fixed rotation returns to the original frame without changing any inequality
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#unrotate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19)
SOURCE_CONCLUSION: all the inequalities of the conclusion are invariant under the inverse fixed rotation
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L18#rotation-invariance, lpM:T19#apply-L14, lpM:T19#osculating
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L18#rotation-invariance | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | rotation invariance of lengths, H and C
EDGE: lpM:T19#apply-L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the inequalities in the aligned frame
EDGE: lpM:T19#osculating | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the osculating inequalities in the aligned frame
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L2#spatialSourceKeplerAxis_pos
KIND: lemma
TITLE: 0 < a_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
CONTRACT_ID: planetary.d59.spatialSourceKeplerAxis_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: 0 < a_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerAxisPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAxis_pos.v1
FROZEN_ABI_SHA256: c473fbddfb2da335b627a6e34dae5eb2013d50c912a601e2700271611738f6de
DEPS: lpM:s1:elements, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | when E_i < 0, a_i = -1/(2E_i) > 0 by (2)
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the statement uses spatialSourceKeplerAxis
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerAxisPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAxis_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerAction_pos
KIND: lemma
TITLE: 0 < Λ_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
CONTRACT_ID: planetary.d59.spatialSourceKeplerAction_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: 0 < Λ_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAction_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAction_pos.v1
FROZEN_ABI_SHA256: 0b19b3858aac95d3274a9b1fb596545adf71161567d87d387b316a6d16c33269
DEPS: lpM:s1:elements, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | Λ_i = ν_i √a_i with ν_i, a_i > 0
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses spatialSourceKeplerAction
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAction_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerAction_sq
KIND: lemma
TITLE: Λ_i^2 = ν_i^2 a_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
CONTRACT_ID: planetary.d59.spatialSourceKeplerAction_sq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: Λ_i^2 = ν_i^2 a_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionSq.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAction_sq
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAction_sq.v1
FROZEN_ABI_SHA256: d57d7de1afd13132b9cbb2fb396ba5e23492418758b2e34a499dba10ed67c8ab
DEPS: lpM:s1:elements, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | Λ_i = ν_i √a_i, (2)
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses spatialSourceKeplerAxis
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAction_sq (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionSq.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_sq
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerEcc_sq
KIND: lemma
TITLE: e_i^2 = 1 - ¦L_i¦^2/Λ_i^2 (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: planetary.d59.spatialSourceKeplerEcc_sq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: e_i^2 = 1 - ¦L_i¦^2/Λ_i^2
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccSq.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEcc_sq.v1
FROZEN_ABI_SHA256: 7c5b493f48a3e2ce6b74f0f11714adc2a0f3ee300381f0060aa789d5bb6c4558
DEPS: lpM:L2, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerEcc, lpM:s1:elements#spatialSourcePlanetAngularMomentum
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | (11): e^2 = 1 - ¦q × v¦^2/a and ¦q × p¦ = I√(1 - e^2)
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerEcc
EDGE: lpM:s1:elements#spatialSourcePlanetAngularMomentum | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourcePlanetAngularMomentum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccSq.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_sq
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerEcc_nonneg
KIND: lemma
TITLE: 0 ≤ e_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L34-L34
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L34-L34
CONTRACT_ID: planetary.d59.spatialSourceKeplerEcc_nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: 0 ≤ e_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccNonneg.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEcc_nonneg.v1
FROZEN_ABI_SHA256: 26d964de20b3d56a50241c95f4b417f3d6825fe3d0e324616c2d4d941115b974
DEPS: lpM:s1:elements, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L34-L34 | e_i = ¦e_i¦ is a length
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L34-L34 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#s1@L34-L34 | the statement uses spatialSourceKeplerEcc
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccNonneg.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_nonneg
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerEcc_le_one
KIND: lemma
TITLE: e_i ≤ 1 (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: planetary.d59.spatialSourceKeplerEcc_le_one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: e_i ≤ 1
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccLeOne.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEcc_le_one.v1
FROZEN_ABI_SHA256: 43c82cd83205dbd5a55345bd116cd00b1f3e4d4a865545a6c96f02b887ffe426
DEPS: lpM:L2, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | (11) gives e^2 = 1 - ¦q × v¦^2/a ≤ 1
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerEcc
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccLeOne.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_le_one
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourcePlanetAngularMomentum_length
KIND: lemma
TITLE: ¦L_i¦ = Λ_i √(1 - e_i^2) (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: planetary.d59.spatialSourcePlanetAngularMomentum_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: ¦L_i¦ = Λ_i √(1 - e_i^2)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourcePlanetAngularMomentum_length.v1
FROZEN_ABI_SHA256: f6e9113ab208e30a3a2469cf64d5ccf4d3d6c11e900d75ecaa1cef164ceed8fd
DEPS: lpM:L2, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerEcc, lpM:s1:elements#spatialSourcePlanetAngularMomentum
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | (11): ¦q × p¦ = I √(1 - e^2)
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerEcc
EDGE: lpM:s1:elements#spatialSourcePlanetAngularMomentum | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourcePlanetAngularMomentum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourcePlanetAngularMomentum_length_le
KIND: lemma
TITLE: ¦L_i¦ ≤ Λ_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: planetary.d59.spatialSourcePlanetAngularMomentum_length_le
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: ¦L_i¦ ≤ Λ_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLengthLe.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le
FROZEN_ANCHOR_ID: planetary.d59.spatialSourcePlanetAngularMomentum_length_le.v1
FROZEN_ABI_SHA256: 2d950df835a3f9ae44e6f4c05773881cd203df43080a359b47e707f7a1fe785f
DEPS: lpM:L2, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourcePlanetAngularMomentum
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | (11): ¦q × p¦ = I √(1 - e^2) ≤ I
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourcePlanetAngularMomentum | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourcePlanetAngularMomentum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLengthLe.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerPeri_le_length
KIND: lemma
TITLE: a_i(1 - e_i) ≤ ¦q_i¦ (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L122
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: planetary.d59.spatialSourceKeplerPeri_le_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: a_i(1 - e_i) ≤ ¦q_i¦
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerPeriLeLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerPeri_le_length.v1
FROZEN_ABI_SHA256: ab638195e8eae674077c06a78ac384ef3c34d38b87ceda9bbe1ae46468fc925a
DEPS: lpM:L2, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerPeri
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L128-L128 | (12): a(1 - e) ≤ ¦q¦
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerPeri | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses spatialSourceKeplerPeri
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerPeriLeLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerPeri_le_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerApo_ge_length
KIND: lemma
TITLE: ¦q_i¦ ≤ a_i(1 + e_i) (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L122
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: planetary.d59.spatialSourceKeplerApo_ge_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: ¦q_i¦ ≤ a_i(1 + e_i)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerApoGeLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerApo_ge_length.v1
FROZEN_ABI_SHA256: 686e73b0b457426b316776af53db5f711e46c8b9b9c5642bad9b9480cdb8e2e6
DEPS: lpM:L2, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerApo
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L128-L128 | (12): ¦q¦ ≤ a(1 + e)
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerApo | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses spatialSourceKeplerApo
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerApoGeLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerApo_ge_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L3#spatialSourceStrongAMD_nonneg
KIND: lemma
TITLE: 0 ≤ C (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L132
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: planetary.d59.spatialSourceStrongAMD_nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z
SOURCE_CONCLUSION: 0 ≤ C
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceStrongAMDNonneg.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceStrongAMD_nonneg.v1
FROZEN_ABI_SHA256: 6d9389729156647f75b9ad2458784dc0e7560c2158efa002c9c21f01705778fd
DEPS: lpM:L3#amd-nonneg, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#amd-nonneg | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | ¦L¦ ≤ Σ¦L_i¦ ≤ Σ I_i
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L3@L132-L132 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/source/MAIN.md#L3@L132-L132 | the statement uses spatialSourceStrongAMD
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceStrongAMDNonneg.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceStrongAMD_nonneg
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L3#spatialSourceAction_mul_eccDeficit_le
KIND: lemma
TITLE: Σ_i Λ_i(1 - √(1 - e_i^2)) ≤ C (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L135
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: planetary.d59.spatialSourceAction_mul_eccDeficit_le
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z
SOURCE_CONCLUSION: Σ_i Λ_i(1 - √(1 - e_i^2)) ≤ C
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceActionMulEccDeficitLe.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceAction_mul_eccDeficit_le.v1
FROZEN_ABI_SHA256: 3bcbb6495450f26b39bc3c82017a9acc587b71a13a08b259b49b0a58a3460534
DEPS: lpM:L3#deficit, lpM:L3#deficit-zero-L, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerEcc, lpM:s1:elements#spatialSourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#deficit | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | for L ≠ 0: the inequality of (13)
EDGE: lpM:L3#deficit-zero-L | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the case L = 0, which the frozen statement includes
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L3@L133-L133 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#L3@L133-L133 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#L3@L133-L133 | the statement uses spatialSourceKeplerEcc
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/source/MAIN.md#L3@L133-L133 | the statement uses spatialSourceStrongAMD
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceActionMulEccDeficitLe.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscParam_pos
KIND: lemma
TITLE: 0 < k_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L512-L512
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscParam_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: 0 < k_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscParamPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscParam_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscParam_pos.v1
FROZEN_ABI_SHA256: 6acaa4099fabe01d3477bcadec3bb8f89e454983d437d299f8bbd96abfaae3f4
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscParam, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | k_i = 1 + μν_i with μ, ν_i > 0
EDGE: lpM:L16:defs#spatialSourceOscParam | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the statement uses spatialSourceOscParam
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscParam_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscParamPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscParam_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscEnergy_neg
KIND: lemma
TITLE: E_i^osc < 0 (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscEnergy_neg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: E_i^osc < 0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEnergyNeg.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEnergy_neg
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEnergy_neg.v1
FROZEN_ABI_SHA256: 2361214739322a443c11e55d2ac6581a4bd6323822478fed43ca89583698bea9
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscEnergy, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | E^osc of (42), negative on the carrier
EDGE: lpM:L16:defs#spatialSourceOscEnergy | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses spatialSourceOscEnergy
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEnergy_neg (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEnergyNeg.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEnergy_neg
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscEcc_lt_one
KIND: lemma
TITLE: e_i^osc < 1 (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscEcc_lt_one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: e_i^osc < 1
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccLtOne.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEcc_lt_one.v1
FROZEN_ABI_SHA256: 5c0b552b09cf9a3239d0d2e632f55a635354c80cd68ab4889dd2ef974ad11ed7
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | e^osc of (42), below one on the carrier
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccLtOne.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_lt_one
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscEcc_nonneg
KIND: lemma
TITLE: 0 ≤ e_i^osc (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L518-L518
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscEcc_nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: 0 ≤ e_i^osc
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccNonneg.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEcc_nonneg.v1
FROZEN_ABI_SHA256: 4b620ed7bef0718a24625ea9f2c7dd0b68977e41aff8645646cc09b982741b17
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | e^osc = ¦e^osc¦ is a length
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccNonneg.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_nonneg
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscAxis_pos
KIND: lemma
TITLE: 0 < a_i^osc (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscAxis_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: 0 < a_i^osc
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscAxisPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscAxis_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscAxis_pos.v1
FROZEN_ABI_SHA256: e2a68783cebe55f3388defeb40ed9632ca90c375a75edb8466da6439919823e1
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscAxis, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L516-L516 | a^osc = -k_i/(2E^osc) with k_i > 0, E^osc < 0
EDGE: lpM:L16:defs#spatialSourceOscAxis | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses spatialSourceOscAxis
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscAxis_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscAxisPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscAxis_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscPeri_pos
KIND: lemma
TITLE: 0 < a_i^osc(1 - e_i^osc) (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscPeri_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: 0 < a_i^osc(1 - e_i^osc)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscPeri_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscPeri_pos.v1
FROZEN_ABI_SHA256: a757086991b433764db2d8127482c0e8268c7764364f1090858354add5ea14df
DEPS: lpM:L16#spatialSourceOscAxis_pos, lpM:L16#spatialSourceOscEcc_lt_one, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#spatialSourceOscAxis_pos | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | a^osc > 0
EDGE: lpM:L16#spatialSourceOscEcc_lt_one | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | e^osc < 1
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscPeri_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscPeri_le_length
KIND: lemma
TITLE: a_i^osc(1 - e_i^osc) ≤ ¦q_i¦ (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L525-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscPeri_le_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: a_i^osc(1 - e_i^osc) ≤ ¦q_i¦
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriLeLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscPeri_le_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscPeri_le_length.v1
FROZEN_ABI_SHA256: bc95e8ef9395be519563edde8996304cd2a61e8738af6d0e2110b2aa3cfcd043
DEPS: lpM:L16#tangent-ellipse, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#tangent-ellipse | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | Lemma 2 with parameter k_i: the ellipse contains the position
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses spaceLength
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscPeri_le_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriLeLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_le_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscApo_ge_length
KIND: lemma
TITLE: ¦q_i¦ ≤ a_i^osc(1 + e_i^osc) (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L525-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscApo_ge_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: ¦q_i¦ ≤ a_i^osc(1 + e_i^osc)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscApoGeLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscApo_ge_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscApo_ge_length.v1
FROZEN_ABI_SHA256: bf21b051b14b444c3d627dfe57c84ded7c73481f4cb387ab34179cc1e28ce82c
DEPS: lpM:L16#tangent-ellipse, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:L16:defs#spatialSourceOscApo, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#tangent-ellipse | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | Lemma 2 with parameter k_i: the ellipse contains the position
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses spaceLength
EDGE: lpM:L16:defs#spatialSourceOscApo | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses spatialSourceOscApo
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscApo_ge_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscApoGeLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscApo_ge_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:T19#spatial_strongAMD_exponentialSafety
KIND: theorem
TITLE: LP2: spatial strong-AMD exponential safety (Theorem 19 with Lemma 16)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: planetary.d59.spatial_strongAMD_exponentialSafety
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; τ > n - 1; spatial (d = 3)
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ spatial phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i, Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-1/(2(τ+1))}): ∃ z : ℝ → spatial phases, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: z(0) = z_0; z solves the spatial (1) on [-T, T] without collision and agrees with every local solution; the barycentric reconstruction solves Newton's equations with masses (1, μν_i); for every t: elliptic, Λ(t) ∈ Q, C(t) ≤ B(Λ(t)) - δ/2, the drift bounds A_Λ√μ, A_a√μ, nA_Λ√μ of (8), (9) with d_⋆, d_pair, star distances ≥ d_⋆, pair distances ≥ d_pair; nondegenerate osculating elements with a^osc > 0, e^osc < 1, a^osc(1 - e^osc) ≤ ¦q_i¦ ≤ a^osc(1 + e^osc), ¦a^osc - a¦ + ¦e^osc - e¦ ≤ A_elem μ, perihelion and aphelion errors ≤ A_osc μ, osculating gaps ≥ d_⋆/2, d_pair/2 (as in LP1, spatial carriers)
CONSTANT_SCOPE: μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ, τ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety
FROZEN_ANCHOR_ID: planetary.d59.spatial_strongAMD_exponentialSafety.v1
FROZEN_ABI_SHA256: 9d34c2a7b12a0614bfb923fbfffc0c67809cc2097021af4eddfbcb0c5995e7a8
DEPS: lpM:T19, lpM:T19#reconstruction, lpM:T19#osculating, lpM:L16#mu0-choice, lpM:L16#spatialSourceOscAxis_pos, lpM:L16#spatialSourceOscPeri_le_length, lpM:L16#spatialSourceOscApo_ge_length, lpM:L16#spatialSourceOscEnergy_neg, lpM:L16#spatialSourceOscEcc_lt_one, lpM:s1:dioph#IsDiophantine, lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:model#IsSpatialMovingSolutionOn, lpM:L1#IsSpatialNewtonSolutionOn, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerEnergy, lpM:s1:model#spatialMasses, lpM:s1:model#SpatialMovingUniqueOn, lpM:L16:defs#spatialOscEcc, lpM:L16:defs#spatialOscEnergy, lpM:L1#spatialSourceBarycentricPositions, lpM:L1#spatialSourceBarycentricVelocities, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerApo, lpM:s1:elements#spatialSourceKeplerAxis, lpM:s1:elements#spatialSourceKeplerEccVector, lpM:s1:elements#spatialSourceKeplerPeri, lpM:L16:defs#spatialSourceOscApo, lpM:L16:defs#spatialSourceOscAxis, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#spatialSourceOscEccVector, lpM:L16:defs#spatialSourceOscEnergy, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase, lpM:s1:elements#spatialSourceStrongAMD, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T19 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | LP2 is Theorem 19 (the §1 conclusion in d = 3)
EDGE: lpM:T19#reconstruction | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the Newtonian reconstruction clause
EDGE: lpM:T19#osculating | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the osculating clauses, including A_elem
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/source/MAIN.md#L16@L528-L528 | A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)
EDGE: lpM:L16#spatialSourceOscAxis_pos | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | a^osc > 0
EDGE: lpM:L16#spatialSourceOscPeri_le_length | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | a^osc(1 - e^osc) ≤ ¦q_i¦
EDGE: lpM:L16#spatialSourceOscApo_ge_length | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | ¦q_i¦ ≤ a^osc(1 + e^osc)
EDGE: lpM:L16#spatialSourceOscEnergy_neg | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | E^osc < 0
EDGE: lpM:L16#spatialSourceOscEcc_lt_one | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | e^osc < 1
EDGE: lpM:s1:dioph#IsDiophantine | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses IsDiophantine
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses bodyVector3
EDGE: lpM:s1:model#IsSpatialMovingSolutionOn | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses IsSpatialMovingSolutionOn
EDGE: lpM:L1#IsSpatialNewtonSolutionOn | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses IsSpatialNewtonSolutionOn
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialKeplerEnergy
EDGE: lpM:s1:model#spatialMasses | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialMasses
EDGE: lpM:s1:model#SpatialMovingUniqueOn | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses SpatialMovingUniqueOn
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialOscEcc
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialOscEnergy
EDGE: lpM:L1#spatialSourceBarycentricPositions | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceBarycentricPositions
EDGE: lpM:L1#spatialSourceBarycentricVelocities | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceBarycentricVelocities
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerApo | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerApo
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerAxis
EDGE: lpM:s1:elements#spatialSourceKeplerEccVector | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerEccVector
EDGE: lpM:s1:elements#spatialSourceKeplerPeri | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerPeri
EDGE: lpM:L16:defs#spatialSourceOscApo | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscApo
EDGE: lpM:L16:defs#spatialSourceOscAxis | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscAxis
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#spatialSourceOscEccVector | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscEccVector
EDGE: lpM:L16:defs#spatialSourceOscEnergy | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscEnergy
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses SpatialSourceOsculatingPhase
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceStrongAMD
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses AdjIdx
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses AdjIdx.upperIdx
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses chamber
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses orderedStrongThreshold
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety (KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety
NOTE: Anchor LP2. Spatial instance of the §1 conclusion (Theorem 19), with Lemma 16's clauses and N10's constant relations; A_elem is the constant A of (43). AMENDED: N8, N10.

NODE: lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger
KIND: corollary
TITLE: LP2-H: LP2 at tau = n - 1/2 (exponent 1/(2n+1))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
CONTRACT_ID: planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; spatial (d = 3); τ = n - 1/2 fixed
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ spatial phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i, Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-1/(2n+1)}): ∃ z : ℝ → spatial phases, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: z(0) = z_0; z solves the spatial (1) on [-T, T] without collision and agrees with every local solution; the barycentric reconstruction solves Newton's equations with masses (1, μν_i); for every t: elliptic, Λ(t) ∈ Q, C(t) ≤ B(Λ(t)) - δ/2, the drift bounds A_Λ√μ, A_a√μ, nA_Λ√μ of (8), (9) with d_⋆, d_pair, star distances ≥ d_⋆, pair distances ≥ d_pair; nondegenerate osculating elements with a^osc > 0, e^osc < 1, a^osc(1 - e^osc) ≤ ¦q_i¦ ≤ a^osc(1 + e^osc), ¦a^osc - a¦ + ¦e^osc - e¦ ≤ A_elem μ, perihelion and aphelion errors ≤ A_osc μ, osculating gaps ≥ d_⋆/2, d_pair/2 (as in LP1, spatial carriers)
CONSTANT_SCOPE: μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger
FROZEN_ANCHOR_ID: planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger.v1
FROZEN_ABI_SHA256: 19e891f2585d908488b799d192ba8ab04ef0bc73374739a9e998330fad54f00b
DEPS: lpM:T19#spatial_strongAMD_exponentialSafety, lpM:s1:half-integer, lpM:s1:dioph#IsDiophantine, lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:model#IsSpatialMovingSolutionOn, lpM:L1#IsSpatialNewtonSolutionOn, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerEnergy, lpM:s1:model#spatialMasses, lpM:s1:model#SpatialMovingUniqueOn, lpM:L16:defs#spatialOscEcc, lpM:L16:defs#spatialOscEnergy, lpM:L1#spatialSourceBarycentricPositions, lpM:L1#spatialSourceBarycentricVelocities, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerApo, lpM:s1:elements#spatialSourceKeplerAxis, lpM:s1:elements#spatialSourceKeplerEccVector, lpM:s1:elements#spatialSourceKeplerPeri, lpM:L16:defs#spatialSourceOscApo, lpM:L16:defs#spatialSourceOscAxis, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#spatialSourceOscEccVector, lpM:L16:defs#spatialSourceOscEnergy, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase, lpM:s1:elements#spatialSourceStrongAMD, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T19#spatial_strongAMD_exponentialSafety | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | LP2 with τ = n - 1/2
EDGE: lpM:s1:half-integer | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | τ = n - 1/2 > n - 1 and 1/(2(τ+1)) = 1/(2n+1)
EDGE: lpM:s1:dioph#IsDiophantine | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses IsDiophantine
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses bodyVector3
EDGE: lpM:s1:model#IsSpatialMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses IsSpatialMovingSolutionOn
EDGE: lpM:L1#IsSpatialNewtonSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses IsSpatialNewtonSolutionOn
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialKeplerEnergy
EDGE: lpM:s1:model#spatialMasses | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialMasses
EDGE: lpM:s1:model#SpatialMovingUniqueOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses SpatialMovingUniqueOn
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialOscEcc
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialOscEnergy
EDGE: lpM:L1#spatialSourceBarycentricPositions | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceBarycentricPositions
EDGE: lpM:L1#spatialSourceBarycentricVelocities | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceBarycentricVelocities
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerApo | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerApo
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerAxis
EDGE: lpM:s1:elements#spatialSourceKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerEccVector
EDGE: lpM:s1:elements#spatialSourceKeplerPeri | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerPeri
EDGE: lpM:L16:defs#spatialSourceOscApo | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscApo
EDGE: lpM:L16:defs#spatialSourceOscAxis | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscAxis
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#spatialSourceOscEccVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscEccVector
EDGE: lpM:L16:defs#spatialSourceOscEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscEnergy
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses SpatialSourceOsculatingPhase
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceStrongAMD
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses AdjIdx
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses AdjIdx.upperIdx
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses chamber
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses orderedStrongThreshold
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger (KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger
NOTE: Anchor LP2-H: the half-integer corollary (MAIN §1 L93) of LP2

NODE: lp3:s1.1#planetaryTimeExponent
KIND: definition
TITLE: planetaryTimeExponent (reused)
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.1@L69-L70
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.planetaryTimeExponent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ (typing data)
SOURCE_QUANTIFIERS: for every n
SOURCE_CONCLUSION: a_n = 2/(6n² - 3n + 14) (Nek77 (12.4), n counts planets, not total canonical pairs.)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean
FROZEN_DECL: KAM.Planetary.planetaryTimeExponent
FROZEN_ANCHOR_ID: planetary.d25.planetaryTimeExponent.v1
FROZEN_ABI_SHA256: d50f6181d0c0f28b50322ce65b1a9831d2ecd43ad5c2c9e3941105da2d0eb152
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planetaryTimeExponent (KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.planetaryTimeExponent.v1, bound as an LP anchor node (Q6); equal to the track-N partial exponents (LP3-PLAN §1.1)

NODE: lp3:s1.1#planetaryDriftExponent
KIND: definition
TITLE: planetaryDriftExponent (reused)
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.1@L69-L70
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.planetaryDriftExponent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ (typing data)
SOURCE_QUANTIFIERS: for every n
SOURCE_CONCLUSION: b_n = 3/(6n² - 3n + 14) (Nek77 (12.5). No optimized exponent is asserted.)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlanetaryDriftExponent.lean
FROZEN_DECL: KAM.Planetary.planetaryDriftExponent
FROZEN_ANCHOR_ID: planetary.d25.planetaryDriftExponent.v1
FROZEN_ABI_SHA256: 96a0f584827900cd21aa60ad82436d7ab45e5e9ea813426b73f55a4ebc50fb97
DEPS: lp3:s1.1#planetaryTimeExponent
ROUTES: -
ROUTE_FOR: -
EDGE: lp3:s1.1#planetaryTimeExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s1.1@L69-L69 | the declaration uses planetaryTimeExponent
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planetaryDriftExponent (KAM/Frozen/Planetary/Defs/PlanetaryDriftExponent.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.planetaryDriftExponent.v1, bound as an LP anchor node (Q6); equal to the track-N partial exponents (LP3-PLAN §1.1)

NODE: lpM:T15#planar_strongAMD_exponentialSafety_noArith
KIND: theorem
TITLE: LP3-1: planar strong-AMD exponential safety without arithmetic hypothesis
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.2@L85-L126
PROOF_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L370
CONTRACT_ID: planetary.d59.planar_strongAMD_exponentialSafety_noArith
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ > 0 (no Diophantine hypothesis, no γ, τ); planar (d = 2)
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-a_n}): ∃ z, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: as LP1/LP2 (the moving solution, uniqueness, Newtonian reconstruction, ellipticity, Λ(t) ∈ Q, C(t) ≤ B(Λ(t)) - δ/2, (9), star and pair distances, osculating clauses and half gaps) with the drifts ‖Λ(t) - Λ(0)‖ ≤ A_Λ μ^{b_n}, ‖a(t) - a(0)‖ ≤ A_a μ^{b_n}, ¦C(t) - C(0)¦ ≤ nA_Λ μ^{b_n}; a_n = planetaryTimeExponent n, b_n = planetaryDriftExponent n
CONSTANT_SCOPE: the constants depend only on (n, ν, 𝒜, δ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith
FROZEN_ANCHOR_ID: planetary.d59.planar_strongAMD_exponentialSafety_noArith.v1
FROZEN_ABI_SHA256: b29ff03f40dc5f47b2ba0fae11d168ed7e2b83919b143d9d51cba0f1795d16f4
DEPS: lp3:s3#first-exit, lpM:L1, lpM:L16, lpM:L16#mu0-choice, lpM:L16#half-gaps, lp3:s2.4, lpM:T15#orientation, lpM:T15#chart-cover, lpM:L8, lpM:L16#sourceOscAxis_pos, lpM:L16#sourceOscPeri_le_planeLength, lpM:L16#planeLength_le_sourceOscApo, lpM:s1:model#actualMasses, lpM:L1#barycentricPositions, lpM:L1#barycentricVelocities, lpM:s1:model#bodyVector, lpM:s1:model#IsMovingSolutionOn, lpM:L1#IsNewtonSolutionOn, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:elements#keplerEnergy, lpM:s1:model#MovingUniqueOn, lpM:s1:model#Phase, lpM:s1:data#planeLength, lp3:s1.1#planetaryDriftExponent, lp3:s1.1#planetaryTimeExponent, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:L16:defs#oscEcc, lpM:L16:defs#oscEnergy, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceKeplerApo, lpM:s1:elements#sourceKeplerPeri, lpM:L16:defs#sourceOscApo, lpM:L16:defs#sourceOscAxis, lpM:L16:defs#sourceOscEcc, lpM:L16:defs#sourceOscEccVector, lpM:L16:defs#sourceOscEnergy, lpM:L16:defs#sourceOscPeri, lpM:L16:defs#SourceOsculatingPhase, lpM:s1:elements#sourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lp3:s3#first-exit | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the stopped first exit with the LP3 drift supplier
EDGE: lpM:L1 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | Newtonian reconstruction (Lemma 1)
EDGE: lpM:L16 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | Lemma 16: the osculating elements on Lemma 5's compact set (m = δ/2)
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)
EDGE: lpM:L16#half-gaps | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the osculating half gaps
EDGE: lp3:s2.4 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L359-L359 | hstop: the planar drift supplier (§2.4)
EDGE: lpM:T15#orientation | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | the orientation reduction (reused verbatim)
EDGE: lpM:T15#chart-cover | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | the Lemma 7 charts cover; C = ¦z¦²/2 in the prograde region
EDGE: lpM:L8 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the planar analytic domain (m = n)
EDGE: lpM:L16#sourceOscAxis_pos | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | a^osc > 0
EDGE: lpM:L16#sourceOscPeri_le_planeLength | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | a^osc(1 - e^osc) ≤ ¦q_i¦
EDGE: lpM:L16#planeLength_le_sourceOscApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | ¦q_i¦ ≤ a^osc(1 + e^osc)
EDGE: lpM:s1:model#actualMasses | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses actualMasses
EDGE: lpM:L1#barycentricPositions | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses barycentricPositions
EDGE: lpM:L1#barycentricVelocities | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses barycentricVelocities
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses bodyVector
EDGE: lpM:s1:model#IsMovingSolutionOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses IsMovingSolutionOn
EDGE: lpM:L1#IsNewtonSolutionOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses IsNewtonSolutionOn
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses keplerAction
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses keplerAxis
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses keplerEccVector
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses keplerEnergy
EDGE: lpM:s1:model#MovingUniqueOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses MovingUniqueOn
EDGE: lpM:s1:model#Phase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses Phase
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses planeLength
EDGE: lp3:s1.1#planetaryDriftExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses planetaryDriftExponent
EDGE: lp3:s1.1#planetaryTimeExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses planetaryTimeExponent
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses AdjIdx
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses AdjIdx.upperIdx
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses chamber
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses orderedStrongThreshold
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses oscEcc
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses oscEnergy
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses SourceCanonicalPhase
EDGE: lpM:s1:elements#sourceKeplerApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceKeplerApo
EDGE: lpM:s1:elements#sourceKeplerPeri | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceKeplerPeri
EDGE: lpM:L16:defs#sourceOscApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscApo
EDGE: lpM:L16:defs#sourceOscAxis | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscAxis
EDGE: lpM:L16:defs#sourceOscEcc | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscEcc
EDGE: lpM:L16:defs#sourceOscEccVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscEccVector
EDGE: lpM:L16:defs#sourceOscEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscEnergy
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscPeri
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses SourceOsculatingPhase
EDGE: lpM:s1:elements#sourceStrongAMD | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceStrongAMD
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith (KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith
NOTE: Anchor LP3-1 (D64). MAIN T15 without (5), the drift supplier Lemmas 12/13 replaced by the sealed partialConvex_nekhoroshev (LP3-PLAN §1-§3); the source is LP3-PLAN (D65 minimal model; no separate LP3 source note)

NODE: lpM:T19#spatial_strongAMD_exponentialSafety_noArith
KIND: theorem
TITLE: LP3-2: spatial strong-AMD exponential safety without arithmetic hypothesis
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.3@L128-L134
PROOF_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L370
CONTRACT_ID: planetary.d59.spatial_strongAMD_exponentialSafety_noArith
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ > 0 (no Diophantine hypothesis, no γ, τ); spatial (d = 3)
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-a_n}): ∃ z, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: as LP1/LP2 (the moving solution, uniqueness, Newtonian reconstruction, ellipticity, Λ(t) ∈ Q, C(t) ≤ B(Λ(t)) - δ/2, (9), star and pair distances, osculating clauses and half gaps) with the drifts ‖Λ(t) - Λ(0)‖ ≤ A_Λ μ^{b_n}, ‖a(t) - a(0)‖ ≤ A_a μ^{b_n}, ¦C(t) - C(0)¦ ≤ nA_Λ μ^{b_n}; a_n = planetaryTimeExponent n, b_n = planetaryDriftExponent n
CONSTANT_SCOPE: the constants depend only on (n, ν, 𝒜, δ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith
FROZEN_ANCHOR_ID: planetary.d59.spatial_strongAMD_exponentialSafety_noArith.v1
FROZEN_ABI_SHA256: 387059c68796b425889eee542afbb9b3989ebf833cec9afaae08be7faa931966
DEPS: lp3:s3#first-exit, lpM:L1, lpM:L16, lpM:L16#mu0-choice, lpM:L16#half-gaps, lp3:s2.5, lpM:T19#align, lpM:L17#deficit-identity, lpM:L18#rotation-invariance, lpM:L16#spatialSourceOscAxis_pos, lpM:L16#spatialSourceOscPeri_le_length, lpM:L16#spatialSourceOscApo_ge_length, lpM:L16#spatialSourceOscEnergy_neg, lpM:L16#spatialSourceOscEcc_lt_one, lpM:s1:model#Phase, lp3:s1.1#planetaryDriftExponent, lp3:s1.1#planetaryTimeExponent, lpM:s1:model#bodyVector3, lpM:s1:model#IsSpatialMovingSolutionOn, lpM:L1#IsSpatialNewtonSolutionOn, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerEnergy, lpM:s1:model#spatialMasses, lpM:s1:model#SpatialMovingUniqueOn, lpM:L16:defs#spatialOscEcc, lpM:L16:defs#spatialOscEnergy, lpM:L1#spatialSourceBarycentricPositions, lpM:L1#spatialSourceBarycentricVelocities, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerApo, lpM:s1:elements#spatialSourceKeplerAxis, lpM:s1:elements#spatialSourceKeplerEccVector, lpM:s1:elements#spatialSourceKeplerPeri, lpM:L16:defs#spatialSourceOscApo, lpM:L16:defs#spatialSourceOscAxis, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#spatialSourceOscEccVector, lpM:L16:defs#spatialSourceOscEnergy, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase, lpM:s1:elements#spatialSourceStrongAMD, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lp3:s3#first-exit | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the stopped first exit with the LP3 drift supplier
EDGE: lpM:L1 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | Newtonian reconstruction (Lemma 1)
EDGE: lpM:L16 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | Lemma 16: the osculating elements on Lemma 5's compact set (m = δ/2)
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)
EDGE: lpM:L16#half-gaps | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the osculating half gaps
EDGE: lp3:s2.5 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L359-L359 | hstop: the spatial drift supplier (§2.5)
EDGE: lpM:T19#align | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | the spatial rotation reduction (reused verbatim)
EDGE: lpM:L17#deficit-identity | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | C_{e_3} = ¦z¦²/2
EDGE: lpM:L18#rotation-invariance | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | back to the original frame
EDGE: lpM:L16#spatialSourceOscAxis_pos | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | a^osc > 0
EDGE: lpM:L16#spatialSourceOscPeri_le_length | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | a^osc(1 - e^osc) ≤ ¦q_i¦
EDGE: lpM:L16#spatialSourceOscApo_ge_length | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | ¦q_i¦ ≤ a^osc(1 + e^osc)
EDGE: lpM:L16#spatialSourceOscEnergy_neg | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | E^osc < 0
EDGE: lpM:L16#spatialSourceOscEcc_lt_one | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | e^osc < 1
EDGE: lpM:s1:model#Phase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses Phase
EDGE: lp3:s1.1#planetaryDriftExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses planetaryDriftExponent
EDGE: lp3:s1.1#planetaryTimeExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses planetaryTimeExponent
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses bodyVector3
EDGE: lpM:s1:model#IsSpatialMovingSolutionOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses IsSpatialMovingSolutionOn
EDGE: lpM:L1#IsSpatialNewtonSolutionOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses IsSpatialNewtonSolutionOn
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialKeplerEnergy
EDGE: lpM:s1:model#spatialMasses | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialMasses
EDGE: lpM:s1:model#SpatialMovingUniqueOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses SpatialMovingUniqueOn
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialOscEcc
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialOscEnergy
EDGE: lpM:L1#spatialSourceBarycentricPositions | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceBarycentricPositions
EDGE: lpM:L1#spatialSourceBarycentricVelocities | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceBarycentricVelocities
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerApo
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerAxis
EDGE: lpM:s1:elements#spatialSourceKeplerEccVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerEccVector
EDGE: lpM:s1:elements#spatialSourceKeplerPeri | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerPeri
EDGE: lpM:L16:defs#spatialSourceOscApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscApo
EDGE: lpM:L16:defs#spatialSourceOscAxis | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscAxis
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#spatialSourceOscEccVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscEccVector
EDGE: lpM:L16:defs#spatialSourceOscEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscEnergy
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses SpatialSourceOsculatingPhase
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceStrongAMD
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses AdjIdx
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses AdjIdx.upperIdx
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses chamber
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses orderedStrongThreshold
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith (KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith
NOTE: Anchor LP3-2 (D64). MAIN T19 without (5), drift supplier replaced as in LP3-1 (LP3-PLAN §2.5, §3)

NODE: lp3:s2.3
KIND: step
TITLE: fixed data F1-F7 and the cell-by-cell discharge of the premises of partialConvex_nekhoroshev
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.2@L177-L201
PROOF_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L203-L257
CONTRACT_ID: lp3:s2.3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data n ≥ 2, ν_i > 0 with max ν = 1, 𝒜 compact and ordered, δ > 0 (no γ, τ, no (5)); planar (the spatial version is §2.5)
SOURCE_QUANTIFIERS: fixed before μ and the initial state
SOURCE_CONCLUSION: the shared tube (U, r_g, Ω_B(4r_g) ≤ δ/16), the uniform holomorphic extension of the chart and perturbation, widths, a finite cover of 𝓛_δ by centres c_j with fast cells G_j ⊂ G'_j and slow sets D_j = {¦y¦²/2 < B(c_j) - 5δ/16}, the Kepler constants and the slow erosion gap are fixed; on every cell the premises of partialConvex_nekhoroshev hold (holomorphic, C², real, bounded Hessian, definite fast part of the Kepler h, partial perturbation P = fc/B_0, the Hamiltonian identity with the chart Hamiltonian); thresholds ν_0, μ_0, r(μ) = (B_0μ)^{b_n}, T(μ) ≤ the frozen horizon T_0 exp(cμ^{-a_n})
CONSTANT_SCOPE: all constants and the cover depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p0:partial, lpM:L8#shared-tube, lpM:L8, lpM:L5, lpM:s1:fast, lpM:ext-compact-cover, lpM:s1:thresholds#orderedStrongThreshold, lp3:s1.1#planetaryTimeExponent, lp3:s1.1#planetaryDriftExponent
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p0:partial | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L154-L154 | the premises of the imported theorem are read from its frozen interface (§2.1)
EDGE: lpM:L8#shared-tube | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L181-L181 | F1: the shared tube U, r_g and Ω_B(4r_g) ≤ δ/16 (N2)
EDGE: lpM:L8 | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L184-L184 | F2/F3: the uniform holomorphic extension, bounds and widths of Lemma 8
EDGE: lpM:L5 | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L198-L198 | F6: the Kepler constants of the safe compact set
EDGE: lpM:s1:fast | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L215-L215 | the Kepler fast part h and its definite Hessian (∂ω_i/∂I_i = -3ν_i³/I_i⁴)
EDGE: lpM:ext-compact-cover | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L190-L190 | F4: a finite cover of the compact 𝓛_δ by centres
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L194-L194 | F5: the slow levels B(c_j) - 5δ/16
EDGE: lp3:s1.1#planetaryTimeExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L248-L248 | the time exponent a_n = 2/(6n² - 3n + 14)
EDGE: lp3:s1.1#planetaryDriftExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L248-L248 | the drift exponent b_n = 3/(6n² - 3n + 14)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: LP3-PLAN §2.2-§2.3 (F1-F7 and the discharge cells) folded into one step (D65 minimal model)

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

<!-- BEGIN PROOF DEPGRAPH GENERATED -->
Regenerated by `proof_depgraph.py`; do not hand-edit.

### Dashboard

* Total nodes: **301**
* Frozen anchors: **149**
* Versioned statement contracts: **301**
* Total edges: **1161**
* Root-closure nodes: **301**
* Dependency leaves in root closure: **33**
* Assumption boundary leaves: **0**
* External boundary leaves: **12**
* Alternative routes: **2**
* Topology review queue: **229**
* Explicit source gaps: **4**
* Coverage items: **438**; excluded: **47**

### Roots

* `lpM:L4#orderedPairThreshold_isLeast` [PROPOSED; frozen] — contract `planetary.d59.orderedPairThreshold_isLeast@1`
* `lpM:L4#orderedPairThreshold_existsUnique_value` [PROPOSED; frozen] — contract `planetary.d59.orderedPairThreshold_existsUnique_value@1`
* `lpM:L4#orderedCrossThreshold_isLeast` [PROPOSED; frozen] — contract `planetary.d59.orderedCrossThreshold_isLeast@1`
* `lpM:L4#orderedStrongThreshold_isLeast` [PROPOSED; frozen] — contract `planetary.d59.orderedStrongThreshold_isLeast@1`
* `lpM:L3#sourceStrongAMD_nonneg` [REVIEWED; frozen] — contract `planetary.d59.sourceStrongAMD_nonneg@1`
* `lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD` [REVIEWED; frozen] — contract `planetary.d59.sum_action_mul_eccDeficit_le_sourceStrongAMD@1`
* `lpM:L2#sourceKepler_axis_pos` [REVIEWED; frozen] — contract `planetary.d59.sourceKepler_axis_pos@1`
* `lpM:L2#sourceKepler_ecc_le_one` [REVIEWED; frozen] — contract `planetary.d59.sourceKepler_ecc_le_one@1`
* `lpM:L2#sourceKeplerPeri_le_planeLength` [REVIEWED; frozen] — contract `planetary.d59.sourceKeplerPeri_le_planeLength@1`
* `lpM:L2#planeLength_le_sourceKeplerApo` [REVIEWED; frozen] — contract `planetary.d59.planeLength_le_sourceKeplerApo@1`
* `lpM:L16#sourceOscAxis_pos` [PROPOSED; frozen] — contract `planetary.d59.sourceOscAxis_pos@1`
* `lpM:L16#sourceOscPeri_pos` [PROPOSED; frozen] — contract `planetary.d59.sourceOscPeri_pos@1`
* `lpM:L16#sourceOscPeri_le_planeLength` [PROPOSED; frozen] — contract `planetary.d59.sourceOscPeri_le_planeLength@1`
* `lpM:L16#planeLength_le_sourceOscApo` [PROPOSED; frozen] — contract `planetary.d59.planeLength_le_sourceOscApo@1`
* `lpM:L2#spatialSourceKeplerAxis_pos` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceKeplerAxis_pos@1`
* `lpM:L2#spatialSourceKeplerAction_pos` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceKeplerAction_pos@1`
* `lpM:L2#spatialSourceKeplerAction_sq` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceKeplerAction_sq@1`
* `lpM:L2#spatialSourceKeplerEcc_sq` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceKeplerEcc_sq@1`
* `lpM:L2#spatialSourceKeplerEcc_nonneg` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceKeplerEcc_nonneg@1`
* `lpM:L2#spatialSourceKeplerEcc_le_one` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceKeplerEcc_le_one@1`
* `lpM:L2#spatialSourcePlanetAngularMomentum_length` [PROPOSED; frozen] — contract `planetary.d59.spatialSourcePlanetAngularMomentum_length@1`
* `lpM:L2#spatialSourcePlanetAngularMomentum_length_le` [PROPOSED; frozen] — contract `planetary.d59.spatialSourcePlanetAngularMomentum_length_le@1`
* `lpM:L2#spatialSourceKeplerPeri_le_length` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceKeplerPeri_le_length@1`
* `lpM:L2#spatialSourceKeplerApo_ge_length` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceKeplerApo_ge_length@1`
* `lpM:L3#spatialSourceStrongAMD_nonneg` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceStrongAMD_nonneg@1`
* `lpM:L3#spatialSourceAction_mul_eccDeficit_le` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceAction_mul_eccDeficit_le@1`
* `lpM:L16#spatialSourceOscParam_pos` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceOscParam_pos@1`
* `lpM:L16#spatialSourceOscEnergy_neg` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceOscEnergy_neg@1`
* `lpM:L16#spatialSourceOscEcc_lt_one` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceOscEcc_lt_one@1`
* `lpM:L16#spatialSourceOscEcc_nonneg` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceOscEcc_nonneg@1`
* `lpM:L16#spatialSourceOscAxis_pos` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceOscAxis_pos@1`
* `lpM:L16#spatialSourceOscPeri_pos` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceOscPeri_pos@1`
* `lpM:L16#spatialSourceOscPeri_le_length` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceOscPeri_le_length@1`
* `lpM:L16#spatialSourceOscApo_ge_length` [PROPOSED; frozen] — contract `planetary.d59.spatialSourceOscApo_ge_length@1`
* `lpM:L5#planar_strongAMD_barrier` [REVIEWED; frozen] — contract `planetary.d59.planar_strongAMD_barrier@1`
* `lpM:T15#planar_strongAMD_exponentialSafety` [PROPOSED; frozen] — contract `planetary.d59.planar_strongAMD_exponentialSafety@1`
* `lpM:T15#planar_strongAMD_exponentialSafety_halfInteger` [PROPOSED; frozen] — contract `planetary.d59.planar_strongAMD_exponentialSafety_halfInteger@1`
* `lpM:T19#spatial_strongAMD_exponentialSafety` [PROPOSED; frozen] — contract `planetary.d59.spatial_strongAMD_exponentialSafety@1`
* `lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger` [PROPOSED; frozen] — contract `planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger@1`
* `lpM:T15#planar_strongAMD_exponentialSafety_noArith` [PROPOSED; frozen] — contract `planetary.d59.planar_strongAMD_exponentialSafety_noArith@1`
* `lpM:T19#spatial_strongAMD_exponentialSafety_noArith` [PROPOSED; frozen] — contract `planetary.d59.spatial_strongAMD_exponentialSafety_noArith@1`

### Topology review queue

* `N:bpN:p0:partial` [PROPOSED] — [N] N-PARTIAL-CONVEX: partialConvex_nekhoroshev (sealed, root of graph N)
* `N:bpN:p11:nonresonant` [PROPOSED] — [N] Nonresonant stability in the extended phase space (KAM.Nekhoroshev.nonresonant)
* `lp3:s1.1#planetaryDriftExponent` [PROPOSED] — planetaryDriftExponent (reused)
* `lp3:s1.1#planetaryTimeExponent` [PROPOSED] — planetaryTimeExponent (reused)
* `lp3:s2.3` [PROPOSED] — fixed data F1-F7 and the cell-by-cell discharge of the premises of partialConvex_nekhoroshev
* `lp3:s2.4` [PROPOSED] — the LP3 drift supplier in the exact hstop shape (planar): drift <= r/2 on stopped orbits
* `lp3:s2.5` [PROPOSED] — spatial version of the drift supplier (k = 2n slow pairs, Lemma 17 chart)
* `lp3:s3#first-exit` [PROPOSED] — the stopped first exit (Lemma 14's argument) with r = (B_0 mu)^{b_n}, T = T(mu) and the LP3 drift supplier
* `lpM:L1#IsNewtonSolutionOn` [PROPOSED] — finite-interval Newton equations with masses m_j
* `lpM:L1#IsSpatialNewtonSolutionOn` [PROPOSED] — IsSpatialNewtonSolutionOn (spatial, d = 3)
* `lpM:L1#barycentricPositions` [PROPOSED] — barycentric positions x_0 = -mu sum nu_i q_i/M, x_i = x_0 + q_i
* `lpM:L1#barycentricVelocities` [PROPOSED] — barycentric velocities x_0' = -mu sum p_i/m_0, x_i' = p_i/m_i
* `lpM:L1#spatialBarycentricPositions` [PROPOSED] — spatialBarycentricPositions (spatial, d = 3)
* `lpM:L1#spatialBarycentricVelocities` [PROPOSED] — spatialBarycentricVelocities (spatial, d = 3)
* `lpM:L1#spatialSourceBarycentricPositions` [PROPOSED] — spatialSourceBarycentricPositions (spatial, d = 3)
* `lpM:L1#spatialSourceBarycentricVelocities` [PROPOSED] — spatialSourceBarycentricVelocities (spatial, d = 3)
* `lpM:L10` [PROPOSED] — Lemma 10: cohomological equation (26) and a controlled Lie step (27)
* `lpM:L10#flow-existence` [PROPOSED] — the flow exists for ¦t¦ <= 1: contraction on paths, holomorphy, inverse, reality, displacement, symplecticity
* `lpM:L10#homological` [PROPOSED] — chi_k = f_k/(i k.omega): (26), the scalar series and reality
* `lpM:L10#lie-flow-identification` [PROPOSED] — the Lie series represents the pullback by the flow; exact scalar identity
* `lpM:L10#lie-series-bound` [PROPOSED] — (28): (1/j!)¦¦ad_Y^j V¦¦_{rho-eta} <= (2eDu/eta)^j ¦¦V¦¦_rho
* `lpM:L10#remainder` [PROPOSED] — L_chi h_0 = -f^osc and the exact remainder (29); (27) with B_D = 16eD
* `lpM:L11` [PROPOSED] — Lemma 11: exponential normal form on the full slow set (30)-(31)
* `lpM:L11#composition` [PROPOSED] — Phi = phi_0 o ... o phi_{N-1}: (31) with Z = g_N, R = f_N; displacement <= 2 q_D/N <= 1/32
* `lpM:L11#induction` [PROPOSED] — g_{j+1} = g_j + <f_j>: ¦X_g¦ <= 2 eps, angle independent; induction on j
* `lpM:L11#inverse` [PROPOSED] — the inverse on D_{3/2} by negative-time flows in reverse order, values in D_2
* `lpM:L11#qD-choice` [PROPOSED] — q_D = min(c_D, 1/(6 B_D), 1/64): (30) validates every step and halves E_j
* `lpM:L11#step-estimate` [PROPOSED] — one Lie step with loss 1/N: u_j <= A N^tau eps 2^{-j}, E_{j+1} <= 3 B_D A eps N^{tau+1} E_j
* `lpM:L12` [PROPOSED] — Lemma 12: planetary scaling, exponential time and the drift (34)
* `lpM:L12#drift` [PROPOSED] — (34): transformed solution in D_2, integrate (33), errors r/16 + r/16: ¦¦I(t) - I^0¦¦ <= r/4
* `lpM:L12#kappa-choice` [PROPOSED] — (36): A M_1 kappa^{tau+1} <= q_D/2 implies (30); N >= kappa mu^{-a}/2, eps <= 1/8
* `lpM:L12#normal-form` [PROPOSED] — Lemma 11 with eps = M_1 sqrt(mu), N; Z := h_0 - h + Z gives (33) and ¦dJ/dt¦ <= r eps 2^{-N}
* `lpM:L12#perturbation-size` [PROPOSED] — ¦¦X_{H_mu - h_0}¦¦_3 <= M_1 sqrt(mu): h - h_0 of size r, mu f of size mu/r + mu/s + mu/b
* `lpM:L12#time-choice` [PROPOSED] — c = (log 2) kappa/4, so T_mu = exp(c mu^{-a}) <= 2^{N/2}
* `lpM:L13` [PROPOSED] — Lemma 13: checked reuse of the repository's finite-cutoff engine (nonresonant)
* `lpM:L13#conclusion` [PROPOSED] — (38): drift <= r/2 through (s_1 r/(5 eps)) exp(2 pi K s_1/6) >= exp(c_1 mu^{-a}) under stopped slow membership
* `lpM:L13#interface` [PROPOSED] — nonresonant's real slow set S is arbitrary: take S = the closed ball (21)
* `lpM:L13#numeric-hypotheses` [PROPOSED] — (37): K L r <= alpha/2, eps <= alpha r/(256 K), 64 pi m s_1 r <= w^2, 2 pi K s_1 >= 6
* `lpM:L13#period-one` [PROPOSED] — theta = lambda/(2 pi), slow rescaling ell = w/r, H-hat = H/(2 pi); bracket 2 pi/ell^2; same equations and time
* `lpM:L13#structural-hypotheses` [PROPOSED] — holomorphy, reality, periodicity, Fourier norm, widths, module {0}, tube inside (22), orbit-field equality
* `lpM:L14` [PROPOSED] — Lemma 14: first exit on the entire allowed secular ball (assembly, conditional on the chart)
* `lpM:L14#axis-drift` [PROPOSED] — ¦a_i(I) - a_i(I^0)¦ <= (2 I_max/min nu_i^2) ¦¦I - I^0¦¦: A_I = 1, A_a, T_0 = 1
* `lpM:L14#backward` [PROPOSED] — the backward direction by the same normal-form estimate with ¦t¦ and backward continuation
* `lpM:L14#centers` [PROPOSED] — by C >= 0, every admissible center I^0 lies in L_delta
* `lpM:L14#choices` [PROPOSED] — shared compact neighborhood U of L_delta; mu_0 so that the radius r has its tube in U and (39)
* `lpM:L14#improvement` [PROPOSED] — the drift supplier improves the action bound (r/4 or r/2); (13), (17), (39) give AMD margin >= 3 delta/4
* `lpM:L14#maximal-solution` [PROPOSED] — the initial state is collision-free (Lemma 5, m = delta); the unique maximal solution exists
* `lpM:L14#no-exit` [PROPOSED] — a forward end t_* <= T_mu is impossible: Lemma 5 compact set, Lemma 6 continuation, persisting improved bounds
* `lpM:L14#route-L12` [PROPOSED] — drift supplier Lemma 12: r = sqrt(mu), improvement to r/4 up to T_mu = exp(c mu^{-a})
* `lpM:L14#route-L13` [PROPOSED] — drift supplier Lemma 13 (Lean route): r = D_0 sqrt(mu), improvement to r/2 up to exp(c_1 mu^{-a})
* `lpM:L14#separation` [PROPOSED] — separation constants of Lemma 5 with m = delta/2, d_star = a_min delta^2/(8 I_max^2) (41); all pairs separated
* `lpM:L14#stopped-membership` [PROPOSED] — (40) on the stopped interval gives ¦z¦^2/2 = C < B(I^0) - 7 delta/16: every point lies in D_1
* `lpM:L16` [PROPOSED] — Lemma 16: actual-velocity osculating ellipses (43), any dimension d
* `lpM:L16#element-error` [PROPOSED] — ¦V_i - v_i¦ <= n P mu, ¦k_i - 1¦ <= mu; expansion: ¦E^osc - E¦ + ¦e^osc - e¦ <= A_0 mu
* `lpM:L16#elliptic` [PROPOSED] — E^osc <= -1/(4 a_max) for small mu_0; reciprocal identity: axis estimate; ¦e^osc - e¦ <= ¦e^osc vec - e vec¦; e^osc < 1
* `lpM:L16#endpoint-estimate` [PROPOSED] — expansion of the products: ¦a^osc(1 +- e^osc) - a(1 +- e)¦ <= A_osc mu
* `lpM:L16#half-gaps` [PROPOSED] — subtracting the endpoint errors: osculating star gap >= d_star/2, adjacent gaps >= d_pair/2
* `lpM:L16#mu0-choice` [PROPOSED] — final mu_0: A_osc mu_0 <= d_star/2 and 2 A_osc mu_0 <= d_pair/2 (N10)
* `lpM:L16#planeLength_le_sourceOscApo` [PROPOSED] — ¦q_i¦ <= a_i^osc(1 + e_i^osc) on source osculating phases
* `lpM:L16#sourceOscAxis_pos` [PROPOSED] — a_i^osc > 0 on source osculating phases
* `lpM:L16#sourceOscPeri_le_planeLength` [PROPOSED] — a_i^osc(1 - e_i^osc) <= ¦q_i¦ on source osculating phases
* `lpM:L16#sourceOscPeri_pos` [PROPOSED] — a_i^osc(1 - e_i^osc) > 0 on source osculating phases
* `lpM:L16#spatialSourceOscApo_ge_length` [PROPOSED] — ¦q_i¦ ≤ a_i^osc(1 + e_i^osc) (d = 3)
* `lpM:L16#spatialSourceOscAxis_pos` [PROPOSED] — 0 < a_i^osc (d = 3)
* `lpM:L16#spatialSourceOscEcc_lt_one` [PROPOSED] — e_i^osc < 1 (d = 3)
* `lpM:L16#spatialSourceOscEcc_nonneg` [PROPOSED] — 0 ≤ e_i^osc (d = 3)
* `lpM:L16#spatialSourceOscEnergy_neg` [PROPOSED] — E_i^osc < 0 (d = 3)
* `lpM:L16#spatialSourceOscParam_pos` [PROPOSED] — 0 < k_i (d = 3)
* `lpM:L16#spatialSourceOscPeri_le_length` [PROPOSED] — a_i^osc(1 - e_i^osc) ≤ ¦q_i¦ (d = 3)
* `lpM:L16#spatialSourceOscPeri_pos` [PROPOSED] — 0 < a_i^osc(1 - e_i^osc) (d = 3)
* `lpM:L16#tangent-ellipse` [PROPOSED] — the two-body ellipse with position q_i, velocity V_i, parameter k_i; Lemma 2 with parameter k_i: it contains q_i
* `lpM:L16:defs` [PROPOSED] — actual-velocity osculating elements (42), any dimension d
* `lpM:L16:defs#SourceOsculatingPhase` [PROPOSED] — source osculating phases (nu > 0, mu > 0, q_i != 0, E^osc < 0, e^osc < 1)
* `lpM:L16:defs#SpatialOscPhase` [PROPOSED] — SpatialOscPhase (spatial, d = 3)
* `lpM:L16:defs#SpatialSourceOsculatingPhase` [PROPOSED] — SpatialSourceOsculatingPhase (spatial, d = 3)
* `lpM:L16:defs#spatialOscApo` [PROPOSED] — spatialOscApo (spatial, d = 3)
* `lpM:L16:defs#spatialOscAxis` [PROPOSED] — spatialOscAxis (spatial, d = 3)
* `lpM:L16:defs#spatialOscEcc` [PROPOSED] — spatialOscEcc (spatial, d = 3)
* `lpM:L16:defs#spatialOscEccVector` [PROPOSED] — spatialOscEccVector (spatial, d = 3)
* `lpM:L16:defs#spatialOscEnergy` [PROPOSED] — spatialOscEnergy (spatial, d = 3)
* `lpM:L16:defs#spatialOscParam` [PROPOSED] — spatialOscParam (spatial, d = 3)
* `lpM:L16:defs#spatialOscPeri` [PROPOSED] — spatialOscPeri (spatial, d = 3)
* `lpM:L16:defs#spatialOscVelocity` [PROPOSED] — spatialOscVelocity (spatial, d = 3)
* `lpM:L16:defs#spatialSourceOscApo` [PROPOSED] — spatialSourceOscApo (spatial, d = 3)
* `lpM:L16:defs#spatialSourceOscAxis` [PROPOSED] — spatialSourceOscAxis (spatial, d = 3)
* `lpM:L16:defs#spatialSourceOscEcc` [PROPOSED] — spatialSourceOscEcc (spatial, d = 3)
* `lpM:L16:defs#spatialSourceOscEccVector` [PROPOSED] — spatialSourceOscEccVector (spatial, d = 3)
* `lpM:L16:defs#spatialSourceOscEnergy` [PROPOSED] — spatialSourceOscEnergy (spatial, d = 3)
* `lpM:L16:defs#spatialSourceOscParam` [PROPOSED] — spatialSourceOscParam (spatial, d = 3)
* `lpM:L16:defs#spatialSourceOscPeri` [PROPOSED] — spatialSourceOscPeri (spatial, d = 3)
* `lpM:L17` [PROPOSED] — Lemma 17: regular spatial Poincare coordinates on the prograde region (44)-(45)
* `lpM:L17#deficit-identity` [PROPOSED] — fixed-plane deficit C_{e_3} = sum I_i - L.e_3 = ¦z¦^2/2 (summing (45))
* `lpM:L17#inverse` [PROPOSED] — inverse from w-hat = (q x p)/G: c, u, v reconstruct R; Lemma 7's inverse gives x, y, lambda
* `lpM:L17#rotation` [PROPOSED] — (46): R from t = (u,-v,0)/(2 sqrt G); R orthogonal, det 1, q x p = G R e_3 gives (45)
* `lpM:L17#symplectic` [PROPOSED] — p.dq = I dlambda + Gamma d(-varpi) + Z d(-h_n) + d(2Ie sin E); density of e > 0, Z > 0
* `lpM:L18` [PROPOSED] — Lemma 18: spatial whole-sublevel complex domain (47), m = 2n
* `lpM:L18#alignment` [PROPOSED] — one fixed rotation per solution takes L/¦L¦ to e_3; C_{e_3} = C along it; Lemma 17 covers it
* `lpM:L18#extension` [PROPOSED] — Lemma 8's gluing, uniform widths and complex denominators verbatim in 6n coordinates
* `lpM:L18#margins` [PROPOSED] — Gamma_i + Z_i <= I_i - 3 delta/16: G_i, H_i >= 3 delta/16, c_i^2 > 1/2
* `lpM:L18#rotation-invariance` [PROPOSED] — scalar products and potentials are invariant under a simultaneous rotation: bounds independent of the frame
* `lpM:L18#whole-ball-safe` [PROPOSED] — fixed-plane deficit = ¦z¦^2/2 >= sum I_i D(e_i): Lemma 5 applies on the whole ball
* `lpM:L2#spatialSourceKeplerAction_pos` [PROPOSED] — 0 < Λ_i (d = 3)
* `lpM:L2#spatialSourceKeplerAction_sq` [PROPOSED] — Λ_i^2 = ν_i^2 a_i (d = 3)
* `lpM:L2#spatialSourceKeplerApo_ge_length` [PROPOSED] — ¦q_i¦ ≤ a_i(1 + e_i) (d = 3)
* `lpM:L2#spatialSourceKeplerAxis_pos` [PROPOSED] — 0 < a_i (d = 3)
* `lpM:L2#spatialSourceKeplerEcc_le_one` [PROPOSED] — e_i ≤ 1 (d = 3)
* `lpM:L2#spatialSourceKeplerEcc_nonneg` [PROPOSED] — 0 ≤ e_i (d = 3)
* `lpM:L2#spatialSourceKeplerEcc_sq` [PROPOSED] — e_i^2 = 1 - ¦L_i¦^2/Λ_i^2 (d = 3)
* `lpM:L2#spatialSourceKeplerPeri_le_length` [PROPOSED] — a_i(1 - e_i) ≤ ¦q_i¦ (d = 3)
* `lpM:L2#spatialSourcePlanetAngularMomentum_length` [PROPOSED] — ¦L_i¦ = Λ_i √(1 - e_i^2) (d = 3)
* `lpM:L2#spatialSourcePlanetAngularMomentum_length_le` [PROPOSED] — ¦L_i¦ ≤ Λ_i (d = 3)
* `lpM:L3` [PROPOSED] — Lemma 3: exact angular momentum and the AMD identity (static and dynamic parts)
* `lpM:L3#planar-orientation` [PROPOSED] — planar case: orient so that L > 0; all scalar L_i are then positive
* `lpM:L3#projections` [PROPOSED] — 0 <= I_i - H_i, sum = C, so H_i >= I_i - C (> 0, >= m)
* `lpM:L3#spatialSourceAction_mul_eccDeficit_le` [PROPOSED] — Σ_i Λ_i(1 - √(1 - e_i^2)) ≤ C (d = 3)
* `lpM:L3#spatialSourceStrongAMD_nonneg` [PROPOSED] — 0 ≤ C (d = 3)
* `lpM:L4` [PROPOSED] — Lemma 4: attained, positive, continuous thresholds and (14)
* `lpM:L4#competitor` [PROPOSED] — competitor (0, 1 - alpha): B_ij <= I_j D(1 - alpha) < I_j, proving (14)
* `lpM:L4#contact-param` [PROPOSED] — (15): contact parameterized over t in [0,1]
* `lpM:L4#contact-reduction` [PROPOSED] — scaling a feasible point to contact does not increase the objective
* `lpM:L4#continuity` [PROPOSED] — continuity of B_ij and B on Q via uniform continuity on compact neighborhoods
* `lpM:L4#feasible-compact` [PROPOSED] — the feasible set is closed and nonempty and the objective continuous: minimum attained
* `lpM:L4#orderedCrossThreshold_isLeast` [PROPOSED] — B_cross(I) is the attained minimum of the adjacent pair thresholds
* `lpM:L4#orderedPairThreshold_existsUnique_value` [PROPOSED] — the pair minimum value is the unique least value
* `lpM:L4#orderedPairThreshold_isLeast` [PROPOSED] — B_ij(I) is the attained minimum of the pair objective over the feasible set
* `lpM:L4#orderedStrongThreshold_isLeast` [PROPOSED] — B(I) is the attained minimum of the adjacent thresholds and the actions
* `lpM:L4#positivity` [PROPOSED] — a zero minimum cannot give contact; finite minima stay positive
* `lpM:L5` [PROPOSED] — Lemma 5: the uniform strong barrier (any dimension d)
* `lpM:L5#gap-positive` [PROPOSED] — a nonpositive adjacent gap would be feasible, so C >= B_{i,i+1} >= B: contradiction
* `lpM:L6` [PROPOSED] — Lemma 6: the moving threshold (17) and continuation
* `lpM:L6#backward` [PROPOSED] — replacing the vector field by its negative gives the backward assertion
* `lpM:L6#continuation` [PROPOSED] — limit at a finite endpoint, local solution there and gluing; ellipticity is not lost
* `lpM:L6#local-existence` [PROPOSED] — Lemma 5 compact set, bounded field and derivative, Picard contraction, uniqueness
* `lpM:L6#moving-threshold` [PROPOSED] — (17) from the identity of (13) and B(I^0) <= B(I(t)) + Omega_B(r)
* `lpM:L6#shared-U` [PROPOSED] — compact neighborhood U of the compact set inside the chamber; modulus Omega_B -> 0
* `lpM:L7` [PROPOSED] — Lemma 7: a regular planar canonical chart
* `lpM:L7#chart-formula` [PROPOSED] — (19): the chart q = a(A c(F) - (k,l)), p = nu A c'(F)/(sqrt(a) D_F)
* `lpM:L7#inverse` [PROPOSED] — analytic inverse: a, I, G from energy and momentum, (k,l) from the eccentricity vector, lambda from (18)
* `lpM:L7#kepler-equation` [PROPOSED] — (18): unique eccentric longitude F, analytic in the data, F(lambda + 2 pi) = F(lambda) + 2 pi
* `lpM:L7#rotated-form` [PROPOSED] — (20) for e > 0; energy -nu^3/(2I^2), angular momentum G = I - Gamma, eccentricity vector (k,l); e = 0 by continuity
* `lpM:L7#symplectic` [PROPOSED] — p.dq = I dlambda + Gamma d(-varpi) + d(2Ie sin E): the chart is symplectic
* `lpM:L8` [PROPOSED] — Lemma 8: a whole-sublevel planar analytic neighborhood (21)-(22)
* `lpM:L8#compact-real-set` [PROPOSED] — the set of (I^0, I, z, lambda) with one closed angle cell is compact; the chart is analytic near it
* `lpM:L8#denominators` [PROPOSED] — Re(w.w) >= d^2/2 for every star and pair denominator; holomorphic square root, reciprocal <= sqrt 2/d
* `lpM:L8#empty-case` [PROPOSED] — L_delta empty: no initial state satisfies (6); otherwise L_delta is compact
* `lpM:L8#exact-split` [PROPOSED] — the product chart gives (4): chart Hamiltonian h(I) + mu f, no truncation
* `lpM:L8#gluing` [PROPOSED] — glue local extensions on complex balls (identity theorem, finite subcover): single-valued on the angle torus
* `lpM:L8#newton-extension` [PROPOSED] — uniform complex extension of the solution of (18): radii rho, eta, contraction by 1/2
* `lpM:L8#real-margin` [PROPOSED] — real tube: sum Gamma_i <= B(I) - 3 delta/16, Gamma_i < I_i, phases safe by Lemma 5, e <= e_* < 1
* `lpM:L8#shared-tube` [PROPOSED] — compact chamber neighborhood U and width r_g: 4r_g tube in U, Omega_B(4 r_g) <= delta/16
* `lpM:L8#widths` [PROPOSED] — Cauchy bounds on a smaller compact complex neighborhood; choice of r_*, s, b (r_* <= 4 r_g) and M
* `lpM:L9` [PROPOSED] — Lemma 9: Fourier, Cauchy and commutator estimates in the norm (24)
* `lpM:L9#banach-algebra` [PROPOSED] — products have convolution coefficients: the Banach-algebra estimate
* `lpM:L9#cauchy-derivative` [PROPOSED] — Cauchy: derivative bound 1/sigma in scaled action and slow coordinates; angle factor 1/(e sigma)
* `lpM:L9#commutator` [PROPOSED] — (25): ¦¦[V,W]¦¦_{rho-sigma} <= (2D/sigma) ¦¦V¦¦_rho ¦¦W¦¦_rho
* `lpM:L9#domains` [PROPOSED] — the complex domains D_rho (23): action, angle-strip and slow max-norm tube
* `lpM:L9#norm` [PROPOSED] — scaled components and the weighted Fourier norm (24)
* `lpM:L9#projections-tail` [PROPOSED] — monotonicity; mean and complementary projections have norm <= 1; tail bound e^{-sigma s K}
* `lpM:L9#sup-to-fourier` [PROPOSED] — contour shift: a sup bound M on width 4s gives ¦V_k¦ <= M e^{-4s¦k¦_1}, hence ¦¦V¦¦_3 <= M((1+e^{-s})/(1-e^{-s}))^n
* `lpM:T15` [PROPOSED] — Theorem 15: planar nonresonant exponential safety (the §1 conclusion for d = 2)
* `lpM:T15#apply-L14` [PROPOSED] — Lemma 14 with the Lemma 7 product chart and Lemma 8 (m = n): (7)-(9) in the plane
* `lpM:T15#chart-cover` [PROPOSED] — the product of the Lemma 7 charts covers every initial state; C = sum Gamma_i = ¦z¦^2/2 in the prograde region
* `lpM:T15#orientation` [PROPOSED] — Lemma 3: L != 0, all L_i of its sign; reverse the plane so that the sign is positive (H, constants invariant)
* `lpM:T15#osculating` [PROPOSED] — Lemma 16 on the Lemma 5 compact set (m = delta/2) gives the osculating conclusion
* `lpM:T15#planar_strongAMD_exponentialSafety` [PROPOSED] — LP1: planar strong-AMD exponential safety (Theorem 15 with Lemma 16)
* `lpM:T15#planar_strongAMD_exponentialSafety_halfInteger` [PROPOSED] — LP1-H: LP1 at tau = n - 1/2 (exponent 1/(2n+1))
* `lpM:T15#planar_strongAMD_exponentialSafety_noArith` [PROPOSED] — LP3-1: planar strong-AMD exponential safety without arithmetic hypothesis
* `lpM:T15#reconstruction` [PROPOSED] — Lemma 1 reconstructs the exact Newtonian motion (masses 1, mu nu_i)
* `lpM:T19` [PROPOSED] — Theorem 19: spatial nonresonant exponential safety (the §1 conclusion for d = 3)
* `lpM:T19#align` [PROPOSED] — Lemma 18 aligns the frame, gives the ball (47) and the collar; Lemma 17 symplectic chart; (1), (4) exact
* `lpM:T19#apply-L14` [PROPOSED] — n fast angles, 2n slow pairs; ¦z(t)¦^2/2 = C(t) by conservation; Lemma 14 proves (7)-(9)
* `lpM:T19#osculating` [PROPOSED] — Lemma 16 in dimension three: the osculating conclusion
* `lpM:T19#reconstruction` [PROPOSED] — Lemma 1 reconstructs the exact Newtonian solution (d = 3)
* `lpM:T19#spatial_strongAMD_exponentialSafety` [PROPOSED] — LP2: spatial strong-AMD exponential safety (Theorem 19 with Lemma 16)
* `lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger` [PROPOSED] — LP2-H: LP2 at tau = n - 1/2 (exponent 1/(2n+1))
* `lpM:T19#spatial_strongAMD_exponentialSafety_noArith` [PROPOSED] — LP3-2: spatial strong-AMD exponential safety without arithmetic hypothesis
* `lpM:T19#unrotate` [PROPOSED] — the inverse fixed rotation returns to the original frame without changing any inequality
* `lpM:ext-cauchy-estimates` [PROPOSED] — Cauchy's integral formula and estimates; holomorphic square root on a half plane
* `lpM:ext-compact-cover` [PROPOSED] — finite subcover of a compact set
* `lpM:ext-fourier-contour` [PROPOSED] — Fourier coefficients of periodic holomorphic maps and the contour shift
* `lpM:ext-ftc` [PROPOSED] — fundamental theorem of calculus (zero derivative on an interval)
* `lpM:ext-holomorphic-limit` [PROPOSED] — uniform limits of holomorphic maps are holomorphic
* `lpM:ext-identity-theorem` [PROPOSED] — identity theorem for analytic maps on a connected domain
* `lpM:s1:chamber#chamber` [PROPOSED] — the action chamber Q
* `lpM:s1:data#spaceDot` [PROPOSED] — spaceDot (spatial, d = 3)
* `lpM:s1:data#spaceLength` [PROPOSED] — spaceLength (spatial, d = 3)
* `lpM:s1:data#spaceSq` [PROPOSED] — spaceSq (spatial, d = 3)
* `lpM:s1:dioph#IsDiophantine` [PROPOSED] — (gamma, tau)-Diophantine vector: gamma/¦k¦_1^tau <= ¦k.omega¦ for k != 0
* `lpM:s1:elements#SourceCanonicalPhase` [PROPOSED] — source canonical phases (nu > 0, q_i != 0, E_i < 0)
* `lpM:s1:elements#SpatialElliptic` [PROPOSED] — SpatialElliptic (spatial, d = 3)
* `lpM:s1:elements#SpatialNegativeEnergy` [PROPOSED] — SpatialNegativeEnergy (spatial, d = 3)
* `lpM:s1:elements#SpatialSourceCanonicalPhase` [PROPOSED] — SpatialSourceCanonicalPhase (spatial, d = 3)
* `lpM:s1:elements#angularMomentum3` [PROPOSED] — angularMomentum3 (spatial, d = 3)
* `lpM:s1:elements#keplerApo` [PROPOSED] — canonical aphelion radius a_i(1 + e_i)
* `lpM:s1:elements#planetAngularMomentum3` [PROPOSED] — planetAngularMomentum3 (spatial, d = 3)
* `lpM:s1:elements#sourceKeplerApo` [PROPOSED] — canonical aphelion on source canonical phases
* `lpM:s1:elements#sourceStrongAMD` [PROPOSED] — strong AMD C on source canonical phases
* `lpM:s1:elements#spaceCross` [PROPOSED] — spaceCross (spatial, d = 3)
* `lpM:s1:elements#spatialKeplerAction` [PROPOSED] — spatialKeplerAction (spatial, d = 3)
* `lpM:s1:elements#spatialKeplerApo` [PROPOSED] — spatialKeplerApo (spatial, d = 3)
* `lpM:s1:elements#spatialKeplerAxis` [PROPOSED] — spatialKeplerAxis (spatial, d = 3)
* `lpM:s1:elements#spatialKeplerEccVector` [PROPOSED] — spatialKeplerEccVector (spatial, d = 3)
* `lpM:s1:elements#spatialKeplerEnergy` [PROPOSED] — spatialKeplerEnergy (spatial, d = 3)
* `lpM:s1:elements#spatialKeplerPeri` [PROPOSED] — spatialKeplerPeri (spatial, d = 3)
* `lpM:s1:elements#spatialSourceAngularMomentum` [PROPOSED] — spatialSourceAngularMomentum (spatial, d = 3)
* `lpM:s1:elements#spatialSourceKeplerAction` [PROPOSED] — spatialSourceKeplerAction (spatial, d = 3)
* `lpM:s1:elements#spatialSourceKeplerApo` [PROPOSED] — spatialSourceKeplerApo (spatial, d = 3)
* `lpM:s1:elements#spatialSourceKeplerAxis` [PROPOSED] — spatialSourceKeplerAxis (spatial, d = 3)
* `lpM:s1:elements#spatialSourceKeplerEcc` [PROPOSED] — spatialSourceKeplerEcc (spatial, d = 3)
* `lpM:s1:elements#spatialSourceKeplerEccVector` [PROPOSED] — spatialSourceKeplerEccVector (spatial, d = 3)
* `lpM:s1:elements#spatialSourceKeplerPeri` [PROPOSED] — spatialSourceKeplerPeri (spatial, d = 3)
* `lpM:s1:elements#spatialSourcePlanetAngularMomentum` [PROPOSED] — spatialSourcePlanetAngularMomentum (spatial, d = 3)
* `lpM:s1:elements#spatialSourceStrongAMD` [PROPOSED] — spatialSourceStrongAMD (spatial, d = 3)
* `lpM:s1:elements#strongAMD` [PROPOSED] — strong AMD C = sum Lambda_i - ¦L¦
* `lpM:s1:elements#totalMomentum` [PROPOSED] — total planar angular momentum L = sum_i q_i x p_i
* `lpM:s1:model` [PROPOSED] — the exact model: units, masses, symplectic form, Hamiltonian (1), domain, time
* `lpM:s1:model#IsHamiltonianSolutionOn` [PROPOSED] — IsHamiltonianSolutionOn (reused)
* `lpM:s1:model#IsMovingSolutionOn` [PROPOSED] — z solves the moving-Sun Hamiltonian (1) on J without collision
* `lpM:s1:model#IsSpatialMovingSolutionOn` [PROPOSED] — IsSpatialMovingSolutionOn (spatial, d = 3)
* `lpM:s1:model#MovingUniqueOn` [PROPOSED] — z agrees with every local solution from z(0) on the overlap with J
* `lpM:s1:model#SpatialMovingUniqueOn` [PROPOSED] — SpatialMovingUniqueOn (spatial, d = 3)
* `lpM:s1:model#SpatialNoCollision` [PROPOSED] — SpatialNoCollision (spatial, d = 3)
* `lpM:s1:model#actualMasses` [PROPOSED] — actual masses (m_0, mu m_1, ..., mu m_n)
* `lpM:s1:model#bodyVector3` [PROPOSED] — bodyVector3 (spatial, d = 3)
* `lpM:s1:model#spatialHamiltonian` [PROPOSED] — spatialHamiltonian (spatial, d = 3)
* `lpM:s1:model#spatialMasses` [PROPOSED] — spatialMasses (spatial, d = 3)
* `lpM:s1:thresholds#orderedStrongThreshold` [PROPOSED] — strong threshold B(I) = min(B_cross(I), B_star(I))
* `lpM:s1:thresholds#pairFeasible` [PROPOSED] — pair feasible set {(u,v) in [0,1]^2 : a_i(1+u) >= a_j(1-v)}
* `lpM:s1:thresholds#pairThreshold` [PROPOSED] — pair threshold helper: sInf of the objective over the feasible set

### Dependency leaves in root closure

* `N:bpN:p0:partial` [PROPOSED] — [N] N-PARTIAL-CONVEX: partialConvex_nekhoroshev (sealed, root of graph N)
* `N:bpN:p11:nonresonant` [PROPOSED] — [N] Nonresonant stability in the extended phase space (KAM.Nekhoroshev.nonresonant)
* `lp3:s1.1#planetaryTimeExponent` [PROPOSED] — planetaryTimeExponent (reused)
* `lpM:L16:defs#oscParam` [REVIEWED] — gravitational parameter k_i = 1 + mu nu_i
* `lpM:L16:defs#spatialOscParam` [PROPOSED] — spatialOscParam (spatial, d = 3)
* `lpM:L9#domains` [PROPOSED] — the complex domains D_rho (23): action, angle-strip and slow max-norm tube
* `lpM:ext-cauchy-estimates` [PROPOSED] — Cauchy's integral formula and estimates; holomorphic square root on a half plane
* `lpM:ext-compact-cover` [PROPOSED] — finite subcover of a compact set
* `lpM:ext-compact-min` [REVIEWED] — extreme values of a continuous function on a nonempty compact set
* `lpM:ext-fourier-contour` [PROPOSED] — Fourier coefficients of periodic holomorphic maps and the contour shift
* `lpM:ext-ftc` [PROPOSED] — fundamental theorem of calculus (zero derivative on an interval)
* `lpM:ext-gronwall` [REVIEWED] — uniqueness of ODE solutions by iterating the integral inequality
* `lpM:ext-heine-cantor` [REVIEWED] — Heine-Cantor: continuity on a compact set is uniform
* `lpM:ext-holomorphic-limit` [PROPOSED] — uniform limits of holomorphic maps are holomorphic
* `lpM:ext-identity-theorem` [PROPOSED] — identity theorem for analytic maps on a connected domain
* `lpM:ext-picard` [REVIEWED] — contraction mapping principle / Picard iteration for the integral equation
* `lpM:s1:data` [REVIEWED] — fixed data of track LP (n, nu, A, delta, gamma, tau, d; the two norms)
* `lpM:s1:data#planeDot` [REVIEWED] — Euclidean scalar product q . v
* `lpM:s1:data#planeSq` [REVIEWED] — squared Euclidean length ¦v¦^2
* `lpM:s1:data#spaceDot` [PROPOSED] — spaceDot (spatial, d = 3)
* `lpM:s1:data#spaceSq` [PROPOSED] — spaceSq (spatial, d = 3)
* `lpM:s1:dioph#IsDiophantine` [PROPOSED] — (gamma, tau)-Diophantine vector: gamma/¦k¦_1^tau <= ¦k.omega¦ for k != 0
* `lpM:s1:elements#planeCross` [REVIEWED] — planar angular momentum q x p (oriented scalar determinant)
* `lpM:s1:elements#spaceCross` [PROPOSED] — spaceCross (spatial, d = 3)
* `lpM:s1:model#IsHamiltonianSolutionOn` [PROPOSED] — IsHamiltonianSolutionOn (reused)
* `lpM:s1:model#Phase` [REVIEWED] — phase type: positions and scaled momenta
* `lpM:s1:model#actualMasses` [PROPOSED] — actual masses (m_0, mu m_1, ..., mu m_n)
* `lpM:s1:model#bodyVector` [REVIEWED] — planet i's planar coordinate vector
* `lpM:s1:model#bodyVector3` [PROPOSED] — bodyVector3 (spatial, d = 3)
* `lpM:s1:model#spatialMasses` [PROPOSED] — spatialMasses (spatial, d = 3)
* `lpM:s1:thresholds#AdjIdx` [REVIEWED] — index type of adjacent pairs (i, i+1)
* `lpM:s1:thresholds#actionAxis` [REVIEWED] — action axis a_i(I) = (I_i/nu_i)^2
* `lpM:s1:thresholds#eccDeficit` [REVIEWED] — eccentricity deficit D(u) = 1 - sqrt(1 - u^2)

### Assumption boundary leaves

* _(none)_

### External boundary leaves

* `N:bpN:p0:partial` [PROPOSED] — [N] N-PARTIAL-CONVEX: partialConvex_nekhoroshev (sealed, root of graph N)
* `N:bpN:p11:nonresonant` [PROPOSED] — [N] Nonresonant stability in the extended phase space (KAM.Nekhoroshev.nonresonant)
* `lpM:ext-cauchy-estimates` [PROPOSED] — Cauchy's integral formula and estimates; holomorphic square root on a half plane
* `lpM:ext-compact-cover` [PROPOSED] — finite subcover of a compact set
* `lpM:ext-compact-min` [REVIEWED] — extreme values of a continuous function on a nonempty compact set
* `lpM:ext-fourier-contour` [PROPOSED] — Fourier coefficients of periodic holomorphic maps and the contour shift
* `lpM:ext-ftc` [PROPOSED] — fundamental theorem of calculus (zero derivative on an interval)
* `lpM:ext-gronwall` [REVIEWED] — uniqueness of ODE solutions by iterating the integral inequality
* `lpM:ext-heine-cantor` [REVIEWED] — Heine-Cantor: continuity on a compact set is uniform
* `lpM:ext-holomorphic-limit` [PROPOSED] — uniform limits of holomorphic maps are holomorphic
* `lpM:ext-identity-theorem` [PROPOSED] — identity theorem for analytic maps on a connected domain
* `lpM:ext-picard` [REVIEWED] — contraction mapping principle / Picard iteration for the integral equation

### Uncovered graph nodes

* _(none)_

### Nodes outside every root closure

* _(none)_

### Explicit source gaps

* `lpM:L10#flow-existence` [PROPOSED] — the flow exists for ¦t¦ <= 1: contraction on paths, holomorphy, inverse, reality, displacement, symplecticity
* `lpM:L10#lie-flow-identification` [PROPOSED] — the Lie series represents the pullback by the flow; exact scalar identity
* `lpM:L14#maximal-solution` [PROPOSED] — the initial state is collision-free (Lemma 5, m = delta); the unique maximal solution exists
* `lpM:L3#deficit-zero-L` [REVIEWED] — the deficit bound when L = 0: C = sum I_i >= sum I_i D(e_i)
<!-- END PROOF DEPGRAPH GENERATED -->
