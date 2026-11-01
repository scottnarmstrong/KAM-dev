# Proof dependency database - track LP

GRAPH_VERSION: 4
ROOTS: lpM:L4#orderedPairThreshold_isLeast, lpM:L4#orderedPairThreshold_existsUnique_value, lpM:L4#orderedCrossThreshold_isLeast, lpM:L4#orderedStrongThreshold_isLeast, lpM:L3#sourceStrongAMD_nonneg, lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD, lpM:L2#sourceKepler_axis_pos, lpM:L2#sourceKepler_ecc_le_one, lpM:L2#sourceKeplerPeri_le_planeLength, lpM:L2#planeLength_le_sourceKeplerApo, lpM:L5#planar_strongAMD_barrier
CORPUS: docs/tracks/LP/source/{MAIN,AMENDMENTS}.md pinned by SHA-256 in docs/graph/LP/CORPUS.sha256 (MAIN 68e9167f...48c1b, 679 lines; AMENDMENTS c887d1e2...51881, 26 lines; N1 fixed in place, N2-N12 override the MAIN lines they cite); branch inp-lp-graph off inp after the D62 freeze (main f46b94fb); wave 1
CONVENTIONS: docs/graph/LP/SPEC.md §4: Euclidean ¦·¦ (planeLength, spaceLength) vs max norm on actions; period 2π angles (L13 converts to period one); G = 1, star mass 1, masses μν_i, max ν = 1, physical AMD μC; C = ΣI - ¦L¦ orientation-free (N8, OD-1); thresholds on the chamber carrier OrderedActions (n ≥ 2) with attained-minimum characterizations; C(0) ≤ B(I^0) - δ, conclusion C(t) ≤ B(I(t)) - δ/2; frozen keplerEnergy is ν_i E_i; MAIN lemmas are d-generic (d ∈ {2,3}) and dimension-specific frozen carriers attach at the anchors (SPEC §5 dimension rule); constants depend only on (d, n, ν, 𝒜, δ, γ, τ), L5's d_⋆, d_pair only on (n, ν, U, m), chosen before μ and the state
STANDING_ASSUMPTIONS: -
EXTERNAL_POLICY: a closed list of Mathlib-level externals lpM:ext-* fixed in SPEC §3 (KIND external, LEAN_STATUS EXTERNAL, located at the first appeal in MAIN); cross-track results that a proof uses are IMPORTED nodes N:<node> / P:<node> (KIND external, source fields copied from that track's graph, NOTE IMPORTED), never read through implementation files; any other unproved fact is a step node with NOTE SOURCE_GAP
FROZEN_ANCHORS: lpM:s1:thresholds#actionAxis, lpM:s1:chamber#chamber, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#pairThreshold, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:elements#strongAMD, lpM:s1:elements#keplerPeri, lpM:s1:elements#keplerApo, lpM:L16:defs#oscVelocity, lpM:L16:defs#oscParam, lpM:L16:defs#oscEnergy, lpM:L16:defs#oscAxis, lpM:L16:defs#oscEccVector, lpM:L16:defs#oscEcc, lpM:L16:defs#oscPeri, lpM:L16:defs#oscApo, lpM:s1:elements#SourceCanonicalPhase, lpM:L16:defs#SourceOsculatingPhase, lpM:s1:elements#sourceStrongAMD, lpM:s1:elements#sourceKeplerPeri, lpM:s1:elements#sourceKeplerApo, lpM:L16:defs#sourceOscVelocity, lpM:L16:defs#sourceOscParam, lpM:L16:defs#sourceOscEnergy, lpM:L16:defs#sourceOscAxis, lpM:L16:defs#sourceOscEccVector, lpM:L16:defs#sourceOscEcc, lpM:L16:defs#sourceOscPeri, lpM:L16:defs#sourceOscApo, lpM:L4#orderedPairThreshold_isLeast, lpM:L4#orderedPairThreshold_existsUnique_value, lpM:L4#orderedCrossThreshold_isLeast, lpM:L4#orderedStrongThreshold_isLeast, lpM:L3#sourceStrongAMD_nonneg, lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD, lpM:L2#sourceKepler_axis_pos, lpM:L2#sourceKepler_ecc_le_one, lpM:L2#sourceKeplerPeri_le_planeLength, lpM:L2#planeLength_le_sourceKeplerApo, lpM:L5#planar_strongAMD_barrier, lpM:s1:model#NoCollision, lpM:s1:model#Phase, lpM:s1:model#bodyVector, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:elements#keplerEnergy, lpM:s1:elements#planeCross, lpM:s1:elements#totalMomentum, lpM:s1:data#planeDot, lpM:s1:data#planeLength, lpM:s1:data#planeSq
FROZEN_MANIFEST: manifest/frozen-anchors.json | sha256:cee8ce3436601b48a03b0c8417b299470c6b6a64ac2ecc080d6b0a27675cded8
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#s1@L41-L41 | the ordering (I_i/ν_i)^2 is a_i(I)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the constraint is written with a_i(I), a_j(I)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the infimum runs over the feasible set
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the infimum is of the pair objective
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the carrier: action vectors in the chamber Q
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | B is the minimum of B_cross and B_star
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/source/MAIN.md#s1@L32-L32 | Λ_i = I_i is the Kepler action
EDGE: lpM:s1:elements#totalMomentum | docs/tracks/LP/source/MAIN.md#s1@L32-L32 | L is the total angular momentum
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L32-L32 | the phase type Phase (n*2) of planar positions and momenta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | a_i is the Kepler axis
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | e_i is the length of the eccentricity vector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | the Euclidean length ¦·¦ of a planar vector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the Euclidean length ¦·¦ of a planar vector
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the carrier requires negative Kepler energy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L32-L32 | the carrier of source canonical phases
EDGE: lpM:s1:elements#strongAMD | docs/tracks/LP/source/MAIN.md#s1@L32-L32 | the value is the strong AMD
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | the carrier of source canonical phases
EDGE: lpM:s1:elements#keplerApo | docs/tracks/LP/source/MAIN.md#s1@L88-L88 | the value is the canonical aphelion
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the Euclidean length ¦·¦ of a planar vector
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the carrier requires e_i^osc < 1
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the carrier requires E_i^osc < 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L16:defs#sourceOscVelocity
KIND: definition
TITLE: actual velocity V_i on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L512-L512
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceOscVelocity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceOsculatingPhase n ν μ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the actual velocity V_i of Lemma 16 on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscVelocity.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscVelocity
FROZEN_ANCHOR_ID: planetary.d59.sourceOscVelocity.v1
FROZEN_ABI_SHA256: d258d9a9606eaa563fe0236af8462a70887af4e1aa8cd4d66d5bcc26a1a0de59
DEPS: lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#oscVelocity
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the carrier of source osculating phases
EDGE: lpM:L16:defs#oscVelocity | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the value is the actual velocity V_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L16:defs#sourceOscParam
KIND: definition
TITLE: gravitational parameter k_i on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L512-L512
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.sourceOscParam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z : SourceOsculatingPhase n ν μ; i : Fin n (typing data)
SOURCE_QUANTIFIERS: for every n, ν, μ, z, i
SOURCE_CONCLUSION: the gravitational parameter k_i of Lemma 16 on the carrier
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Defs/SourceOscParam.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscParam
FROZEN_ANCHOR_ID: planetary.d59.sourceOscParam.v1
FROZEN_ABI_SHA256: 5a70f7aae97bf0d1eaff664dc304453c7f382487d72d581975032ace8c7020f2
DEPS: lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#oscParam
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the carrier of source osculating phases
EDGE: lpM:L16:defs#oscParam | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the value is the gravitational parameter k_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: reused frozen definition planetary.d25.planeCross.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:elements#totalMomentum
KIND: definition
TITLE: total planar angular momentum L = sum_i q_i x p_i
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L34-L34
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
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L34-L34 | planet i's coordinates q_i or p_i are extracted by bodyVector
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L34-L34 | the phase type Phase (n*2) of planar positions and momenta
EDGE: lpM:s1:elements#planeCross | docs/tracks/LP/source/MAIN.md#s1@L34-L34 | L_i = q_i × p_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
DEPS: lpM:L4#feasible-compact, lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the feasible set is compact and nonempty and the objective is continuous, so the minimum is attained
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the statement is on the chamber carrier I ∈ Q
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | B_ij occurs
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the feasible set occurs
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the objective occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: L4 says 'for all positive masses'; the frozen statement has no positive-mass premise and rests on the carrier I ∈ Q, which gives I_i > 0 and 0 ≤ a_i(I) < a_j(I) for i < j (so α = a_i/a_j ∈ [0,1))

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
DEPS: lpM:L4#feasible-compact, lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | existence: the minimum of the pair objective is attained; uniqueness of a least element is order-theoretic
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the statement is on the chamber carrier I ∈ Q
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the feasible set occurs
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#s1@L47-L47 | the objective occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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
DEPS: lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the statement is on the chamber carrier I ∈ Q
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | B_cross occurs
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the pair thresholds B_{i,i+1} occur
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L11-L11 | n ≥ 2 makes the adjacent family nonempty, so the finite minimum is attained
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: MAIN L55 asserts that the minima of (3) are attained and points to Lemma 4; for the finite minimum over the n - 1 adjacent pairs this is elementary (L4 L156: 'Finite minima preserve continuity and positivity')

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
DEPS: lpM:L4#orderedCrossThreshold_isLeast, lpM:s1:chamber#OrderedActions, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#orderedPairThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#orderedCrossThreshold_isLeast | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_cross(I) is attained among the adjacent thresholds
EDGE: lpM:s1:chamber#OrderedActions | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the statement is on the chamber carrier I ∈ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | B occurs
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#s1@L52-L52 | the pair thresholds B_{i,i+1} occur
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:ext-ftc
KIND: external
TITLE: fundamental theorem of calculus (zero derivative on an interval)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-ftc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f differentiable on a connected interval J with derivative 0 (or with integrable derivative)
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: f is constant on J (f(t) - f(s) = ∫_s^t f')
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: hypothesis package (SPEC §3): not a global standing assumption; a result that assumes part of it names that part in SOURCE_HYPOTHESES and depends on this node

NODE: lpM:s1:model
KIND: definition
TITLE: the exact model: units, masses, symplectic form, Hamiltonian (1), domain, time
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L24
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
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
DEPS: lpM:L3#static, lpM:L3#dynamic, lpM:L3#planar-orientation
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the static clauses: C ≥ 0, L ≠ 0, H_i > 0, H_i ≥ m and the inequality of (13)
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the dynamic clauses: conservation of L and the identity of (13)
EDGE: lpM:L3#planar-orientation | docs/tracks/LP/source/MAIN.md#L3@L137-L137 | the planar orientation clause
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L3#projections
KIND: step
TITLE: 0 <= I_i - H_i, sum = C, so H_i >= I_i - C (> 0, >= m)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L137
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#projections
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a negative-energy state with L ≠ 0); local data: L̂ = L/¦L¦, H_i = L_i·L̂
SOURCE_QUANTIFIERS: for every such state and every m > 0
SOURCE_CONCLUSION: H_i ≤ ¦L_i¦ ≤ I_i, so every I_i - H_i ≥ 0, and Σ_i (I_i - H_i) = C; hence H_i ≥ I_i - C ≥ B_⋆(I) - C, so H_i > 0 when C < B_⋆(I) and H_i ≥ m when C ≤ B_⋆(I) - m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#L-nonzero, lpM:L2, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#L-nonzero | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | L ≠ 0 (when C < B_⋆) makes L̂ and H_i defined
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | ¦L_i¦ ≤ I_i by (11)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | Σ_i H_i = ¦L¦ and C = Σ I_i - ¦L¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
DEPS: lpM:L3#projections
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#projections | docs/tracks/LP/source/MAIN.md#L3@L137-L137 | in the plane H_i = L_i·sign(L) > 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: consumed by Theorem 15's orientation step (wave 2; N8, OD-1)

NODE: lpM:L4
KIND: lemma
TITLE: Lemma 4: attained, positive, continuous thresholds and (14)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L146
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L156
CONTRACT_ID: lpM:L4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν_i > 0 for every i ('all positive masses'); I ∈ Q
SOURCE_QUANTIFIERS: for every ν > 0 and I ∈ Q (each pair i < j)
SOURCE_CONCLUSION: every minimum in (3) is attained and positive; each B_ij and B is continuous on Q; B_ij(I) < I_j and B(I) = min(B_cross(I), I_1) (14)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#feasible-compact, lpM:L4#continuity, lpM:L4#positivity, lpM:L4#competitor, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Q4 split (ruling root-b8): the statement clauses on radial contact and the Laskar-Petit identification (L143) and on geometric sharpness (L147) are not part of this record; no proof consumes them (N9). Their items lpM:L4#stmt-contact-lp and lpM:L4#stmt-sharpness and the supporting prose L158 and L160 are EXCLUDED

NODE: lpM:L4#feasible-compact
KIND: step
TITLE: the feasible set is closed and nonempty and the objective continuous: minimum attained
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
CONTRACT_ID: lpM:L4#feasible-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)
SOURCE_CONCLUSION: the feasible subset of [0,1]^2 is closed and nonempty, since (0, 1 - α) is feasible, and the objective I_i D(u) + I_j D(v) is continuous, so the pair minimum is attained
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#actionAxis, lpM:s1:chamber#chamber, lpM:ext-compact-min
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the feasible set
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the objective
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | continuity of D on [0,1]
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | α = a_i(I)/a_j(I)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | I ∈ Q gives α < 1
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | a continuous function on a nonempty compact set attains its minimum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L4#contact-reduction
KIND: step
TITLE: scaling a feasible point to contact does not increase the objective
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
CONTRACT_ID: lpM:L4#contact-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4); for every feasible (u,v)
SOURCE_CONCLUSION: replacing (u,v) by t(u,v) with t = (1 - α)/(αu + v) ≤ 1 gives contact a_i(1 + tu) = a_j(1 - tv) and does not increase the objective
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | feasibility and contact
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the objective
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | D is nondecreasing on [0,1]
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L4#contact-param
KIND: step
TITLE: (15): contact parameterized over t in [0,1]
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L150-L153
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L153
CONTRACT_ID: lpM:L4#contact-param
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4); t ∈ [0,1]
SOURCE_CONCLUSION: with m(α) = min(1, (1 - α)/α), u = m(α)t, v = 1 - α - αm(α)t (15) parameterizes the contact set over the fixed interval [0,1], so B_ij(I) = min_{t ∈ [0,1]} F(I,t) with F the objective along (15)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#contact-reduction, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#contact-reduction | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the minimum is attained on the contact set
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L151-L151 | F is the objective along (15)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L4#continuity
KIND: step
TITLE: continuity of B_ij and B on Q via uniform continuity on compact neighborhoods
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L154-L156
CONTRACT_ID: lpM:L4#continuity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j
SOURCE_QUANTIFIERS: for every ν > 0 and every I, J ∈ Q
SOURCE_CONCLUSION: the objective in (15) is jointly continuous in (I,t), hence uniformly continuous on K × [0,1] for every compact neighborhood K ⊂ Q; ¦min_t F(I,t) - min_t F(J,t)¦ ≤ sup_t ¦F(I,t) - F(J,t)¦ proves continuity of B_ij on Q; finite minima preserve continuity, so B_cross and B are continuous
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#contact-param, lpM:ext-heine-cantor, lpM:ext-compact-min, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#contact-param | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | B_ij is the minimum over t of the objective in (15)
EDGE: lpM:ext-heine-cantor | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | uniform continuity on compact sets
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L4@L155-L155 | the minima over t ∈ [0,1] are attained
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | compact neighborhoods inside the open chamber Q
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L155-L155 | continuity of B_ij
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | finite minimum B_cross
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | finite minimum B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L4#positivity
KIND: step
TITLE: a zero minimum cannot give contact; finite minima stay positive
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
CONTRACT_ID: lpM:L4#positivity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)
SOURCE_CONCLUSION: a zero minimum would require u = v = 0, which is not feasible because α < 1; so B_ij(I) > 0, and the finite minima B_cross(I), B(I) are positive (I_i > 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#feasible-compact, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | the minimum is attained at a feasible point
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | D(u) = 0 only at u = 0
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | (0,0) is not feasible when α < 1
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B is a finite minimum of positive numbers
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L4#competitor
KIND: step
TITLE: competitor (0, 1 - alpha): B_ij <= I_j D(1 - alpha) < I_j, proving (14)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L144-L146
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
CONTRACT_ID: lpM:L4#competitor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)
SOURCE_CONCLUSION: the feasible competitor (0, 1 - α) gives B_ij(I) ≤ I_j D(1 - α) < I_j; since B_{i,i+1}(I) < I_{i+1}, B(I) = min(B_cross(I), I_1) (14)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#feasible-compact, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | (0, 1 - α) is feasible
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | the objective at the competitor is I_j D(1 - α)
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | D(1 - α) < 1 for 0 < α
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_ij
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_cross in (14)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B in (14)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L5
KIND: lemma
TITLE: Lemma 5: the uniform strong barrier (any dimension d)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L175
CONTRACT_ID: lpM:L5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 and ν_i > 0 (lpM:s1:data); U ⊂ Q compact; m > 0
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0: there exist d_⋆ > 0 and d_pair > 0, then for every negative-energy state with I ∈ U and C ≤ B(I) - m and every list e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m
SOURCE_CONCLUSION: perihelia a_i(1 - e_i) ≥ d_⋆ and adjacent-annulus gaps a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair, for these states and for these lists; all these states belong to a compact subset of the nonsingular physical region and satisfy H_i ≥ m in their invariable frame
CONSTANT_SCOPE: d_⋆ and d_pair are uniform: they depend only on (n, ν, U, m)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5#gap-positive, lpM:L5#Km-compact, lpM:L5#empty-case, lpM:L5#perihelion, lpM:L5#compact-physical, lpM:L5#projection, lpM:s1:data, lpM:s1:elements, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#eccDeficit
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
DEPS: lpM:L3#static, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#actionAxis, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the inequality of (13), C ≥ Σ I_k D(e_k); its premise C < B_⋆ holds because C ≤ B(I) - m < B(I) ≤ B_⋆(I)
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | a nonpositive gap makes the pair feasible
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the feasible pair costs at least B_{i,i+1}(I)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | B_{i,i+1}(I) ≥ B(I)
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the constraint uses a_i(I) = (I_i/ν_i)^2
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the Kepler axis of a state equals a_i(I) since I_i = ν_i √a_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L6
KIND: lemma
TITLE: Lemma 6: the moving threshold (17) and continuation
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L179-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model (1) with its data (n, ν, d, μ > 0); 𝓛 ⊂ Q compact; δ > 0
SOURCE_QUANTIFIERS: for every compact 𝓛 ⊂ Q and δ > 0: there exist a compact neighborhood U ⊂ Q of 𝓛 and the modulus Ω_B; then for every r > 0 and every solution with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ, whose actions stay within r of I^0 with that tube in U, and every t
SOURCE_CONCLUSION: Ω_B(r) = sup{¦B(I) - B(J)¦ : I, J ∈ U, ‖I - J‖_∞ ≤ r} → 0 as r ↓ 0; C(t) ≤ B(I(t)) - δ + nr + Ω_B(r) (17); if nr + Ω_B(r) ≤ δ/2, the solution cannot terminate at a finite time while those action and ellipticity conditions hold; the same holds backwards in time
CONSTANT_SCOPE: U and Ω_B depend only on 𝓛 and the fixed data (chosen before the solution)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#shared-U, lpM:L6#moving-threshold, lpM:L6#continuation, lpM:L6#backward, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the neighborhood U and the modulus Ω_B
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | (17)
EDGE: lpM:L6#continuation | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | no finite-time termination
EDGE: lpM:L6#backward | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the backward assertion
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L6@L179-L179 | 𝓛, U ⊂ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L181-L181 | B and Ω_B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): U is the one compact set shared with Lemmas 8 and 14; it contains the closed 4r_g sup-norm tube about 𝓛_δ, its modulus Ω_B serves (17), Lemma 8 and (39), and r ≤ r_g (the consumers in wave 2 record where these requirements are used)

NODE: lpM:L6#shared-U
KIND: step
TITLE: compact neighborhood U of the compact set inside the chamber; modulus Omega_B -> 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L179-L182
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#shared-U
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n, ν, d, μ > 0); compact 𝓛 ⊂ Q; δ > 0; a solution with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ, whose actions stay within r of I^0 inside U
SOURCE_QUANTIFIERS: for every compact 𝓛 ⊂ Q, δ > 0, r > 0 and every such solution (inherited from lpM:L6)
SOURCE_CONCLUSION: a sufficiently small closed neighborhood U of 𝓛 inside the open chamber is compact, and uniform continuity of B on U gives Ω_B(r) → 0 as r ↓ 0
CONSTANT_SCOPE: U depends only on 𝓛 and the fixed data
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
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): the closed neighborhood is the one shared compact U containing the closed 4r_g-tube about 𝓛_δ

NODE: lpM:L6#moving-threshold
KIND: step
TITLE: (17) from the identity of (13) and B(I^0) <= B(I(t)) + Omega_B(r)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L183-L186
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#moving-threshold
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n, ν, d, μ > 0); compact 𝓛 ⊂ Q; δ > 0; a solution with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ, whose actions stay within r of I^0 inside U
SOURCE_QUANTIFIERS: for every compact 𝓛 ⊂ Q, δ > 0, r > 0 and every such solution (inherited from lpM:L6)
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
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L6#local-existence
KIND: step
TITLE: Lemma 5 compact set, bounded field and derivative, Picard contraction, uniqueness
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L187-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#local-existence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n, ν, d, μ > 0); compact 𝓛 ⊂ Q; δ > 0; a solution with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ, whose actions stay within r of I^0 inside U; nr + Ω_B(r) ≤ δ/2
SOURCE_QUANTIFIERS: for every compact 𝓛 ⊂ Q, δ > 0, r > 0 and every such solution (inherited from lpM:L6)
SOURCE_CONCLUSION: by (17), C ≤ B(I) - δ/2 along the solution, so Lemma 5 (with U and m = δ/2) supplies a compact nonsingular physical set with bounded momenta and energies separated from zero; the vector field of (1) and its derivative are bounded on a neighborhood of it; at every point of that set a local solution exists and is unique: on a small closed ball, z(t) = z_* + ∫_0^t X_H(z(u)) du is a contraction for times below the ball radius divided by the field bound and the inverse derivative bound (Picard iteration), and the same Lipschitz bound gives uniqueness by iterating the integral inequality
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5, lpM:L6#moving-threshold, lpM:s1:model, lpM:ext-picard, lpM:ext-gronwall
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | Lemma 5 supplies the compact nonsingular physical set (its premise C ≤ B(I) - δ/2 comes from (17))
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | (17) gives C ≤ B(I) - δ/2 along the solution
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the vector field X_H of (1)
EDGE: lpM:ext-picard | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | contraction mapping and Picard iteration
EDGE: lpM:ext-gronwall | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | uniqueness by iterating the integral inequality
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L6#continuation
KIND: step
TITLE: limit at a finite endpoint, local solution there and gluing; ellipticity is not lost
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L187-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#continuation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n, ν, d, μ > 0); compact 𝓛 ⊂ Q; δ > 0; a solution with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ, whose actions stay within r of I^0 inside U; nr + Ω_B(r) ≤ δ/2
SOURCE_QUANTIFIERS: for every compact 𝓛 ⊂ Q, δ > 0, r > 0 and every such solution (inherited from lpM:L6)
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
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the limit lies in the compact set of Lemma 5
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L6#backward
KIND: step
TITLE: replacing the vector field by its negative gives the backward assertion
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L187-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#backward
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n, ν, d, μ > 0); compact 𝓛 ⊂ Q; δ > 0; a solution with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ, whose actions stay within r of I^0 inside U
SOURCE_QUANTIFIERS: for every compact 𝓛 ⊂ Q, δ > 0, r > 0 and every such solution (inherited from lpM:L6); t ≤ 0
SOURCE_CONCLUSION: the assertions hold backwards in time
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
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -





<!-- BEGIN PROOF DEPGRAPH GENERATED -->
Regenerated by `proof_depgraph.py`; do not hand-edit.

### Dashboard

* Total nodes: **109**
* Frozen anchors: **59**
* Versioned statement contracts: **109**
* Total edges: **317**
* Root-closure nodes: **72**
* Dependency leaves in root closure: **11**
* Assumption boundary leaves: **0**
* External boundary leaves: **2**
* Alternative routes: **0**
* Topology review queue: **109**
* Explicit source gaps: **1**
* Coverage items: **153**; excluded: **26**

### Roots

* `lpM:L4#orderedPairThreshold_isLeast` [PROPOSED; frozen] — contract `planetary.d59.orderedPairThreshold_isLeast@1`
* `lpM:L4#orderedPairThreshold_existsUnique_value` [PROPOSED; frozen] — contract `planetary.d59.orderedPairThreshold_existsUnique_value@1`
* `lpM:L4#orderedCrossThreshold_isLeast` [PROPOSED; frozen] — contract `planetary.d59.orderedCrossThreshold_isLeast@1`
* `lpM:L4#orderedStrongThreshold_isLeast` [PROPOSED; frozen] — contract `planetary.d59.orderedStrongThreshold_isLeast@1`
* `lpM:L3#sourceStrongAMD_nonneg` [PROPOSED; frozen] — contract `planetary.d59.sourceStrongAMD_nonneg@1`
* `lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD` [PROPOSED; frozen] — contract `planetary.d59.sum_action_mul_eccDeficit_le_sourceStrongAMD@1`
* `lpM:L2#sourceKepler_axis_pos` [PROPOSED; frozen] — contract `planetary.d59.sourceKepler_axis_pos@1`
* `lpM:L2#sourceKepler_ecc_le_one` [PROPOSED; frozen] — contract `planetary.d59.sourceKepler_ecc_le_one@1`
* `lpM:L2#sourceKeplerPeri_le_planeLength` [PROPOSED; frozen] — contract `planetary.d59.sourceKeplerPeri_le_planeLength@1`
* `lpM:L2#planeLength_le_sourceKeplerApo` [PROPOSED; frozen] — contract `planetary.d59.planeLength_le_sourceKeplerApo@1`
* `lpM:L5#planar_strongAMD_barrier` [PROPOSED; frozen] — contract `planetary.d59.planar_strongAMD_barrier@1`

### Topology review queue

* `lpM:L1` [PROPOSED] — Lemma 1: normalization and Newtonian reconstruction
* `lpM:L1#reconstruction` [PROPOSED] — explicit inverse: barycentric positions and velocities, Newton's equations
* `lpM:L1#reduction` [PROPOSED] — translation reduction with P_i = mu p_i, cancelling mu gives (1)
* `lpM:L1#velocity` [PROPOSED] — (10): Hamilton's equation for q_i, the actual velocity
* `lpM:L16:defs#SourceOsculatingPhase` [PROPOSED] — source osculating phases (nu > 0, mu > 0, q_i != 0, E^osc < 0, e^osc < 1)
* `lpM:L16:defs#oscApo` [PROPOSED] — osculating aphelion a_i^osc(1 + e_i^osc)
* `lpM:L16:defs#oscAxis` [PROPOSED] — osculating axis a_i^osc = -k_i/(2 E_i^osc)
* `lpM:L16:defs#oscEcc` [PROPOSED] — osculating eccentricity e_i^osc = ¦e_i^osc¦
* `lpM:L16:defs#oscEccVector` [PROPOSED] — osculating eccentricity vector
* `lpM:L16:defs#oscEnergy` [PROPOSED] — osculating energy E_i^osc = ¦V_i¦^2/2 - k_i/¦q_i¦
* `lpM:L16:defs#oscParam` [PROPOSED] — gravitational parameter k_i = 1 + mu nu_i
* `lpM:L16:defs#oscPeri` [PROPOSED] — osculating perihelion a_i^osc(1 - e_i^osc)
* `lpM:L16:defs#oscVelocity` [PROPOSED] — actual heliocentric velocity V_i = p_i/nu_i + mu sum_j p_j
* `lpM:L16:defs#sourceOscApo` [PROPOSED] — osculating aphelion on source osculating phases
* `lpM:L16:defs#sourceOscAxis` [PROPOSED] — osculating axis on source osculating phases
* `lpM:L16:defs#sourceOscEcc` [PROPOSED] — osculating eccentricity on source osculating phases
* `lpM:L16:defs#sourceOscEccVector` [PROPOSED] — osculating eccentricity vector on source osculating phases
* `lpM:L16:defs#sourceOscEnergy` [PROPOSED] — osculating energy on source osculating phases
* `lpM:L16:defs#sourceOscParam` [PROPOSED] — gravitational parameter k_i on source osculating phases
* `lpM:L16:defs#sourceOscPeri` [PROPOSED] — osculating perihelion on source osculating phases
* `lpM:L16:defs#sourceOscVelocity` [PROPOSED] — actual velocity V_i on source osculating phases
* `lpM:L2` [PROPOSED] — Lemma 2: elementary orbital identities (11)-(12)
* `lpM:L2#ecc-identity` [PROPOSED] — (11): e^2 = 1 + 2E¦q x v¦^2 = 1 - ¦q x v¦^2/a and ¦q x p¦ = I sqrt(1 - e^2)
* `lpM:L2#planeLength_le_sourceKeplerApo` [PROPOSED] — ¦q_i¦ <= a_i(1 + e_i) on source canonical phases
* `lpM:L2#radial-bounds` [PROPOSED] — (12): a(1-e) <= ¦q¦ <= a(1+e) and ¦p¦^2 = nu^2(2/¦q¦ - 1/a)
* `lpM:L2#sourceKeplerPeri_le_planeLength` [PROPOSED] — a_i(1 - e_i) <= ¦q_i¦ on source canonical phases
* `lpM:L2#sourceKepler_axis_pos` [PROPOSED] — a_i > 0 on source canonical phases
* `lpM:L2#sourceKepler_ecc_le_one` [PROPOSED] — e_i <= 1 on source canonical phases
* `lpM:L3` [PROPOSED] — Lemma 3: exact angular momentum and the AMD identity (static and dynamic parts)
* `lpM:L3#L-nonzero` [PROPOSED] — C < B_star forces L != 0
* `lpM:L3#amd-nonneg` [PROPOSED] — ¦L¦ <= sum ¦L_i¦ <= sum I_i, so C >= 0
* `lpM:L3#conservation` [PROPOSED] — dL/dt = 0: recoil term, central forces and pair torques vanish; constancy by FTC
* `lpM:L3#deficit` [PROPOSED] — H_i <= I_i sqrt(1 - e_i^2) gives C >= sum I_i D(e_i) (inequality of (13))
* `lpM:L3#deficit-zero-L` [PROPOSED] — the deficit bound when L = 0: C = sum I_i >= sum I_i D(e_i)
* `lpM:L3#dynamic` [PROPOSED] — Lemma 3, dynamic part: L is conserved and C(t) - C(0) = sum(I_i(t) - I_i(0))
* `lpM:L3#planar-orientation` [PROPOSED] — planar case: orient so that L > 0; all scalar L_i are then positive
* `lpM:L3#projections` [PROPOSED] — 0 <= I_i - H_i, sum = C, so H_i >= I_i - C (> 0, >= m)
* `lpM:L3#sourceStrongAMD_nonneg` [PROPOSED] — C >= 0 on source canonical phases
* `lpM:L3#static` [PROPOSED] — Lemma 3, static part: C >= 0, L != 0, positive projections, H_i >= m, inequality of (13)
* `lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD` [PROPOSED] — the deficit bound sum Lambda_i D(e_i) <= C on source canonical phases
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
* `lpM:L5#Km-compact` [PROPOSED] — K_m is compact by Lemma 4; d_pair is the minimum of the gaps over K_m
* `lpM:L5#bounds` [PROPOSED] — ¦q_i¦ <= 2 a_max and ¦p_i¦ <= nu_i sqrt(2/d_star) by (12)
* `lpM:L5#compact-physical` [PROPOSED] — energies <= -1/(2 a_max): a compact nonsingular physical set
* `lpM:L5#empty-case` [PROPOSED] — K_m empty: any positive constants, the assertions are vacuous
* `lpM:L5#gap-positive` [PROPOSED] — a nonpositive adjacent gap would be feasible, so C >= B_{i,i+1} >= B: contradiction
* `lpM:L5#pair-distances` [PROPOSED] — ¦q_i¦ >= d_star and ordered radial intervals give ¦q_j - q_i¦ >= d_pair
* `lpM:L5#perihelion` [PROPOSED] — (16): sqrt(1 - e_i^2) >= m/I_max and a_i(1 - e_i) >= a_min m^2/(2 I_max^2) =: d_star
* `lpM:L5#planar_strongAMD_barrier` [PROPOSED] — LP0: the planar sharp strong barrier (planar case of Lemma 5)
* `lpM:L5#projection` [PROPOSED] — H_i >= m by Lemma 3
* `lpM:L6` [PROPOSED] — Lemma 6: the moving threshold (17) and continuation
* `lpM:L6#backward` [PROPOSED] — replacing the vector field by its negative gives the backward assertion
* `lpM:L6#continuation` [PROPOSED] — limit at a finite endpoint, local solution there and gluing; ellipticity is not lost
* `lpM:L6#local-existence` [PROPOSED] — Lemma 5 compact set, bounded field and derivative, Picard contraction, uniqueness
* `lpM:L6#moving-threshold` [PROPOSED] — (17) from the identity of (13) and B(I^0) <= B(I(t)) + Omega_B(r)
* `lpM:L6#shared-U` [PROPOSED] — compact neighborhood U of the compact set inside the chamber; modulus Omega_B -> 0
* `lpM:ext-compact-min` [PROPOSED] — extreme values of a continuous function on a nonempty compact set
* `lpM:ext-ftc` [PROPOSED] — fundamental theorem of calculus (zero derivative on an interval)
* `lpM:ext-gronwall` [PROPOSED] — uniqueness of ODE solutions by iterating the integral inequality
* `lpM:ext-heine-cantor` [PROPOSED] — Heine-Cantor: continuity on a compact set is uniform
* `lpM:ext-picard` [PROPOSED] — contraction mapping principle / Picard iteration for the integral equation
* `lpM:s1:chamber#OrderedActions` [PROPOSED] — the carrier of action vectors in the chamber Q
* `lpM:s1:chamber#chamber` [PROPOSED] — the action chamber Q
* `lpM:s1:data` [PROPOSED] — fixed data of track LP (n, nu, A, delta, gamma, tau, d; the two norms)
* `lpM:s1:data#planeDot` [PROPOSED] — Euclidean scalar product q . v
* `lpM:s1:data#planeLength` [PROPOSED] — Euclidean length ¦v¦
* `lpM:s1:data#planeSq` [PROPOSED] — squared Euclidean length ¦v¦^2
* `lpM:s1:dioph` [PROPOSED] — the Diophantine condition (5) at omega(I^0); angles of period 2 pi
* `lpM:s1:elements` [PROPOSED] — canonical Kepler elements and the strong AMD (2), in dimension d
* `lpM:s1:elements#SourceCanonicalPhase` [PROPOSED] — source canonical phases (nu > 0, q_i != 0, E_i < 0)
* `lpM:s1:elements#keplerAction` [PROPOSED] — Kepler action I_i = Lambda_i = nu_i sqrt(a_i)
* `lpM:s1:elements#keplerApo` [PROPOSED] — canonical aphelion radius a_i(1 + e_i)
* `lpM:s1:elements#keplerAxis` [PROPOSED] — Kepler axis a_i = -1/(2 E_i)
* `lpM:s1:elements#keplerEccVector` [PROPOSED] — eccentricity vector e_i
* `lpM:s1:elements#keplerEnergy` [PROPOSED] — Kepler term nu_i E_i = ¦p_i¦^2/(2 nu_i) - nu_i/¦q_i¦
* `lpM:s1:elements#keplerPeri` [PROPOSED] — canonical perihelion radius a_i(1 - e_i)
* `lpM:s1:elements#planeCross` [PROPOSED] — planar angular momentum q x p (oriented scalar determinant)
* `lpM:s1:elements#sourceKeplerApo` [PROPOSED] — canonical aphelion on source canonical phases
* `lpM:s1:elements#sourceKeplerPeri` [PROPOSED] — canonical perihelion on source canonical phases
* `lpM:s1:elements#sourceStrongAMD` [PROPOSED] — strong AMD C on source canonical phases
* `lpM:s1:elements#strongAMD` [PROPOSED] — strong AMD C = sum Lambda_i - ¦L¦
* `lpM:s1:elements#totalMomentum` [PROPOSED] — total planar angular momentum L = sum_i q_i x p_i
* `lpM:s1:fast` [PROPOSED] — fast Hamiltonian h(I) and radian frequencies omega(I) (4)
* `lpM:s1:half-integer` [PROPOSED] — tau = n - 1/2 is admissible and gives exponent 1/(2n+1)
* `lpM:s1:model` [PROPOSED] — the exact model: units, masses, symplectic form, Hamiltonian (1), domain, time
* `lpM:s1:model#NoCollision` [PROPOSED] — collision-free configurations: q_i != 0, q_i != q_j
* `lpM:s1:model#Phase` [PROPOSED] — phase type: positions and scaled momenta
* `lpM:s1:model#bodyVector` [PROPOSED] — planet i's planar coordinate vector
* `lpM:s1:thresholds#AdjIdx` [PROPOSED] — index type of adjacent pairs (i, i+1)
* `lpM:s1:thresholds#AdjIdx.upperIdx` [PROPOSED] — upper index i+1 of an adjacent pair
* `lpM:s1:thresholds#actionAxis` [PROPOSED] — action axis a_i(I) = (I_i/nu_i)^2
* `lpM:s1:thresholds#eccDeficit` [PROPOSED] — eccentricity deficit D(u) = 1 - sqrt(1 - u^2)
* `lpM:s1:thresholds#orderedCrossThreshold` [PROPOSED] — cross threshold B_cross(I) = min_{i<n} B_{i,i+1}(I)
* `lpM:s1:thresholds#orderedPairThreshold` [PROPOSED] — pair threshold B_ij(I) on the chamber carrier
* `lpM:s1:thresholds#orderedStrongThreshold` [PROPOSED] — strong threshold B(I) = min(B_cross(I), B_star(I))
* `lpM:s1:thresholds#pairFeasible` [PROPOSED] — pair feasible set {(u,v) in [0,1]^2 : a_i(1+u) >= a_j(1-v)}
* `lpM:s1:thresholds#pairObjective` [PROPOSED] — pair objective I_i D(u) + I_j D(v)
* `lpM:s1:thresholds#pairThreshold` [PROPOSED] — pair threshold helper: sInf of the objective over the feasible set

### Dependency leaves in root closure

* `lpM:ext-compact-min` [PROPOSED] — extreme values of a continuous function on a nonempty compact set
* `lpM:ext-heine-cantor` [PROPOSED] — Heine-Cantor: continuity on a compact set is uniform
* `lpM:s1:data` [PROPOSED] — fixed data of track LP (n, nu, A, delta, gamma, tau, d; the two norms)
* `lpM:s1:data#planeDot` [PROPOSED] — Euclidean scalar product q . v
* `lpM:s1:data#planeSq` [PROPOSED] — squared Euclidean length ¦v¦^2
* `lpM:s1:elements#planeCross` [PROPOSED] — planar angular momentum q x p (oriented scalar determinant)
* `lpM:s1:model#Phase` [PROPOSED] — phase type: positions and scaled momenta
* `lpM:s1:model#bodyVector` [PROPOSED] — planet i's planar coordinate vector
* `lpM:s1:thresholds#AdjIdx` [PROPOSED] — index type of adjacent pairs (i, i+1)
* `lpM:s1:thresholds#actionAxis` [PROPOSED] — action axis a_i(I) = (I_i/nu_i)^2
* `lpM:s1:thresholds#eccDeficit` [PROPOSED] — eccentricity deficit D(u) = 1 - sqrt(1 - u^2)

### Assumption boundary leaves

* _(none)_

### External boundary leaves

* `lpM:ext-compact-min` [PROPOSED] — extreme values of a continuous function on a nonempty compact set
* `lpM:ext-heine-cantor` [PROPOSED] — Heine-Cantor: continuity on a compact set is uniform

### Uncovered graph nodes

* _(none)_

### Nodes outside every root closure

* `lpM:L1` [PROPOSED] — Lemma 1: normalization and Newtonian reconstruction
* `lpM:L1#reconstruction` [PROPOSED] — explicit inverse: barycentric positions and velocities, Newton's equations
* `lpM:L1#reduction` [PROPOSED] — translation reduction with P_i = mu p_i, cancelling mu gives (1)
* `lpM:L1#velocity` [PROPOSED] — (10): Hamilton's equation for q_i, the actual velocity
* `lpM:L16:defs#SourceOsculatingPhase` [PROPOSED] — source osculating phases (nu > 0, mu > 0, q_i != 0, E^osc < 0, e^osc < 1)
* `lpM:L16:defs#oscApo` [PROPOSED] — osculating aphelion a_i^osc(1 + e_i^osc)
* `lpM:L16:defs#oscAxis` [PROPOSED] — osculating axis a_i^osc = -k_i/(2 E_i^osc)
* `lpM:L16:defs#oscEcc` [PROPOSED] — osculating eccentricity e_i^osc = ¦e_i^osc¦
* `lpM:L16:defs#oscEccVector` [PROPOSED] — osculating eccentricity vector
* `lpM:L16:defs#oscEnergy` [PROPOSED] — osculating energy E_i^osc = ¦V_i¦^2/2 - k_i/¦q_i¦
* `lpM:L16:defs#oscParam` [PROPOSED] — gravitational parameter k_i = 1 + mu nu_i
* `lpM:L16:defs#oscPeri` [PROPOSED] — osculating perihelion a_i^osc(1 - e_i^osc)
* `lpM:L16:defs#oscVelocity` [PROPOSED] — actual heliocentric velocity V_i = p_i/nu_i + mu sum_j p_j
* `lpM:L16:defs#sourceOscApo` [PROPOSED] — osculating aphelion on source osculating phases
* `lpM:L16:defs#sourceOscAxis` [PROPOSED] — osculating axis on source osculating phases
* `lpM:L16:defs#sourceOscEcc` [PROPOSED] — osculating eccentricity on source osculating phases
* `lpM:L16:defs#sourceOscEccVector` [PROPOSED] — osculating eccentricity vector on source osculating phases
* `lpM:L16:defs#sourceOscEnergy` [PROPOSED] — osculating energy on source osculating phases
* `lpM:L16:defs#sourceOscParam` [PROPOSED] — gravitational parameter k_i on source osculating phases
* `lpM:L16:defs#sourceOscPeri` [PROPOSED] — osculating perihelion on source osculating phases
* `lpM:L16:defs#sourceOscVelocity` [PROPOSED] — actual velocity V_i on source osculating phases
* `lpM:L3` [PROPOSED] — Lemma 3: exact angular momentum and the AMD identity (static and dynamic parts)
* `lpM:L3#conservation` [PROPOSED] — dL/dt = 0: recoil term, central forces and pair torques vanish; constancy by FTC
* `lpM:L3#dynamic` [PROPOSED] — Lemma 3, dynamic part: L is conserved and C(t) - C(0) = sum(I_i(t) - I_i(0))
* `lpM:L3#planar-orientation` [PROPOSED] — planar case: orient so that L > 0; all scalar L_i are then positive
* `lpM:L6` [PROPOSED] — Lemma 6: the moving threshold (17) and continuation
* `lpM:L6#backward` [PROPOSED] — replacing the vector field by its negative gives the backward assertion
* `lpM:L6#continuation` [PROPOSED] — limit at a finite endpoint, local solution there and gluing; ellipticity is not lost
* `lpM:L6#local-existence` [PROPOSED] — Lemma 5 compact set, bounded field and derivative, Picard contraction, uniqueness
* `lpM:L6#moving-threshold` [PROPOSED] — (17) from the identity of (13) and B(I^0) <= B(I(t)) + Omega_B(r)
* `lpM:L6#shared-U` [PROPOSED] — compact neighborhood U of the compact set inside the chamber; modulus Omega_B -> 0
* `lpM:ext-ftc` [PROPOSED] — fundamental theorem of calculus (zero derivative on an interval)
* `lpM:ext-gronwall` [PROPOSED] — uniqueness of ODE solutions by iterating the integral inequality
* `lpM:ext-picard` [PROPOSED] — contraction mapping principle / Picard iteration for the integral equation
* `lpM:s1:dioph` [PROPOSED] — the Diophantine condition (5) at omega(I^0); angles of period 2 pi
* `lpM:s1:fast` [PROPOSED] — fast Hamiltonian h(I) and radian frequencies omega(I) (4)
* `lpM:s1:half-integer` [PROPOSED] — tau = n - 1/2 is admissible and gives exponent 1/(2n+1)

### Explicit source gaps

* `lpM:L3#deficit-zero-L` [PROPOSED] — the deficit bound when L = 0: C = sum I_i >= sum I_i D(e_i)
<!-- END PROOF DEPGRAPH GENERATED -->
