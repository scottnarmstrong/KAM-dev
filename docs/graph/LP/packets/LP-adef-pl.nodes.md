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
